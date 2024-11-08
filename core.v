`default_nettype none

module core (
    input wire i_clk,
    input wire i_rst_n,
    // imem interface - output 64 bit address, receive 32 bit data
    // immediately on the same cycle
    output wire [63:0] o_imem_addr,
    input wire [31:0] i_imem_data,
    // dmem interface - output 64 bit address and read/write enable, one of:
    // * receive 64 bit data on same cycle
    // * write 64 bit data, latched on next clock
    // * none, if no memory op this cycle
    output wire [7:0] o_dmem_rmask,
    output wire [7:0] o_dmem_wmask,
    output wire [63:0] o_dmem_addr,
    output wire [63:0] o_dmem_wdata,
    input wire [63:0] i_dmem_rdata,
    // purely for debug introspection
    // output wire [63 * 31:0] dbg_rdata,

    output wire rvfi_valid,
    output wire [63:0] rvfi_order,
    output wire [31:0] rvfi_insn,
    output wire rvfi_trap,
    output wire rvfi_halt,
    output wire rvfi_intr,
    output wire [1:0] rvfi_mode,
    output wire [1:0] rvfi_ixl,
    output wire [4:0] rvfi_rs1_addr,
    output wire [4:0] rvfi_rs2_addr,
    output wire [63:0] rvfi_rs1_rdata,
    output wire [63:0] rvfi_rs2_rdata,
    output wire [4:0] rvfi_rd_addr,
    output wire [63:0] rvfi_rd_wdata,
    output wire [63:0] rvfi_pc_rdata,
    output wire [63:0] rvfi_pc_wdata,
    output wire [63:0] rvfi_mem_addr,
    output wire [7:0] rvfi_mem_rmask,
    output wire [7:0] rvfi_mem_wmask,
    output wire [63:0] rvfi_mem_rdata,
    output wire [63:0] rvfi_mem_wdata
);
    // program counter control
    reg [63:0] pc;
    wire [63:0] next_pc;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            pc <= 64'h0;
        else
            pc <= next_pc;
    end

    // read from imem using PC as an address to get a single
    // 32 bit instruction word
    // same cycle/combinational - doesn't require clock pulse
    // which is quite unrealistic for synthesis but works for simulation
    assign o_imem_addr = pc;
    wire [31:0] inst = i_imem_data;

    wire valid, rd_wen;
    wire [4:0] rs1, rs2, rd;
    wire [31:0] imm;
    wire [2:0] funct3;
    wire op1_sel, op2_sel;
    wire [4:0] alu_op;
    wire [1:0] alu_mode;
    wire [7:0] mem_rmask, mem_wmask;
    wire mem_read, mem_write;
    wire branch, jump;
    wire [2:0] rd_sel;
    decoder id (
        .i_inst(inst),
        .o_valid(valid), .o_rd_wen(rd_wen),
        .o_rs1(rs1), .o_rs2(rs2), .o_rd(rd),
        .o_imm(imm),
        .o_funct3(funct3),
        .o_op1_sel(op1_sel), .o_op2_sel(op2_sel),
        .o_alu_op(alu_op), .o_alu_mode(alu_mode),
        .o_mem_rmask(mem_rmask), .o_mem_wmask(mem_wmask),
        .o_mem_read(mem_read), .o_mem_write(mem_write),
        .o_branch(branch), .o_jump(jump), .o_rd_sel(rd_sel)
    );

    // double read (asynchronous), single write (synchronous) register file
    // rd_wen defined above, tied directly to decoder
    wire [63:0] rd_wdata;
    wire [63:0] rs1_data, rs2_data;
    register_file rf (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .i_rs1(rs1), .i_rs2(rs2), .i_rd(rd),
        .i_wen(rd_wen && valid), .i_wdata(rd_wdata),
        .o_rs1(rs1_data), .o_rs2(rs2_data)
    );

    wire [63:0] alu_op1 = op1_sel ? pc : rs1_data;
    wire [63:0] sext_imm = {{32{imm[31]}}, imm};
    wire [63:0] alu_op2 = op2_sel ? sext_imm : rs2_data;
    wire [63:0] alu_result;
    alu alu (
        .i_op1(alu_op1), .i_op2(alu_op2),
        .i_op(alu_op), .i_mode(alu_mode),
        .o_result(alu_result)
    );

    // branch comparator
    wire beq  = rs1_data == rs2_data;
    wire blt  = $signed(rs1_data) < $signed(rs2_data);
    wire bltu = rs1_data < rs2_data;
    wire bsel = (funct3[2:1] == 2'b00 ? beq :
                ((funct3[2:1] == 2'b10) ? blt : bltu));
    wire take_branch = branch && (bsel ^ funct3[0]);

    wire [63:0] mem_addr_aligned = alu_result & ~64'h7;
    wire [7:0] mem_rmask_aligned = mem_rmask << alu_result[2:0];
    wire [7:0] mem_wmask_aligned = mem_wmask << alu_result[2:0];
    // both read and write to dmem are gated, since
    // even load has a "side effect" - address fault
    assign o_dmem_addr = mem_addr_aligned;
    assign o_dmem_wdata = rs2_data;
    assign o_dmem_rmask = mem_rmask_aligned;
    assign o_dmem_wmask = mem_wmask_aligned;

    // write to register one of:
    // * none (i.e. load, conditional branch)
    // * alu result
    // * memory load result
    // * pc (for jump and link)
    assign rd_wdata = rd_sel[0] ? alu_result :
                      (rd_sel[1] ? i_dmem_rdata : 
                      (rd_sel[2] ? (pc + 64'h4) : 64'h0));

    wire branch_aligned = take_branch ? !alu_result[1] : 1'b1;
    wire jump_aligned = jump ? !alu_result[1] : 1'b1;
    wire load_aligned = mem_read && (alu_result[2:0] == 3'b000);
    wire store_aligned = mem_write && (alu_result[2:0] == 3'b000);
    wire trap = !i_rst_n || !valid || !branch_aligned || !jump_aligned || !load_aligned || !store_aligned;

    // decide if next_pc should increment or jump
    assign next_pc = (take_branch || jump) ? (alu_result & ~64'b1) : (pc + 64'h4);

    reg [63:0] order;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            order <= 64'h0;
        else
            order <= order + 64'h1;
    end

    reg halt;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            halt <= 1'b0;
        else if (!valid || halt)
            halt <= 1'b1;
    end

    // retire exactly one instruction each cycle
    assign rvfi_valid = i_rst_n;
    assign rvfi_order = order; // in order execution
    assign rvfi_insn = inst;
    assign rvfi_trap = trap;
    assign rvfi_halt = halt;
    assign rvfi_intr = 1'b0; // TODO: trap handler needed?
    assign rvfi_mode = 2'b00; // 0 = U mode
    assign rvfi_ixl = 2'b01; // 1 = 32 bit
    assign rvfi_rs1_addr = rs1;
    assign rvfi_rs2_addr = rs2;
    assign rvfi_rs1_rdata = rs1_data;
    assign rvfi_rs2_rdata = rs2_data;
    assign rvfi_rd_addr = rd_wen ? rd : 5'd0;
    assign rvfi_rd_wdata = (rvfi_rd_addr == 5'd0) ? 64'h0 : rd_wdata;
    assign rvfi_pc_rdata = pc;
    assign rvfi_pc_wdata = next_pc;
    assign rvfi_mem_addr = o_dmem_addr;
    assign rvfi_mem_rmask = mem_rmask;
    assign rvfi_mem_wmask = mem_wmask;
    assign rvfi_mem_rdata = i_dmem_rdata;
    assign rvfi_mem_wdata = o_dmem_wdata;
endmodule

module register (
    input wire i_clk,
    input wire i_rst_n,
    input wire i_wen,
    input wire [63:0] i_wdata,
    output wire [63:0] o_rdata
);
    reg [63:0] register;

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            register <= 64'h0;
        else if (i_wen)
            register <= i_wdata;
    end

    assign o_rdata = register;
endmodule

module register_file (
    input wire i_clk,
    input wire i_rst_n,
    // input register indices
    input wire [4:0] i_rs1,
    input wire [4:0] i_rs2,
    input wire [4:0] i_rd,
    input wire i_wen,
    input wire [63:0] i_wdata,
    output wire [63:0] o_rs1,
    output wire [63:0] o_rs2
);
    // 64 bit x 32 deep single-cycle register file with two read lanes
    // and one write lane
    // x0 is hardwired to 64'h0
    wire [31:1] wen;
    wire [63:0] rdata[31:1];
    genvar i;
    generate
        for (i = 1; i < 32; i = i + 1) begin
            wire wen = i_wen && (i == i_rd);
            register entry (
                .i_clk(i_clk), .i_rst_n(i_rst_n),
                .i_wen(wen), .i_wdata(i_wdata), .o_rdata(rdata[i])
            );
        end
    endgenerate

    assign o_rs1 = (!i_rst_n || (i_rs1 == 5'd0)) ? 64'h0 : rdata[i_rs1];
    assign o_rs2 = (!i_rst_n || (i_rs2 == 5'd0)) ? 64'h0 : rdata[i_rs2];
endmodule

module decoder (
    input wire [31:0] i_inst,
    output wire o_valid,
    output wire o_rd_wen,
    output wire [4:0] o_rs1,
    output wire [4:0] o_rs2,
    output wire [4:0] o_rd,
    output wire [31:0] o_imm,
    output wire [2:0] o_funct3,
    output wire o_op1_sel, // selects between rs1 (0) and pc (1)
    output wire o_op2_sel, // selects between rs2 (0) and imm (1)
    output wire [4:0] o_alu_op,   // selects between major operations of the alu
    output wire [1:0] o_alu_mode, // selects between minor operations of the alu
    output wire [7:0] o_mem_rmask,
    output wire [7:0] o_mem_wmask,
    output wire o_mem_read,
    output wire o_mem_write,
    output wire o_branch,
    output wire o_jump,
    output wire [2:0] o_rd_sel  // 0 = alu, 1 = mem, 2 = pc
);
    wire [4:0] opcode = i_inst[6:2];
    wire [4:0] rd = i_inst[11:7];
    wire [4:0] rs1 = i_inst[19:15];
    wire [4:0] rs2 = i_inst[24:20];
    wire [2:0] funct3 = i_inst[14:12];
    wire [6:0] funct7 = i_inst[31:25];

    wire wide = i_inst[1:0] == 2'b11;

    // major opcode selection
    wire op_load     = wide && opcode == 5'b00000;
    wire op_misc_mem = wide && opcode == 5'b00011;
    wire op_op_imm   = wide && opcode == 5'b00100;
    wire op_auipc    = wide && opcode == 5'b00101;
    wire op_op_imm32 = wide && opcode == 5'b00110;
    wire op_store    = wide && opcode == 5'b01000;
    wire op_amo      = wide && opcode == 5'b01011;
    wire op_op       = wide && opcode == 5'b01100;
    wire op_lui      = wide && opcode == 5'b01101;
    wire op_op_32    = wide && opcode == 5'b01110;
    wire op_branch   = wide && opcode == 5'b11000;
    wire op_jalr     = wide && opcode == 5'b11001;
    wire op_jal      = wide && opcode == 5'b11011;
    wire op_system   = wide && opcode == 5'b11100;

    // branch funct3 selection
    wire branch_eq  = funct3 == 3'b000;
    wire branch_ne  = funct3 == 3'b001;
    wire branch_lt  = funct3 == 3'b100;
    wire branch_ge  = funct3 == 3'b101;
    wire branch_ltu = funct3 == 3'b110;
    wire branch_geu = funct3 == 3'b111;

    // arithmetic (op, op_imm) funct3/funct7 selection
    wire alu_funct7 = funct7 == 7'b0100000;
    wire alu_add  = (funct3 == 3'b000) && (format_i || !alu_funct7);
    wire alu_sub  = (funct3 == 3'b000) && !format_i && alu_funct7;
    wire alu_sll  = (funct3 == 3'b001) && !alu_funct7;
    wire alu_srl  = (funct3 == 3'b101) && !alu_funct7;
    wire alu_sra  = (funct3 == 3'b101) && alu_funct7;
    wire alu_slt  = (funct3 == 3'b010) && (format_i || !alu_funct7);
    wire alu_sltu = (funct3 == 3'b011) && (format_i || !alu_funct7);
    wire alu_xor  = (funct3 == 3'b100) && (format_i || !alu_funct7);
    wire alu_or   = (funct3 == 3'b110) && (format_i || !alu_funct7);
    wire alu_and  = (funct3 == 3'b111) && (format_i || !alu_funct7);

    // load funct3 selection
    wire load_b  = funct3 == 3'b000;
    wire load_h  = funct3 == 3'b001;
    wire load_w  = funct3 == 3'b010;
    wire load_bu = funct3 == 3'b100;
    wire load_hu = funct3 == 3'b101;

    // store funct3 selection
    wire store_b = funct3 == 3'b000;
    wire store_h = funct3 == 3'b001;
    wire store_w = funct3 == 3'b010;

    // immediate decoding
    wire format_r = op_op;
    wire format_i = op_op_imm || op_jalr || op_load;
    wire format_s = op_store;
    wire format_b = op_branch;
    wire format_u = op_lui || op_auipc;
    wire format_j = op_jal;

    wire format_sb = format_s | format_b;
    wire format_ij = format_i | format_j;
    wire format_uj = format_u | format_j;

    assign o_rs1 = rs1;
    assign o_rs2 = rs2;
    assign o_rd = rd;

    assign o_imm[0] = (format_s & i_inst[7]) | (format_i && i_inst[20]);
    assign o_imm[4:1] = ({4{format_sb}} & i_inst[11:8]) | ({4{format_ij}} & i_inst[24:21]);
    assign o_imm[10:5] = {6{!format_u}} & i_inst[30:25];
    assign o_imm[11] = format_b ? i_inst[7] : (format_j ? i_inst[20] : (format_u ? 1'b0 : i_inst[31]));
    assign o_imm[19:12] = format_uj ? i_inst[19:12] : {8{i_inst[31]}};
    assign o_imm[30:20] = format_u ? i_inst[30:20] : {11{i_inst[31]}};
    assign o_imm[31] = i_inst[31];

    assign o_funct3 = funct3;

    assign o_op1_sel = op_branch || op_auipc || op_jal;
    assign o_op2_sel = |{format_i, format_s, format_b, format_u, format_j};

    wire arith = op_op_imm || op_op;
    wire arith_adder = arith && (alu_add || alu_sub);
    assign o_alu_op[4] = op_lui;
    assign o_alu_op[3] = arith_adder || op_load || op_store || op_auipc || op_branch || op_jal || op_jalr;
    assign o_alu_op[2] = arith && (alu_sll || alu_srl || alu_sra);
    assign o_alu_op[1] = arith && (alu_slt || alu_sltu);
    assign o_alu_op[0] = arith && (alu_xor || alu_or || alu_and);
    wire [1:0] shift_mode = alu_sll ? 2'b00 : (alu_srl ? 2'b01 : 2'b10);
    assign o_alu_mode = o_alu_op[2] ? shift_mode : (arith_adder ? {1'b0, alu_sub} : ((op_auipc || op_branch || op_jal || op_jalr) ? 2'b00 : funct3[1:0]));

    assign o_mem_rmask[7:4] = 4'h0;
    assign o_mem_rmask[3:2] = op_load && load_w;
    assign o_mem_rmask[1]   = op_load && (load_w || load_h || load_hu);
    assign o_mem_rmask[0]   = op_load && (load_w || load_h || load_hu || load_b || load_bu);
    assign o_mem_wmask[7:4] = 4'h0;
    assign o_mem_wmask[3:2] = op_store && store_w;
    assign o_mem_wmask[1]   = op_store && (store_w || store_h);
    assign o_mem_wmask[0]   = op_store && (store_w || store_h || store_b);
    assign o_mem_read = op_load;
    assign o_mem_write = op_store;

    assign o_branch = op_branch;
    assign o_jump = op_jal || op_jalr;

    assign o_rd_wen = format_r || format_i || format_u || format_j;
    assign o_rd_sel[0] = format_r || format_u || op_op_imm;
    assign o_rd_sel[1] = op_load;
    assign o_rd_sel[2] = op_jal || op_jalr;

    wire branch_valid = branch_eq || branch_ne || branch_lt || branch_ge || branch_ltu || branch_geu;
    wire alu_valid = alu_add || alu_sub || alu_sll || alu_srl || alu_sra || alu_slt || alu_sltu || alu_xor || alu_or || alu_and;
    wire load_valid = load_b || load_h || load_w || load_bu || load_hu;
    wire store_valid = store_b || store_h || store_w;

    assign o_valid = (op_load && load_valid) || (op_op_imm && alu_valid) || op_auipc || (op_op && alu_valid) || (op_store && store_valid) || op_lui || (op_branch && branch_valid) || op_jalr || op_jal;
endmodule

module alu (
    input wire [63:0] i_op1,
    input wire [63:0] i_op2,
    // i_op2, add, shift, slt, bool
    input wire [4:0] i_op,
    input wire [1:0] i_mode,
    output wire [63:0] o_result
);
    // addition/subtraction
    wire sub = i_mode[0];
    wire [63:0] add_result = i_op1 + (i_op2 ^ {64{sub}}) + {63'h0, sub};
    // sll/srl/sra
    wire [5:0] shamt = i_op2[5:0];
    wire sll = i_mode == 2'b00;
    wire srl = i_mode == 2'b01;
    wire sra = i_mode == 2'b10;
    wire [63:0] shift_result = sll ? (i_op1 << shamt) :
                               (srl ? (i_op1 >> shamt) :
                               (sra ? ($signed(i_op1) >> shamt) : 64'h0));
    // slt/sltu
    wire sltu = i_mode[0];
    wire lt = sltu ? (i_op1 < i_op2) : ($signed(i_op1) < $signed(i_op2));
    wire [63:0] slt_result = {63'h0, lt};
    // xor/or/and
    wire [63:0] bool_result = ((i_op1 ^ i_op2) & ~{64{i_mode[0]}}) | ({64{i_mode[1]}} & i_op1 & i_op2);

    wire op_op2 = i_op[4];
    wire op_add = i_op[3];
    wire op_shift = i_op[2];
    wire op_slt = i_op[1];
    wire op_bool = i_op[0];
    assign o_result = op_op2 ? i_op2 :
                      (op_add ? add_result :
                      (op_shift ? shift_result :
                      (op_slt ? slt_result :
                      (op_bool ? bool_result : 64'h0))));
endmodule
