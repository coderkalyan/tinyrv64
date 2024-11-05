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
    output wire o_dmem_ren,
    output wire o_dmem_wen,
    output wire [63:0] o_dmem_addr,
    output wire [63:0] o_dmem_wdata,
    input wire [63:0] i_dmem_rdata
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
        .i_wen(rd_wen), .i_wdata(rd_wdata),
        .o_rs1(rs1_data), .o_rs2(rs2_data)
    );

    wire [63:0] alu_op1 = op1_sel ? pc : rs1_data;
    wire [63:0] alu_op2 = op2_sel ? imm : rs2_data;
    wire [63:0] alu_result;
    // wire alu_start = 1'b1;
    // wire alu_done;
    alu alu (
        // .i_clk(i_clk), .i_rst_n(i_rst_n),
        .i_op1(alu_op1), .i_op2(alu_op2), // .i_start(alu_start),
        .o_result(alu_result) //, .o_done(alu_done)
    );

    // branch comparator
    wire beq  = rs1_data == rs2_data;
    wire blt  = $signed(rs1_data) < $signed(rs2_data);
    wire bltu = rs1_data < rs2_data;
    wire bsel = (funct3[2:1] == 2'b00 ? beq :
                ((funct3[2:1] == 2'b10) ? blt : bltu));
    wire take_branch = branch && (bsel ^ funct3[0]);

    // both read and write to dmem are gated, since
    // even load has a "side effect" - address fault
    assign o_dmem_addr = alu_result;
    assign o_dmem_wdata = rs2_data;
    assign o_dmem_ren = mem_read;
    assign o_dmem_wen = mem_write;

    // write to register one of:
    // * none (i.e. load, conditional branch)
    // * alu result
    // * memory load result
    // * pc (for jump and link)
    assign rd_wdata = rd_sel[0] ? alu_result :
                      (rd_sel[1] ? i_dmem_rdata : 
                      (rd_sel[2] ? (pc + 64'h4) : 64'h0));


    // decide if next_pc should increment or jump
    assign next_pc = (branch || jump) ? alu_result : (pc + 64'h4);
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
        for (i = 1; i <= 31; i = i + 1) begin
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

    wire op_load     = opcode == 5'b00000;
    wire op_misc_mem = opcode == 5'b00011;
    wire op_op_imm   = opcode == 5'b00100;
    wire op_auipc    = opcode == 5'b00101;
    wire op_op_imm32 = opcode == 5'b00110;
    wire op_store    = opcode == 5'b01000;
    wire op_amo      = opcode == 5'b01011;
    wire op_op       = opcode == 5'b01100;
    wire op_lui      = opcode == 5'b01101;
    wire op_op_32    = opcode == 5'b01110;
    wire op_branch   = opcode == 5'b11000;
    wire op_jalr     = opcode == 5'b11001;
    wire op_jal      = opcode == 5'b11011;
    wire op_system   = opcode == 5'b11100;

    wire funct3_branch_valid = funct3[2:1] != 2'b01;

    wire format_r = op_op;
    wire format_i = op_op_imm || op_jalr || op_load;
    wire format_s = op_store;
    wire format_b = op_branch;
    wire format_u = op_lui || op_auipc;
    wire format_j = op_jal;

    wire format_sb = format_s | format_b;
    wire format_ij = format_i | format_j;
    wire format_uj = format_u | format_j;

    assign o_imm[0] = (format_s & i_inst[7]) | (format_i && i_inst[20]);
    assign o_imm[4:1] = ({4{format_sb}} & i_inst[11:8]) | ({4{format_ij}} & i_inst[24:21]);
    assign o_imm[10:5] = {5{!format_u}} & i_inst[30:25];
    assign o_imm[11] = format_b ? i_inst[7] : (format_j ? i_inst[20] : (format_u ? 1'b0 : i_inst[31]));
    assign o_imm[19:12] = format_uj ? i_inst[19:12] : {8{i_inst[31]}};
    assign o_imm[30:20] = format_u ? i_inst[30:20] : {11{i_inst[31]}};
    assign o_imm[31] = i_inst[31];

    assign o_op1_sel = 1'b0;
    assign o_op2_sel = |{format_i, format_s, format_b, format_u, format_j};

    assign o_mem_read = op_load;
    assign o_mem_write = op_store;
    assign o_branch = op_branch;
    assign o_jump = op_jal || op_jalr;
    assign o_rd_wen = format_r || format_i || format_u || format_j;
    assign o_rd_sel[0] = format_r || format_u || op_op_imm;
    assign o_rd_sel[1] = op_load;
    assign o_rd_sel[2] = format_j;
endmodule

module alu (
    // input wire i_clk,
    // input wire i_rst_n,
    input wire [63:0] i_op1,
    input wire [63:0] i_op2,
    // input wire i_start,
    output wire [63:0] o_result,
    output wire o_done
);
    assign o_done = 1'b1;
    // localparam idle = 2'b00;

    // reg [1:0] state;
    // reg done, next_done;
    // reg [63:0] result, next_result;

    // always @(*) begin
    //     next_done = 1'b0;
    //     next_result = 64'h0;
    //
    //     case (state)
    //         idle: begin
    //             if (i_start) begin
    //                 next_done = 1'b1;
    //                 next_result = i_op1 + i_op2;
    //             end
    //         end
    //     endcase
    // end
    //
    // always @(posedge i_clk, negedge i_rst_n) begin
    //     if (!i_rst_n) begin
    //         done <= 1'b0;
    //         result <= 64'h0;
    //     end else begin
    //         done <= next_done;
    //         result <= next_result;
    //     end
    // end

    // assign o_done = done;
    // assign o_result = next_result;
endmodule