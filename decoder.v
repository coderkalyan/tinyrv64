module decoder (
    input wire [31:0] i_inst
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
endmodule
