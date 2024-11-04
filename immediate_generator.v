`default_nettype none

module immediate_generator (
    input wire [31:0] i_inst,
    // [5:0] = [r, i, s, b, u, j]
    input wire [5:0] i_type,
    output wire [31:0] o_imm
);
    wire type_r = i_type[5];
    wire type_i = i_type[4];
    wire type_s = i_type[3];
    wire type_b = i_type[2];
    wire type_u = i_type[1];
    wire type_j = i_type[0];
    wire type_sb = type_s | type_b;
    wire type_ij = type_i | type_j;
    wire type_uj = type_u | type_j;

    assign o_imm[0] = (type_s & i_inst[7]) | (type_i && i_inst[20]);
    assign o_imm[4:1] = ({4{type_sb}} & i_inst[11:8]) | ({4{type_ij}} & i_inst[24:21]);
    assign o_imm[10:5] = {5{!type_u}} & i_inst[30:25];
    assign o_imm[11] = type_b ? i_inst[7] : (type_j ? i_inst[20] : (type_u ? 1'b0 : i_inst[31]));
    assign o_imm[19:12] = type_uj ? i_inst[19:12] : {8{i_inst[31]}};
    assign o_imm[30:20] = type_u ? i_inst[30:20] : {11{i_inst[31]}};
    assign o_imm[31] = i_inst[31];
endmodule
