`default_nettype none

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

    assign o_rs1 = (!i_rst_n || (i_rs1 == 5'd0)) ? 63'h0 : rdata[i_rs1];
    assign o_rs2 = (!i_rst_n || (i_rs2 == 5'd0)) ? 63'h0 : rdata[i_rs2];
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
            register <= 63'h0;
        else if (i_wen)
            register <= i_wdata;
    end

    assign o_rdata = register;
endmodule
