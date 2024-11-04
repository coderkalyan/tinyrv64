`default_nettype none

module alu (
    input wire i_clk,
    input wire i_rst_n,
    input wire [63:0] i_op1,
    input wire [63:0] i_op2,
    input wire i_start,
    output wire [63:0] o_result,
    output wire o_done
);
    localparam idle = 2'b00;

    reg [1:0] state;
    reg done, next_done;
    reg [63:0] result, next_result;

    always @(*) begin
        next_done = 1'b0;
        next_result = 64'h0;

        case (state)
            idle: begin
                if (i_start) begin
                    next_done = 1'b1;
                    next_result = i_op1 + i_op2;
                end
            end
        endcase
    end

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            done <= 1'b0;
            result <= 64'h0;
        end else begin
            done <= next_done;
            result <= next_result;
        end
    end

    assign o_done = done;
    assign o_result = next_result;
endmodule
