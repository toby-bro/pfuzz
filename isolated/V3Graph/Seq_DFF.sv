module Seq_DFF (
    output reg [7:0] q_out,
    input wire clk,
    input wire rst,
    input wire [7:0] d_in
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            q_out <= 8'b0;
        end else begin
            q_out <= d_in;
        end
    end
endmodule

