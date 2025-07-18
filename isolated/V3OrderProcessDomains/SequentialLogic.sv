module SequentialLogic (
    input logic clk,
    input logic [7:0] data_in,
    input logic rst,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            internal_reg <= 8'h00;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule

