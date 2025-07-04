module LogicDependencyChain (
    input logic clk,
    input logic d_in,
    output logic q_out
);
    logic q1, q2;
    always @(posedge clk) begin
        q1 <= d_in;
    end
    always @(q1) begin
        q2 = ~q1;
    end
    assign q_out = q2;
endmodule

