module split_diff_vars_branches_minimal (
    input logic clk,
    input logic condition,
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always @(posedge clk) begin
        if (condition) begin
            out1 <= in1;
        end else begin
            out2 <= in2;
        end
    end
endmodule

module top;
    logic clk;
    logic condition;
    logic [7:0] in1, in2;
    logic [7:0] out1, out2;

    split_diff_vars_branches_minimal uut (
        .clk(clk),
        .condition(condition),
        .in1(in1),
        .in2(in2),
        .out1(out1),
        .out2(out2)
    );

    initial begin
        // Initialize inputs
        clk = 0;
        condition = 1'bx; // Set condition to x
        in1 = 8'h00;
        in2 = 8'hff;

        // Apply a positive edge on clk
        #10;
        clk = 1;
        #10;
        clk = 0;

        // Check the outputs after some time
        #10;
        $display("out1 = %h, out2 = %h", out1, out2);
        $finish;
    end
endmodule
