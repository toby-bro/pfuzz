module minimal_repro (
    input logic clk,
    output logic out2
);
    logic condition;
    logic q1 = 1'bx; // Start with x to replicate initial condition

    always @(posedge clk) begin
        q1 <= 0;
    end
    assign condition = ~q1;

    always @(posedge clk) begin
        if (condition) begin
            // out1 updating is omitted since we're focusing on out2
        end else begin
            out2 <= 1'b1; // Set out2 to 1 (was 8'hff)
        end
    end
endmodule

module top;
    logic clk;
    logic out2;

    minimal_repro uut (
        .clk(clk),
        .out2(out2)
    );

    initial begin
        clk = 0;
        #10;
        repeat (5) begin
            clk = 0;
            #5;
            clk = 1;
            #5;
            $write("out2: %b\n", out2);
        end
        $finish;
    end
endmodule
