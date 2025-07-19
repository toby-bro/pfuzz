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

