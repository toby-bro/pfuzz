module procedural_complex (
    input logic [15:0] in2,
    output logic [15:0] out1,
    output logic [15:0] out2,
    input logic sel,
    input logic [15:0] in1
);
    logic [15:0] temp1;
    logic [15:0] temp2;
    always_comb begin
        temp1 = (in1 + in2) * 10;
        if (sel) begin
            temp2 = temp1 ^ (in1 >>> 2);
            out1 = temp2 & in2;
        end else begin
            temp2 = temp1 | (in2 <<< 3);
            out1 = temp2 + in1;
        end
        out2 = temp1 - temp2;
    end
endmodule

