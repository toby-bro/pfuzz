module module_ternary (
    input wire in_cond_ternary,
    input wire [7:0] in_val1,
    input wire [7:0] in_val2,
    output logic [7:0] out_ternary_result
);
    always_comb begin
    out_ternary_result = in_cond_ternary ? in_val1 : in_val2;
    end
endmodule

