# Issue

[yosys/issue](https://github.com/YosysHQ/yosys/issues/5151)
[yosys-slang/issue](https://github.com/povik/yosys-slang/issues/161)

This issue has been confirmed and was triggered by the following code:

```verilog
module expr_postsub_comb (
    input logic [7:0] in_val_m2,
    input logic [7:0] sub_val_m2,
    output logic [7:0] out_diff_m2,
    output logic [7:0] var_out_m2
);
    logic [7:0] var_m2;
    always_comb begin
        var_m2 = in_val_m2;
        out_diff_m2 = (var_m2--) - sub_val_m2;
        var_out_m2 = var_m2;
    end
endmodule
```

This file was generated for the following Verilator file: `V3LinkInc`
