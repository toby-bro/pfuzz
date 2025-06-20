module ModuleWithUnion (
    input logic select,
    input byte val_byte,
    input int val_int,
    output int out_int
);
    typedef union {
        int u_field_int;
        byte u_field_byte;
    } MyUnion;
    MyUnion union_var;
    int result_int;
    always_comb begin
        if (select) begin
            union_var.u_field_int = val_int;
        end else begin
            union_var.u_field_byte = val_byte;
        end
        result_int = union_var.u_field_int;
        out_int = result_int;
    end
endmodule

