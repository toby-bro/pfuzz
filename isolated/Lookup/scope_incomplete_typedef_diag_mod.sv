module scope_incomplete_typedef_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = IncompleteClass::static_member;
endmodule

