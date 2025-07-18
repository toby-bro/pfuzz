module mod_basic (
    input wire i_clk,
    output logic o_done
);
    logic r_state;
    parameter int PARAM_BASIC = 42;
    always_ff @(posedge i_clk) begin
        r_state <= ~r_state;
    end
    always_comb begin
        o_done = r_state;
    end
endmodule

