module CombinationalLogicExplicit (
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic sel,
    output logic [15:0] data_out
);
    always @(sel or data0 or data1) begin
        if (sel) begin
            data_out = data1;
        end else begin
            data_out = data0;
        end
    end
endmodule

