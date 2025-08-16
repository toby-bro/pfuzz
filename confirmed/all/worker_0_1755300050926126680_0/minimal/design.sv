// Code your design here
class pkt;
    rand bit [7:0]  id;
    bit  [31:0] data;
    function new(bit [7:0] id_i, bit [31:0] data_i);
        id   = id_i;
        data = data_i;
    endfunction
endclass

class pkt_ext extends pkt;
    bit [15:0] crc;
    function new(bit [7:0] id_i, bit [31:0] data_i);
        super.new(id_i, data_i);
        crc = ^{id_i, data_i};
    endfunction
endclass

module class_user (
    input wire clk,
    input logic [31:0] data_i,
    input logic [7:0] id_i,
    input wire rst,
    output logic [15:0] crc_o
);
    always_comb begin
        static pkt_ext p = new(id_i, data_i);
        crc_o = p.crc;
    end
endmodule
