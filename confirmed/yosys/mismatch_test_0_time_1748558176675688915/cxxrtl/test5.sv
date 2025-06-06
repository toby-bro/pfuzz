/* Generated by Yosys 0.53+60 (git sha1 3790be114, g++ 12.2.0-14+deb12u1 -fPIC -O3) */

module expr_postsub_comb(in_val_m2, sub_val_m2, out_diff_m2, var_out_m2);
  wire [7:0] _0_;
  wire [7:0] _1_;
  input [7:0] in_val_m2;
  wire [7:0] in_val_m2;
  output [7:0] out_diff_m2;
  wire [7:0] out_diff_m2;
  input [7:0] sub_val_m2;
  wire [7:0] sub_val_m2;
  wire [7:0] var_m2;
  output [7:0] var_out_m2;
  wire [7:0] var_out_m2;
  assign _0_ = in_val_m2 - 2'h1;
  assign _1_ = _0_ - sub_val_m2;
  assign var_m2 = _0_;
  assign out_diff_m2 = _1_;
  assign var_out_m2 = _0_;
endmodule
