/* Generated by Yosys 0.53+70 (git sha1 3ef4c91c3, g++ 12.2.0-14+deb12u1 -fPIC -O3) */

module expr_postsub_comb(in_val_m2, sub_val_m2, out_diff_m2, var_out_m2);
  wire [31:0] _0_;
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
  assign { _0_[31:8], var_out_m2 } = in_val_m2 - 32'd1;
  assign _1_ = var_out_m2 - 1'h1;
  assign out_diff_m2 = _1_ - sub_val_m2;
  assign _0_[7:0] = var_out_m2;
  assign var_m2 = var_out_m2;
endmodule
