module ModuleBasic (
	a,
	b,
	out_a,
	out_b
);
	reg _sv2v_0;
	input wire a;
	input wire signed [31:0] b;
	output wire out_a;
	output wire signed [31:0] out_b;
	parameter signed [31:0] P1 = 10;
	localparam signed [31:0] LP1 = 20;
	reg c;
	wire signed [31:0] d;
	always @(*) begin : sv2v_autoblock_1
		reg temp_v;
		if (_sv2v_0)
			;
		temp_v = d;
		c = temp_v;
	end
	assign out_a = a;
	assign d = b;
	assign out_b = (d + P1) + LP1;
	initial _sv2v_0 = 0;
endmodule
module mod_simple_ref (
	i_data,
	o_result
);
	reg _sv2v_0;
	input wire i_data;
	output reg o_result;
	reg internal_sig;
	always @(*) begin
		if (_sv2v_0)
			;
		internal_sig = i_data;
		o_result = internal_sig;
	end
	initial _sv2v_0 = 0;
endmodule
module module_packed_variables (
	data_in_pa,
	data_in_pv,
	enable_pv,
	data_out_pa,
	data_out_pv
);
	reg _sv2v_0;
	input wire [15:0] data_in_pa;
	input wire [7:0] data_in_pv;
	input wire enable_pv;
	output wire [7:0] data_out_pa;
	output wire [3:0] data_out_pv;
	reg [31:0] data_pv;
	reg [7:0] data_pa [0:1];
	always @(*) begin
		if (_sv2v_0)
			;
		if (enable_pv) begin
			data_pv[7:0] = data_in_pv;
			data_pv[15:8] = ~data_in_pv;
			data_pv[23:16] = data_pv[7:0];
			data_pv[31:24] = data_pv[15:8];
			data_pa[0] = data_in_pa[7:0];
			data_pa[1] = data_in_pa[15:8];
		end
		else begin
			data_pv = 32'h00000000;
			data_pa[0] = 8'h00;
			data_pa[1] = 8'h00;
		end
	end
	assign data_out_pv = data_pv[3:0];
	assign data_out_pa = data_pa[0];
	initial _sv2v_0 = 0;
endmodule
module module_with_params (
	param_in,
	param_out
);
	parameter integer DATA_WIDTH = 8;
	input wire [7:0] param_in;
	output wire [7:0] param_out;
	assign param_out = param_in;
endmodule
module split_diff_vars_branches (
	clk_z,
	condition_z,
	in1_z,
	in2_z,
	out1_z,
	out2_z
);
	input wire clk_z;
	input wire condition_z;
	input wire [7:0] in1_z;
	input wire [7:0] in2_z;
	output reg [7:0] out1_z;
	output reg [7:0] out2_z;
	always @(posedge clk_z)
		if (condition_z)
			out1_z <= in1_z;
		else
			out2_z <= in2_z;
endmodule
module sub_module (
	sub_in,
	sub_out
);
	input wire sub_in;
	output wire sub_out;
	assign sub_out = !sub_in;
endmodule
module simple_sub (
	a,
	b,
	clk,
	inj_b_1752819266756_987,
	inj_case_expr_1752819266746_805,
	inj_data_in_pa_1752819266766_541,
	inj_g_ctrl_p_1752819266789_473,
	inj_in1_1752819266737_561,
	inj_in_value_1752819266797_854,
	inj_mode_1752819266763_150,
	inj_param_in_1752819266779_75,
	rst,
	inj_bind_out_1752819266775_769,
	inj_data_out_pa_1752819266766_827,
	inj_data_out_pv_1752819266766_825,
	inj_g_out_and_1752819266788_695,
	inj_g_out_or_1752819266788_428,
	inj_internal_out_1752819266746_945,
	inj_main_out_1752819266737_718,
	inj_o_result_1752819266790_107,
	inj_out1_1752819266737_535,
	inj_out1_bind_def_1752819266759_958,
	inj_out1_z_1752819266783_68,
	inj_out2_z_1752819266783_763,
	inj_out_1752819266792_285,
	inj_out_a_1752819266756_158,
	inj_out_b_1752819266756_116,
	inj_out_category_1752819266797_521,
	inj_out_diff_m2_1752819266800_46,
	inj_out_reg_d_1752819266786_792,
	inj_out_reg_p_1752819266754_760,
	inj_out_val_o_1752819266750_870,
	inj_param_out_1752819266779_584,
	inj_q_out_1752819266770_633,
	inj_res_1752819266763_116,
	inj_tok_out_1752819266743_425,
	inj_var_out_m2_1752819266800_582,
	sum
);
	reg _sv2v_0;
	input wire [7:0] a;
	input wire [7:0] b;
	input wire clk;
	input wire signed [31:0] inj_b_1752819266756_987;
	input wire [1:0] inj_case_expr_1752819266746_805;
	input wire [15:0] inj_data_in_pa_1752819266766_541;
	input wire inj_g_ctrl_p_1752819266789_473;
	input wire inj_in1_1752819266737_561;
	input wire [7:0] inj_in_value_1752819266797_854;
	input wire [2:0] inj_mode_1752819266763_150;
	input wire [7:0] inj_param_in_1752819266779_75;
	input wire rst;
	output wire inj_bind_out_1752819266775_769;
	output wire [7:0] inj_data_out_pa_1752819266766_827;
	output wire [3:0] inj_data_out_pv_1752819266766_825;
	output wire inj_g_out_and_1752819266788_695;
	output wire inj_g_out_or_1752819266788_428;
	output reg [4:0] inj_internal_out_1752819266746_945;
	output wire inj_main_out_1752819266737_718;
	output wire inj_o_result_1752819266790_107;
	output wire [31:0] inj_out1_1752819266737_535;
	output wire inj_out1_bind_def_1752819266759_958;
	output wire [7:0] inj_out1_z_1752819266783_68;
	output wire [7:0] inj_out2_z_1752819266783_763;
	output reg [7:0] inj_out_1752819266792_285;
	output wire inj_out_a_1752819266756_158;
	output wire signed [31:0] inj_out_b_1752819266756_116;
	output reg [2:0] inj_out_category_1752819266797_521;
	output reg [7:0] inj_out_diff_m2_1752819266800_46;
	output reg [7:0] inj_out_reg_d_1752819266786_792;
	output reg [7:0] inj_out_reg_p_1752819266754_760;
	output reg [7:0] inj_out_val_o_1752819266750_870;
	output wire [7:0] inj_param_out_1752819266779_584;
	output wire inj_q_out_1752819266770_633;
	output reg [7:0] inj_res_1752819266763_116;
	output reg inj_tok_out_1752819266743_425;
	output reg [7:0] inj_var_out_m2_1752819266800_582;
	output wire [8:0] sum;
	reg q1_ts1752819266771;
	reg q2_ts1752819266771;
	reg [7:0] var_m2_ts1752819266800;
	always @(*) begin
		if (_sv2v_0)
			;
		var_m2_ts1752819266800 = b;
		var_m2_ts1752819266800 = var_m2_ts1752819266800 - 1;
		inj_out_diff_m2_1752819266800_46 = (var_m2_ts1752819266800 - 1'sd1) - a;
		inj_var_out_m2_1752819266800_582 = var_m2_ts1752819266800;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_in_value_1752819266797_854 < 10)
			inj_out_category_1752819266797_521 = 3'd0;
		else if (inj_in_value_1752819266797_854 < 50)
			inj_out_category_1752819266797_521 = 3'd1;
		else if (inj_in_value_1752819266797_854 < 100)
			inj_out_category_1752819266797_521 = 3'd2;
		else
			inj_out_category_1752819266797_521 = 3'd3;
	end
	always @(posedge clk) inj_out_1752819266792_285 <= b;
	mod_simple_ref mod_simple_ref_inst_1752819266790_2027(
		.o_result(inj_o_result_1752819266790_107),
		.i_data(inj_in1_1752819266737_561)
	);
	and a1 (inj_g_out_and_1752819266788_695, rst, rst);
	or o1 (inj_g_out_or_1752819266788_428, rst, rst);
	always @(posedge clk)
		if (inj_in1_1752819266737_561)
			inj_out_reg_d_1752819266786_792 <= b;
		else
			inj_out_reg_d_1752819266786_792 <= a;
	split_diff_vars_branches split_diff_vars_branches_inst_1752819266783_2733(
		.out2_z(inj_out2_z_1752819266783_763),
		.clk_z(clk),
		.condition_z(q2_ts1752819266771),
		.in1_z(b),
		.in2_z(a),
		.out1_z(inj_out1_z_1752819266783_68)
	);
	module_with_params module_with_params_inst_1752819266779_2342(
		.param_in(inj_param_in_1752819266779_75),
		.param_out(inj_param_out_1752819266779_584)
	);
	assign inj_bind_out_1752819266775_769 = q2_ts1752819266771;
	always @(posedge clk) q1_ts1752819266771 <= inj_in1_1752819266737_561;
	always @(q1_ts1752819266771) q2_ts1752819266771 = ~q1_ts1752819266771;
	assign inj_q_out_1752819266770_633 = q2_ts1752819266771;
	module_packed_variables module_packed_variables_inst_1752819266766_7262(
		.enable_pv(inj_in1_1752819266737_561),
		.data_out_pa(inj_data_out_pa_1752819266766_827),
		.data_out_pv(inj_data_out_pv_1752819266766_825),
		.data_in_pa(inj_data_in_pa_1752819266766_541),
		.data_in_pv(a)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_res_1752819266763_116 = 1'sb0;
		if (inj_mode_1752819266763_150 == 3'b001) begin
			if (a > b)
				inj_res_1752819266763_116 = a + b;
			else
				inj_res_1752819266763_116 = a - b;
		end
		else if (inj_mode_1752819266763_150 == 3'b010) begin
			if (a > b)
				inj_res_1752819266763_116 = a + b;
			else
				inj_res_1752819266763_116 = a - b;
		end
		else if (inj_mode_1752819266763_150 == 3'b011) begin
			if (a < b)
				inj_res_1752819266763_116 = a * b;
			else
				inj_res_1752819266763_116 = a / (b == 0 ? 1 : b);
		end
		else if (inj_mode_1752819266763_150 == 3'b100) begin
			if (a != b) begin
				if (a > b)
					inj_res_1752819266763_116 = a;
				else
					inj_res_1752819266763_116 = b;
			end
			else
				inj_res_1752819266763_116 = a + b;
		end
		else
			inj_res_1752819266763_116 = a ^ b;
	end
	assign inj_out1_bind_def_1752819266759_958 = ~inj_in1_1752819266737_561;
	ModuleBasic ModuleBasic_inst_1752819266756_4336(
		.b(inj_b_1752819266756_987),
		.out_a(inj_out_a_1752819266756_158),
		.out_b(inj_out_b_1752819266756_116),
		.a(inj_in1_1752819266737_561)
	);
	always @(posedge clk)
		if (inj_in1_1752819266737_561)
			;
		else
			inj_out_reg_p_1752819266754_760 <= a;
	always @(*)
		if (inj_in1_1752819266737_561)
			inj_out_val_o_1752819266750_870 = a;
		else
			inj_out_val_o_1752819266750_870 = b;
	always @(*)
		(* parallel_case *)
		casez (inj_case_expr_1752819266746_805)
			2'b1z: inj_internal_out_1752819266746_945 = 8;
			2'b11: inj_internal_out_1752819266746_945 = 9;
			2'bz1: inj_internal_out_1752819266746_945 = 10;
			2'b00: inj_internal_out_1752819266746_945 = 11;
		endcase
	reg my_var;
	always @(*) begin
		if (_sv2v_0)
			;
		my_var = inj_in1_1752819266737_561;
		inj_tok_out_1752819266743_425 = my_var;
	end
	sub_module u_sub(
		.sub_in(inj_in1_1752819266737_561),
		.sub_out(inj_main_out_1752819266737_718)
	);
	generate
		if (1) begin : if_inst
			wire clk;
			reg data;
			reg ready;
		end
	endgenerate
	assign if_inst.clk = clk;
	always @(*) begin
		if (_sv2v_0)
			;
		if_inst.data = inj_in1_1752819266737_561;
		if_inst.ready = inj_main_out_1752819266737_718;
	end
	assign inj_out1_1752819266737_535 = (inj_in1_1752819266737_561 ? 12348 : 32'd0);
	assign sum = a - b;
	initial _sv2v_0 = 0;
endmodule