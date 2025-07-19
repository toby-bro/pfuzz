interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module mod_simple_ref (
    input logic i_data,
    output logic o_result
);
    logic internal_sig;
    always_comb begin
        internal_sig = i_data;
        o_result = internal_sig;
    end
endmodule

module module_packed_variables (
    input logic [15:0] data_in_pa,
    input logic [7:0] data_in_pv,
    input logic enable_pv,
    output logic [7:0] data_out_pa,
    output logic [3:0] data_out_pv
);
    logic [31:0] data_pv ;
    logic [7:0] data_pa[0:1] ;
    always_comb begin
        if (enable_pv) begin
            data_pv[7:0] = data_in_pv;
            data_pv[15:8] = ~data_in_pv;
            data_pv[23:16] = data_pv[7:0];
            data_pv[31:24] = data_pv[15:8];
            data_pa[0] = data_in_pa[7:0];
            data_pa[1] = data_in_pa[15:8];
        end else begin
            data_pv = 32'h0;
            data_pa[0] = 8'h0;
            data_pa[1] = 8'h0;
        end
    end
    assign data_out_pv = data_pv[3:0];
    assign data_out_pa = data_pa[0];
endmodule

module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module split_diff_vars_branches (
    input logic clk_z,
    input logic condition_z,
    input logic [7:0] in1_z,
    input logic [7:0] in2_z,
    output logic [7:0] out1_z,
    output logic [7:0] out2_z
);
    always @(posedge clk_z) begin
        if (condition_z) begin
            out1_z <= in1_z;
        end else begin
            out2_z <= in2_z;
        end
    end
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module simple_sub (
    input logic [7:0] a,
    input logic [7:0] b,
    input wire clk,
    input int inj_b_1752819266756_987,
    input logic [1:0] inj_case_expr_1752819266746_805,
    input logic [15:0] inj_data_in_pa_1752819266766_541,
    input wire inj_g_ctrl_p_1752819266789_473,
    input logic inj_in1_1752819266737_561,
    input bit [7:0] inj_in_value_1752819266797_854,
    input logic [2:0] inj_mode_1752819266763_150,
    input wire [7:0] inj_param_in_1752819266779_75,
    input wire rst,
    output logic inj_bind_out_1752819266775_769,
    output logic [7:0] inj_data_out_pa_1752819266766_827,
    output logic [3:0] inj_data_out_pv_1752819266766_825,
    output wire inj_g_out_and_1752819266788_695,
    output wire inj_g_out_or_1752819266788_428,
    output logic [4:0] inj_internal_out_1752819266746_945,
    output logic inj_main_out_1752819266737_718,
    output logic inj_o_result_1752819266790_107,
    output logic [31:0] inj_out1_1752819266737_535,
    output logic inj_out1_bind_def_1752819266759_958,
    output logic [7:0] inj_out1_z_1752819266783_68,
    output logic [7:0] inj_out2_z_1752819266783_763,
    output logic [7:0] inj_out_1752819266792_285,
    output logic inj_out_a_1752819266756_158,
    output int inj_out_b_1752819266756_116,
    output bit [2:0] inj_out_category_1752819266797_521,
    output logic [7:0] inj_out_diff_m2_1752819266800_46,
    output logic [7:0] inj_out_reg_d_1752819266786_792,
    output logic [7:0] inj_out_reg_p_1752819266754_760,
    output logic [7:0] inj_out_val_o_1752819266750_870,
    output wire [7:0] inj_param_out_1752819266779_584,
    output logic inj_q_out_1752819266770_633,
    output logic [7:0] inj_res_1752819266763_116,
    output logic inj_tok_out_1752819266743_425,
    output logic [7:0] inj_var_out_m2_1752819266800_582,
    output logic [8:0] sum
);
    // BEGIN: simple_macro_user_ts1752819266737
    `define SIMPLE_VALUE 32'd12345
    // BEGIN: hierarchy_if_ts1752819266738
    // BEGIN: Module_MacroTokens_ts1752819266744
    // BEGIN: case_unique0_violating_mod_ts1752819266747
    // BEGIN: split_conditional_blocking_ts1752819266751
    // BEGIN: split_if_empty_then_ts1752819266754
    // BEGIN: mod_basic_bind_ts1752819266762
    // BEGIN: dup_nested_if_ts1752819266763
    // BEGIN: LogicDependencyChain_ts1752819266771
    logic q1_ts1752819266771, q2_ts1752819266771;
        // BEGIN: expr_postsub_comb_ts1752819266800
        logic [7:0] var_m2_ts1752819266800;
        always_comb begin
            var_m2_ts1752819266800 = b;
            inj_out_diff_m2_1752819266800_46 = (var_m2_ts1752819266800--) - a;
            inj_var_out_m2_1752819266800_582 = var_m2_ts1752819266800;
        end
        // END: expr_postsub_comb_ts1752819266800

        // BEGIN: mod_if_elseif_chained_ts1752819266797
    always_comb begin
        if (inj_in_value_1752819266797_854 < 10) begin
            inj_out_category_1752819266797_521 = 3'd0;
        end else if (inj_in_value_1752819266797_854 < 50) begin
            inj_out_category_1752819266797_521 = 3'd1;
        end else if (inj_in_value_1752819266797_854 < 100) begin
            inj_out_category_1752819266797_521 = 3'd2;
        end else begin
            inj_out_category_1752819266797_521 = 3'd3;
        end
    end
        // END: mod_if_elseif_chained_ts1752819266797

        // BEGIN: sequential_always_assign_ts1752819266792
        always @(posedge clk) begin
            inj_out_1752819266792_285 <= b;
        end
        // END: sequential_always_assign_ts1752819266792

        mod_simple_ref mod_simple_ref_inst_1752819266790_2027 (
            .o_result(inj_o_result_1752819266790_107),
            .i_data(inj_in1_1752819266737_561)
        );
        // BEGIN: Module_GatePrimitives_ts1752819266789
        and a1 (inj_g_out_and_1752819266788_695, rst, rst);
        or  o1 (inj_g_out_or_1752819266788_428 , rst, rst);
        // END: Module_GatePrimitives_ts1752819266789

        // BEGIN: split_conditional_nb_ts1752819266786
        always @(posedge clk) begin
            if (inj_in1_1752819266737_561) begin
                inj_out_reg_d_1752819266786_792 <= b;
            end else begin
                inj_out_reg_d_1752819266786_792 <= a;
            end
        end
        // END: split_conditional_nb_ts1752819266786

        split_diff_vars_branches split_diff_vars_branches_inst_1752819266783_2733 (
            .out2_z(inj_out2_z_1752819266783_763),
            .clk_z(clk),
            .condition_z(q2_ts1752819266771),
            .in1_z(b),
            .in2_z(a),
            .out1_z(inj_out1_z_1752819266783_68)
        );
        module_with_params module_with_params_inst_1752819266779_2342 (
            .param_in(inj_param_in_1752819266779_75),
            .param_out(inj_param_out_1752819266779_584)
        );
        // BEGIN: bind_module_ts1752819266775
        assign inj_bind_out_1752819266775_769 = q2_ts1752819266771;
        // END: bind_module_ts1752819266775

    always @(posedge clk) begin
        q1_ts1752819266771 <= inj_in1_1752819266737_561;
    end
    always @(q1_ts1752819266771) begin
        q2_ts1752819266771 = ~q1_ts1752819266771;
    end
    assign inj_q_out_1752819266770_633 = q2_ts1752819266771;
    // END: LogicDependencyChain_ts1752819266771

    module_packed_variables module_packed_variables_inst_1752819266766_7262 (
        .enable_pv(inj_in1_1752819266737_561),
        .data_out_pa(inj_data_out_pa_1752819266766_827),
        .data_out_pv(inj_data_out_pv_1752819266766_825),
        .data_in_pa(inj_data_in_pa_1752819266766_541),
        .data_in_pv(a)
    );
    always_comb begin
        inj_res_1752819266763_116 = '0;
        if (inj_mode_1752819266763_150 == 3'b001) begin
            if (a > b) begin
                inj_res_1752819266763_116 = a + b;
            end else begin
                inj_res_1752819266763_116 = a - b;
            end
        end else if (inj_mode_1752819266763_150 == 3'b010) begin
            if (a > b) begin
                inj_res_1752819266763_116 = a + b;
            end else begin
                inj_res_1752819266763_116 = a - b;
            end
        end else if (inj_mode_1752819266763_150 == 3'b011) begin
            if (a < b) begin
                inj_res_1752819266763_116 = a * b;
            end else begin
                inj_res_1752819266763_116 = a / ((b == 0) ? 1 : b);
            end
        end else if (inj_mode_1752819266763_150 == 3'b100) begin
            if (a != b) begin
                if (a > b) inj_res_1752819266763_116 = a;
                else inj_res_1752819266763_116 = b;
            end else begin
                inj_res_1752819266763_116 = a + b;
            end
        end
        else begin
            inj_res_1752819266763_116 = a ^ b;
        end
    end
    // END: dup_nested_if_ts1752819266763

    assign inj_out1_bind_def_1752819266759_958 = ~inj_in1_1752819266737_561;
    // END: mod_basic_bind_ts1752819266762

    ModuleBasic ModuleBasic_inst_1752819266756_4336 (
        .b(inj_b_1752819266756_987),
        .out_a(inj_out_a_1752819266756_158),
        .out_b(inj_out_b_1752819266756_116),
        .a(inj_in1_1752819266737_561)
    );
    always @(posedge clk) begin
        if (inj_in1_1752819266737_561) begin
        end else begin
            inj_out_reg_p_1752819266754_760 <= a;
        end
    end
    // END: split_if_empty_then_ts1752819266754

    always @(*) begin
        if (inj_in1_1752819266737_561) begin
            inj_out_val_o_1752819266750_870 = a;
        end else begin
            inj_out_val_o_1752819266750_870 = b;
        end
    end
    // END: split_conditional_blocking_ts1752819266751

    always @* begin
        unique0 casez (inj_case_expr_1752819266746_805)
            2'b1?: inj_internal_out_1752819266746_945 = 8;
            2'b11: inj_internal_out_1752819266746_945 = 9;  
            2'b?1: inj_internal_out_1752819266746_945 = 10; 
            2'b00: inj_internal_out_1752819266746_945 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1752819266747

    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_in1_1752819266737_561;
        inj_tok_out_1752819266743_425         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1752819266744

    sub_module u_sub (
        .sub_in(inj_in1_1752819266737_561),
        .sub_out(inj_main_out_1752819266737_718)
    );
    simple_if if_inst (.clk(clk));
    always_comb begin
        if_inst.data = inj_in1_1752819266737_561;
        if_inst.ready = inj_main_out_1752819266737_718;
    end
    // END: hierarchy_if_ts1752819266738

    `define ANOTHER_SIMPLE (1 + 2)
    assign inj_out1_1752819266737_535 = inj_in1_1752819266737_561 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
    // END: simple_macro_user_ts1752819266737

    assign sum = a - b;
endmodule

