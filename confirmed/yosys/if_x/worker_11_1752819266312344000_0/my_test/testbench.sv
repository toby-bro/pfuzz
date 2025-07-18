// Generated SystemVerilog testbench
// Do not edit this file directly : edit the template in internal/testgen/testbenches.go and generator.go

module top;
    logic [7:0] a;
    logic [7:0] b;
    logic clk;
    logic [31:0] inj_b_1752819266756_987;
    logic [1:0] inj_case_expr_1752819266746_805;
    logic [15:0] inj_data_in_pa_1752819266766_541;
    logic inj_g_ctrl_p_1752819266789_473;
    logic inj_in1_1752819266737_561;
    logic [7:0] inj_in_value_1752819266797_854;
    logic [2:0] inj_mode_1752819266763_150;
    logic [7:0] inj_param_in_1752819266779_75;
    logic rst;
    logic inj_bind_out_1752819266775_769;
    logic [7:0] inj_data_out_pa_1752819266766_827;
    logic [3:0] inj_data_out_pv_1752819266766_825;
    logic inj_g_out_and_1752819266788_695;
    logic inj_g_out_or_1752819266788_428;
    logic [4:0] inj_internal_out_1752819266746_945;
    logic inj_main_out_1752819266737_718;
    logic inj_o_result_1752819266790_107;
    logic [31:0] inj_out1_1752819266737_535;
    logic inj_out1_bind_def_1752819266759_958;
    logic [7:0] inj_out1_z_1752819266783_68;
    logic [7:0] inj_out2_z_1752819266783_763;
    logic [7:0] inj_out_1752819266792_285;
    logic inj_out_a_1752819266756_158;
    logic [31:0] inj_out_b_1752819266756_116;
    logic [2:0] inj_out_category_1752819266797_521;
    logic [7:0] inj_out_diff_m2_1752819266800_46;
    logic [7:0] inj_out_reg_d_1752819266786_792;
    logic [7:0] inj_out_reg_p_1752819266754_760;
    logic [7:0] inj_out_val_o_1752819266750_870;
    logic [7:0] inj_param_out_1752819266779_584;
    logic inj_q_out_1752819266770_633;
    logic [7:0] inj_res_1752819266763_116;
    logic inj_tok_out_1752819266743_425;
    logic [7:0] inj_var_out_m2_1752819266800_582;
    logic [8:0] sum;

    simple_sub dut (
        .a(a),
        .b(b),
        .clk(clk),
        .inj_b_1752819266756_987(inj_b_1752819266756_987),
        .inj_case_expr_1752819266746_805(inj_case_expr_1752819266746_805),
        .inj_data_in_pa_1752819266766_541(inj_data_in_pa_1752819266766_541),
        .inj_g_ctrl_p_1752819266789_473(inj_g_ctrl_p_1752819266789_473),
        .inj_in1_1752819266737_561(inj_in1_1752819266737_561),
        .inj_in_value_1752819266797_854(inj_in_value_1752819266797_854),
        .inj_mode_1752819266763_150(inj_mode_1752819266763_150),
        .inj_param_in_1752819266779_75(inj_param_in_1752819266779_75),
        .rst(rst),
        .inj_bind_out_1752819266775_769(inj_bind_out_1752819266775_769),
        .inj_data_out_pa_1752819266766_827(inj_data_out_pa_1752819266766_827),
        .inj_data_out_pv_1752819266766_825(inj_data_out_pv_1752819266766_825),
        .inj_g_out_and_1752819266788_695(inj_g_out_and_1752819266788_695),
        .inj_g_out_or_1752819266788_428(inj_g_out_or_1752819266788_428),
        .inj_internal_out_1752819266746_945(inj_internal_out_1752819266746_945),
        .inj_main_out_1752819266737_718(inj_main_out_1752819266737_718),
        .inj_o_result_1752819266790_107(inj_o_result_1752819266790_107),
        .inj_out1_1752819266737_535(inj_out1_1752819266737_535),
        .inj_out1_bind_def_1752819266759_958(inj_out1_bind_def_1752819266759_958),
        .inj_out1_z_1752819266783_68(inj_out1_z_1752819266783_68),
        .inj_out2_z_1752819266783_763(inj_out2_z_1752819266783_763),
        .inj_out_1752819266792_285(inj_out_1752819266792_285),
        .inj_out_a_1752819266756_158(inj_out_a_1752819266756_158),
        .inj_out_b_1752819266756_116(inj_out_b_1752819266756_116),
        .inj_out_category_1752819266797_521(inj_out_category_1752819266797_521),
        .inj_out_diff_m2_1752819266800_46(inj_out_diff_m2_1752819266800_46),
        .inj_out_reg_d_1752819266786_792(inj_out_reg_d_1752819266786_792),
        .inj_out_reg_p_1752819266754_760(inj_out_reg_p_1752819266754_760),
        .inj_out_val_o_1752819266750_870(inj_out_val_o_1752819266750_870),
        .inj_param_out_1752819266779_584(inj_param_out_1752819266779_584),
        .inj_q_out_1752819266770_633(inj_q_out_1752819266770_633),
        .inj_res_1752819266763_116(inj_res_1752819266763_116),
        .inj_tok_out_1752819266743_425(inj_tok_out_1752819266743_425),
        .inj_var_out_m2_1752819266800_582(inj_var_out_m2_1752819266800_582),
        .sum(sum)
    );


    initial begin
        string line;
        int fd;
        int status;

        // Read 10 input files

        fd = $fopen("input_a.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_a.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", a);
        $fclose(fd);

        fd = $fopen("input_b.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_b.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", b);
        $fclose(fd);
        clk = 0;

        fd = $fopen("input_inj_b_1752819266756_987.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_b_1752819266756_987.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_b_1752819266756_987);
        $fclose(fd);

        fd = $fopen("input_inj_case_expr_1752819266746_805.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_case_expr_1752819266746_805.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_case_expr_1752819266746_805);
        $fclose(fd);

        fd = $fopen("input_inj_data_in_pa_1752819266766_541.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_data_in_pa_1752819266766_541.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_data_in_pa_1752819266766_541);
        $fclose(fd);

        fd = $fopen("input_inj_g_ctrl_p_1752819266789_473.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_g_ctrl_p_1752819266789_473.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_g_ctrl_p_1752819266789_473);
        $fclose(fd);

        fd = $fopen("input_inj_in1_1752819266737_561.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_in1_1752819266737_561.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_in1_1752819266737_561);
        $fclose(fd);

        fd = $fopen("input_inj_in_value_1752819266797_854.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_in_value_1752819266797_854.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_in_value_1752819266797_854);
        $fclose(fd);

        fd = $fopen("input_inj_mode_1752819266763_150.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_mode_1752819266763_150.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_mode_1752819266763_150);
        $fclose(fd);

        fd = $fopen("input_inj_param_in_1752819266779_75.hex", "r");
        if (fd == 0) begin
            $display("Error: Unable to open input_inj_param_in_1752819266779_75.hex");
            $finish;
        end
        status = $fgets(line, fd);
        status = $sscanf(line, "%h", inj_param_in_1752819266779_75);
        $fclose(fd);
        rst = 0;


        // Toggle reset if a reset signal was identified

        // Toggle reset signal rst
        rst = 1; // Assert reset (active high)
        #10;
        rst = 0; // De-assert reset
        #10; // Wait after de-asserting reset


        // Toggle clock signals

        // Toggle clocks for several cycles with timeout protection
        // Set simulation timeout to prevent infinite loops
        fork
            begin
                #780;
                $display("ERROR: Simulation timeout after 780 time units");
                $finish;
            end
            begin
                repeat (50) begin
                    clk = 0;
                    #5;
                    clk = 1;
                    #5;
                end
            end
        join_any
        disable fork; // Kill timeout process


        // Allow module to process and settle
        #10; // Increased delay for settling
        
        // Additional clock cycles to ensure all sequential logic settles
        #10;
        #10;

        // Write 26 output files

        fd = $fopen("output_inj_bind_out_1752819266775_769.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_bind_out_1752819266775_769.hex' for port 'inj_bind_out_1752819266775_769'.", "output_inj_bind_out_1752819266775_769.hex", "inj_bind_out_1752819266775_769");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_bind_out_1752819266775_769);
        $fclose(fd);

        fd = $fopen("output_inj_data_out_pa_1752819266766_827.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_data_out_pa_1752819266766_827.hex' for port 'inj_data_out_pa_1752819266766_827'.", "output_inj_data_out_pa_1752819266766_827.hex", "inj_data_out_pa_1752819266766_827");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_data_out_pa_1752819266766_827[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_data_out_pv_1752819266766_825.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_data_out_pv_1752819266766_825.hex' for port 'inj_data_out_pv_1752819266766_825'.", "output_inj_data_out_pv_1752819266766_825.hex", "inj_data_out_pv_1752819266766_825");
            $finish;
        end
        for (int i = 3; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_data_out_pv_1752819266766_825[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_g_out_and_1752819266788_695.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_g_out_and_1752819266788_695.hex' for port 'inj_g_out_and_1752819266788_695'.", "output_inj_g_out_and_1752819266788_695.hex", "inj_g_out_and_1752819266788_695");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_g_out_and_1752819266788_695);
        $fclose(fd);

        fd = $fopen("output_inj_g_out_or_1752819266788_428.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_g_out_or_1752819266788_428.hex' for port 'inj_g_out_or_1752819266788_428'.", "output_inj_g_out_or_1752819266788_428.hex", "inj_g_out_or_1752819266788_428");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_g_out_or_1752819266788_428);
        $fclose(fd);

        fd = $fopen("output_inj_internal_out_1752819266746_945.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_internal_out_1752819266746_945.hex' for port 'inj_internal_out_1752819266746_945'.", "output_inj_internal_out_1752819266746_945.hex", "inj_internal_out_1752819266746_945");
            $finish;
        end
        for (int i = 4; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_internal_out_1752819266746_945[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_main_out_1752819266737_718.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_main_out_1752819266737_718.hex' for port 'inj_main_out_1752819266737_718'.", "output_inj_main_out_1752819266737_718.hex", "inj_main_out_1752819266737_718");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_main_out_1752819266737_718);
        $fclose(fd);

        fd = $fopen("output_inj_o_result_1752819266790_107.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_o_result_1752819266790_107.hex' for port 'inj_o_result_1752819266790_107'.", "output_inj_o_result_1752819266790_107.hex", "inj_o_result_1752819266790_107");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_o_result_1752819266790_107);
        $fclose(fd);

        fd = $fopen("output_inj_out1_1752819266737_535.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out1_1752819266737_535.hex' for port 'inj_out1_1752819266737_535'.", "output_inj_out1_1752819266737_535.hex", "inj_out1_1752819266737_535");
            $finish;
        end
        for (int i = 31; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out1_1752819266737_535[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out1_bind_def_1752819266759_958.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out1_bind_def_1752819266759_958.hex' for port 'inj_out1_bind_def_1752819266759_958'.", "output_inj_out1_bind_def_1752819266759_958.hex", "inj_out1_bind_def_1752819266759_958");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_out1_bind_def_1752819266759_958);
        $fclose(fd);

        fd = $fopen("output_inj_out1_z_1752819266783_68.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out1_z_1752819266783_68.hex' for port 'inj_out1_z_1752819266783_68'.", "output_inj_out1_z_1752819266783_68.hex", "inj_out1_z_1752819266783_68");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out1_z_1752819266783_68[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out2_z_1752819266783_763.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out2_z_1752819266783_763.hex' for port 'inj_out2_z_1752819266783_763'.", "output_inj_out2_z_1752819266783_763.hex", "inj_out2_z_1752819266783_763");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out2_z_1752819266783_763[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_1752819266792_285.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_1752819266792_285.hex' for port 'inj_out_1752819266792_285'.", "output_inj_out_1752819266792_285.hex", "inj_out_1752819266792_285");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_1752819266792_285[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_a_1752819266756_158.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_a_1752819266756_158.hex' for port 'inj_out_a_1752819266756_158'.", "output_inj_out_a_1752819266756_158.hex", "inj_out_a_1752819266756_158");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_out_a_1752819266756_158);
        $fclose(fd);

        fd = $fopen("output_inj_out_b_1752819266756_116.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_b_1752819266756_116.hex' for port 'inj_out_b_1752819266756_116'.", "output_inj_out_b_1752819266756_116.hex", "inj_out_b_1752819266756_116");
            $finish;
        end
        for (int i = 31; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_b_1752819266756_116[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_category_1752819266797_521.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_category_1752819266797_521.hex' for port 'inj_out_category_1752819266797_521'.", "output_inj_out_category_1752819266797_521.hex", "inj_out_category_1752819266797_521");
            $finish;
        end
        for (int i = 2; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_category_1752819266797_521[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_diff_m2_1752819266800_46.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_diff_m2_1752819266800_46.hex' for port 'inj_out_diff_m2_1752819266800_46'.", "output_inj_out_diff_m2_1752819266800_46.hex", "inj_out_diff_m2_1752819266800_46");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_diff_m2_1752819266800_46[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_reg_d_1752819266786_792.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_reg_d_1752819266786_792.hex' for port 'inj_out_reg_d_1752819266786_792'.", "output_inj_out_reg_d_1752819266786_792.hex", "inj_out_reg_d_1752819266786_792");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_reg_d_1752819266786_792[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_reg_p_1752819266754_760.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_reg_p_1752819266754_760.hex' for port 'inj_out_reg_p_1752819266754_760'.", "output_inj_out_reg_p_1752819266754_760.hex", "inj_out_reg_p_1752819266754_760");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_reg_p_1752819266754_760[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_out_val_o_1752819266750_870.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_out_val_o_1752819266750_870.hex' for port 'inj_out_val_o_1752819266750_870'.", "output_inj_out_val_o_1752819266750_870.hex", "inj_out_val_o_1752819266750_870");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_out_val_o_1752819266750_870[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_param_out_1752819266779_584.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_param_out_1752819266779_584.hex' for port 'inj_param_out_1752819266779_584'.", "output_inj_param_out_1752819266779_584.hex", "inj_param_out_1752819266779_584");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_param_out_1752819266779_584[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_q_out_1752819266770_633.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_q_out_1752819266770_633.hex' for port 'inj_q_out_1752819266770_633'.", "output_inj_q_out_1752819266770_633.hex", "inj_q_out_1752819266770_633");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_q_out_1752819266770_633);
        $fclose(fd);

        fd = $fopen("output_inj_res_1752819266763_116.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_res_1752819266763_116.hex' for port 'inj_res_1752819266763_116'.", "output_inj_res_1752819266763_116.hex", "inj_res_1752819266763_116");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_res_1752819266763_116[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_inj_tok_out_1752819266743_425.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_tok_out_1752819266743_425.hex' for port 'inj_tok_out_1752819266743_425'.", "output_inj_tok_out_1752819266743_425.hex", "inj_tok_out_1752819266743_425");
            $finish;
        end
        $fwrite(fd, "%b\n", inj_tok_out_1752819266743_425);
        $fclose(fd);

        fd = $fopen("output_inj_var_out_m2_1752819266800_582.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_inj_var_out_m2_1752819266800_582.hex' for port 'inj_var_out_m2_1752819266800_582'.", "output_inj_var_out_m2_1752819266800_582.hex", "inj_var_out_m2_1752819266800_582");
            $finish;
        end
        for (int i = 7; i >= 0; i--) begin
            $fwrite(fd, "%b", inj_var_out_m2_1752819266800_582[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);

        fd = $fopen("output_sum.hex", "w");
        if (fd == 0) begin
            $display("Error: Unable to open output file 'output_sum.hex' for port 'sum'.", "output_sum.hex", "sum");
            $finish;
        end
        for (int i = 8; i >= 0; i--) begin
            $fwrite(fd, "%b", sum[i]);
        end
        $fwrite(fd, "\n");        $fclose(fd);


        $finish;
    end
endmodule