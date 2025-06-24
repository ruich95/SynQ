module sine (
    input wire clk,
    output wire [7:0] w_66);

  wire [7:0] w_70;
  wire [7:0] w_63;
  wire [7:0] w_0;
  wire [7:0] w_71;
  wire [7:0] w_1;
  wire [7:0] w_64;
  wire [0:0] w_2;
  wire [0:0] w_3;
  wire [0:0] w_4;
  wire [0:0] w_5;
  wire [0:0] w_6;
  wire [7:0] w_7;
  wire [0:0] w_8;
  wire [7:0] w_9;
  wire [7:0] w_10;
  wire [0:0] w_11;
  wire [0:0] w_12;
  wire [7:0] w_13;
  wire [0:0] w_14;
  wire [7:0] w_15;
  wire [7:0] w_16;
  wire [7:0] w_17;
  wire [0:0] w_18;
  wire [0:0] w_19;
  wire [0:0] w_20;
  wire [7:0] w_21;
  wire [0:0] w_22;
  wire [7:0] w_23;
  wire [7:0] w_24;
  wire [0:0] w_25;
  wire [0:0] w_26;
  wire [7:0] w_27;
  wire [0:0] w_28;
  wire [7:0] w_29;
  wire [7:0] w_30;
  wire [7:0] w_31;
  wire [7:0] w_32;
  wire [0:0] w_33;
  wire [0:0] w_34;
  wire [0:0] w_35;
  wire [0:0] w_36;
  wire [7:0] w_37;
  wire [0:0] w_38;
  wire [7:0] w_39;
  wire [7:0] w_40;
  wire [0:0] w_41;
  wire [0:0] w_42;
  wire [7:0] w_43;
  wire [0:0] w_44;
  wire [7:0] w_45;
  wire [7:0] w_46;
  wire [7:0] w_47;
  wire [0:0] w_48;
  wire [0:0] w_49;
  wire [0:0] w_50;
  wire [7:0] w_51;
  wire [0:0] w_52;
  wire [7:0] w_53;
  wire [7:0] w_54;
  wire [0:0] w_55;
  wire [0:0] w_56;
  wire [7:0] w_57;
  wire [0:0] w_58;
  wire [7:0] w_59;
  wire [7:0] w_60;
  wire [7:0] w_61;
  wire [7:0] w_62;
  wire [0:0] w_67;
  wire [8:0] w_68;
  wire [7:0] w_69;

  reg [7:0] r_0;

  assign w_0 = r_0;

  assign w_71 = w_70;
  assign w_66 = w_63;
  assign w_1 = w_0;
  assign w_64 = w_0;

  slice #(.LEN(8), .LOWER(4), .UPPER(5))
    slice_2 (.slice_in_1(w_1), .slice_out(w_2));
  slice #(.LEN(8), .LOWER(3), .UPPER(4))
    slice_3 (.slice_in_1(w_1), .slice_out(w_3));
  slice #(.LEN(8), .LOWER(2), .UPPER(3))
    slice_4 (.slice_in_1(w_1), .slice_out(w_4));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_5 (.slice_in_1(w_1), .slice_out(w_5));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_6 (.slice_in_1(w_1), .slice_out(w_6));
  mux21_comp #(.LEN(8))
    mux21_comp_7 (.mux21_comp_sel(w_6), .mux21_comp_in_1(8'd80), .mux21_comp_in_2(8'd61), .mux21_comp_out(w_7));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_8 (.slice_in_1(w_1), .slice_out(w_8));
  mux21_comp #(.LEN(8))
    mux21_comp_9 (.mux21_comp_sel(w_8), .mux21_comp_in_1(8'd44), .mux21_comp_in_2(8'd29), .mux21_comp_out(w_9));
  mux21_comp #(.LEN(8))
    mux21_comp_10 (.mux21_comp_sel(w_5), .mux21_comp_in_1(w_7), .mux21_comp_in_2(w_9), .mux21_comp_out(w_10));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_11 (.slice_in_1(w_1), .slice_out(w_11));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_12 (.slice_in_1(w_1), .slice_out(w_12));
  mux21_comp #(.LEN(8))
    mux21_comp_13 (.mux21_comp_sel(w_12), .mux21_comp_in_1(8'd16), .mux21_comp_in_2(8'd7), .mux21_comp_out(w_13));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_14 (.slice_in_1(w_1), .slice_out(w_14));
  mux21_comp #(.LEN(8))
    mux21_comp_15 (.mux21_comp_sel(w_14), .mux21_comp_in_1(8'd1), .mux21_comp_in_2(8'd0), .mux21_comp_out(w_15));
  mux21_comp #(.LEN(8))
    mux21_comp_16 (.mux21_comp_sel(w_11), .mux21_comp_in_1(w_13), .mux21_comp_in_2(w_15), .mux21_comp_out(w_16));
  mux21_comp #(.LEN(8))
    mux21_comp_17 (.mux21_comp_sel(w_4), .mux21_comp_in_1(w_10), .mux21_comp_in_2(w_16), .mux21_comp_out(w_17));
  slice #(.LEN(8), .LOWER(2), .UPPER(3))
    slice_18 (.slice_in_1(w_1), .slice_out(w_18));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_19 (.slice_in_1(w_1), .slice_out(w_19));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_20 (.slice_in_1(w_1), .slice_out(w_20));
  mux21_comp #(.LEN(8))
    mux21_comp_21 (.mux21_comp_sel(w_20), .mux21_comp_in_1(8'd1), .mux21_comp_in_2(8'd7), .mux21_comp_out(w_21));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_22 (.slice_in_1(w_1), .slice_out(w_22));
  mux21_comp #(.LEN(8))
    mux21_comp_23 (.mux21_comp_sel(w_22), .mux21_comp_in_1(8'd16), .mux21_comp_in_2(8'd29), .mux21_comp_out(w_23));
  mux21_comp #(.LEN(8))
    mux21_comp_24 (.mux21_comp_sel(w_19), .mux21_comp_in_1(w_21), .mux21_comp_in_2(w_23), .mux21_comp_out(w_24));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_25 (.slice_in_1(w_1), .slice_out(w_25));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_26 (.slice_in_1(w_1), .slice_out(w_26));
  mux21_comp #(.LEN(8))
    mux21_comp_27 (.mux21_comp_sel(w_26), .mux21_comp_in_1(8'd44), .mux21_comp_in_2(8'd61), .mux21_comp_out(w_27));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_28 (.slice_in_1(w_1), .slice_out(w_28));
  mux21_comp #(.LEN(8))
    mux21_comp_29 (.mux21_comp_sel(w_28), .mux21_comp_in_1(8'd80), .mux21_comp_in_2(8'd100), .mux21_comp_out(w_29));
  mux21_comp #(.LEN(8))
    mux21_comp_30 (.mux21_comp_sel(w_25), .mux21_comp_in_1(w_27), .mux21_comp_in_2(w_29), .mux21_comp_out(w_30));
  mux21_comp #(.LEN(8))
    mux21_comp_31 (.mux21_comp_sel(w_18), .mux21_comp_in_1(w_24), .mux21_comp_in_2(w_30), .mux21_comp_out(w_31));
  mux21_comp #(.LEN(8))
    mux21_comp_32 (.mux21_comp_sel(w_3), .mux21_comp_in_1(w_17), .mux21_comp_in_2(w_31), .mux21_comp_out(w_32));
  slice #(.LEN(8), .LOWER(3), .UPPER(4))
    slice_33 (.slice_in_1(w_1), .slice_out(w_33));
  slice #(.LEN(8), .LOWER(2), .UPPER(3))
    slice_34 (.slice_in_1(w_1), .slice_out(w_34));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_35 (.slice_in_1(w_1), .slice_out(w_35));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_36 (.slice_in_1(w_1), .slice_out(w_36));
  mux21_comp #(.LEN(8))
    mux21_comp_37 (.mux21_comp_sel(w_36), .mux21_comp_in_1(8'd119), .mux21_comp_in_2(8'd138), .mux21_comp_out(w_37));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_38 (.slice_in_1(w_1), .slice_out(w_38));
  mux21_comp #(.LEN(8))
    mux21_comp_39 (.mux21_comp_sel(w_38), .mux21_comp_in_1(8'd155), .mux21_comp_in_2(8'd170), .mux21_comp_out(w_39));
  mux21_comp #(.LEN(8))
    mux21_comp_40 (.mux21_comp_sel(w_35), .mux21_comp_in_1(w_37), .mux21_comp_in_2(w_39), .mux21_comp_out(w_40));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_41 (.slice_in_1(w_1), .slice_out(w_41));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_42 (.slice_in_1(w_1), .slice_out(w_42));
  mux21_comp #(.LEN(8))
    mux21_comp_43 (.mux21_comp_sel(w_42), .mux21_comp_in_1(8'd183), .mux21_comp_in_2(8'd192), .mux21_comp_out(w_43));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_44 (.slice_in_1(w_1), .slice_out(w_44));
  mux21_comp #(.LEN(8))
    mux21_comp_45 (.mux21_comp_sel(w_44), .mux21_comp_in_1(8'd198), .mux21_comp_in_2(8'd200), .mux21_comp_out(w_45));
  mux21_comp #(.LEN(8))
    mux21_comp_46 (.mux21_comp_sel(w_41), .mux21_comp_in_1(w_43), .mux21_comp_in_2(w_45), .mux21_comp_out(w_46));
  mux21_comp #(.LEN(8))
    mux21_comp_47 (.mux21_comp_sel(w_34), .mux21_comp_in_1(w_40), .mux21_comp_in_2(w_46), .mux21_comp_out(w_47));
  slice #(.LEN(8), .LOWER(2), .UPPER(3))
    slice_48 (.slice_in_1(w_1), .slice_out(w_48));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_49 (.slice_in_1(w_1), .slice_out(w_49));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_50 (.slice_in_1(w_1), .slice_out(w_50));
  mux21_comp #(.LEN(8))
    mux21_comp_51 (.mux21_comp_sel(w_50), .mux21_comp_in_1(8'd198), .mux21_comp_in_2(8'd192), .mux21_comp_out(w_51));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_52 (.slice_in_1(w_1), .slice_out(w_52));
  mux21_comp #(.LEN(8))
    mux21_comp_53 (.mux21_comp_sel(w_52), .mux21_comp_in_1(8'd183), .mux21_comp_in_2(8'd170), .mux21_comp_out(w_53));
  mux21_comp #(.LEN(8))
    mux21_comp_54 (.mux21_comp_sel(w_49), .mux21_comp_in_1(w_51), .mux21_comp_in_2(w_53), .mux21_comp_out(w_54));
  slice #(.LEN(8), .LOWER(1), .UPPER(2))
    slice_55 (.slice_in_1(w_1), .slice_out(w_55));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_56 (.slice_in_1(w_1), .slice_out(w_56));
  mux21_comp #(.LEN(8))
    mux21_comp_57 (.mux21_comp_sel(w_56), .mux21_comp_in_1(8'd155), .mux21_comp_in_2(8'd138), .mux21_comp_out(w_57));
  slice #(.LEN(8), .LOWER(0), .UPPER(1))
    slice_58 (.slice_in_1(w_1), .slice_out(w_58));
  mux21_comp #(.LEN(8))
    mux21_comp_59 (.mux21_comp_sel(w_58), .mux21_comp_in_1(8'd119), .mux21_comp_in_2(8'd100), .mux21_comp_out(w_59));
  mux21_comp #(.LEN(8))
    mux21_comp_60 (.mux21_comp_sel(w_55), .mux21_comp_in_1(w_57), .mux21_comp_in_2(w_59), .mux21_comp_out(w_60));
  mux21_comp #(.LEN(8))
    mux21_comp_61 (.mux21_comp_sel(w_48), .mux21_comp_in_1(w_54), .mux21_comp_in_2(w_60), .mux21_comp_out(w_61));
  mux21_comp #(.LEN(8))
    mux21_comp_62 (.mux21_comp_sel(w_33), .mux21_comp_in_1(w_47), .mux21_comp_in_2(w_61), .mux21_comp_out(w_62));
  mux21_comp #(.LEN(8))
    mux21_comp_63 (.mux21_comp_sel(w_2), .mux21_comp_in_1(w_32), .mux21_comp_in_2(w_62), .mux21_comp_out(w_63));
  ltu #(.LEN(8))
    ltu_67 (.ltu_in_1(w_1), .ltu_in_2(8'd31), .ltu_out(w_67));
  add #(.LEN(8))
    add_68 (.add_in_1(w_1), .add_in_2(8'd1), .add_out(w_68));
  slice #(.LEN(9), .LOWER(0), .UPPER(8))
    slice_69 (.slice_in_1(w_68), .slice_out(w_69));
  mux21_comp #(.LEN(8))
    mux21_comp_70 (.mux21_comp_sel(w_67), .mux21_comp_in_1(w_69), .mux21_comp_in_2(8'd0), .mux21_comp_out(w_70));

  always @ (posedge clk) begin
    r_0 <= w_71;
end

endmodule
