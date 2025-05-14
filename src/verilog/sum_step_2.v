module sum_step_2 (
    input wire [31:0] w_0,
    input wire [31:0] w_1,
    input wire [31:0] w_2,
    input wire [31:0] w_3,
    input wire [31:0] w_4,
    input wire [31:0] w_5,
    input wire [31:0] w_6,
    input wire [31:0] w_7,
    output wire [31:0] w_99);

  wire [31:0] w_36;
  wire [31:0] w_34;
  wire [31:0] w_38;
  wire [31:0] w_35;
  wire [31:0] w_32;
  wire [31:0] w_33;
  wire [31:0] w_37;
  wire [31:0] w_39;
  wire [31:0] w_28;
  wire [31:0] w_29;
  wire [31:0] w_48;
  wire [31:0] w_46;
  wire [31:0] w_50;
  wire [31:0] w_47;
  wire [31:0] w_44;
  wire [31:0] w_45;
  wire [31:0] w_49;
  wire [31:0] w_51;
  wire [31:0] w_30;
  wire [31:0] w_31;
  wire [31:0] w_24;
  wire [31:0] w_25;
  wire [31:0] w_26;
  wire [31:0] w_27;
  wire [31:0] w_43;
  wire [31:0] w_55;
  wire [31:0] w_16;
  wire [31:0] w_17;
  wire [31:0] w_18;
  wire [31:0] w_19;
  wire [31:0] w_72;
  wire [31:0] w_70;
  wire [31:0] w_74;
  wire [31:0] w_71;
  wire [31:0] w_68;
  wire [31:0] w_69;
  wire [31:0] w_73;
  wire [31:0] w_75;
  wire [31:0] w_64;
  wire [31:0] w_65;
  wire [31:0] w_84;
  wire [31:0] w_82;
  wire [31:0] w_86;
  wire [31:0] w_83;
  wire [31:0] w_80;
  wire [31:0] w_81;
  wire [31:0] w_85;
  wire [31:0] w_87;
  wire [31:0] w_66;
  wire [31:0] w_67;
  wire [31:0] w_60;
  wire [31:0] w_61;
  wire [31:0] w_62;
  wire [31:0] w_63;
  wire [31:0] w_79;
  wire [31:0] w_91;
  wire [31:0] w_20;
  wire [31:0] w_21;
  wire [31:0] w_22;
  wire [31:0] w_23;
  wire [31:0] w_8;
  wire [31:0] w_9;
  wire [31:0] w_10;
  wire [31:0] w_11;
  wire [31:0] w_12;
  wire [31:0] w_13;
  wire [31:0] w_14;
  wire [31:0] w_15;
  wire [31:0] w_59;
  wire [31:0] w_95;
  wire [31:0] w_40;
  wire [31:0] w_41;
  wire [31:0] w_52;
  wire [31:0] w_53;
  wire [31:0] w_56;
  wire [31:0] w_57;
  wire [31:0] w_76;
  wire [31:0] w_77;
  wire [31:0] w_88;
  wire [31:0] w_89;
  wire [31:0] w_92;
  wire [31:0] w_93;
  wire [31:0] w_96;
  wire [31:0] w_97;
  wire [32:0] w_42;
  wire [32:0] w_54;
  wire [32:0] w_58;
  wire [32:0] w_78;
  wire [32:0] w_90;
  wire [32:0] w_94;
  wire [32:0] w_98;

  assign w_37 = w_36;
  assign w_36 = w_34;
  assign w_39 = w_38;
  assign w_38 = w_35;
  assign w_34 = w_32;
  assign w_35 = w_33;
  assign w_40 = w_37;
  assign w_41 = w_39;
  assign w_32 = w_28;
  assign w_33 = w_29;
  assign w_49 = w_48;
  assign w_48 = w_46;
  assign w_51 = w_50;
  assign w_50 = w_47;
  assign w_46 = w_44;
  assign w_47 = w_45;
  assign w_52 = w_49;
  assign w_53 = w_51;
  assign w_44 = w_30;
  assign w_45 = w_31;
  assign w_28 = w_24;
  assign w_29 = w_25;
  assign w_30 = w_26;
  assign w_31 = w_27;
  assign w_56 = w_43;
  assign w_57 = w_55;
  assign w_24 = w_16;
  assign w_25 = w_17;
  assign w_26 = w_18;
  assign w_27 = w_19;
  assign w_73 = w_72;
  assign w_72 = w_70;
  assign w_75 = w_74;
  assign w_74 = w_71;
  assign w_70 = w_68;
  assign w_71 = w_69;
  assign w_76 = w_73;
  assign w_77 = w_75;
  assign w_68 = w_64;
  assign w_69 = w_65;
  assign w_85 = w_84;
  assign w_84 = w_82;
  assign w_87 = w_86;
  assign w_86 = w_83;
  assign w_82 = w_80;
  assign w_83 = w_81;
  assign w_88 = w_85;
  assign w_89 = w_87;
  assign w_80 = w_66;
  assign w_81 = w_67;
  assign w_64 = w_60;
  assign w_65 = w_61;
  assign w_66 = w_62;
  assign w_67 = w_63;
  assign w_92 = w_79;
  assign w_93 = w_91;
  assign w_60 = w_20;
  assign w_61 = w_21;
  assign w_62 = w_22;
  assign w_63 = w_23;
  assign w_16 = w_8;
  assign w_17 = w_9;
  assign w_18 = w_10;
  assign w_19 = w_11;
  assign w_20 = w_12;
  assign w_21 = w_13;
  assign w_22 = w_14;
  assign w_23 = w_15;
  assign w_96 = w_59;
  assign w_97 = w_95;
  assign w_8 = w_0;
  assign w_9 = w_1;
  assign w_10 = w_2;
  assign w_11 = w_3;
  assign w_12 = w_4;
  assign w_13 = w_5;
  assign w_14 = w_6;
  assign w_15 = w_7;

  add #(.LEN(32))
    add_42 (.add_in_1(w_40), .add_in_2(w_41), .add_out(w_42));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_43 (.slice_in_1(w_42), .slice_out(w_43));
  add #(.LEN(32))
    add_54 (.add_in_1(w_52), .add_in_2(w_53), .add_out(w_54));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_55 (.slice_in_1(w_54), .slice_out(w_55));
  add #(.LEN(32))
    add_58 (.add_in_1(w_56), .add_in_2(w_57), .add_out(w_58));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_59 (.slice_in_1(w_58), .slice_out(w_59));
  add #(.LEN(32))
    add_78 (.add_in_1(w_76), .add_in_2(w_77), .add_out(w_78));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_79 (.slice_in_1(w_78), .slice_out(w_79));
  add #(.LEN(32))
    add_90 (.add_in_1(w_88), .add_in_2(w_89), .add_out(w_90));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_91 (.slice_in_1(w_90), .slice_out(w_91));
  add #(.LEN(32))
    add_94 (.add_in_1(w_92), .add_in_2(w_93), .add_out(w_94));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_95 (.slice_in_1(w_94), .slice_out(w_95));
  add #(.LEN(32))
    add_98 (.add_in_1(w_96), .add_in_2(w_97), .add_out(w_98));
  slice #(.LEN(33), .LOWER(0), .UPPER(32))
    slice_99 (.slice_in_1(w_98), .slice_out(w_99));

endmodule
