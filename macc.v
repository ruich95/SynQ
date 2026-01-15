module macc (
    input wire clk,
    input wire [17:0] w_0,
    input wire [17:0] w_1,
    output wire [47:0] w_31);

  wire [47:0] w_21;
  wire [47:0] w_13;
  wire [35:0] w_11;
  wire [35:0] w_10;
  wire [47:0] w_26;
  wire [47:0] w_24;
  wire [47:0] w_22;
  wire [35:0] w_6;
  wire [17:0] w_7;
  wire [17:0] w_8;
  wire [35:0] w_12;
  wire [35:0] w_28;
  wire [47:0] w_29;
  wire [17:0] w_2;
  wire [17:0] w_3;
  wire [0:0] w_15;
  wire [11:0] w_16;
  wire [47:0] w_17;
  wire [47:0] w_18;
  wire [47:0] w_19;
  wire [48:0] w_20;

  reg [17:0] r_2;
  reg [17:0] r_3;
  reg [35:0] r_11;
  reg [47:0] r_13;

  assign w_2 = r_2;
  assign w_3 = r_3;
  assign w_11 = r_11;
  assign w_13 = r_13;

  assign w_7 = w_0;
  assign w_8 = w_1;
  assign w_22 = w_21;
  assign w_24 = w_13;
  assign w_12 = w_11;
  assign w_28 = w_10;
  assign w_29 = w_26;
  assign w_31 = w_24;
  assign w_26 = w_22;
  assign w_10 = w_6;

  mult18 mult18_6 (.mult18_in_1(w_2), .mult18_in_2(w_3), .mult18_out(w_6));
  slice #(.LEN(36), .LOWER(35), .UPPER(36))
    slice_15 (.slice_in_1(w_12), .slice_out(w_15));
  not_comp #(.LEN(12))
    not_comp_16 (.not_comp_in_1(12'd0), .not_comp_out(w_16));
  concat #(.LEN1(12), .LEN2(36))
    concat_17 (.concat_in_1(w_16), .concat_in_2(w_12), .concat_out(w_17));
  concat #(.LEN1(12), .LEN2(36))
    concat_18 (.concat_in_1(12'd0), .concat_in_2(w_12), .concat_out(w_18));
  mux21_comp #(.LEN(48))
    mux21_comp_19 (.mux21_comp_sel(w_15), .mux21_comp_in_1(w_17), .mux21_comp_in_2(w_18), .mux21_comp_out(w_19));
  add #(.LEN(48))
    add_20 (.add_in_1(w_13), .add_in_2(w_19), .add_out(w_20));
  slice #(.LEN(49), .LOWER(0), .UPPER(48))
    slice_21 (.slice_in_1(w_20), .slice_out(w_21));

  always @ (posedge clk) begin
    r_2 <= w_7;
    r_3 <= w_8;
    r_11 <= w_28;
    r_13 <= w_29;
end

endmodule
