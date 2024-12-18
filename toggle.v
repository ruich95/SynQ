module toggle (
    input wire clk,
    input wire [0:0] w_0,
    output wire [0:0] w_31);

  wire [0:0] w_6;
  wire [0:0] w_2;
  wire [0:0] w_1;
  wire [0:0] w_5;
  wire [0:0] w_7;
  wire [0:0] w_15;
  wire [0:0] w_28;
  wire [0:0] w_25;
  wire [0:0] w_24;
  wire [0:0] w_29;
  wire [0:0] w_16;
  wire [0:0] w_21;
  wire [0:0] w_22;
  wire [0:0] w_14;
  wire [0:0] w_9;
  wire [0:0] w_3;
  wire [0:0] w_10;
  wire [0:0] w_32;
  wire [0:0] w_26;
  wire [0:0] w_12;
  wire [0:0] w_13;
  wire [0:0] w_17;
  wire [0:0] w_18;
  wire [0:0] w_19;
  wire [0:0] w_20;

  reg [0:0] r_1;
  reg [0:0] r_14;

  assign w_1 = r_1;
  assign w_14 = r_14;

  assign w_7 = w_6;
  assign w_5 = w_2;
  assign w_6 = w_0;
  assign w_2 = w_1;
  assign w_3 = w_1;
  assign w_9 = w_5;
  assign w_10 = w_7;
  assign w_16 = w_15;
  assign w_29 = w_28;
  assign w_28 = w_25;
  assign w_31 = w_24;
  assign w_32 = w_29;
  assign w_24 = w_16;
  assign w_25 = w_21;
  assign w_26 = w_22;
  assign w_15 = w_14;
  assign w_22 = w_14;
  assign w_12 = w_0;
  assign w_13 = w_9;

  eq #(.LEN(1))
    eq_17 (.eq_in_1(w_12), .eq_in_2(1'd1), .eq_out(w_17));
  eq #(.LEN(1))
    eq_18 (.eq_in_1(w_13), .eq_in_2(1'd0), .eq_out(w_18));
  and_comp #(.LEN(1))
    and_comp_19 (.and_comp_in_1(w_17), .and_comp_in_2(w_18), .and_comp_out(w_19));
  not_comp #(.LEN(1))
    not_comp_20 (.not_comp_in_1(w_16), .not_comp_out(w_20));
  mux21_comp #(.LEN(1))
    mux21_comp_21 (.mux21_comp_sel(w_19), .mux21_comp_in_1(w_20), .mux21_comp_in_2(w_16), .mux21_comp_out(w_21));

  always @ (posedge clk) begin
    r_1 <= w_10;
    r_14 <= w_32;
end

endmodule
