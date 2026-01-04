module div2 (
    input wire clk,
    input wire [0:0] w_0,
    output wire [0:0] w_12);

  wire [0:0] w_8;
  wire [0:0] w_13;
  wire [0:0] w_14;
  wire [0:0] w_1;
  wire [0:0] w_5;
  wire [0:0] w_6;
  wire [0:0] w_2;
  wire [0:0] w_7;
  wire [0:0] w_9;
  wire [0:0] w_10;
  wire [0:0] w_11;

  reg [0:0] r_1;
  reg [0:0] r_2;

  assign w_1 = r_1;
  assign w_2 = r_2;

  assign w_13 = w_0;
  assign w_14 = w_8;

  not_comp #(.LEN(1))
    not_comp_5 (.not_comp_in_1(w_1), .not_comp_out(w_5));
  and_comp #(.LEN(1))
    and_comp_6 (.and_comp_in_1(w_5), .and_comp_in_2(w_0), .and_comp_out(w_6));
  not_comp #(.LEN(1))
    not_comp_7 (.not_comp_in_1(w_2), .not_comp_out(w_7));
  mux21_comp #(.LEN(1))
    mux21_comp_8 (.mux21_comp_sel(w_6), .mux21_comp_in_1(w_7), .mux21_comp_in_2(w_2), .mux21_comp_out(w_8));
  not_comp #(.LEN(1))
    not_comp_9 (.not_comp_in_1(w_1), .not_comp_out(w_9));
  and_comp #(.LEN(1))
    and_comp_10 (.and_comp_in_1(w_9), .and_comp_in_2(w_0), .and_comp_out(w_10));
  not_comp #(.LEN(1))
    not_comp_11 (.not_comp_in_1(w_2), .not_comp_out(w_11));
  mux21_comp #(.LEN(1))
    mux21_comp_12 (.mux21_comp_sel(w_10), .mux21_comp_in_1(w_11), .mux21_comp_in_2(w_2), .mux21_comp_out(w_12));

  always @ (posedge clk) begin
    r_1 <= w_13;
    r_2 <= w_14;
end

endmodule
