module sys (
    input wire clk,
    input wire [7:0] w_0,
    output wire [7:0] w_25);

  wire [7:0] w_3;
  wire [7:0] w_4;
  wire [7:0] w_2;
  wire [7:0] w_15;
  wire [7:0] w_12;
  wire [7:0] w_11;
  wire [7:0] w_16;
  wire [7:0] w_8;
  wire [7:0] w_9;
  wire [7:0] w_1;
  wire [7:0] w_21;
  wire [7:0] w_18;
  wire [7:0] w_19;
  wire [7:0] w_5;
  wire [7:0] w_6;
  wire [7:0] w_13;
  wire [7:0] w_22;
  wire [7:0] w_23;
  wire [7:0] w_26;
  wire [8:0] w_7;
  wire [8:0] w_24;

  reg [7:0] r_1;

  assign w_1 = r_1;

  assign w_5 = w_3;
  assign w_6 = w_4;
  assign w_3 = w_0;
  assign w_4 = w_2;
  assign w_16 = w_15;
  assign w_15 = w_12;
  assign w_18 = w_11;
  assign w_19 = w_16;
  assign w_11 = w_4;
  assign w_12 = w_8;
  assign w_13 = w_9;
  assign w_2 = w_1;
  assign w_9 = w_1;
  assign w_22 = w_21;
  assign w_23 = w_21;
  assign w_21 = w_18;
  assign w_26 = w_19;

  add #(.LEN(8))
    add_7 (.add_in_1(w_5), .add_in_2(w_6), .add_out(w_7));
  slice #(.LEN(9), .LOWER(0), .UPPER(8))
    slice_8 (.slice_in_1(w_7), .slice_out(w_8));
  add #(.LEN(8))
    add_24 (.add_in_1(w_22), .add_in_2(w_23), .add_out(w_24));
  slice #(.LEN(9), .LOWER(0), .UPPER(8))
    slice_25 (.slice_in_1(w_24), .slice_out(w_25));

  always @ (posedge clk) begin
    r_1 <= w_26;
end

endmodule
