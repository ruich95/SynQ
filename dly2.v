module dly2 (
    input wire clk,
    input wire [7:0] w_0,
    output wire [7:0] w_18);

  wire [7:0] w_3;
  wire [7:0] w_7;
  wire [7:0] w_2;
  wire [7:0] w_15;
  wire [7:0] w_11;
  wire [7:0] w_12;
  wire [7:0] w_13;
  wire [7:0] w_8;
  wire [7:0] w_9;
  wire [7:0] w_1;
  wire [7:0] w_4;
  wire [7:0] w_5;
  wire [7:0] w_19;
  wire [7:0] w_16;
  wire [8:0] w_6;

  reg [7:0] r_1;

  assign w_1 = r_1;

  assign w_4 = w_0;
  assign w_5 = w_3;
  assign w_8 = w_7;
  assign w_3 = w_2;
  assign w_19 = w_15;
  assign w_18 = w_11;
  assign w_15 = w_12;
  assign w_16 = w_13;
  assign w_11 = w_8;
  assign w_12 = w_8;
  assign w_13 = w_9;
  assign w_2 = w_1;
  assign w_9 = w_1;

  add #(.LEN(8))
    add_6 (.add_in_1(w_4), .add_in_2(w_5), .add_out(w_6));
  slice #(.LEN(9), .LOWER(0), .UPPER(8))
    slice_7 (.slice_in_1(w_6), .slice_out(w_7));

  always @ (posedge clk) begin
    r_1 <= w_19;
end

endmodule
