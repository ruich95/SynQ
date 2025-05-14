module test (
    input wire clk,
    input wire [7:0] w_0,
    input wire [7:0] w_1,
    output wire [7:0] w_7);

  wire [7:0] w_11;
  wire [7:0] w_2;
  wire [7:0] w_3;
  wire [7:0] w_4;
  wire [7:0] w_8;
  wire [7:0] w_9;
  wire [7:0] w_10;
  wire [7:0] w_5;
  wire [7:0] w_6;

  reg [7:0] r_2;
  reg [7:0] r_3;
  reg [7:0] r_4;

  assign w_2 = r_2;
  assign w_3 = r_3;
  assign w_4 = r_4;

  assign w_8 = w_0;
  assign w_9 = w_1;
  assign w_10 = w_11;
  assign w_5 = w_2;
  assign w_6 = w_3;
  assign w_7 = w_4;


  always @ (posedge clk) begin
    r_2 <= w_8;
    r_3 <= w_9;
    r_4 <= w_10;
end

endmodule
