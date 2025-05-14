module btree_2 (
    input wire clk,
    input wire [31:0] w_0,
    input wire [31:0] w_1,
    input wire [31:0] w_2,
    input wire [31:0] w_3,
    input wire [31:0] w_4,
    input wire [31:0] w_5,
    input wire [31:0] w_6,
    input wire [31:0] w_7,
    output wire [31:0] w_25);

  wire [31:0] w_125;
  wire [31:0] w_8;
  wire [31:0] w_9;
  wire [31:0] w_10;
  wire [31:0] w_11;
  wire [31:0] w_12;
  wire [31:0] w_13;
  wire [31:0] w_14;
  wire [31:0] w_15;
  wire [31:0] w_16;
  wire [31:0] w_26;
  wire [31:0] w_27;
  wire [31:0] w_28;
  wire [31:0] w_29;
  wire [31:0] w_30;
  wire [31:0] w_31;
  wire [31:0] w_32;
  wire [31:0] w_33;
  wire [31:0] w_34;
  wire [31:0] w_17;
  wire [31:0] w_18;
  wire [31:0] w_19;
  wire [31:0] w_20;
  wire [31:0] w_21;
  wire [31:0] w_22;
  wire [31:0] w_23;
  wire [31:0] w_24;

  reg [31:0] r_8;
  reg [31:0] r_9;
  reg [31:0] r_10;
  reg [31:0] r_11;
  reg [31:0] r_12;
  reg [31:0] r_13;
  reg [31:0] r_14;
  reg [31:0] r_15;
  reg [31:0] r_16;

  assign w_8 = r_8;
  assign w_9 = r_9;
  assign w_10 = r_10;
  assign w_11 = r_11;
  assign w_12 = r_12;
  assign w_13 = r_13;
  assign w_14 = r_14;
  assign w_15 = r_15;
  assign w_16 = r_16;

  assign w_26 = w_0;
  assign w_27 = w_1;
  assign w_28 = w_2;
  assign w_29 = w_3;
  assign w_30 = w_4;
  assign w_31 = w_5;
  assign w_32 = w_6;
  assign w_33 = w_7;
  assign w_34 = w_125;
  assign w_17 = w_8;
  assign w_18 = w_9;
  assign w_19 = w_10;
  assign w_20 = w_11;
  assign w_21 = w_12;
  assign w_22 = w_13;
  assign w_23 = w_14;
  assign w_24 = w_15;
  assign w_25 = w_16;


  always @ (posedge clk) begin
    r_8 <= w_26;
    r_9 <= w_27;
    r_10 <= w_28;
    r_11 <= w_29;
    r_12 <= w_30;
    r_13 <= w_31;
    r_14 <= w_32;
    r_15 <= w_33;
    r_16 <= w_34;
end

endmodule
