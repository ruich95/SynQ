module demo_sys (
    input wire clk,
    input wire [7:0] w_0,
    output wire [0:0] w_8);

  wire [7:0] w_1;
  wire [0:0] w_6;
  wire [0:0] w_7;
  wire [0:0] w_3;
  wire [7:0] w_4;
  wire [7:0] w_2;
  wire [0:0] w_9;

  reg [7:0] r_1;
  reg [0:0] r_7;

  assign w_1 = r_1;
  assign w_7 = r_7;

  assign w_4 = w_0;
  assign w_2 = w_1;
  assign w_9 = w_6;
  assign w_8 = w_7;
  assign w_6 = w_3;

  ltu #(.LEN(8))
    ltu_3 (.ltu_in_1(w_2), .ltu_in_2(w_0), .ltu_out(w_3));

  always @ (posedge clk) begin
    r_1 <= w_4;
    r_7 <= w_9;
end

endmodule
