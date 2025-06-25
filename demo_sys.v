module demo_sys (
    input wire clk,
    input wire [7:0] w_0,
    output wire [0:0] w_3);

  wire [7:0] w_4;
  wire [7:0] w_1;

  reg [7:0] r_1;

  assign w_1 = r_1;

  assign w_4 = w_0;

  ltu #(.LEN(8))
    ltu_3 (.ltu_in_1(w_1), .ltu_in_2(w_0), .ltu_out(w_3));

  always @ (posedge clk) begin
    r_1 <= w_4;
end

endmodule
