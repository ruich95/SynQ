module add
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] add_in_1, 
       input  wire [LEN-1:0] add_in_2, 
       output wire [LEN:0] add_out);

       assign add_out = add_in_1 + add_in_2;
endmodule

module concat 
      #( parameter LEN1 = 32,
         parameter LEN2 = 32)

      (input wire [LEN1-1:0] concat_in_1, 
       input wire [LEN2-1:0] concat_in_2, 
       output wire [LEN1+LEN2-1:0] concat_out);

       assign concat_out[LEN1+LEN2-1:LEN2] = concat_in_1;
       assign concat_out[LEN2-1:0] = concat_in_2;
endmodule

module not_comp 
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] not_comp_in_1, 
       output wire [LEN-1:0] not_comp_out);

       assign not_comp_out = ~not_comp_in_1;
endmodule

module and_comp
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] and_comp_in_1, 
       input  wire [LEN-1:0] and_comp_in_2, 
       output wire [LEN-1:0] and_comp_out);

       assign and_comp_out = and_comp_in_1 & and_comp_in_2;
endmodule

module or_comp
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] or_comp_in_1, 
       input  wire [LEN-1:0] or_comp_in_2, 
       output wire [LEN-1:0] or_comp_out);

       assign or_comp_out = or_comp_in_1 | or_comp_in_2;
endmodule

module xor_comp
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] xor_comp_in_1, 
       input  wire [LEN-1:0] xor_comp_in_2, 
       output wire [LEN-1:0] xor_comp_out);

       assign xor_comp_out = xor_comp_in_1 ^ xor_comp_in_2;
endmodule

module slice
      #( parameter LEN   = 32,
         parameter LOWER = 0,
         parameter UPPER = 32)
      
      (input  wire [LEN-1:0] slice_in_1,
       output wire [UPPER-LOWER-1: 0] slice_out);
       
       assign slice_out = slice_in_1[UPPER-1:LOWER];
endmodule

module eq
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] eq_in_1, 
       input  wire [LEN-1:0] eq_in_2, 
       output wire eq_out);

       assign eq_out = eq_in_1 == eq_in_2 ? 1'b1 : 1'b0;
endmodule

module ltu
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] ltu_in_1, 
       input  wire [LEN-1:0] ltu_in_2, 
       output wire ltu_out);

       assign ltu_out = ltu_in_1 < ltu_in_2 ? 1'b1 : 1'b0;
endmodule

module lt
      #( parameter LEN = 32)

      (input  wire [LEN-1:0] lt_in_1, 
       input  wire [LEN-1:0] lt_in_2, 
       output wire lt_out);

      wire signed [LEN-1:0] x_signed;
      wire signed [LEN-1:0] y_signed;

      assign x_signed = $signed(lt_in_1);
      assign y_signed = $signed(lt_in_2);

      assign lt_out = x_signed < y_signed ? 1'b1 : 1'b0;
endmodule

module sll
      #( parameter LEN = 32,
         parameter SHAMT = 0)

      (input  wire [LEN-1:0] sll_in_1, 
       output wire [LEN-1:0] sll_out);

      assign sll_out = sll_in_1 << SHAMT;
endmodule

module srl
      #( parameter LEN = 32,
         parameter SHAMT = 0)

      (input  wire [LEN-1:0] srl_in_1, 
       output wire [LEN-1:0] srl_out);

      assign srl_out = srl_in_1 >> SHAMT;
endmodule

module sra
      #( parameter LEN = 32,
         parameter SHAMT = 0)

      (input  wire [LEN-1:0] sra_in_1, 
       output wire [LEN-1:0] sra_out);

      wire signed [LEN-1:0] sra_in_signed;
      wire signed [LEN-1:0] sra_out_signed;

      assign sra_in_signed = $signed(sra_in_1);
      assign sra_out_signed = sra_in_signed >>> SHAMT;
      assign sra_out = $unsigned(sra_out_signed);
endmodule

module mux21_comp
      #( parameter LEN = 32)

      (input  wire mux21_comp_sel,
       input  wire [LEN-1:0] mux21_comp_in_1, 
       input  wire [LEN-1:0] mux21_comp_in_2, 
       output wire [LEN-1:0] mux21_comp_out);

      assign mux21_comp_out = mux21_comp_sel == 1'd1 ? mux21_comp_in_1 : mux21_comp_in_2;
endmodule

