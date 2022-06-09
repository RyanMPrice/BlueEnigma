
module ram_unit 
  #( 
    parameter A = 8
  , parameter D = 8
  ) ( 
  input                 clk
, input       [A - 1:0] address
, output wire [D - 1:0] dbuso
, input  wire [D - 1:0] dbusi
, input                 ce
, input                 we

, input       [A - 1:0] iaddress
, output wire [D - 1:0] idbuso
, input  wire [D - 1:0] idbusi
, input                 ice
, input                 iwe
);

  localparam memory_size = 2 ** A;
  reg [D - 1:0] memory [memory_size - 1:0];

  assign dbuso  = memory[address];
  assign idbuso = memory[iaddress];
  
  always @ (posedge clk)
    if(ce & we)
      memory[address] <= dbusi;

  always @ (posedge clk)
    if(ice & iwe)
      memory[iaddress] <= idbusi;
  
  integer ii;
  initial begin
      for ( ii = 0; ii < memory_size; ii = ii + 1 ) begin
        memory[ii] = 0;
      end
    end
  
endmodule
