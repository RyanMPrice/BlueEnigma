
module rom_unit 
  #( 
    parameter A = 8
  , parameter D = 8
  ) ( 
  input       [A - 1:0] address
, output wire [D - 1:0] dbuso

, input                 clk
, input       [A - 1:0] addressw
, output wire [D - 1:0] dbusr
, input  wire [D - 1:0] dbusw
, input                 we
);

  localparam memory_size = 2 ** A;
  reg [D - 1:0] memory [memory_size - 1:0];

  assign dbuso = memory[address];
  assign dbusr = memory[addressw];
  
  always @ (posedge clk)
    if(we)
      memory[addressw] <= dbusw;
  
  integer ii;
  initial begin
      for ( ii = 0; ii < memory_size; ii = ii + 1 ) begin
        memory[ii] = 0;
      end
      
    end
  
endmodule
