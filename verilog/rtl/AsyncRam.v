
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
);

  localparam memory_size = 2 ** A;
  reg [D - 1:0] memory [memory_size - 1:0];

  assign dbuso = memory[address];
  
  always @ (posedge clk)
    if(ce & we)
      memory[address] <= dbusi;
  
  integer ii;
  initial begin
      for ( ii = 0; ii < memory_size; ii = ii + 1 ) begin
        memory[ii] = 0;
      end
    end
  
endmodule
