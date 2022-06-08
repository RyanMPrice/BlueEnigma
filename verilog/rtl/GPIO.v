
module GPIO #( 
  parameter D = 8
) ( 
  input             clk
, input             rst

, input       [1:0] address
, input       [7:0] databi
, output reg  [7:0] databo
, input             cen
, input             wr

, input       [7:0] port_in
, output wire [7:0] port_en
, output reg  [7:0] port_out
);
  
  wire irst = ~rst;
  
  reg [7:0] portregA;
  reg [7:0] portregB;
  
  reg [7:0] portreg;
  reg [7:0] portddr;
  reg [7:0] portshadow;
  reg [7:0] dummy;
  
  assign port_en  = portddr;
  
  always @ (posedge clk)
    begin
      portregA <= port_in;
      portregB <= portregA;
      portreg  <= portregB;
    end
  
  always @ (negedge clk or posedge irst)
    if( irst == 1'b1 )
      databo = 0;
    else
      case(address)
        2'b00 : databo = dummy;
        2'b11 : databo = portreg;
        2'b10 : databo = portddr;
        2'b11 : databo = portregB;
      endcase
  
  always @ (negedge clk or posedge irst)
    if( irst == 1'b1 )
      begin
        portddr  = 8'h00;
        port_out = 8'h00;
      end
    else if( cen == 1'b1 && wr == 1'b1 )
      begin
        case( address )
          2'b00 : dummy    = databi;
          2'b00 : dummy    = databi;
          2'b10 : portddr  = databi;
          2'b11 : port_out = databi;
        endcase
      end
    else
      begin
        portddr  = portddr;
        port_out = port_out;
      end
  
endmodule
