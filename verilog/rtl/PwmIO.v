
module pwm #( 
  parameter D = 8
) ( 
  input            clk
, input            rst

, input      [2:0] address
, input      [7:0] databi
, output reg [7:0] databo
, input            cen
, input            wr

, output wire      q0
, output wire      n0
);

  reg [7:0] regCon;
    //reg[7] enable q0
    //reg[6] enable q0
    //reg[5] enable divider
  reg [7:0] regDivHigh;
  reg [7:0] regDivLow;
  reg [7:0] regPulsePh;
  reg [7:0] regPulseNh;
  reg [7:0] regPulsePl;
  reg [7:0] regPulseNl;
  reg [7:0] dummy;
  
  reg [15:0] regDiver;
  reg [ 7:0] regCounter;
  
  wire irst = ~rst;
  wire TDO  = regDiver >= {regDivHigh, regDivLow};
  
  always @ (posedge clk or negedge rst)
    if ( rst == 1'b0 )
      regDiver <= 0;
    else if ( TDO == 1'b1 )
      regDiver <= 0;
    else if (regCon[5] == 1'b1)
      regDiver <= regDiver + 1;
  
  always @ (posedge clk or negedge rst)
    if ( rst == 1'b0 )
      regCounter <= 0;
    else if ( regCon[5] == 1'b1 && TDO == 1'b1 )
      regCounter <= regCounter + 1;
    else
      regCounter <= regCounter;
  
  wire PD;
  wire ND;
  assign q0 = PD & regCon[7];
  assign n0 = ND & regCon[6];
  wire PDH = (regCounter == regPulsePh);
  wire PDL = (regCounter == regPulsePl);
  wire NDH = (regCounter == regPulseNh);
  wire NDL = (regCounter == regPulseNl);
  
  mysrlatch platc (PD, clk, PDH, PDL, rst);
  mysrlatch nlatc (ND, clk, NDH, NDL, rst);
  
  always @ (negedge clk or posedge irst)
    if( irst == 1'b1 )
      databo <= 8'h00;
    else if( cen == 1'b1 )
      case( address )
        3'b000  : databo <= 8'h01;
        3'b001  : databo <= regCon;
        3'b010  : databo <= regDivLow;
        3'b011  : databo <= regDivHigh;
        3'b100  : databo <= regPulsePl;
        3'b101  : databo <= regPulseNl;
        3'b110  : databo <= regPulsePh;
        3'b111  : databo <= regPulseNh;
        default : databo <= dummy;
      endcase
    else
      databo <= 0;
  
  always @ (negedge clk or posedge irst)
    if( irst == 1'b1 )
      begin
        regCon     = 8'h00;
        regDivHigh = 8'h00;
        regDivLow  = 8'h00;
        regPulsePl = 8'h00;
        regPulseNl = 8'h00;
        regPulsePh = 8'h00;
        regPulseNh = 8'h00;
      end
    else if( cen == 1'b1 && wr == 1'b1 )
      begin
        case( address )
          3'b000  : dummy      <= databi;
          3'b001  : regCon     <= databi;
          3'b010  : regDivLow  <= databi;
          3'b011  : regDivHigh <= databi;
          3'b100  : regPulsePl <= databi;
          3'b101  : regPulseNl <= databi;
          3'b110  : regPulsePh <= databi;
          3'b111  : regPulseNh <= databi;
          default : dummy      <= databi;
        endcase
      end
    else
      begin
        regCon     = regCon;
        regDivHigh = regDivHigh;
        regDivLow  = regDivLow;
        regPulsePl = regPulsePl;
        regPulseNl = regPulseNl;
        regPulsePh = regPulsePh;
        regPulseNh = regPulseNh;
      end
    
  
endmodule

module mysrlatch (
  output reg Q
, input      clk
, input      H
, input      L
, input      rst
);

  always @ (posedge clk or negedge rst)
    if( rst == 1'b0 )
      Q = 1'b0;
    else if( H == 1'b1 )
      Q = 1'b1;
    else if( L == 1'b1 )
      Q = 1'b0;
    else
      Q = Q;

endmodule

