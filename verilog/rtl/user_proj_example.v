// SPDX-FileCopyrightText: 2020 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none
/*
 *-------------------------------------------------------------
 *
 * user_proj_example
 *
 * This is an example of a (trivially simple) user project,
 * showing how the user project can connect to the logic
 * analyzer, the wishbone bus, and the I/O pads.
 *
 * This project generates an integer count, which is output
 * on the user area GPIO pads (digital output only).  The
 * wishbone connection allows the project to be controlled
 * (start and stop) from the management SoC program.
 *
 * See the testbenches in directory "mprj_counter" for the
 * example programs that drive this user project.  The three
 * testbenches are "io_ports", "la_test1", and "la_test2".
 *
 *-------------------------------------------------------------
 */

module user_proj_example #(
    parameter BITS = 32
)(
`ifdef USE_POWER_PINS
    inout vccd1,	// User area 1 1.8V supply
    inout vssd1,	// User area 1 digital ground
`endif

    // Wishbone Slave ports (WB MI A)
    input wb_clk_i,
    input wb_rst_i,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i,
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i,
    output wbs_ack_o,
    output [31:0] wbs_dat_o,

    // Logic Analyzer Signals
    input  [127:0] la_data_in,
    output [127:0] la_data_out,
    input  [127:0] la_oenb,

    // IOs
    input  [`MPRJ_IO_PADS-1:0] io_in,
    output [`MPRJ_IO_PADS-1:0] io_out,
    output [`MPRJ_IO_PADS-1:0] io_oeb,

    // IRQ
    output [2:0] irq
);
    
    wire [7:0] inAddress, inRom, inRam, inPage, inValue;
    wire       masterWrite, writeRom, writeRam, writePage;
    wire [7:0] user_abus, user_dfor;
    wire       user_romce  = (user_abus[7:6] == 2'b00);
    wire       user_ramce  = (user_abus[7:6] == 2'b01);
    wire       user_pagece = (user_abus[7:6] == 2'b10);
    wire       user_ioce   = (user_abus[7:6] == 2'b11);
    wire [3:0] user_masce  = {user_romce, user_ramce, user_pagece, user_ioce};
    
    wire       user_halt, user_rd, user_wr;
    wire [7:0] user_rom, user_ram, user_page;
    wire [7:0] user_dback = (user_romce)  ? user_rom   : 
                            (user_ramce)  ? user_ram   : 
                            (user_pagece) ? user_page  : 
                            (user_ioce)   ? user_iobus : 8'h00;
    
    wire [2:0] pstate;
    wire [7:0] regR0, regR1, regR2, regR3;
    wire       pwmA_q0, pwmA_n0;
    wire       pwmB_q0, pwmB_n0;
    wire       pwmC_q0, pwmC_n0;
    wire [7:0] user_gpio_in, user_gpio_en, user_gpio_out;
    wire [7:0] user_ioGPIO;
    wire [7:0] user_ioPWMA;
    wire [7:0] user_ioPWMB;
    wire [7:0] user_ioPWMC;
    wire       user_ioGPIOce = user_ioce & (user_abus[5:4] == 2'b00);
    wire       user_ioPWMAce = user_ioce & (user_abus[5:4] == 2'b01);
    wire       user_ioPWMBce = user_ioce & (user_abus[5:4] == 2'b10);
    wire       user_ioPWMCce = user_ioce & (user_abus[5:4] == 2'b11);
    wire [3:0] user_iomasce  = {user_ioGPIOce, user_ioPWMAce, user_ioPWMBce, user_ioPWMCce};
    wire [7:0] user_iobus    = (user_ioGPIOce) ? user_ioGPIO: 
                               (user_ioPWMAce) ? user_ioPWMA: 
                               (user_ioPWMBce) ? user_ioPWMB: 
                               (user_ioPWMCce) ? user_ioPWMC: 8'h00;
    
    wire clk;
    wire rst;

    wire [`MPRJ_IO_PADS-1:0] io_in;
    wire [`MPRJ_IO_PADS-1:0] io_out;
    wire [`MPRJ_IO_PADS-1:0] io_oeb;

    wire valid;
    wire [3:0] wstrb;

    // WB MI A
    //assign valid     = wbs_cyc_i && wbs_stb_i; 
    //assign wstrb     = wbs_sel_i & {4{wbs_we_i}};
    //assign wbs_dat_o = rdata;
    //assign wdata     = wbs_dat_i;

    // IO
    assign io_out = {user_gpio_out, pwmA_q0, pwmB_q0, pwmC_q0, pwmA_n0, pwmB_n0, pwmC_n0, user_halt, {(`MPRJ_IO_PADS-1-8-6-1){1'b0}}};
    assign io_oeb = {user_gpio_en,  {(`MPRJ_IO_PADS-1-8){rst}}};

    // IRQ
    assign irq = 3'b000;	// Unused
    
    // LA
    assign la_data_out = {pstate, regR0, regR1, regR2, regR3, user_halt, user_gpio_out, user_rd, user_wr, user_abus, user_dfor, user_dback, user_masce, user_iomasce, 1'b0, masterWrite, clk, rst, inRom, inRam, inPage};
    // Assuming LA probes [63:32] are for controlling the count register  
    
    assign         clk =  (~la_oenb[0])  ? la_data_in[0]     :  wb_clk_i;
    assign         rst =  (~la_oenb[1])  ? la_data_in[1]     : irst ^ wb_rst_i;
    wire          irst =  (~la_oenb[2])  ? la_data_in[2]     : 1'b1;
    assign masterWrite =  (~la_oenb[3])  ? la_data_in[3]     : 1'b0;
    assign writePage   =  (~la_oenb[4])  ? la_data_in[4]     : 1'b0;
    assign writeRam    =  (~la_oenb[5])  ? la_data_in[5]     : 1'b0;
    assign writeRom    =  (~la_oenb[6])  ? la_data_in[6]     : 1'b0;
    assign inValue     = ~la_oenb[15:7]  ? la_data_in[15:7]  : 8'h00;
    assign inAddress   = ~la_oenb[23:16] ? la_data_in[23:16] : 8'h00;
    
    MinxTop processor (
      .clk(clk)
    , .clr(rst)
    , .pstate(pstate)
    , .regR0(regR0)
    , .regR1(regR1)
    , .regR2(regR2)
    , .regR3(regR3)
    , .abus(user_abus)
    , .dbuso(user_dfor)
    , .dbusi(user_dback)
    , .rd(user_rd)
    , .wr(user_wr)
    , .sig_halt(user_halt)
    );
    
    rom_unit #(6, 8) ROM (
      .address(user_abus)
    , .dbuso(user_rom)
    
    , .clk(clk)
    , .addressw(inAddress)
    , .dbusr(inRom)
    , .dbusw(inValue)
    , .we(writeRom)
    );
    
    ram_unit #(6, 8) RAM (
      .clk(clk)
    , .address(user_abus)
    , .dbuso(user_ram)
    , .dbusi(user_dfor)
    , .ce(user_ramce)
    , .we(user_wr)
    
    , .iaddress(inAddress)
    , .idbuso(inRam)
    , .idbusi(inValue)
    , .ice(masterWrite)
    , .iwe(writePage)
    );
    
    ram_unit #(6, 8) PAGERAM (
      .clk(clk)
    , .address(user_abus)
    , .dbuso(user_page)
    , .dbusi(user_dfor)
    , .ce(user_pagece)
    , .we(user_wr)
    
    , .iaddress(inAddress)
    , .idbuso(inPage)
    , .idbusi(inValue)
    , .ice(masterWrite)
    , .iwe(writeRam)
    );
    
    pwm pmodA (
      .clk(clk)
    , .rst(rst)
    , .address(user_abus[2:0])
    , .databi(user_dfor)
    , .databo(user_ioPWMA)
    , .cen(user_ioPWMAce)
    , .wr(user_wr)
    , .q0(pwmA_q0)
    , .n0(pwmA_n0)
    );

    pwm pmodB (
      .clk(clk)
    , .rst(rst)
    , .address(user_abus[2:0])
    , .databi(user_dfor)
    , .databo(user_ioPWMB)
    , .cen(user_ioPWMBce)
    , .wr(user_wr)
    , .q0(pwmB_q0)
    , .n0(pwmB_n0)
    );

    pwm pmodC (
      .clk(clk)
    , .rst(rst)
    , .address(user_abus[2:0])
    , .databi(user_dfor)
    , .databo(user_ioPWMC)
    , .cen(user_ioPWMCce)
    , .wr(user_wr)
    , .q0(pwmC_q0)
    , .n0(pwmC_n0)
    );
    
    GPIO gpioblock (
      .clk(clk)
    , .rst(rst)
    
    , .address(user_abus[1:0])
    , .databi(user_dfor)
    , .databo(user_ioGPIO)
    , .cen(user_ioGPIOce)
    
    , .wr(user_wr)
    , .port_in (user_gpio_in)
    , .port_en (user_gpio_en)
    , .port_out(user_gpio_out)
    );
    
endmodule

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


// Op-codes
`define OPNOP  4'b0000 //NOP
`define OPADD  4'b0001 //ADD Rd, Rs
`define OPADC  4'b0010 //ADC Rd, Rs
`define OPSUB  4'b0011 //SUB Rd, Rs
`define OPAND  4'b0100 //AND Rd, Rs
`define OPNOT  4'b0101 //NOT Rd
`define OPIOR  4'b0110 //OR Rd, Rs
`define OPEOR  4'b0111 //XOR Rd, Rs
`define OPRD   4'b1000 //RD R, (IMMA)
`define OPWR   4'b1001 //WR (IMMA), R
`define OPLD   4'b1010 //LD R, IMM
`define OPSTO  4'b1011 //STO (R), R
`define OPBR   4'b1100 //Branch
`define OPBIT  4'b1101 //Branch if bit
`define OPBRC  4'b1110 //Free
`define OPHALT 4'b1111 //Halt the machine

//Register Selections
`define R0 2'b00
`define R1 2'b01
`define R2 2'b10
`define R3 2'b11
`define RX 2'b00

//Condition bits
`define BRA    4'b0000
`define BRN    4'b0001 
`define BRC    4'b0010 
`define BRZ    4'b0011 
`define BRNC   4'b0100 
`define BRNZ   4'b0101 
`define BRRJ   4'b1111 //Jump to address in R3

//Bit Conditions
`define CLRB0  4'b0000
`define CLRB1  4'b0001
`define CLRB2  4'b0010
`define CLRB3  4'b0011
`define CLRB4  4'b0100
`define CLRB5  4'b0101
`define CLRB6  4'b0110
`define CLRB7  4'b0111
`define SETB0  4'b1000
`define SETB1  4'b1001
`define SETB2  4'b1010
`define SETB3  4'b1011
`define SETB4  4'b1100
`define SETB5  4'b1101
`define SETB6  4'b1110
`define SETB7  4'b1111

module MinxTop (
  input clk
, input clr 

, output wire [2:0] pstate
, output wire [7:0] regR0
, output wire [7:0] regR1
, output wire [7:0] regR2
, output wire [7:0] regR3

, output wire [7:0] abus
, output wire [7:0] dbuso
, input  wire [7:0] dbusi
, output wire       rd
, output wire       wr
, output wire       sig_halt
);

  //Data nets
  wire [7:0] instruction;
  
  //Control nets
  wire [2:0] sel_dbus_mux;
  wire [1:0] sel_bus2_mux;
  wire ld_r0, ld_r1, ld_r2, ld_r3, ld_pc, inc_pc, ld_ir;
  wire ld_address_reg, ld_reg_y, ld_reg_z, carry, zero;
    
  processing_unit processor(
    .clk(clk)
,   .clr(clr)
,   .instruction(instruction)
,   .zero_flag(zero)
,   .carry_flag(carry)
,   .address(abus)
,   .dbuso(dbuso)
,   .dbusi(dbusi)
,   .ld_r0(ld_r0)
,   .regR0(regR0)
,   .ld_r1(ld_r1)
,   .regR1(regR1)
,   .ld_r2(ld_r2)
,   .regR2(regR2)
,   .ld_r3(ld_r3)
,   .regR3(regR3)
,   .ld_pc(ld_pc)
,   .inc_pc(inc_pc)
,   .ld_ir(ld_ir)
,   .ld_address_reg(ld_address_reg)
,   .ld_reg_y(ld_reg_y)
,   .ld_reg_z(ld_reg_z)
,   .sel_dbus_mux(sel_dbus_mux)
,   .sel_bus2_mux(sel_bus2_mux)
);

  control_unit controller(
    .clk(clk)
,   .clr(clr)

,   .pstate(pstate)
,   .ld_r0(ld_r0)
,   .ld_r1(ld_r1)
,   .ld_r2(ld_r2)
,   .ld_r3(ld_r3)
,   .ld_pc(ld_pc)
,   .inc_pc(inc_pc)
,   .sel_dbus_mux(sel_dbus_mux)
,   .sel_bus2_mux(sel_bus2_mux)
,   .ld_ir(ld_ir)
,   .ld_address_reg(ld_address_reg)
,   .ld_reg_y(ld_reg_y)
,   .ld_reg_z(ld_reg_z)
,   .read(rd)
,   .write(wr)
,   .instruction(instruction)
,   .regR0(regR0)
,   .zero(zero)
,   .carry(carry)
,   .sig_halt(sig_halt)
);

endmodule

module control_unit (
  input            clk
, input            clr
, input            carry
, input            zero
, input      [7:0] instruction
, input      [7:0] regR0

, output reg [2:0] pstate
, output wire      ld_r0
, output wire      ld_r1
, output wire      ld_r2
, output wire      ld_r3
, output reg       ld_pc
, output reg       inc_pc
, output reg       ld_ir
, output reg       ld_address_reg
, output reg       ld_reg_y
, output reg       ld_reg_z
, output reg       write
, output reg       read
, output reg       sig_halt
, output reg [2:0] sel_dbus_mux
, output reg [1:0] sel_bus2_mux
);

parameter opcode_size = 4;
parameter src_size    = 2;
parameter dest_size   = 2;

// State Machine Parameters
parameter STATE_IDLE     = 3'b000;
parameter STATE_FETCH1   = 3'b001;
parameter STATE_FETCH2   = 3'b010;
parameter STATE_DECODE   = 3'b011;
parameter STATE_EXECUTE  = 3'b100;
parameter STATE_STATE1   = 3'b101;
parameter STATE_STATE2   = 3'b110;
parameter STATE_HALT     = 3'b111;

parameter     REG_R0     = 2'b00;
parameter     REG_R1     = 2'b01;
parameter     REG_R2     = 2'b10;
parameter     REG_R3     = 2'b11;
parameter SEL_BUS_ALU    = 2'b00;
parameter SEL_BUS_DB     = 2'b01;
parameter SEL_BUS_MEM    = 2'b10;
parameter SEL_BUS_R0     = 3'b000;
parameter SEL_BUS_R1     = 3'b001;
parameter SEL_BUS_R2     = 3'b010;
parameter SEL_BUS_R3     = 3'b011;
parameter SEL_BUS_PC     = 3'b100;

// Source & Destination codes

reg       ld_reg = 0;
reg [2:0] nstate = 0;

assign ld_r0 = (dest == 2'b00) ? ld_reg : 1'b0;
assign ld_r1 = (dest == 2'b01) ? ld_reg : 1'b0;
assign ld_r2 = (dest == 2'b10) ? ld_reg : 1'b0;
assign ld_r3 = (dest == 2'b11) ? ld_reg : 1'b0;

wire [3:0] opcode = instruction [7:4];
wire [3:0] cond   = instruction [3:0]; 
wire [1:0] src    = instruction [3:2];
wire [1:0] dest   = instruction [1:0];

always @ (posedge clk or negedge clr)
  begin
    if(!clr)
        pstate <= STATE_IDLE;
    else
        pstate <= nstate;
  end

always @*
  begin
    ld_reg = 0;
    ld_pc = 0;
    ld_ir = 0;
    ld_address_reg = 0;
    ld_reg_y = 0;
    ld_reg_z = 0;
    inc_pc = 0;

    read  = 0;
    write = 0;

    case(pstate)
        STATE_IDLE   : begin 
            sig_halt       = 0;
            ld_reg         = 0;
            read           = 0;
            write          = 0;
            sel_dbus_mux   = SEL_BUS_PC;
            sel_bus2_mux   = SEL_BUS_DB; 
            sig_halt       = 0;
            nstate         = STATE_FETCH1; 
        end
        
        STATE_FETCH1 : begin
            sig_halt       = 0;
            ld_reg         = 0;
            read           = 0;
            write          = 0;
            ld_address_reg = 1;
            sel_dbus_mux   = SEL_BUS_PC;
            sel_bus2_mux   = SEL_BUS_DB; 
            nstate         = STATE_FETCH2;
        end
        
        STATE_FETCH2 : begin
            sig_halt       = 0;
            ld_reg         = 0;
            read           = 1;
            write          = 0;
            ld_ir          = 1;
            inc_pc         = 1;
            sel_dbus_mux   = SEL_BUS_PC;
            sel_bus2_mux   = SEL_BUS_MEM;
            nstate         = STATE_DECODE;
        end
        
        STATE_DECODE : case (opcode)
                    `OPNOP     : begin
                      sig_halt       = 0;
                      ld_reg         = 0;
                      nstate         = STATE_FETCH1;
                    end
                    `OPADD, `OPADC, `OPSUB, `OPAND, `OPEOR, `OPIOR : begin
                                sig_halt     = 0;
                                ld_reg       = 0;
                                ld_reg_y     = 1;
                                sel_dbus_mux = {1'b0, src};
                                sel_bus2_mux = SEL_BUS_DB; 
                                nstate       = STATE_EXECUTE;
                    end
                    `OPNOT     : begin
                                sig_halt       = 0;
                                ld_reg         = 1;
                                ld_reg_z       = 1;
                                sel_dbus_mux   = {1'b0, src};
                                sel_bus2_mux   = SEL_BUS_ALU; 
                                nstate         = STATE_FETCH1;
                    end
                    `OPRD      : begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                ld_address_reg = 1;
                                sel_dbus_mux   = SEL_BUS_PC;
                                sel_bus2_mux   = SEL_BUS_DB;
                                nstate         = STATE_STATE1;
                    end
                    `OPWR      : begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                ld_address_reg = 1;
                                sel_dbus_mux   = SEL_BUS_PC;
                                sel_bus2_mux   = SEL_BUS_DB;
                                nstate         = STATE_STATE1;
                    end
                    `OPLD      : begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                ld_address_reg = 1;
                                sel_dbus_mux   = SEL_BUS_PC;
                                sel_bus2_mux   = SEL_BUS_DB;
                                nstate         = STATE_STATE1;
                    end
                    `OPSTO     : begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                ld_address_reg = 1;
                                sel_dbus_mux   = {1'b0, dest};
                                sel_bus2_mux   = SEL_BUS_DB;
                                nstate         = STATE_STATE1;
                    end
                    `OPBR      : begin
                                  case( cond )
                                    `BRA  : begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_STATE1;
                                           end
                                    `BRN  : begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 0;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_FETCH1;
                                           end
                                    `BRC  : if(carry == 1'b1) begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_STATE1;
                                           end else begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             inc_pc         = 1;
                                             nstate         = STATE_FETCH1;
                                           end
                                    `BRZ  : if(zero == 1'b1) begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_STATE1;
                                           end else begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             inc_pc         = 1;
                                             nstate         = STATE_FETCH1;
                                           end
                                    `BRNC : if(carry == 1'b0) begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_STATE1;
                                           end else begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             inc_pc         = 1;
                                             nstate         = STATE_FETCH1;
                                           end
                                    `BRNZ : if(zero == 1'b0) begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             sel_dbus_mux   = SEL_BUS_PC;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_STATE1;
                                           end else begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             inc_pc         = 1;
                                             nstate         = STATE_FETCH1;
                                           end
                                    `BRRJ : begin
                                             sig_halt       = 0;
                                             ld_reg         = 0;
                                             ld_address_reg = 1;
                                             ld_pc          = 1;
                                             sel_dbus_mux   = SEL_BUS_R3;
                                             sel_bus2_mux   = SEL_BUS_DB;
                                             nstate         = STATE_FETCH1;
                                           end
                                    default : begin
                                                sig_halt       = 0;
                                                ld_reg         = 0;
                                                ld_address_reg = 0;
                                                sel_dbus_mux   = SEL_BUS_PC;
                                                sel_bus2_mux   = SEL_BUS_DB;
                                                nstate         = STATE_FETCH1;
                                              end
                                  endcase
                                end
                    `OPBIT     : begin
                                  case( cond[2:0] )
                                    3'b000 : begin
                                               if(regR0[0] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b001 : begin
                                               if(regR0[1] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b010 : begin
                                               if(regR0[2] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b011 : begin
                                               if(regR0[3] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b100 : begin
                                               if(regR0[4] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b101 : begin
                                               if(regR0[5] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b110 : begin
                                               if(regR0[6] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                    3'b111 : begin
                                               if(regR0[7] == cond[3]) begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 ld_address_reg = 1;
                                                 sel_dbus_mux   = SEL_BUS_PC;
                                                 sel_bus2_mux   = SEL_BUS_DB;
                                                 nstate         = STATE_STATE1;
                                               end else begin
                                                 sig_halt       = 0;
                                                 ld_reg         = 0;
                                                 inc_pc         = 1;
                                                 nstate         = STATE_FETCH1;
                                               end
                                             end
                                  endcase
                                end
                    `OPBRC     : if(carry == 1) begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                ld_address_reg = 1;
                                sel_dbus_mux   = SEL_BUS_PC;
                                sel_bus2_mux   = SEL_BUS_DB;
                                nstate         = STATE_STATE1;
                              end else begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                inc_pc         = 1;
                                nstate         = STATE_FETCH1;
                    end
                    `OPHALT    : begin
                                sig_halt       = 0;
                                ld_reg         = 0;
                                nstate         = STATE_HALT;
                    end
                    default : begin 
                                sig_halt       = 0;
                                ld_reg         = 0;
                                nstate = STATE_HALT;
                    end
                endcase

        STATE_EXECUTE : begin
            sig_halt     = 0;
            ld_reg       = 1;
            ld_reg_z     = 1;
            sel_dbus_mux = {1'b0, dest};
            sel_bus2_mux = SEL_BUS_ALU;
            nstate       = STATE_FETCH1;
        end
        
        STATE_STATE1 : begin
          case(opcode)
            `OPRD : begin
              sig_halt       = 0;
              ld_reg         = 0;
              read           = 1;
              ld_address_reg = 1;
              inc_pc         = 1;
              sel_bus2_mux   = SEL_BUS_MEM;
              sel_dbus_mux   = SEL_BUS_PC;
              nstate         = STATE_STATE2;
            end
            `OPWR : begin
              sig_halt       = 0;
              ld_reg         = 0;
              read           = 1;
              ld_address_reg = 1;
              inc_pc         = 1;
              sel_bus2_mux   = SEL_BUS_MEM;
              sel_dbus_mux   = SEL_BUS_PC;
              nstate         = STATE_STATE2;
            end
            `OPLD : begin
              sig_halt       = 0;
              ld_reg         = 1;
              read           = 1;
              inc_pc         = 1;
              sel_bus2_mux   = SEL_BUS_MEM;
              sel_dbus_mux   = SEL_BUS_PC;
              nstate         = STATE_FETCH1;
            end
            `OPSTO : begin
              sig_halt       = 0;
              ld_reg         = 0;
              read           = 0;
              write          = 1;
              sel_dbus_mux   = {1'b0, src};
              sel_bus2_mux   = SEL_BUS_MEM;
              nstate         = STATE_FETCH1;
            end
            `OPBR, `OPBRC, `OPBIT: begin
              sig_halt       = 0;
              ld_reg         = 0;
              read           = 1;
              ld_pc          = 1;
              sel_dbus_mux   = SEL_BUS_PC;
              sel_bus2_mux   = SEL_BUS_MEM;
              nstate         = STATE_FETCH1;
            end
          endcase
        end
        
        STATE_STATE2 : begin
          case(opcode)
            `OPRD : begin
              sig_halt       = 0;
              ld_reg         = 1;
              read           = 1;
              sel_bus2_mux   = SEL_BUS_MEM;
              sel_dbus_mux   = SEL_BUS_PC;
              nstate         = STATE_FETCH1;
            end
            `OPWR : begin
              sig_halt       = 0;
              ld_reg         = 0;
              write          = 1;
              sel_dbus_mux   = {1'b0, src};
              sel_bus2_mux   = SEL_BUS_MEM;
              nstate         = STATE_FETCH1;
            end
          endcase
        end
        
        STATE_HALT: begin
            ld_reg           = 0;
            sig_halt         = 1;
            nstate           = STATE_HALT;
        end
        default: nstate      = STATE_IDLE;
    endcase
  end

endmodule   

module processing_unit (
  input             clk
, input             clr
, output wire [7:0] instruction
, output wire       zero_flag
, output wire       carry_flag
, output wire [7:0] address
, output reg  [7:0] dbuso
, input       [7:0] dbusi
, input             ld_r0
, output wire [7:0] regR0
, input             ld_r1
, output wire [7:0] regR1
, input             ld_r2
, output wire [7:0] regR2
, input             ld_r3
, output wire [7:0] regR3
, input             ld_ir
, input             ld_address_reg
, input             ld_reg_y
, input             ld_reg_z
, input             ld_pc
, input             inc_pc
, input       [2:0] sel_dbus_mux
, input       [1:0] sel_bus2_mux
);

  // Intermediate wires declaration
  wire       reg_ZeroFlag, reg_CarryFlag;
  wire                     alu_carry_flag;
  wire [7:0] reg_R0, reg_R1, reg_R2, reg_R3, reg_MAR, reg_IR, reg_PC, reg_Y;
  reg  [7:0] bus2;
  reg  [7:0] aluY;
  wire [7:0] aluAdderY;
  wire       alu_zero_flag = ~|aluY;
  wire [3:0] opcode = instruction [7:4];
  wire       aluAdderC = (opcode == `OPSUB) ? 1'b1 : ((opcode == `OPADD) ? 1'b0 : reg_CarryFlag);
  wire [7:0] aluAdderB = (opcode == `OPSUB) ? ~dbuso : dbuso;
  
  assign regR0       = reg_R0;
  assign regR1       = reg_R1;
  assign regR2       = reg_R2;
  assign regR3       = reg_R3;
  assign carry_flag  = reg_CarryFlag;
  assign zero_flag   = reg_ZeroFlag;
  assign address     = reg_MAR;
  assign instruction = reg_IR;
  
  // Instantiations of register units, flipflops, address register, instruction register, program counter, ALU and Multiplexers
  MinxProgramCounter #(8) unit_PC (clk, clr, ld_pc, inc_pc, bus2, reg_PC);
  
  //Memory Address Register
  MinxRegister #(8) unit_MAR (clk, clr, ld_address_reg, bus2, reg_MAR);
  
  //Instruction Register and alu_opcode_seperation
  MinxRegister #(8) unit_IR  (clk, clr, ld_ir, bus2, reg_IR);
  
  //Y register
  MinxRegister #(8) unit_Y   (clk, clr, ld_reg_y, bus2, reg_Y);

  //Alu Flags
  MinxRegister #(1) unit_ZF  (clk, clr, ld_reg_z, alu_zero_flag,  reg_ZeroFlag);
  MinxRegister #(1) unit_CF  (clk, clr, ld_reg_z, alu_carry_flag, reg_CarryFlag);

  // Clear is an active low signal - Register Partition
  MinxRegister #(8) unit_R0  (clk, clr, ld_r0, bus2, reg_R0);
  MinxRegister #(8) unit_R1  (clk, clr, ld_r1, bus2, reg_R1);
  MinxRegister #(8) unit_R2  (clk, clr, ld_r2, bus2, reg_R2);
  MinxRegister #(8) unit_R3  (clk, clr, ld_r3, bus2, reg_R3);

  always @* 
    case(sel_dbus_mux)
      3'b000  : dbuso <= reg_R0;
      3'b001  : dbuso <= reg_R1;
      3'b010  : dbuso <= reg_R2;
      3'b011  : dbuso <= reg_R3;
      3'b100  : dbuso <= reg_PC;
      3'b101  : dbuso <= 8'h00;
      3'b110  : dbuso <= 8'h00;
      3'b111  : dbuso <= 8'h00;
      default : dbuso <= 8'h00;
    endcase
  
  always @*
    case(sel_bus2_mux)
      2'b00   : bus2 <= aluY;
      2'b01   : bus2 <= dbuso;
      2'b10   : bus2 <= dbusi;
      2'b11   : bus2 <= 8'h00;
      default : bus2 <= 8'h00;
    endcase

  cla_adder_parm #(8) addmagic (aluAdderC, reg_Y, aluAdderB, aluAdderY, alu_carry_flag); 
  
  always @*
    case(opcode)
      `OPNOP  : aluY = 0;
      `OPADD  : aluY = aluAdderY;
      `OPADC  : aluY = aluAdderY;
      `OPSUB  : aluY = aluAdderY;
      `OPAND  : aluY = reg_Y & dbuso;
      `OPNOT  : aluY =        ~dbuso;
      `OPIOR  : aluY = reg_Y | dbuso;
      `OPEOR  : aluY = reg_Y ^ dbuso;
      default : aluY = 0;
    endcase

endmodule

module cla_adder_parm #(parameter D = 16) (
  input          carry_i,
  input  [D-1:0] A,
  input  [D-1:0] B,
  output [D-1:0] result_o, 
  output         carry_o
);
  
  wire [D-0:0] w_C;
  wire [D-1:0] w_G, w_P; 

  assign w_C[0]  = carry_i;
  assign carry_o = w_C[D-0];

  genvar ii; //Generate the internal signals
  generate
    for (ii=0; ii<D; ii=ii+1) 
      begin
        assign result_o[ii] = A[ii]   ^  B[ii] ^ w_C[ii];
        assign w_G[ii]      = A[ii]   &  B[ii];
        assign w_P[ii]      = A[ii]   |  B[ii];
        assign w_C[ii+1]    = w_G[ii] | (w_P[ii] & w_C[ii]);
      end
  endgenerate
 
endmodule

module MinxRegister #( 
  parameter W = 8
) (
  input              clk
, input              rst

, input              LD
, input      [W-1:0] D
, output reg [W-1:0] Q
);

  initial Q = 0;
  
  always @ (posedge clk or negedge rst)
    begin
        if( rst == 1'b0 )
          Q <= 0;
        else if (LD == 1'b1)
          Q <= D;
        else
          Q <= Q;
    end

endmodule

module MinxProgramCounter #( 
  parameter W = 8
) (
  input              clk
, input              rst

, input              LD
, input              INC
, input      [W-1:0] D
, output reg [W-1:0] Q
);

  initial Q = 0;
  
  always @ (posedge clk or negedge rst)
    begin
        if( rst == 1'b0 )
          Q <= 0;
        else if (LD == 1'b1)
          Q <= D;
        else if (INC == 1'b1)
          Q <= Q + 1;
        else
          Q <= Q;
    end

endmodule

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

`default_nettype wire
