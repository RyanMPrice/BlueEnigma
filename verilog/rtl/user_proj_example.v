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
    wire       user_paegce = (user_abus[7:6] == 2'b10);
    wire       user_ioce   = (user_abus[7:6] == 2'b11);
    wire [3:0] user_masce  = {user_romce, user_ramce, user_pagece, user_ioce};
    
    wire [7:0] user_rom, user_ram, user_page;
    wire [7:0] user_dback = (user_romce) ? user_rom   : 
                            (user_ramce) ? user_ram   : 
                            (user_pagce) ? user_page  : 
                            (user_ioce)  ? user_iobus : 8'h00;
    
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
    wire       user_ioGPIOce = (user_abus[5:4] == 2'b00);
    wire       user_ioPWMAce = (user_abus[5:4] == 2'b01);
    wire       user_ioPWMBce = (user_abus[5:4] == 2'b10);
    wire       user_ioPWMCce = (user_abus[5:4] == 2'b11);
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
    assign valid     = wbs_cyc_i && wbs_stb_i; 
    assign wstrb     = wbs_sel_i & {4{wbs_we_i}};
    assign wbs_dat_o = rdata;
    assign wdata     = wbs_dat_i;

    // IO
    assign io_out = {user_gpio_out, pwmA_q0, pwmB_q0, pwmC_q0, pwmA_n0, pwmB_qn, pwmC_n0, user_halt, {(`MPRJ_IO_PADS-1-8-6-1){1'b0}}};
    assign io_oeb = {user_gpio_en,  {(`MPRJ_IO_PADS-1-8){rst}}};

    // IRQ
    assign irq = 3'b000;	// Unused
    
    // LA
    assign la_data_out = {0, pstate, regR0, regR1, regR2, regR3, user_halt, user_gpio_out, user_rd, user_wr, user_abus, user_dfor, user_dback, user_masce, user_iomasce, 1'b0, masterWrite, clk, rst, inRom, inRam, inPage};
    // Assuming LA probes [63:32] are for controlling the count register  
    
    assign         clk =  (~la_oenb[0])  ? la_data_in[0]     : wb_clk_i;
    assign         rst =  (~la_oenb[1])  ? la_data_in[1]     : wb_rst_i;
    assign masterWrite =  (~la_oenb[2])  ? la_data_in[2]     : 1'b0;
    assign writePage   =  (~la_oenb[3])  ? la_data_in[3]     : 1'b0;
    assign writeRam    =  (~la_oenb[4])  ? la_data_in[4]     : 1'b0;
    assign writeRom    =  (~la_oenb[5])  ? la_data_in[5]     : 1'b0;
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
    
    ram_unit #(6, 8) RAM (
      .clk(clk)
    , .address(user_abus)
    , .dbuso(user_ram)
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
    , .cen(pwm_ioPWMAce)
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
    , .cen(pwm_ioPWMBce)
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
    , .cen(pwm_ioPWMCce)
    , .wr(user_wr)
    , .q0(pwmC_q0)
    , .n0(pwmC_n0)
    );
    
    GPIO gpioblock (
      .clk(clk)
    , .rst(rst)
    
    , .address(user_address[1:0])
    , .databi(user_dfor)
    , .databo(user_ioGPIO)
    , .cen(user_ioGPIOce)
    
    , .wr(user_wr)
    , .port_in (user_gpio_in)
    , .port_en (user_gpio_en)
    , .port_out(user_gpio_out)
    );
    
endmodule
`default_nettype wire
