`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/16/2021 08:24:33 PM
// Design Name: 
// Module Name: testbench
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module testbench;

/*Uncomment following for instruction memory*/

//reg  [31:0]program_counter;
//wire [31:0]instruction;

//Instruction_Memory A1(.pc(program_counter),.instruction(instruction));

//initial
//    begin
//    program_counter = 0;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 program_counter = program_counter+4;
//#50 $stop;
        
//    end

/*Uncomment following for instruction Fetch */

//reg [31:0]instruction;

//wire [6:0]opcode;
//wire [4:0]rd;
//wire [4:0]rs1;
//wire [4:0]rs2;
//wire [2:0]func3; 
//wire [6:0]func7;
//wire [20:0]imm;

//Instruction_fetch A1(.instruction(instruction), .opcode(opcode),.rd(rd), .rs1(rs1), .rs2(rs2), .func3(func3), .func7(func7), .imm(imm));

//initial
//begin
//instruction     = 32'b00000000110000000000010000010011; // addi x8, x0, 12
//#50 instruction = 32'b00000000100100000000010010010011; // addi x9, x0, 9
//#50 instruction = 32'b00000000100101000000110001100011; // beq  x8, x9, stop
//#50 instruction = 32'b00000000100101000100101001100011; // blt  x8, x9, less
//#50 instruction = 32'b01000000100101000000010000110011; // sub  x8, x8, x9
//#50 instruction = 32'b11111111010111111111000001101111; // j    gcd 
//#50 instruction = 32'b01000000100001001000010010110011; // sub  x9, x9, x8
//#50 instruction = 32'b11111110110111111111000001101111; // j    gcd
//#50 instruction = 32'b00000000000000000000000001101111; // j    stop
//#50 $stop;
//end

reg rst,clk;

wire [6:0]result;
main_module a1 (.clk(clk), .LED_out(result),.rst(rst));
//main a1 (.clk(clk), .Result(result),.rst(rst));
initial
begin
//execute=1;
clk = 1'b1;
rst = 1; 
#10;rst = 0;

end

initial begin
forever #10 clk=~clk;
end
endmodule