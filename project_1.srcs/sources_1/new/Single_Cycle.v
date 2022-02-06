

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    12:49:01 01/10/2021 
// Design Name: 
// Module Name:    Basic RISC-V single cycle implementation on Verilog 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
//module main_module(clk, Anode_Activate, LED_out,rst);
//wire [7:0]Result;
//input clk,rst;						// 1 button to reset, clock signal as input

//output reg[7:0] Anode_Activate;		// Anodes to control 7-segments
//output reg [7:0] LED_out;			// output result to be sent on 7-segments
//wire [31:0] pc;


//	// ALL modules will be called in this file. Code will be executed and results will be shown on 7-segment display
//// Code segment for BCD to 7-segment Decoder. Keep this code as it is
//reg [31:0] counter;		// A 32 bit flashing counter
//reg toggle = 0;			// A variable to toggle between two 7-segments 


////wire new_clk;

//main   f4 (.rst(rst), .clk(clk),.Result(Result));

//always @(posedge clk)
//    begin
//            if(counter>=10) begin
//                 counter <= 0;
//				 toggle = ~toggle; end
//            else begin
//                counter <= counter + 1;
//				end
//    end 
//    // anode activating signals for 8 segments, digit period of 1ms
//    // decoder to generate anode signals 
//    always @(*)
//    begin
//        case(toggle)
//        1'b0: begin
//            Anode_Activate = 8'b01111111; 
//            // activate SEGMENT1 and Deactivate all others
//              end
//        1'b1: begin
//            Anode_Activate = 8'b10111111; 
//            // activate LED2 and Deactivate all others    
//               end
//        endcase
//    end
//    // Cathode patterns of the 7-segment 1 LED display 
//    always @(*)
//    begin
//	if (toggle) begin
//        case(Result[3:0])				// First 4 bits of Result from ALU will be displayed on 1st segment
//        4'b0000: LED_out = 7'b0000001; // "0"     
//        4'b0001: LED_out = 7'b1001111; // "1" 
//        4'b0010: LED_out = 7'b0010010; // "2" 
//        4'b0011: LED_out = 7'b0000110; // "3" 
//        4'b0100: LED_out = 7'b1001100; // "4" 
//        4'b0101: LED_out = 7'b0100100; // "5" 
//        4'b0110: LED_out = 7'b0100000; // "6" 
//        4'b0111: LED_out = 7'b0001111; // "7" 
//        4'b1000: LED_out = 7'b0000000; // "8"     
//        4'b1001: LED_out = 7'b0000100; // "9"
//		4'b1010: LED_out = 7'b0001000; // "A"     
//        4'b1011: LED_out = 7'b1100000; // "b"     
//        4'b1100: LED_out = 7'b0110001; // "C"     
//        4'b1101: LED_out = 7'b1000010; // "d"     
//        4'b1110: LED_out = 7'b0110000; // "E"     
//        4'b1111: LED_out = 7'b0111000; // "F"     
        
//        default: LED_out = 7'b0000001; // "0"
//        endcase
//		end
    

//	// Cathode patterns of the 7-segment 2 LED display
//if(!toggle) begin	
//        case(Result[7:4])			// Next 4 bits of Result from ALU will be displayed on 2nd segment
//        4'b0000: LED_out = 7'b0000001; // "0"     
//        4'b0001: LED_out = 7'b1001111; // "1" 
//        4'b0010: LED_out = 7'b0010010; // "2" 
//        4'b0011: LED_out = 7'b0000110; // "3" 
//        4'b0100: LED_out = 7'b1001100; // "4" 
//        4'b0101: LED_out = 7'b0100100; // "5" 
//        4'b0110: LED_out = 7'b0100000; // "6" 
//        4'b0111: LED_out = 7'b0001111; // "7" 
//        4'b1000: LED_out = 7'b0000000; // "8"     
//        4'b1001: LED_out = 7'b0000100; // "9"
//		4'b1010: LED_out = 7'b0001000; // "A"     
//        4'b1011: LED_out = 7'b1100000; // "b"     
//        4'b1100: LED_out = 7'b0110001; // "C"     
//        4'b1101: LED_out = 7'b1000010; // "d"     
//        4'b1110: LED_out = 7'b0110000; // "E"     
//        4'b1111: LED_out = 7'b0111000; // "F"     
        
//        default: LED_out = 7'b0000001; // "0"
//        endcase
//    end
//end

//	// Keep writing your code (calling lower module) here!


//endmodule

module main_module(rst, clk, Anode_Activate, LED_out);
input rst, clk;						// 1 button to reset, clock signal as input
//output alu_z;						// An LED turned ON if result is zero
output reg[7:0] Anode_Activate;		// Anodes to control 7-segments
output reg [6:0] LED_out;			// output result to be sent on 7-segments
wire [31:0] pc;
wire new_clk;
wire [31:0] instruction,out;
main f4 (.clk(clk),.rst(rst),.Result(out));

	// ALL modules will be called in this file. Code will be executed and results will be shown on 7-segment display
// Code segment for BCD to 7-segment Decoder. Keep this code as it is
reg [31:0] counter;		// A 32 bit flashing counter
reg toggle;			// A variable to toggle between two 7-segments 
wire [7:0]Result;
assign Result[7:0]= 12;//out[7:0];
wire [4:0]first_four_bits = out[3:0];
wire [4:0]next_four_bits = out[7:4];
// first_four_bits = out[3:0];
// next_four_bits = out[7:4];

always @(posedge clk)
    begin
        if(!rst) begin
            if(counter>=100000) begin
                 counter <= 0;
				 toggle = ~toggle; end
            else begin
                counter <= counter + 1;
				end
		end
		else begin
		toggle<=0;
		  counter<=0;
		end
    end 
    // anode activating signals for 8 segments, digit period of 1ms
    // decoder to generate anode signals 
    always @(*)
    begin
        
            case(toggle)
            1'b0: begin
                Anode_Activate = 8'b01111111; 
                // activate SEGMENT1 and Deactivate all others
                  end
            1'b1: begin
                Anode_Activate = 8'b10111111; 
                // activate LED2 and Deactivate all others    
                   end
            endcase


    end
    // Cathode patterns of the 7-segment 1 LED display 
    always @(*)
    begin
	if (toggle) begin
        case(out)				// First 4 bits of Result from ALU will be displayed on 1st segment
        32'b0000: LED_out = 7'b0000001; // "0"     
        32'b0001: LED_out = 7'b1001111; // "1" 
        32'b0010: LED_out = 7'b0010010; // "2" 
        32'b0011: LED_out = 7'b0000110; // "3" 
        32'b0100: LED_out = 7'b1001100; // "4" 
        32'b0101: LED_out = 7'b0100100; // "5" 
        32'b0110: LED_out = 7'b0100000; // "6" 
        32'b0111: LED_out = 7'b0001111; // "7" 
        32'b1000: LED_out = 7'b0000000; // "8"     
        32'b1001: LED_out = 7'b0000100; // "9"
		32'b1010: LED_out = 7'b0001000; // "A"     
        32'b1011: LED_out = 7'b1100000; // "b"     
        32'b1100: LED_out = 7'b0110001; // "C"     
        32'b1101: LED_out = 7'b1000010; // "d"     
        32'b1110: LED_out = 7'b0110000; // "E"     
        32'b1111: LED_out = 7'b0111000; // "F"     
        
        //default: LED_out = 7'b0000001; // "0"
        endcase

	end
    

	// Cathode patterns of the 7-segment 2 LED display
if(!toggle) begin	
        case(out[7:4])			// Next 4 bits of Result from ALU will be displayed on 2nd segment
        4'b0000: LED_out = 7'b0000001; // "0"     
        4'b0001: LED_out = 7'b1001111; // "1" 
        4'b0010: LED_out = 7'b0010010; // "2" 
        4'b0011: LED_out = 7'b0000110; // "3" 
        4'b0100: LED_out = 7'b1001100; // "4" 
        4'b0101: LED_out = 7'b0100100; // "5" 
        4'b0110: LED_out = 7'b0100000; // "6" 
        4'b0111: LED_out = 7'b0001111; // "7" 
        4'b1000: LED_out = 7'b0000000; // "8"     
        4'b1001: LED_out = 7'b0000100; // "9"
		4'b1010: LED_out = 7'b0001000; // "A"     
        4'b1011: LED_out = 7'b1100000; // "b"     
        4'b1100: LED_out = 7'b0110001; // "C"     
        4'b1101: LED_out = 7'b1000010; // "d"     
        4'b1110: LED_out = 7'b0110000; // "E"     
        4'b1111: LED_out = 7'b0111000; // "F"     
        
        default: LED_out = 7'b0000011; // "0"
        endcase

    end
end

	// Keep writing your code (calling lower module) here!


endmodule



module main(rst, clk, alu_z, LED_out,Result);

output [31:0]Result;
input rst, clk;						// 1 button to reset, clock signal as input
output alu_z;						// An LED turned ON if result is zero
output reg [6:0] LED_out;			// output result to be sent on 7-segments
wire [31:0] pc;

/* Following wires are newly made.*/

//Following are Control lines
wire [1:0]control_immsrc;
wire control_PCSrc, control_ALUSrc,Zero, less_than,RegWrite;
wire [3:0]control_ALUControl;

//Following are from instruction fetch
wire [31:0] instruction;
wire [6:0]opcode;
wire [2:0]funct3;
wire [6:0]funct7;
wire [4:0] rd,rs1,rs2;

//Follwing are from ALU
wire  [31:0]ALU_result;
wire [31:0] ALU_A,register_file_B;
wire  [31:0]ALU_B;

//Follwing are from sign extender
wire [31:0]sign_extend;


Instruction_fetch   B1 (.instruction(instruction),.opcode(opcode),
                        .rd(rd),.rs1(rs1),.rs2(rs2),
                        .func3(funct3),.func7(funct7));

Control_Unit        B2 (.ALUControl(control_ALUControl), .ALUSrc(control_ALUSrc),
                        .ImmSrc(control_immsrc),.PCSrc(control_PCSrc), .RegWrite(RegWrite),
                        .op(opcode),.funct3(funct3),.Zero(Zero), .less_than(less_than));

extend              B3 (.instr(instruction[31:7]), .immsrc(control_immsrc),    // This module takes instruction 
                        .immext(sign_extend));                           // from instruction memory, immsrc as control 
                                                                         // line
                                                                         // and outputs extended immediate value
                                                                         
address_generator   B4 (.pc(pc), .label_address(sign_extend),            // This module takes label address
                        .clk(clk), .PCSrc(control_PCSrc),.rst(rst));             // from immediate extender, clock as
                                                                         // input, PCSrc as control line and outputs pc.
                                     
Instruction_Memory  B5 (.pc(pc), .instruction(instruction));             // This module takes pc from address 
                                                                         // generator and
                                                                         // outputs instruction.
                                                                         
ALU_2nd_operand_mux B6 (.o(ALU_B),.from_register_file(register_file_B),
                        .from_imm_gen(sign_extend),.sel(control_ALUSrc));
                        
register_file       B7 (.Port_A(ALU_A),.Port_B(register_file_B),.Din(ALU_result),
                        .Addr_A(rs1),.Addr_B(rs2),.Addr_Wr(rd),
                        .wr(RegWrite),.clk(clk));
                        
ALU                 B8 (.A(ALU_A),.B(ALU_B),.ALU_Sel(control_ALUControl), 
                        .ALU_Out(ALU_result), .ZeroOut(Zero),.less_than(less_than));
Return_Result       B9 (.zero_flag(Zero),.Port_A(ALU_A),.Result(Result));
endmodule





// A module to generate the address of next instruction
// LOGIC: 	Add 1 in program counter if its a normal instruction
//			Add address of label in PC if its a branch instruction			
// other parameters can also be added based on Datapath and Controller Inputs/Outputs
module address_generator (
                          output reg [31:0] pc, 
                          input  [31:0]label_address,
                          input      clk,
                          input      PCSrc,
                          input      rst
                         );
//    initial
//    begin
//    pc=0;
//    end
    
    //initial
    //begin
    //pc=0;
    //end
    
    always @ (posedge clk)
        begin
            if (rst)
                pc = 0;
            
            else if (!rst)
            begin
            case (PCSrc)
               1'b0:pc <= pc+4;                // Simple instruction increment.
               1'b1: begin
                     if (label_address[31] == 1'b0)
                     pc <= pc+ label_address;   // Jump or branch detected.
                     else if (label_address[31] == 1'b1)
                     pc<=pc+$signed(label_address);
                     end
            endcase
            end
        end 
endmodule


// A module that will carry the all instructions. PC value will be provided to this module and it will return 
// the instuction
// other parameters can also be added based on Datapath and Controller Inputs/Outputs
module Instruction_Memory (input      [31:0] pc,
                           output reg [31:0] instruction);
    always @(pc)
    begin
        case (pc)
//            32'h00: instruction = 32'b00000000110000000000010000010011; // addi x8, x0, 12
//            32'h04: instruction = 32'b00000000100100000000010010010011; // addi x9, x0, 9
            32'h00: instruction = 32'h00c00413; //addi x8, x0, 12
            32'h04: instruction = 32'h02400493; //addi x9, x0, 24
            32'h08: instruction = 32'b00000000100101000000110001100011; // gcd:beq  x8, x9, stop
            32'h0C: instruction = 32'b00000000100101000100011001100011; // blt  x8, x9, less
            32'h10: instruction = 32'b01000000100101000000010000110011; // sub  x8, x8, x9
            32'h14: instruction = 32'b11111111010111111111000001101111; // j    gcd 
            32'h18: instruction = 32'b01000000100001001000010010110011; // less:sub  x9, x9, x8
            32'h1C: instruction = 32'b11111110110111111111000001101111; // j    gcd
            32'h20: instruction = 32'b00000000000000000000000001101111; // j    stop
        endcase
    end
endmodule


// This module will take a 32-bit instruction, and find its op-code, operands, and functions.
// based on the op-code and functions, the controller will be operated.
// other parameters can also be added based on Datapath and Controller Inputs/Outputs
module Instruction_fetch (
                          input [31:0] instruction, 
                          output reg [6:0] opcode,                               //opcode
                                 reg [4:0] rd,    reg[4:0]rs1,  reg  [4:0]rs2,   //registers
                                 reg [2:0] func3, reg[6:0]func7,                 //functions
                                 reg [20:0]imm
                           );
always @ (instruction)
    begin
        
        //Finding instruction type using opcode.
        case (instruction[6:0])
        
            7'b0010011: begin //I-type instruction
                opcode       <= 7'b0010011;
                rd           <= instruction[11:7];
                func3        <= instruction[14:12];
                rs1          <= instruction[19:15];
                imm[11:0]    <= instruction[31:20];
            end
        
            7'b1100011:begin //B-type instruction
                opcode     <= 7'b1100011;
                imm[11]    <= instruction[7];
                imm[4:1]   <= instruction[11:8];
                func3      <= instruction[14:12];
                rs1        <= instruction[19:15];
                rs2        <= instruction[24:20];
                imm[10:5]  <= instruction[30:25];
                imm[12]    <= instruction[31];
                imm[0]     <= 1'b0;
            end
        
            7'b0110011:begin //R-type instruction
                opcode <= 7'b0110011;
                rd     <= instruction[11:7];
                func3  <= instruction[14:12];
                rs1    <= instruction[19:15];
                rs2    <= instruction[24:20];
                func7  <= instruction[31:25];
            end
        
            7'b1101111:begin //J-type instruction
                opcode      <= 7'b1101111;
                rd          <= instruction[11:7];
                imm[19:12]  <= instruction[19:12];
                imm[11]     <= instruction[20];
                imm[10:1]   <= instruction[30:21];
                imm[20]     <= instruction[31];
                imm[0]      <= 1'b0;
            end
        endcase
    end
endmodule


// This module is called Data_Memory. It will consists of 256 byte memory unit. It will have 
// one input as 8-bit address, 1 input flag wr that will decide if you want to read memory or write memory
module Data_Memory(output [31:0] Data_Out, input [31:0] Data_In, input [7:0] D_Addr, input wr);
		reg [31:0] Mem [255:0];			// Data Memory

	// Write your code here
endmodule



// This module is called Register_Memory. It will consists of 32 registers each of 32-bits. It will have 
// one input flag wr that will decide if you want to read any register or write or update any value in register
// This module will 2 addresses and provide the data in 2 different outputs
module register_file(Port_A, Port_B, Din, Addr_A, Addr_B, Addr_Wr, wr, clk);
    output  [31:0]Port_A, Port_B;			// Data to be provided from register to execute the instruction
	input [31:0] Din;						// Data to be loaded in the register
	input [4:0] Addr_A, Addr_B, Addr_Wr;	// Address (or number) of register to be written or to be read
	input wr;								// input wr flag input
	input clk;
	reg [31:0] Reg_File [31:0];				// Register file
	assign Port_A = Reg_File[Addr_A]; // Reading... 
    assign Port_B = Reg_File[Addr_B];
	initial begin
	        Reg_File[0] = 32'b0; // x0 is initialized as 0
	        end
	
	always @ ( posedge clk) begin
	                        if (wr == 1'b1)
	                           Reg_File[Addr_Wr] = Din;  //Data writing to register.
	                        end
	        
//	always @ (*) begin
//	             Port_A = Reg_File[Addr_A]; // Reading... 
//                 Port_B = Reg_File[Addr_B];
//	             end
endmodule


module Control_Unit(
                    output reg [3:0]ALUControl,reg ALUSrc,reg [1:0]ImmSrc,reg RegWrite,reg MemWrite,reg ResultSrc,
                           reg PCSrc,
                     input  [6:0]op        , [2:0]funct3 , [6:0]funct7 , 
                     input  Zero, less_than
                   );
    always @ (*)
    begin
    case (op)
            7'b1100011:begin //--- B-type instruction ---
            
            ImmSrc      <= 2'b10; //Mux value for immediate generate for B type instruction.
            ALUSrc      <= 1'b0;  //Take operand B from register value.
            RegWrite    <= 1'b0;
                case(funct3)         
                    3'b000:begin
                           ALUControl = 4'b1111; //BEQ
                           case (Zero)
                              1'b0:PCSrc=1'b0;
                              1'b1:PCSrc=1'b1;
                           endcase
                           end  
                    3'b100:begin
                           ALUControl <= 4'b1110; //BLT
                           case (less_than)
                              1'b0:PCSrc<=1'b0;
                              1'b1:PCSrc<=1'b1;
                           endcase
                           end
                endcase
                       end
            7'b0010011:begin                  //--- I-type instruction ---
            
                       ImmSrc     <= 2'b00;   // mux value for immediate generator for I type instruction.
                       ALUSrc     <= 1'b1;    // Taking operand B as immediate value.      
                       ALUControl <= 4'b0000; // Addition operation.
                       RegWrite   <= 1'b1;
                       PCSrc      <= 0;
                       end        
                                  
            7'b1101111:begin                  //--- JAL-type instruction ---
            
                       ImmSrc     <= 2'b11;   // mux value for immediate generator for j-type instruction.
                       ALUSrc     <= 1'b1;    // Taking operand B as immediate value.
                       RegWrite   <= 1'b0;
                       PCSrc      <= 1;
                       end
                       
            7'b0110011:begin                  //--- R-type instruction ---
            
                       ALUSrc     <= 1'b0;    // Taking operand B from register memory.
                       ALUControl <= 4'b0001; //Subtraction operation
                       RegWrite   <= 1'b1;
                       PCSrc      <= 0;
                       end
    endcase
    end
			
	
endmodule





// The final module ALU which will accept the signal (Function) from Control Unit
// and two operands (either from register file or from memory (data or address),
// will perform the desired operarion and proivde the output in Result and Zero flag.
//module ALU(Result, alu_z, Op_A, Op_B, Function,alu_lt);
//	output [31:0] Result;		    // 32 bit Result
//	output alu_z;				    // Zero flag (1 if result is zero)
//	output alu_lt;                  // If less than less than condition is true
//	input [31:0] Op_A, Op_B;	    // Two operands based on the type of instruction
//	input [3:0] Function;			// Function to be performed as per instructed by Control Unit
	
//	// Write your code here
//endmodule


module ALU(
           input [31:0] A,B,       // ALU 8-bit Inputs
           input [3:0] ALU_Sel,    // ALU Selection
           
           output [31:0] ALU_Out,  // ALU 8-bit Output
           output CarryOut,        // Carry Out Flag
		   output  ZeroOut,	       // Zero Flag
		   output less_than        // Less than flag for blt
    );
    reg [31:0] ALU_Result,zero_result,less_than_result;
    wire [32:0] tmp;
    assign ALU_Out   = ALU_Result;               // ALU out
    assign tmp       = {1'b0,A} + {1'b0,B};
    assign CarryOut  = tmp[32];                 // Carryout flag
	assign ZeroOut   = (zero_result == 0);       // Zero Flag
	assign less_than = (less_than_result == 0);     // Less than flag for blt
    always @(*)
    begin
        case(ALU_Sel)
        4'b0000: // Addition
           ALU_Result = A + B ;
        4'b0001: // Subtraction
           ALU_Result = A - B ;
        4'b0010: // Multiplication
           ALU_Result = A * B;
        4'b0011: // Division
           ALU_Result = A/B;
        4'b0100: // Logical shift left
           ALU_Result = A<<B;
         4'b0101: // Logical shift right
           ALU_Result = A>>B;
         4'b0110: // Rotate left
           ALU_Result = {A[30:0],A[31]};
         4'b0111: // Rotate right
           ALU_Result = {A[0],A[31:1]};
          4'b1000: //  Logical and
           ALU_Result = A & B;
          4'b1001: //  Logical or
           ALU_Result = A | B;
          4'b1010: //  Logical xor
           ALU_Result = A ^ B;
          4'b1011: //  Logical nor
           ALU_Result = ~(A | B);
          4'b1100: // Logical nand
           ALU_Result = ~(A & B);
          4'b1101: // Logical xnor
           ALU_Result = ~(A ^ B);
          4'b1110: // Lesser comparison
           less_than_result = (A<B)?32'd0:32'd1 ;
          4'b1111: // Equal comparison
           zero_result = (A==B)?32'd0:32'd1 ;
                  
          default: ALU_Result = A + B ;
        endcase
    end

endmodule




module extend(input  		[31:7] instr,
              input  		[1:0]  immsrc,
              output reg 	[31:0] immext);
    always @ (*)
    case(immsrc)
         // I−type
    2'b00:     immext = {{20{instr[31]}}, instr[31:20]};
		 // S−type (stores)
    2'b01:     immext = {{20{instr[31]}}, instr[31:25],   instr[11:7]};
         // B−type (branches)
    2'b10:      immext = {{20{instr[31]}}, instr[7],      instr[30:25],  instr[11:8], 1'b0};
		// J−type (branches)
	2'b11:      immext = {{12{instr[31]}}, instr[19:12],  instr[20], instr[30:21], 1'b0};
           
	default: 	immext = 32'bx; // undefined
    endcase
endmodule


// General Module of two input (5 bit) multiplexer. This multiplexer will be connected with ALU control signals

// A two by one 32 bit multiplexer (to select the branch instruction)
module ALU_2nd_operand_mux(output reg [31:0]o,		                                // 32 bit output
					       input      [31:0]from_register_file, from_imm_gen,		// 32 bit inputs
					       input sel			                                    // Selection Signal
			);
always @(*) begin
            case (sel)
            1'b0: o <= from_register_file;   //name explains it all... no need for explanation here !
            1'b1: o <= from_imm_gen;            
            endcase
	        end
endmodule

module clkdiv(clock_in,clock_out);
input clock_in; // input clock on FPGA
output reg clock_out; // output clock after dividing the input clock by divisor
reg[27:0] counter=28'd0;
parameter DIVISOR = 28'd100000;//
// The frequency of the output clk_out
//  = The frequency of the input clk_in divided by DIVISOR
// For example: Fclk_in = 50Mhz, if you want to get 1Hz signal to blink LEDs
// You will modify the DIVISOR parameter value to 28'd50.000.000
// Then the frequency of the output clk_out = 50Mhz/50.000.000 = 1Hz
always @(posedge clock_in)
begin
 counter <= counter + 28'd1;
 if(counter>=(DIVISOR-1))
  counter <= 28'd0;
 clock_out <= (counter<DIVISOR/2)?1'b1:1'b0;
end
endmodule

module Return_Result(input zero_flag,
                     input [31:0] Port_A,
                     output  [31:0] Result);
//    always @ (*)
//    begin 
//    if (zero_flag)
assign        Result = Port_A;
//    end       
endmodule