/* ********************************************
 *	COSE222 Lab #4
 *
 *	Module: pipelined_cpu.sv
 *  - Top design of the 5-stage pipelined RISC-V processor
 *  - Processor supports ld, sd, add, sub, or, and, beq, bne, blt, bge
 *
 *  Author: Gunjae Koo (gunjaekoo@korea.ac.kr)
 *
 * ********************************************
 */

`timescale 1ns/1ps

// Packed structures for pipeline registers
// COMPLETE THE PIPELINE INTERFACES USING PACKED STRUCTURES
// Pipe reg: IF/ID
typedef struct packed {
    logic   [31:0]  pc;
    logic   [31:0]  inst;
} pipe_if_id;

// Pipe reg: ID/EX
typedef struct packed {
    logic   [31:0]  pc;
    logic   [31:0]  rs1_dout;
    logic   [31:0]  rs2_dout;
    logic   [31:0]  imm32;
    logic   [2:0]   funct3;
    logic   [6:0]   funct7;
    logic   [3:0]   branch;     // branch[0] = beq, branch[1] = bne, branch[2] = blt, branch[3] = bge
    logic           alu_src;
    logic   [1:0]   alu_op;
    logic           mem_read;
    logic           mem_write;
    logic   [4:0]   rs1;
    logic   [4:0]   rs2;
    logic   [4:0]   rd;         // rd for regfile
    logic           reg_write;
    logic           mem_to_reg;
} pipe_id_ex;

// Pipe reg: EX/MEM
typedef struct packed {
    logic   [31:0]  alu_result; // for address
    logic   [31:0]  rs2_dout;   // for store
    logic           mem_read;
    logic           mem_write;
    logic   [4:0]   rd;
    logic           reg_write;
    logic           mem_to_reg;
} pipe_ex_mem;

// Pipe reg: MEM/WB
typedef struct packed {
    logic   [31:0]  alu_result;
    logic   [31:0]  dmem_dout;
    logic   [4:0]   rd;
    logic           reg_write;
    logic           mem_to_reg;
} pipe_mem_wb;

/* verilator lint_off UNUSED */
module pipeline_cpu
#(  parameter IMEM_DEPTH = 1024,    // imem depth (default: 1024 entries = 4 KB)
              IMEM_ADDR_WIDTH = 10,
              REG_WIDTH = 32,
              DMEM_DEPTH = 1024,    // dmem depth (default: 1024 entries = 8 KB)
              DMEM_ADDR_WIDTH = 10 )
(
    input           clk,            // System clock
    input           reset_b         // Asychronous negative reset
);

    // -------------------------------------------------------------------
    /* Instruction fetch stage:
     * - Accessing the instruction memory with PC
     * - Control PC udpates for pipeline stalls
     */

    // Program counter
    logic           pc_write;   // enable PC updates
    logic   [31:0]  pc_curr, pc_next;
    logic   [31:0]  pc_next_plus4, pc_next_branch;
    logic           pc_next_sel;
    logic           branch_taken;
    logic           regfile_zero;   // zero detection from regfile, REMOVED

    assign pc_next_plus4 = pc_curr + 4;
    assign pc_next_sel = /* FILL THIS */ 
    assign pc_next = (pc_next_sel) ? pc_next_branch: pc_next_plus4;

    always_ff @ (posedge clk or negedge reset_b) begin
        if (~reset_b) begin
            pc_curr <= 'b0;
        end else begin
            pc_curr = pc_next;
             /* FILL THIS */ 
        end
    end

    // imem
    logic   [IMEM_ADDR_WIDTH-1:0]   imem_addr;
    logic   [31:0]  inst;   // instructions = an output of ????
    
    assign imem_addr = pc_curr[IMEM_ADDR_WIDTH+1:2];

    // instantiation: instruction memory
    imem #(
        .IMEM_DEPTH         (IMEM_DEPTH),
        .IMEM_ADDR_WIDTH    (IMEM_ADDR_WIDTH)
    ) u_imem_0 (
        .addr               ( imem_addr     ),
        .dout               ( inst          )
    );
    // -------------------------------------------------------------------

    // -------------------------------------------------------------------
    /* IF/ID pipeline register
     * - Supporting pipeline stalls and flush
     */
    pipe_if_id      id;         // THINK WHY THIS IS ID...
    pipe_id_ex      ex;
    pipe_ex_mem     mem;
    pipe_mem_wb     wb;

    logic           if_flush, if_stall;

    always_ff @ (posedge clk or negedge reset_b) begin
        if (~reset_b) begin
            id <= 'b0;
        end else begin
            if (if_flush) begin
                id <= 'b0;
            end else if (~if_stall) begin
                id.pc <= pc_curr;  
                id.inst <=  inst;
            end
        end
    end
    // -------------------------------------------------------------------

    // ------------------------------------------------------------------
    /* Instruction decoder stage:
     * - Generating control signals
     * - Register file
     * - Immediate generator
     * - Hazard detection unit
     */
    
    // -------------------------------------------------------------------
    /* Main control unit:
     * Main control unit generates control signals for datapath elements
     * The control signals are determined by decoding instructions
     * Generating control signals using opcode = inst[6:0]
     */
    logic   [6:0]   opcode;
    logic   [3:0]   branch;
    logic           alu_src, mem_to_reg;
    logic   [1:0]   alu_op;
    logic           mem_read, mem_write, reg_write; // declared above
    logic   [6:0]   funct7;
    logic   [2:0]   funct3;

    assign opcode = id.inst[6:0];
    assign branch[0] = ((opcode==7'b1100011) && (funct3==3'b000)) ? 1'b1: 1'b0;
    assign branch[1] = ((opcode==7'b1100011) && (funct3==3'b001)) ? 1'b1: 1'b0;
    assign branch[2] = ((opcode==7'b1100011) && (funct3==3'b100)) ? 1'b1: 1'b0;
    assign branch[3] = ((opcode==7'b1100011) && (funct3==3'b101)) ? 1'b1: 1'b0;

    assign mem_read = (opcode==7'b0000011) ? 1'b1: 1'b0;    // ld
    assign mem_write = (opcode==7'b0100011) ? 1'b1: 1'b0;   // sd
    assign mem_to_reg = mem_read;
    assign reg_write = (opcode==7'b0110011) | (opcode==7'b0010011) | mem_read; // ld, r-type, or i-type
    // ld, sd, or i-type
    assign alu_src = ( mem_read | mem_write | (opcode==7'b0010011) ) ? 1'b1: 1'b0;   

    assign alu_op[0] = |branch;
    assign alu_op[1] = (opcode==7'b0110011) | (opcode==7'b0010011);    // r-type or i-type


    // --------------------------------------------------------------------

    // ---------------------------------------------------------------------
    /* Immediate generator:
     * Generating immediate value from inst[31:0]
     */
    logic   [31:0]  imm32;
    logic   [31:0]  imm32_branch;  // imm64 left shifted by 1

    // COMPLETE IMMEDIATE GENERATOR HERE
    logic   [11:0]  imm12;

    assign imm12 = (|branch) ? {inst[31], inst[7], inst[30:25], inst[11:8]}: 
                ( (mem_write) ? {inst[31:25], inst[11:7]}: inst[31:20] );
    assign imm32 = { {20{imm12[11]}}, imm12 };
    assign imm32_branch = {imm32[30:0], 1'b0}; // << 1 for branch

    // Computing branch target
    assign pc_next_branch =  pc_curr + imm32_branch;

    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    /* Hazard detection unit
     * - Detecting data hazards from load instrcutions
     * - Detecting control hazards from taken branches
     */
    logic   [4:0]   rs1, rs2;

    logic           stall_by_load_use;
    logic           flush_by_branch;
    
    logic           id_stall, id_flush;


    assign stall_by_load_use = ex.mem_read && ((ex.rd == rs1) || (ex.rd == rs2));
    assign flush_by_branch = branch_taken; 
  
    assign id_flush =  flush_by_branch
    assign id_stall =  stall_by_load_use;
	
    assign if_flush =  flush_by_branch;
    assign if_stall =  /* FILL THIS */ 
    assign pc_write =  /* FILL THIS */

    // ----------------------------------------------------------------------


    // regfile/
    logic   [4:0]   rd;    // register numbers
    logic   [REG_WIDTH-1:0] rd_din;
    logic   [REG_WIDTH-1:0] rs1_dout, rs2_dout;
    
    assign rs1 = inst[19:15];
    assign rs2 = inst[24:20];
    assign rd = inst[11:7];
    // rd, rd_din, and reg_write will be determined in WB stage
    
    // instnatiation of register file
    regfile #(
        .REG_WIDTH          (REG_WIDTH)
    ) u_regfile_0 (
        //From ID stage
        .clk                (clk),
        .rs1                (rs1),
        .rs2                (rs2),
        //From WB stage
        .rd                 (wb.rd),
        .reg_write          (wb.reg_write),
        .rd_din             (rd_din),
        //For EX stage
        .rs1_dout           (rs1_dout),
        .rs2_dout           (rs2_dout)
    );

    assign regfile_zero = ~|(rs1_dout ^ rs2_dout);

    assign funct7 = inst[31:25];
    assign funct3 = inst[14:12];

    // ------------------------------------------------------------------

    // -------------------------------------------------------------------
    /* ID/EX pipeline register
     * - Supporting pipeline stalls
     */
    //pipe_id_ex      ex;         // THINK WHY THIS IS EX...

    always_ff @ (posedge clk or negedge reset_b) begin
        if (~reset_b) begin
            ex <= 'b0;
        end else begin
             /* FILL THIS */ 
             ex.pc <= id.pc;
             ex.rs1_dout <= rs1_dout;
             ex.rs2_dout <= rs2_dout;
             ex.imm32 <= imm32;
             ex.funct3 <= funct3;
             ex.funct7 <= funct7;
             ex.branch <= branch;
             ex.alu_src <= alu_src;
             ex.alu_op <= alu_op;
             ex.mem_read <= mem_read;
             ex.mem_write <= mem_write;
             ex.rs1 <= rs1;
             ex.rs2 <= rs2;
             ex.reg_write <= reg_write;
             ex.mem_to_reg <= mem_to_reg;
        end
    end

    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    /* Excution stage:
     * - ALU & ALU control
     * - Data forwarding unit
     */
     alu



     

    // --------------------------------------------------------------------
    /* ALU control unit:
     * ALU control unit generate alu_control signal which selects ALU operations
     * Generating control signals using alu_op, funct7, and funct3 fileds
     */

    logic   [3:0]   alu_control;    // ALU control signal

    // COMPLETE ALU CONTROL UNIT
    //

    // COMPLETE THE ALU CONTROL UNIT HERE

    always_comb begin
        if (alu_op[1]) begin
            case (ex.funct3)
                3'b111: alu_control = 4'b0000;
                3'b110: alu_control = 4'b0001;
                3'b100: alu_control = 4'b0011;
                default: alu_control = (funct7[5]) ? 4'b0110: 4'b0010;
            endcase
        end else begin
            alu_control = (alu_op[0]) ? 4'b0110: 4'b0010;
        end
    end

    // ---------------------------------------------------------------------

    // ----------------------------------------------------------------------
    /* Forwarding unit:
     * - Forwarding from EX/MEM and MEM/WB
     */
    logic   [1:0]   forward_a, forward_b;
    logic   [REG_WIDTH-1:0]  alu_fwd_in1, alu_fwd_in2;   // outputs of forward MUXes

	/* verilator lint_off CASEX */
   // COMPLETE FORWARDING MUXES

   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
	/* verilator lint_on CASEX */

	// COMPLETE THE FORWARDING UNIT
    // Need to prioritize forwarding conditions

















    // -----------------------------------------------------------------------

    // ALU
    logic   [REG_WIDTH-1:0] alu_in1, alu_in2;
    logic   [REG_WIDTH-1:0] alu_result;
    //logic           alu_zero;   // will not be used

    assign alu_in1 =  /* FILL THIS */ 
    assign alu_in2 =  /* FILL THIS */ 

    // instantiation: ALU
    alu #(
        .REG_WIDTH          (REG_WIDTH)
    ) u_alu_0 (
        .in1                (alu_in1),
        .in2                (alu_in2),
        .alu_control        (alu_control),
        .result             (alu_result)
        //.zero               (alu_zero),	// REMOVED
		//.sign				(alu_sign)		// REMOVED
    );

    // branch unit (BU)
    logic   [REG_WIDTH-1:0] sub_for_branch;
    logic           bu_zero, bu_sign;
    //logic           branch_taken;

    assign sub_for_branch =  /* FILL THIS */ 
    assign bu_zero =  /* FILL THIS */ 
    assign bu_sign =  /* FILL THIS */ 
    assign branch_taken =  /* FILL THIS */

    // -------------------------------------------------------------------------
    /* Ex/MEM pipeline register
     */
    //pipe_ex_mem     mem;

    always_ff @ (posedge clk or negedge reset_b) begin
        if (~reset_b) begin
            mem <= 'b0;
        end else begin
            mem.alu_result <= alu_result;
            mem.rs2_dout <= ex.rs2_dout;
            mem.mem_read <= ex.mem_read;
            mem.mem_write <= ex.mem_write;
            mem.rd <= ex.rd;
            mem.reg_write <= ex.reg_write;
            mem.mem_to_reg <= ex.mem_to_reg;
        end
    end


    // --------------------------------------------------------------------------
    /* Memory srage
     * - Data memory accesses
     */

    // dmem
    logic   [DMEM_ADDR_WIDTH-1:0]    dmem_addr;
    logic   [31:0]  dmem_din, dmem_dout;

    assign dmem_addr =  /* FILL THIS */ 
    assign dmem_din =  /* FILL THIS */ 
    
    // instantiation: data memory
    dmem #(
        .DMEM_DEPTH         (DMEM_DEPTH),
        .DMEM_ADDR_WIDTH    (DMEM_ADDR_WIDTH)
    ) u_dmem_0 (
        .clk                (clk),
        .addr               (dmem_addr),
        .din                (dmem_din),
        .mem_read           ( /* FILL THIS */ ),
        .mem_write          ( /* FILL THIS */ ),
        .dout               (dmem_dout)
    );


    // -----------------------------------------------------------------------
    /* MEM/WB pipeline register
     */

    //pipe_mem_wb         wb;

    always_ff @ (posedge clk or negedge reset_b) begin
        if (~reset_b) begin
            wb <= 'b0;
        end else begin
             /* FILL THIS */ 
            wb.alu_result <= mem.alu_result;
            wb.dmem_dout <= dmem_dout;
            wb.rd <= mem.rd;
            wb.reg_write <= mem.reg_write;
            wb.mem_to_reg <= mem.mem_to_reg;
        end
    end

    // ----------------------------------------------------------------------
    /* Writeback stage
     * - Write results to regsiter file
     */
    
    assign rd_din = wb.rd;  

endmodule
