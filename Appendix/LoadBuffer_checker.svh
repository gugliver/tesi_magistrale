//`define FORMAL // please comment this when performing the Functional Verification

import EPI_pkg::*;

localparam TADDR_WIDTH_LOC = 8;
localparam BANK_IDX_SZ = (N_BANKS == 1)?1:$clog2(N_BANKS);
localparam MAX_LB_DELAY = $;

bind LoadBuffer LoadBuffer_checker bind_LoadBuffer_checker (.*);



module LoadBuffer_checker
	(
	input 						clk_i,
	input 						rsn_i,
	input 						load_req_i,
	input [SB_WIDTH-1:0] 				load_sb_id_i, // IT IS POSSIBLE THAT WE HAVE TO MANAGE TWO LOADS IN PARALLEL
	input 						load_masked_i,
	input [SEW_WIDTH-2:0] 				load_sew_i,
	input 						lmu_dvalid_load_i,
	input [DATA_PATH_WIDTH-1:0] 			lmu_data_i,
	input [MASK_BANK_WORD-1:0] 			lmu_enable_i,
	input [SB_WIDTH-1:0] 				lmu_sb_id_i,       // sb_id corresponding to the data received in lmu_dvalid_load_i
	input [$clog2(MASK_BANK_WORD)-1:0] 		lmu_min_el_id_i,         // element_id corresponding to the data received in lmu_dvalid_load_i
	input [MASK_BANK_WORD-1:0][EL_ID_WIDTH-1:0] 	lmu_el_id_i,         // element_id corresponding to the data received in lmu_dvalid_load_i
	input 						fsm_read_en_lbuf_i,   // this signal comes from main FSM WB state (in order to be able to read data from the buffers in MEM state)
	input 						fsm_mem_write_en_i,  // this signal indicates that we're in FSM MEM state so we can write in the VRF
	input [VADDR_WIDTH-1:0] 			load_addr_i,
	input [1:0][TADDR_WIDTH_LOC-1:0] 		load_addr_trans_i,
	input 						memop_sync_end_i,
	input [SB_WIDTH-1:0] 				memop_sb_id_i, // sb_id of the memop_sync_end, identifies which load operation is finishing!
	input 						load_write_en_rf_o,  // write enable to the register file
	input 						load_gnt_o,
	input 						load_valid_o,            // indicates that the load operation was completed successfully
	input [SB_WIDTH-1:0] 				load_sb_id_o,
	input [VADDR_WIDTH-1:0] 			load_valid_addr_o,
	input 						load_masked_o,
	input 						load_ready_o,
	input reg [N_BANKS*DATA_PATH_WIDTH-1:0] 	load_data_o,
	input reg [N_BANKS-1:0][MASK_BANK_WORD-1:0] 	load_data_en_o, // TODO TBD the final interface
	input [VADDR_WIDTH-1:0] 			load_addr_o,
	input 						load_inflight_o,
	input [1:0][TADDR_WIDTH_LOC-1:0] 		load_addr_trans_o,
	input 						kill_i,
	input 						load_ack_i,
	input [SB_WIDTH-1:0] 				load_ack_sb_id_i,
	input [CSR_VLEN_START-1:0] 			vstart_self_i,
	input [CSR_VLEN_START-1:0] 			vstart_next_i,
	input reg [CSR_VLEN_START-1:0] 			vstart_self_o,
	input reg [CSR_VLEN_START-1:0] 			vstart_next_o,
	input reg 					retry_self_o,
	input reg 					retry_next_o,
	input reg [SB_WIDTH-1:0] 			retry_sb_id_o
	);

//////////////////////////////////////////////////////
//////////////////// variables ///////////////////////
//////////////////////////////////////////////////////
typedef struct {
	bit [SB_WIDTH-1:0] sb_id;
	bit done;
	bit [SEW_WIDTH-2:0] sew;
	bit asked_for_retry;
	bit now_granted;
} granted_load;


granted_load fifo[1:0];
int num_gnt;
int num_load_completed;
int num_ended;
bit [SB_WIDTH-1:0] sb_id0;
bit [SB_WIDTH-1:0] sb_id1;
bit ng_0;
bit ng_1;
bit done0;
bit done1;


//////////////////////////////////////////////////////
/////////////////////processes////////////////////////
//////////////////////////////////////////////////////

always_comb begin
	assign ng_0 = fifo[0].now_granted;
	assign ng_1 = fifo[1].now_granted;
	assign sb_id0 = fifo[0].sb_id;
	assign sb_id1 = fifo[1].sb_id;
	assign done0 = fifo[0].done;
	assign done1 = fifo[1].done;
end

initial begin 
	fifo[0].done = 1;
	fifo[0].sb_id = 20; // we have to initialize it to a value that cannot be in input, to avoid to read the wrong SEW and STRIDE from the wrong fifo cell
	fifo[0].sew = 0;
	fifo[0].asked_for_retry = 0;
	fifo[0].now_granted = 0;
	fifo[1].done = 1;
	fifo[1].sb_id = 20;
	fifo[1].sew = 0;
	fifo[1].asked_for_retry = 0;
	fifo[1].now_granted = 0;
end



//for each load_gnt_o there is a fell(load_req_i)
always @(negedge clk_i or negedge rsn_i) begin

	if ( !rsn_i || kill_i) begin
		num_gnt = 0;	
		num_load_completed = 0;
		num_ended = 0;
		fifo[0].done = 1;
		fifo[0].sb_id = 20;
		fifo[0].sew = 0;
		fifo[0].asked_for_retry = 0;
		fifo[0].now_granted = 0;
		fifo[1].done = 1;
		fifo[1].sb_id = 20;
		fifo[1].sew = 0;
		fifo[1].asked_for_retry = 0;
		fifo[1].now_granted = 0;
	end
	else 	begin
		fifo[0].now_granted = 0;
		fifo[1].now_granted = 0;
		if ( load_gnt_o ) begin
			if ( fifo[0].done ) begin
				fifo[0].sb_id = load_sb_id_i;
				fifo[0].done = 0;
				fifo[0].sew = load_sew_i;
				fifo[0].asked_for_retry = 0;
				fifo[0].now_granted = 1;
			end 
			else if ( fifo[1].done ) begin
				fifo[1].sb_id = load_sb_id_i;
				fifo[1].done = 0;
				fifo[1].sew = load_sew_i;
				fifo[1].asked_for_retry = 0;
				fifo[1].now_granted = 1;
			end
		end
		if ( load_ack_i ) begin
			if ( (fifo[0].sb_id == load_ack_sb_id_i) && !fifo[0].done ) begin
				fifo[0].done = 1;
				num_gnt = num_gnt - 1 ;
				num_load_completed = num_load_completed - 1 ;
				num_ended = num_ended - 1 ;
			end
			else if ( (fifo[1].sb_id == load_ack_sb_id_i) && !fifo[1].done ) begin
				fifo[1].done = 1;
				num_gnt = num_gnt - 1 ;
				num_load_completed = num_load_completed - 1 ;
				num_ended = num_ended - 1 ;
			end
		end
		if ( retry_self_o || retry_next_o ) begin
			if ( (fifo[0].sb_id == retry_sb_id_o) && !fifo[0].done ) begin
				fifo[0].asked_for_retry = 1;
			end
			else if ( (fifo[1].sb_id == retry_sb_id_o) && !fifo[1].done ) begin
				fifo[1].asked_for_retry = 1;
			end
		end
			
		num_gnt = num_gnt + load_gnt_o ;
		num_load_completed = num_load_completed + load_valid_o ;
		if ( memop_sync_end_i && ( ( (memop_sb_id_i==fifo[0].sb_id) && !fifo[0].done ) | ( (memop_sb_id_i==fifo[1].sb_id) && !fifo[1].done ) ) ) begin
					num_ended = num_ended + 1 ;
		end
	
	end
	
end



//////////////////////////////////////////////////////
/////////////////////properties///////////////////////
//////////////////////////////////////////////////////

 `ifdef FORMAL

	//vp0.0.0
	property p_load_req_i_sync;
		@(negedge clk_i)
		1 |=> @(posedge clk_i)  $stable(load_req_i);
	endproperty :  p_load_req_i_sync

	//vp 0.0.1
	property p_memop_sync_end_i_sync;
		@(negedge clk_i)
		1 |=>  @(posedge clk_i) $stable(memop_sync_end_i);
	endproperty :  p_memop_sync_end_i_sync

	//vp0.0.2
	property p_load_ack_i_sync;
		@(negedge clk_i)
		1 |=>  @(posedge clk_i) $stable(load_ack_i);
	endproperty :  p_load_ack_i_sync

`endif

//AVISPADO IF///////////////////
//vp 1.0.1
property p_mem_sync_end_i;
	@(posedge clk_i)
	memop_sync_end_i |-> !$isunknown(memop_sb_id_i);
endproperty : p_mem_sync_end_i

//vp 1.0.2
property p_valid_after_sync_end; 
	bit [SB_WIDTH-1 : 0] valid_id;
	@(posedge clk_i)
	( memop_sync_end_i && ( ((memop_sb_id_i==fifo[0].sb_id) && !fifo[0].done) || ((memop_sb_id_i==fifo[1].sb_id) && !fifo[1].done)) ) ##0 (1, valid_id = memop_sb_id_i) |-> ##[1:$] load_valid_o && (load_sb_id_o == valid_id);
endproperty : p_valid_after_sync_end

//vp 1.0.3
property p_memop_sync_end_num;
	@(negedge clk_i)
	num_ended == 2 |-> ##1 !memop_sync_end_i || ( memop_sync_end_i && ( ( (memop_sb_id_i!=fifo[0].sb_id) || ( (memop_sb_id_i==fifo[0].sb_id) && fifo[0].done ) )&& ( (memop_sb_id_i!=fifo[1].sb_id) || ( (memop_sb_id_i==fifo[1].sb_id) && fifo[1].done) ) ) ) ;// implement the memory to store the ids plz
endproperty : p_memop_sync_end_num

//vp 1.0.4
property p_load_ack_i_num;
	@(posedge clk_i)
	num_ended == 0 |-> !load_ack_i || ( load_ack_i && ( ( (load_ack_sb_id_i!=fifo[0].sb_id) || ( (load_ack_sb_id_i==fifo[0].sb_id) && fifo[0].done ) )&& ( (load_ack_sb_id_i!=fifo[1].sb_id) || ( (load_ack_sb_id_i==fifo[1].sb_id) && fifo[1].done) ) ) ) ;// implement the memory to store the ids plz
endproperty : p_load_ack_i_num

//vp 1.0.5
property p_unique_request;
	@(posedge clk_i)
	load_req_i |-> ( (load_sb_id_i!=fifo[0].sb_id) || ( (load_sb_id_i==fifo[0].sb_id) && (fifo[0].now_granted || fifo[0].done) ) ) && ( (load_sb_id_i!=fifo[1].sb_id) || ((load_sb_id_i==fifo[1].sb_id) && (fifo[1].now_granted || fifo[1].done) ) )  ;
endproperty : p_unique_request

//LMU IF////////////////////////
//vp 1.1.1
property p_lmu_valid_load_i;
	@(posedge clk_i)
	lmu_dvalid_load_i |-> 
	!$isunknown(load_req_i) && !$isunknown(load_sb_id_i) && !$isunknown(load_masked_i) && !$isunknown(load_sew_i) && !$isunknown(lmu_dvalid_load_i) && !$isunknown(lmu_enable_i) && !$isunknown(lmu_sb_id_i) && !$isunknown(lmu_min_el_id_i) && !$isunknown(lmu_el_id_i) && !$isunknown(fsm_read_en_lbuf_i) && !$isunknown(fsm_mem_write_en_i) && !$isunknown(load_addr_i) && !$isunknown(load_addr_trans_i) && !$isunknown(memop_sync_end_i) && !$isunknown(memop_sb_id_i) && !$isunknown(load_ack_i) && !$isunknown(load_ack_sb_id_i) && !$isunknown(vstart_self_i) && !$isunknown(vstart_next_i);

endproperty : p_lmu_valid_load_i 

//vp 1.1.2
property p_enable_coherence;
	int sew;
	@(posedge clk_i)
	(lmu_dvalid_load_i, sew=load_sew_i) |->  is_coherent(lmu_enable_i,sew);
endproperty : p_enable_coherence


//MQ IF/////////////////////////
//vp 1.2.1
property p_load_request_i;
	@(posedge clk_i)
	load_req_i |-> !$isunknown(load_sb_id_i) && !$isunknown(load_masked_i) && !$isunknown(load_sew_i) && !$isunknown(load_addr_i) && !$isunknown(load_addr_trans_i) && !$isunknown(lmu_min_el_id_i) && !$isunknown(lmu_el_id_i);
endproperty : p_load_request_i

//vp 1.2.2
property p_req_after_gnt;
	@(posedge clk_i)
	$fell(load_req_i) |-> $fell(load_gnt_o);
endproperty : p_req_after_gnt

//vp 1.2.3
property p_gnt_after_req;
	@(posedge clk_i)
	$rose(load_req_i) |-> $rose(load_req_i)[=1] ##0 load_gnt_o;
endproperty : p_gnt_after_req


//vp 1.2.4
property p_gnt_beh;
	@(posedge clk_i)
	load_gnt_o |-> ##1 (!load_gnt_o) || (load_gnt_o && num_gnt == 1) ; //(!load_gnt_o || num_gnt == 1) ;//or ##1 !load_gnt_o;
endproperty : p_gnt_beh

//vp 1.2.5
property p_num_gnt;
	@(posedge clk_i)
	load_gnt_o || load_ack_i |-> num_gnt < 3 ;
endproperty : p_num_gnt



//vp 1.2.6
property p_num_req_end;
	@(posedge clk_i)
	(num_gnt == 0) |-> !load_ack_i || ( load_ack_i && ( load_ack_sb_id_i!=fifo[0].sb_id || (load_ack_sb_id_i==fifo[0].sb_id && fifo[0].done) )  && ( load_ack_sb_id_i!=fifo[1].sb_id || (load_ack_sb_id_i==fifo[1].sb_id && fifo[1].done) )  ) ;
endproperty : p_num_req_end

//FSM IF////////////////////////
//vp 1.3.1
property p_read_write_en;
	@(posedge clk_i)
	fsm_read_en_lbuf_i || fsm_mem_write_en_i |-> !(fsm_read_en_lbuf_i && fsm_mem_write_en_i);
endproperty : p_read_write_en

//vp 1.3.2
property p_write_after_read;
	@(posedge clk_i)
	fsm_read_en_lbuf_i ##1 load_ready_o |-> fsm_mem_write_en_i;
endproperty : p_write_after_read


//CU IF/////////////////////////
//vp 1.4.1
property p_cu_ack;
	bit [SB_WIDTH-1:0] ID;
	@(posedge clk_i)
	load_valid_o ##0 (1, ID = load_sb_id_o) |-> ##[1:$] load_ack_i && (load_ack_sb_id_i == ID);
endproperty : p_cu_ack

//vp 1.4.2
property p_cu_ack_num;
	@(posedge clk_i)
	load_valid_o || load_ack_i |-> num_load_completed < 3 ;
endproperty : p_cu_ack_num


//vp 1.4.3
property p_num_load_completed;
	@(posedge clk_i)
	(num_load_completed == 0) |-> !load_ack_i || ( load_ack_i && ( load_ack_sb_id_i!=fifo[0].sb_id || (load_ack_sb_id_i==fifo[0].sb_id && fifo[0].done) )  && ( load_ack_sb_id_i!=fifo[1].sb_id || (load_ack_sb_id_i==fifo[1].sb_id && fifo[1].done) )  ) ;
endproperty : p_num_load_completed


//VRF IF////////////////////////
//vp 1.5.1
property p_output_data_known;
	@(posedge clk_i)
	load_write_en_rf_o |-> !$isunknown(load_addr_o) && !$isunknown(load_addr_trans_o) && !$isunknown(load_data_o) && !$isunknown(load_data_en_o);
endproperty : p_output_data_known

//vp 1.5.2
property p_write_en_rf;
	@(posedge clk_i)
	fsm_mem_write_en_i && load_ready_o |-> load_write_en_rf_o;
endproperty : p_write_en_rf

//vp 1.5.3
property p_load_valid_addr;
	bit [VADDR_WIDTH-1:0] load_addr;
	@(posedge clk_i)
	($rose(load_req_i), load_addr = load_addr_i) |-> ##[1:$] $rose(load_valid_o) && load_valid_addr_o == load_addr;
endproperty : p_load_valid_addr



//VL IF////////////////////////
//vp 1.6.1
property p_load_inflight_o;
	@(negedge clk_i)
	$rose(load_inflight_o) || $fell(load_inflight_o) |-> (load_inflight_o && num_gnt>0) || (!load_inflight_o && num_gnt==0);
endproperty : p_load_inflight_o

//vp 1.6.2
property p_load_ready_o;
	@(posedge clk_i)
	 load_inflight_o && lmu_dvalid_load_i |-> ##[0:$] fsm_read_en_lbuf_i ##1 load_ready_o;
endproperty : p_load_ready_o

//vp 1.6.3
	//vp 1.6.3.0
	property p_data_corruption_64;
		logic [DATA_PATH_WIDTH-1:0] data_i;
		logic [SEW_WIDTH-2:0] sew_i;
		logic [EL_ID_WIDTH-1:0] el_id_i;
		logic [MASK_BANK_WORD-1:0] enable_i;
		logic [SB_WIDTH-1:0] sb_id_i;

		@(posedge clk_i)
		
		(lmu_dvalid_load_i, data_i = lmu_data_i, sb_id_i = lmu_sb_id_i,el_id_i = lmu_el_id_i[0], enable_i = lmu_enable_i) ##0 
		((lmu_sb_id_i == fifo[0].sb_id && !fifo[0].done, sew_i = fifo[0].sew) or (lmu_sb_id_i == fifo[1].sb_id && !fifo[1].done, sew_i = fifo[1].sew)) ##0	
		sew_i == 2'b11
		|-> first_match( (1) [*0:$] ##0 ( (load_write_en_rf_o && (load_data_o[get_el_bank(el_id_i, sew_i)*64 + 63 -: 64] == data_i)) || 
		!enable_i[0] || 
		(load_ack_i && (sb_id_i==load_ack_sb_id_i)) ||
		( (lmu_sb_id_i == fifo[0].sb_id && fifo[0].asked_for_retry && !fifo[0].done) ||
		(lmu_sb_id_i == fifo[1].sb_id && fifo[1].asked_for_retry && !fifo[1].done) ))) 
		|-> !(load_ack_i && (sb_id_i==load_ack_sb_id_i));
	endproperty : p_data_corruption_64



	//vp 1.6.3.1
	property p_data_corruption_32(i_32);
		logic [DATA_PATH_WIDTH-1:0] data_i;
		logic [SEW_WIDTH-2:0] sew_i;
		logic [MASK_BANK_WORD-1:0][EL_ID_WIDTH-1:0] el_id_i;
		logic [MASK_BANK_WORD-1:0] enable_i;
		logic [SB_WIDTH-1:0] sb_id_i;

		@(posedge clk_i)

		(lmu_dvalid_load_i, data_i = lmu_data_i, sb_id_i = lmu_sb_id_i, el_id_i = lmu_el_id_i[i_32*4], enable_i = lmu_enable_i) ##0
		(((lmu_sb_id_i == fifo[0].sb_id) && (fifo[0].done == 0), sew_i = fifo[0].sew) or ((lmu_sb_id_i == fifo[1].sb_id) && (fifo[1].done == 0), sew_i = fifo[1].sew)) ##0 
		sew_i == 2'b10
		|-> first_match( (1) [*0:$] ##0 ( ( load_write_en_rf_o && ( (load_data_o[get_el_bank(el_id_i, sew_i)*64 + 63 -: 32] == data_i[i_32*32 + 31 -: 32]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 31 -: 32] == data_i[i_32*32 + 31 -: 32]) )) ||  
		!enable_i[i_32*4] || 
		(load_ack_i && (sb_id_i==load_ack_sb_id_i)) ||
		( (lmu_sb_id_i == fifo[0].sb_id && fifo[0].asked_for_retry && !fifo[0].done) ||
		(lmu_sb_id_i == fifo[1].sb_id && fifo[1].asked_for_retry && !fifo[1].done) ))) 
		|-> !(load_ack_i && (sb_id_i==load_ack_sb_id_i));

	endproperty : p_data_corruption_32

	//vp 1.6.3.2
	property p_data_corruption_16(i_16);
		logic [DATA_PATH_WIDTH-1:0] data_i;
		logic [SEW_WIDTH-2:0] sew_i;
		logic [MASK_BANK_WORD-1:0][EL_ID_WIDTH-1:0] el_id_i;
		logic [MASK_BANK_WORD-1:0] enable_i;
		logic [SB_WIDTH-1:0] sb_id_i;

		@(posedge clk_i)

		(lmu_dvalid_load_i, data_i = lmu_data_i, sb_id_i = lmu_sb_id_i, el_id_i = lmu_el_id_i[i_16*2], enable_i = lmu_enable_i) ##0 
		(((lmu_sb_id_i == fifo[0].sb_id) && (fifo[0].done == 0), sew_i = fifo[0].sew) or ((lmu_sb_id_i == fifo[1].sb_id) && (fifo[1].done == 0), sew_i = fifo[1].sew)) ##0 
		sew_i == 2'b01
		|-> first_match( (1) [*0:$] ##0 ( ( load_write_en_rf_o && (	(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 63 -: 16] == data_i[i_16*16 + 15 -: 16]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 47 -: 16] == data_i[i_16*16 + 15 -: 16]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 31 -: 16] == data_i[i_16*16 + 15 -: 16]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 15 -: 16] == data_i[i_16*16 + 15 -: 16]) ) ) ||
		!enable_i[i_16*2] ||
		( load_ack_i && (sb_id_i==load_ack_sb_id_i)) ||
		( (lmu_sb_id_i == fifo[0].sb_id && fifo[0].asked_for_retry && !fifo[0].done) || 
		(lmu_sb_id_i == fifo[1].sb_id && fifo[1].asked_for_retry && !fifo[1].done)))
		|-> !(load_ack_i && (sb_id_i==load_ack_sb_id_i));

	endproperty : p_data_corruption_16

	//vp 1.6.3.3
	property p_data_corruption_8(i_8);
		logic [DATA_PATH_WIDTH-1:0] data_i;
		logic [SEW_WIDTH-2:0] sew_i;
		logic [MASK_BANK_WORD-1:0][EL_ID_WIDTH-1:0] el_id_i;
		logic [MASK_BANK_WORD-1:0] enable_i;
		logic [SB_WIDTH-1:0] sb_id_i;

		@(posedge clk_i)

		(lmu_dvalid_load_i, data_i = lmu_data_i, sb_id_i = lmu_sb_id_i, el_id_i = lmu_el_id_i[i_8], enable_i = lmu_enable_i) ##0 
		(((lmu_sb_id_i == fifo[0].sb_id) && (fifo[0].done == 0), sew_i = fifo[0].sew) or ((lmu_sb_id_i == fifo[1].sb_id) && (fifo[1].done == 0), sew_i = fifo[1].sew)) ##0 
		sew_i == 2'b00
		|-> first_match( (1) [*0:$] ##0 ( ( load_write_en_rf_o && (	(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 63 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 55 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 47 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 39 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 31 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 23 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 + 15 -: 8] == data_i[i_8*8 + 7 -: 8]) ||
		(load_data_o[get_el_bank(el_id_i, sew_i)*64 +  7 -: 8] == data_i[i_8*8 + 7 -: 8]) ) ) ||
		!enable_i[i_8] ||
		( load_ack_i && (sb_id_i==load_ack_sb_id_i))  ||
		( (lmu_sb_id_i == fifo[0].sb_id && fifo[0].asked_for_retry && !fifo[0].done) || 
		(lmu_sb_id_i == fifo[1].sb_id && fifo[1].asked_for_retry && !fifo[1].done) )))
		|-> !(load_ack_i && (sb_id_i==load_ack_sb_id_i));


	endproperty : p_data_corruption_8



//RSN IF///////////////////////
//vp 1.7.1
property p_rsn_output;
	@(posedge clk_i)
	!rsn_i |-> !load_write_en_rf_o && !load_gnt_o && !load_valid_o && !load_inflight_o && retry_self_o == '0 && retry_next_o == '0;
endproperty : p_rsn_output

//vp 1.7.2
property p_rsn_input;
	@(posedge clk_i)
	!rsn_i |-> lmu_enable_i == '0 && !load_req_i && !fsm_read_en_lbuf_i;
endproperty : p_rsn_input

//vp 1.7.3
property p_kill_input;
	@(posedge clk_i)
	kill_i |-> !load_req_i;
endproperty : p_kill_input



///////////////////////////////////////////////////////
///////////////////assert & assume/////////////////////
///////////////////////////////////////////////////////

//FORMAL ASSUMPTION//////////////

`ifdef FORMAL

	//vp 0.0.0
	a_load_req_i_sync :		assume property( disable iff (!rsn_i || kill_i) p_load_req_i_sync) else $error("load_req_i changed on the negedge");

	//vp 0.0.1
	a_memop_sync_end_i_sync :	assume property( disable iff (!rsn_i || kill_i) p_memop_sync_end_i_sync) else $error("load_req_i changed on the negedge");

	//vp 0.0.2
	a_load_ack_i_sync :		assume property( disable iff (!rsn_i || kill_i) p_load_ack_i_sync) else $error("load_req_i changed on the negedge");

`endif

//AVISPADO IF///////////////////
//vp 1.0.1
a_mem_sync_end_i :		assume property (disable iff (!rsn_i || kill_i) p_mem_sync_end_i) else $error("unknown memop scoreboard id on memop_sync_end_i asserted");

//vp 1.0.2
a_valid_after_sync_end :	assert property (disable iff (!rsn_i || kill_i) p_valid_after_sync_end) else $error("no load_valid after a sync_end");


//vp 1.0.3
a_memop_sync_end_num :		assume property (disable iff (!rsn_i || kill_i) p_memop_sync_end_num) else $error("too much memop_sync_end ");


//vp 1.0.4
a_load_ack_i_num :		assume property (disable iff (!rsn_i || kill_i) p_load_ack_i_num) else $error("too much memop_sync_end ");

//vp 1.0.5
a_unique_request : 		assume property (disable iff (!rsn_i || kill_i) p_unique_request) else $error("requested an already issued load");

//LMU IF////////////////////////
//vp 1.1.1
a_lmu_valid_load_i :		assume property (disable iff (!rsn_i || kill_i) p_lmu_valid_load_i) else $error("unknown input on mem_dvalid_load_i asserted");

//vp 1.1.2
a_enable_coherence :		assume property (disable iff (!rsn_i || kill_i) p_enable_coherence) else $error("wrong lmu_enable_i to LB");

//MQ IF/////////////////////////
//vp 1.2.1
a_load_request_i :		assume property (disable iff (!rsn_i || kill_i) p_load_request_i) else $error("unknown load_inputs on load_req_i asserted");

//vp 1.2.2
a_req_after_gnt :		assume property (disable iff (!rsn_i || kill_i) p_req_after_gnt) else $error("req was 1 after a gnt");

//vp 1.2.3
a_gnt_after_req :		assert property (disable iff (!rsn_i || kill_i) p_gnt_after_req) else $error("no gnt after a req");

//vp 1.2.4
a_gnt_beh :			assert property (disable iff (!rsn_i || kill_i) p_gnt_beh) else $error("gnt lasted more than 1 clock cycle");

//vp 1.2.5
a_num_gnt :			assert property (disable iff (!rsn_i || kill_i) p_num_gnt) else $error("a load_gnt_o was asserted with no enought requests");

//vp 1.2.6
a_num_req_end :			assume property (disable iff (!rsn_i || kill_i) p_num_req_end) else $error("too many mem_sync_ends or too many load_req_i");


//FSM IF////////////////////////
//vp 1.3.1
a_read_write_en :		assume property (disable iff (!rsn_i || kill_i) p_read_write_en) else $error("read and write enables at the same time");

//vp 1.3.2
a_write_after_read :		assume property (disable iff (!rsn_i || kill_i) p_write_after_read) else $error("no write after a read");


//CU IF/////////////////////////
//vp 1.4.1
a_cu_ack :			assume property (disable iff (!rsn_i || kill_i) p_cu_ack) else $error("wrong handshake of load_valid with load_ack");

//vp 1.4.2
a_cu_ack_num :			assert property (disable iff (!rsn_i || kill_i) p_cu_ack_num) else $error("load_ack without a load_valid_o");

//vp 1.4.3
a_num_load_completed : 		assume property (disable iff (!rsn_i || kill_i) p_num_load_completed) else $error("to many load_ack_i");

//VRF IF////////////////////////
//vp 1.5.1
a_output_data_known :		assert property (disable iff (!rsn_i || kill_i) p_output_data_known) else $error("unknown outputs on load_write_en_rf_o");

//vp 1.5.2
a_write_en_rf :			assert property (disable iff (!rsn_i || kill_i) p_write_en_rf) else $error("load_write_en_rf_o when a valid load_write was possible");

//vp 1.5.3
a_load_valid_addr :		assert property (disable iff (!rsn_i || kill_i) p_load_valid_addr) else $error("load addr is not matching");


//VL IF////////////////////////
//vp 1.6.1
a_load_inflight_o  : 		assert property (disable iff(!rsn_i || kill_i) p_load_inflight_o) else $error("wrong load_inflight_o");

//vp 1.6.2
a_load_ready_o : 		assert property (disable iff(!rsn_i || kill_i) p_load_ready_o) else $error("ready_o = 0 when a data was into the buffer during the write");

//vp 1.6.3
generate
	//1.6.3.0
	a_data_corruption_64 :	assert property (disable iff (!rsn_i || kill_i) p_data_corruption_64) else $error("data_i didn't pass trought the LB");
	
	//1.6.3.1
	for (genvar i_32 = 0; i_32 < 2; i_32++)
		a_data_corruption_32 :	assert property (disable iff (!rsn_i || kill_i) p_data_corruption_32(i_32)) else $error("data_i didn't pass trought the LB");
	//1.6.3.2
	for (genvar i_16 = 0; i_16 < 4; i_16++)
		a_data_corruption_16 :	assert property (disable iff (!rsn_i || kill_i) p_data_corruption_16(i_16)) else $error("data_i didn't pass trought the LB");
	//1.6.3.3
	for (genvar i_8 = 0; i_8 < 8; i_8++)
		a_data_corruption_8 :	assert property (disable iff (!rsn_i || kill_i) p_data_corruption_8(i_8)) else $error("data_i didn't pass trought the LB");

endgenerate

//RSN IF///////////////////////
//vp 1.7.1
a_rsn_output :			assert property (p_rsn_output) else $error("wrong outputs on reset");

//vp 1.7.2
a_rsn_input :			assume property (p_rsn_input) else $error("wrong inputs on reset");

//vp 1.7.3
a_kill_input :			assume property (p_kill_input) else $error("wrong inputs on kill");



///////////////////////////////////////////////////////
/////////////////////// tasks /////////////////////////
///////////////////////////////////////////////////////


// This function computes the bank of an element
function [BANK_IDX_SZ-1:0] get_el_bank([EL_ID_WIDTH-1:0] el_id, [SEW_WIDTH-1:0] sew);
    case (sew[1:0])
        SEW64: get_el_bank=((el_id/N_LANES)%N_BANKS); // 0, 1 ... 7 go to bank 0, 8 to 15 to bank 1 ... until 40-47 that go again to bank 0, etc.
        SEW32: get_el_bank=(((el_id>>1)/N_LANES)%N_BANKS); // 0 to 15 go to bank 0, 16 to 31 to bank 1 ... until 80-95 that go again to bank 0, etc.
        SEW16: get_el_bank=(((el_id>>2)/N_LANES)%N_BANKS); // 0 to 31 go to bank 0, 32 to 63 to bank 1 ... until 160-191 that go again to bank 0, etc.
        SEW8:  get_el_bank=(((el_id>>3)/N_LANES)%N_BANKS); // 0 to 63 go to bank 0, 64 to 128 to bank 1 ... until 320-383 that go again to bank 0, etc.
    endcase
endfunction

// This function checks the coherence of lmu_enable_i
function bit is_coherent([MASK_BANK_WORD-1:0] lmu_enable_i, [SEW_WIDTH-1:0] sew);
    is_coherent = 0;
    case (sew[1:0])
        SEW64: if( (lmu_enable_i == '0) || (lmu_enable_i == '1) ) is_coherent = 1;
        SEW32:	if ( ( (lmu_enable_i[3:0] == '0) || (lmu_enable_i[3:0] == '1) ) && ( (lmu_enable_i[7:4] == '0) || (lmu_enable_i[7:4] == '1) ) ) is_coherent = 1;
		
        SEW16:	if ( ( (lmu_enable_i[1:0] == '0) || (lmu_enable_i[1:0] == '1) ) && ( (lmu_enable_i[3:2] == '0) || (lmu_enable_i[3:2] == '1) ) && ( (lmu_enable_i[5:4] == '0) || (lmu_enable_i[5:4] == '1) ) && ( (lmu_enable_i[7:6] == '0) || (lmu_enable_i[7:6] == '1) ) )  is_coherent = 1;
        SEW8: is_coherent=1;
    endcase
endfunction






endmodule: LoadBuffer_checker 






