`define FUNCTIONAL // comment this when doing formal verification, (Quest CDC does not support task)

import EPI_pkg::*;

bind load_management_unit load_management_unit_checker #(
	.MEM_DATA_WIDTH(MEM_DATA_WIDTH),
	.SEQ_ID_WIDTH(SEQ_ID_WIDTH),
	.MAX_NUMBER_ELEMENTS(MAX_NUMBER_ELEMENTS),
	.AVISPADO_LOAD_MASK_WIDTH(AVISPADO_LOAD_MASK_WIDTH),
	.NUM_LANES(NUM_LANES)) bind_load_management_unit_checker (.*);



module load_management_unit_checker
	#(
	parameter MEM_DATA_WIDTH = 512,
	parameter SEQ_ID_WIDTH = 33,
        parameter MAX_NUMBER_ELEMENTS = 64,
        parameter AVISPADO_LOAD_MASK_WIDTH = 64,
        parameter NUM_LANES = 8
	)(
	input							clk_i,
	input							rsn_i,
	input 							kill_i,
	input 							load_granted_i,
	input [SB_WIDTH-1:0] 					load_granted_sb_id_i,
	input 							indexed_load_granted_i,
	input							load_sync_end_i,
	input [SB_WIDTH-1:0]					load_sync_end_sb_id_i,
	input                       				load_data_valid_i,
	input [MEM_DATA_WIDTH-1:0]  				load_data_i,
	input [SEQ_ID_WIDTH-1:0]    				seq_id_i,
	input                       				mask_valid_i,
	input [AVISPADO_LOAD_MASK_WIDTH-1:0]      		mask_i,
	input [SEW_WIDTH-2:0]      				sew_i,      // SEW (00:8 - 01:16 - 10:32 - 11:64)
	input signed [XREG_WIDTH-1:0] 				stride_i,   // stride in bytes
	input [MEM_DATA_WIDTH-1:0] 				load_data_o,
	input 							load_dvalid_o,
	input [AVISPADO_LOAD_MASK_WIDTH-1:0] 			mask_o,
	input [MAX_NUMBER_ELEMENTS-1:0] [EL_ID_WIDTH-1:0] 	element_ids_o,
	input [SB_WIDTH-1:0] 					sb_id_o,
	input [CSR_VLEN_START-1:0] 				vstart_self_o,
	input [CSR_VLEN_START-1:0] 				vstart_next_o,
	input [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	min_element_id_idx_o
	);

//////////////////////////////////////////////////////
//////////////////// variables ///////////////////////
//////////////////////////////////////////////////////

typedef struct {
	longint signed STRIDE;
	int unsigned SEW;
	int unsigned sb_id;
	bit is_indexed;
	bit done;
} granted_load;


granted_load fifo[1:0];
bit is_indexed;
bit sb_correct;
int unsigned SEW;
longint signed STRIDE;
int unsigned EL_COUNT;
int unsigned OFFSET;
int unsigned EL_ID;
int unsigned N_ELEMENTS;
int unsigned num_load_inflight; 

bit [MEM_DATA_WIDTH-1:0]  computed_data_o;
bit [MEM_DATA_WIDTH-1:0]  x_display0;
bit [MEM_DATA_WIDTH-1:0]  x_display1;
bit [MEM_DATA_WIDTH-1:0]  x_display2;
bit [AVISPADO_LOAD_MASK_WIDTH-1:0] m_result;
bit [MAX_NUMBER_ELEMENTS-1:0][EL_ID_WIDTH-1:0] computed_el_id_o;
bit [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	c_min_element_id_idx;
bit [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	c_min_element_id_idx_1;
bit [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	c_min_element_id_idx_2;
bit [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	c_min_element_id_idx_3;
bit [MEM_DATA_WIDTH-1:0] big_mask;
bit [AVISPADO_LOAD_MASK_WIDTH-1:0] valid_bytes;
bit [NUM_LANES-1:0] valid_mins;

//////////////////////////////////////////////////////
/////////////////////processes////////////////////////
//////////////////////////////////////////////////////


initial begin 
	sb_correct = 1;
	computed_data_o = '0;
	fifo[0].sb_id = 20; // we have to initialize it to a value that cannot be in input, to avoid to read the wrong SEW and STRIDE from the wrong fifo cell
	fifo[1].sb_id = 20;
	fifo[1].done = 1;
	fifo[0].done = 1;
	num_load_inflight = 0;
end


// sew and stride fifo 
always @(negedge clk_i)
	begin
	if ( !rsn_i || kill_i ) begin
		fifo[1].SEW = '0;
		fifo[1].STRIDE = '0 ;
		fifo[1].sb_id = 20 ;
		fifo[1].done = 1;
		fifo[0].SEW = '0;
		fifo[0].STRIDE = '0;
		fifo[0].sb_id = 20;
		fifo[0].done = 1;
	end
	
	if ( load_sync_end_i ) begin
		if ( load_sync_end_sb_id_i == fifo[1].sb_id ) begin
			fifo[1].done = 1;
		end
		if ( load_sync_end_sb_id_i == fifo[0].sb_id ) begin
			fifo[0].done = 1;
		end
	end

	if ( load_granted_i ) begin
		if ( fifo[1].done ) begin
			fifo[1].SEW = sew_i;
			fifo[1].STRIDE = stride_i;
			fifo[1].sb_id = load_granted_sb_id_i ;
			fifo[1].is_indexed = indexed_load_granted_i;
			fifo[1].done = 0;
		end
		else if( fifo[0].done ) begin
			fifo[0].SEW = sew_i;
			fifo[0].STRIDE = stride_i;
			fifo[0].sb_id = load_granted_sb_id_i;
			fifo[0].is_indexed = indexed_load_granted_i;
			fifo[0].done = 0;
		end
	end
	
	// check number of load_inflight
	if ( !rsn_i || kill_i) begin
		num_load_inflight = 0;
	end
	else begin
		num_load_inflight = num_load_inflight + load_granted_i - ( load_sync_end_i && ( ( load_sync_end_sb_id_i == fifo[0].sb_id ) | ( load_sync_end_sb_id_i == fifo[1].sb_id ) ) );
	end

	`ifdef FUNCTIONAL

		// sb_id check and start computing data
		if ( load_data_valid_i ) begin
			check_sb_correct();
		end
		

		// big_mask calculation
		if ( load_dvalid_o ) begin
			compute_big_mask_o();
		end

	`endif

end




//////////////////////////////////////////////////////
/////////////////////properties///////////////////////
//////////////////////////////////////////////////////


// 1.0.1  vp 
property p_el_count;
	int SEW0, SEW1, OFFSET;
	longint signed STRIDE0, STRIDE1;
	@(posedge clk_i)

	( load_data_valid_i && sb_correct, 
	OFFSET = seq_id_i[21:16],
	SEW0 = 2**(3+fifo[0].SEW), 
	STRIDE0 = (fifo[0].STRIDE > 0) ? fifo[0].STRIDE : -fifo[0].STRIDE,
	SEW1 = 2**(3+fifo[1].SEW), 
	STRIDE1 = (fifo[1].STRIDE > 0) ? fifo[1].STRIDE : -fifo[1].STRIDE
	)
	|-> 
	( (seq_id_i[32:29] == fifo[0].sb_id) && ( seq_id_i[28:22] <= (MEM_DATA_WIDTH/(STRIDE0*8) - OFFSET*SEW0/(STRIDE0*8)) ) ) or 
	( (seq_id_i[32:29] == fifo[1].sb_id) && ( seq_id_i[28:22] <= (MEM_DATA_WIDTH/(STRIDE1*8) - OFFSET*SEW1/(STRIDE1*8)) ) ) or 
	( seq_id_i[28:22] == 1 ) ;
endproperty : p_el_count


// 1.0.2 vp 
property p_stride_i;
	int SEW0, SEW1;
	longint signed STRIDE0, STRIDE1;
	@(posedge clk_i)
	( load_data_valid_i && 
	( ( (seq_id_i[32:29] == fifo[0].sb_id) && !fifo[0].is_indexed && !fifo[0].done) || 
	  ( (seq_id_i[32:29] == fifo[1].sb_id) && !fifo[1].is_indexed && !fifo[1].done) ),
	SEW0 = (2**(3+fifo[0].SEW))/8, 
	SEW1 = (2**(3+fifo[1].SEW))/8, 
	STRIDE0 = (fifo[0].STRIDE > 0) ? fifo[0].STRIDE : -fifo[0].STRIDE,
	STRIDE1 = (fifo[1].STRIDE > 0) ? fifo[1].STRIDE : -fifo[1].STRIDE
	)
	|->
	( ( (seq_id_i[32:29] == fifo[0].sb_id) && !fifo[0].done) && !(STRIDE0 % SEW0) ) ||
	( ( (seq_id_i[32:29] == fifo[1].sb_id) && !fifo[1].done) && !(STRIDE1 % SEW1) );
endproperty : p_stride_i


// 1.0.3 vp
property p_load_granted_i_known;
	@(posedge clk_i)
	load_granted_i |-> !$isunknown(sew_i) && !$isunknown(load_granted_sb_id_i) ;
endproperty : p_load_granted_i_known

// 1.0.4 vp
property p_load_data_i_known;
	@(posedge clk_i)
	load_data_valid_i |-> !$isunknown(load_data_i) && !$isunknown(seq_id_i) && !$isunknown(mask_valid_i) && !$isunknown(mask_i) ;
endproperty : p_load_data_i_known

// 1.0.5 vp
property p_sb_id_o;
	int sb ;
	@(posedge clk_i)
	(load_data_valid_i && sb_correct, sb=seq_id_i[32:29]) |-> ##1 sb_id_o == sb;
endproperty : p_sb_id_o

// 1.0.6 vp 
property p_load_dvalid_known;
	@(posedge clk_i)
	load_dvalid_o |-> 	!$isunknown(load_data_o) && !$isunknown(mask_o) && !$isunknown(element_ids_o) && !$isunknown(vstart_self_o)  && !$isunknown(vstart_next_o) && 					!$isunknown(min_element_id_idx_o);
endproperty : p_load_dvalid_known

// 1.0.7 vp
property p_dvalid_o;
	@(posedge clk_i)
	load_data_valid_i && sb_correct |-> ##1 load_dvalid_o ;
endproperty : p_dvalid_o

// 1.0.8 vp
property p_vstart_o;
	int unsigned count, id;
	@(negedge clk_i)
	(load_data_valid_i  , count=seq_id_i[28:22], id=seq_id_i[15:5])|-> ##1 ( (vstart_self_o == id) && (vstart_next_o == count + id) );
endproperty : p_vstart_o

// 1.0.9 vp
property p_granted_ids;
	@(negedge clk_i)
	load_granted_i |-> ( ( load_granted_sb_id_i != fifo[0].sb_id && !fifo[0].done ) || fifo[0].done ) && ( ( load_granted_sb_id_i != fifo[1].sb_id && !fifo[1].done ) || fifo[1].done ); 
endproperty : p_granted_ids

// 1.0.10 vp
property p_indexed_instr;
	@(posedge clk_i)
	load_data_valid_i && ( ( (seq_id_i[32:29] == fifo[0].sb_id) && fifo[0].is_indexed ) || ( (seq_id_i[32:29] == fifo[1].sb_id) && fifo[1].is_indexed ) ) |-> seq_id_i[28:22]==1 ;
endproperty : p_indexed_instr

// 1.0.11 vp
property p_load_sync_end_i;
	bit [SB_WIDTH-1:0] sb_id_granted;
	int counter; 
	@(posedge clk_i)
	( load_granted_i , sb_id_granted = load_granted_sb_id_i, counter = 3 ) |-> ##[1:$] load_sync_end_i && sb_id_granted == load_sync_end_sb_id_i;
endproperty : p_load_sync_end_i

// 1.0.12 vp
property p_load_grant_beh; 
	@(posedge clk_i)
	num_load_inflight == 2 |-> ##1 !load_granted_i;
endproperty : p_load_grant_beh


// 1.0.13 vp
property p_load_sync_end_beh; 
	@(posedge clk_i)
	num_load_inflight == 0 |-> ##1 !load_sync_end_i || ( load_sync_end_i && (load_sync_end_sb_id_i!=fifo[0].sb_id || (load_sync_end_sb_id_i==fifo[0].sb_id && fifo[0].done) ) && (load_sync_end_sb_id_i!=fifo[1].sb_id || (load_sync_end_sb_id_i==fifo[1].sb_id && fifo[1].done) ) );
endproperty : p_load_sync_end_beh

// 1.0.14 vp
property p_load_req_sync_end;
	@(posedge clk_i)
	load_granted_i |-> !load_sync_end_i || ( load_sync_end_i && load_sync_end_sb_id_i!=load_granted_sb_id_i );
endproperty : p_load_req_sync_end

// 1.0.15 vp
property p_el_count_sew_i;
	int SEW0, SEW1, OFFSET;
	longint signed STRIDE0, STRIDE1;
	@(posedge clk_i)
	( load_data_valid_i && sb_correct, 
	OFFSET = seq_id_i[21:16],
	SEW0 = (2**(3+fifo[0].SEW))/8, 
	STRIDE0 = (fifo[0].STRIDE > 0) ? fifo[0].STRIDE : -fifo[0].STRIDE,
	SEW1 = (2**(3+fifo[1].SEW))/8, 
	STRIDE1 = (fifo[1].STRIDE > 0) ? fifo[1].STRIDE : -fifo[1].STRIDE
	) ##0
	( (seq_id_i[32:29]==fifo[0].sb_id) && !fifo[0].is_indexed && !fifo[0].done && ( STRIDE0!=SEW0 && STRIDE0!=2*SEW0 && STRIDE0!=3*SEW0 && STRIDE0!=4*SEW0 ) || 
	  (seq_id_i[32:29]==fifo[1].sb_id) && !fifo[1].is_indexed && !fifo[1].done && ( STRIDE1!=SEW1 && STRIDE1!=2*SEW1 && STRIDE1!=3*SEW1 && STRIDE1!=4*SEW1 ) )
	|-> 
	( seq_id_i[28:22] == 1 ) ;
endproperty : p_el_count_sew_i

`ifdef FUNCTIONAL
	// 1.1.1 vp
	property p_sb_correct;
		@(posedge clk_i)
		load_data_valid_i && !sb_correct |-> ##1 !load_dvalid_o;
	endproperty : p_sb_correct

	// 1.1.2 vp
	property p_data_o;
		bit [MEM_DATA_WIDTH-1:0] data_out;
		@(posedge clk_i)
		(load_data_valid_i && sb_correct, data_out = computed_data_o) |-> ##1 (load_data_o & big_mask) == (data_out & big_mask);
	endproperty : p_data_o

	// 1.1.3 vp
	property p_mask_o;
		bit [MEM_DATA_WIDTH-1:0] mask_out;
		@(posedge clk_i)
		(load_data_valid_i && sb_correct, mask_out = m_result)|-> ##1 mask_o == mask_out;
	endproperty : p_mask_o

	// 1.1.4 vp
	property p_el_ids_o;
		bit [MAX_NUMBER_ELEMENTS-1:0][EL_ID_WIDTH-1:0] buffer_ids;
		@(posedge clk_i)
		(load_data_valid_i  && sb_correct, buffer_ids = computed_el_id_o)|-> ##1 element_ids_o == buffer_ids;
	endproperty : p_el_ids_o

	// 1.1.5 vp
	property p_min_element_id_idx_o;
		bit [NUM_LANES-1:0][$clog2(MASK_BANK_WORD)-1:0] 	b_min_ids,b_min_ids_1,b_min_ids_2,b_min_ids_3;
		bit [NUM_LANES-1:0] b_valid_mins;
		int SEW0, SEW1;
		bit [3:0] sb_id;
		@(posedge clk_i)
		(load_data_valid_i && sb_correct, b_min_ids = c_min_element_id_idx, b_min_ids_1 = c_min_element_id_idx_1, b_min_ids_2 = c_min_element_id_idx_2, b_min_ids_3 = c_min_element_id_idx_3, SEW0 = fifo[0].SEW, SEW1 = fifo[1].SEW, sb_id=seq_id_i[32:29], b_valid_mins=valid_mins)|-> ##1 
( sb_id == fifo[0].sb_id && SEW0==3 ) || ( sb_id == fifo[1].sb_id && SEW1==3 ) || (
( ( min_element_id_idx_o[0]==b_min_ids[0] || min_element_id_idx_o[0]==b_min_ids_1[0] || min_element_id_idx_o[0]==b_min_ids_2[0] || min_element_id_idx_o[0]==b_min_ids_3[0] ) || !b_valid_mins[0] ) && 
( ( min_element_id_idx_o[1]==b_min_ids[1] || min_element_id_idx_o[1]==b_min_ids_1[1] || min_element_id_idx_o[1]==b_min_ids_2[1] || min_element_id_idx_o[1]==b_min_ids_3[1] ) || !b_valid_mins[1] ) && 
( ( min_element_id_idx_o[2]==b_min_ids[2] || min_element_id_idx_o[2]==b_min_ids_1[2] || min_element_id_idx_o[2]==b_min_ids_2[2] || min_element_id_idx_o[2]==b_min_ids_3[2] ) || !b_valid_mins[2] ) && 
( ( min_element_id_idx_o[3]==b_min_ids[3] || min_element_id_idx_o[3]==b_min_ids_1[3] || min_element_id_idx_o[3]==b_min_ids_2[3] || min_element_id_idx_o[3]==b_min_ids_3[3] ) || !b_valid_mins[3] ) && 
( ( min_element_id_idx_o[4]==b_min_ids[4] || min_element_id_idx_o[4]==b_min_ids_1[4] || min_element_id_idx_o[4]==b_min_ids_2[4] || min_element_id_idx_o[4]==b_min_ids_3[4] ) || !b_valid_mins[4] ) && 
( ( min_element_id_idx_o[5]==b_min_ids[5] || min_element_id_idx_o[5]==b_min_ids_1[5] || min_element_id_idx_o[5]==b_min_ids_2[5] || min_element_id_idx_o[5]==b_min_ids_3[5] ) || !b_valid_mins[5] ) && 
( ( min_element_id_idx_o[6]==b_min_ids[6] || min_element_id_idx_o[6]==b_min_ids_1[6] || min_element_id_idx_o[6]==b_min_ids_2[6] || min_element_id_idx_o[6]==b_min_ids_3[6] ) || !b_valid_mins[6] ) && 
( ( min_element_id_idx_o[7]==b_min_ids[7] || min_element_id_idx_o[7]==b_min_ids_1[7] || min_element_id_idx_o[7]==b_min_ids_2[7] || min_element_id_idx_o[7]==b_min_ids_3[7] ) || !b_valid_mins[7] )
) ;
	endproperty : p_min_element_id_idx_o

`endif

// 1.2.1 vp
property p_rsn_o;
	@(posedge clk_i)
	!rsn_i |-> ##1 !load_dvalid_o && mask_o == '0;
endproperty : p_rsn_o

// 1.2.2 vp
property p_rsn_i;
	@(posedge clk_i)
	!rsn_i |-> !load_data_valid_i && !load_granted_i;
endproperty : p_rsn_i


///////////////////////////////////////////////////////
///////////////////assert & assume/////////////////////
///////////////////////////////////////////////////////

// 1.0.1 vp
a_el_count : 			assume property( disable iff(!rsn_i || kill_i) p_el_count ) else $error("Avispado sent a EL_COUNT greater than allowed"); 

// 1.0.2 vp
a_stride_i : 			assume property( disable iff(!rsn_i || kill_i) p_stride_i ) else $error("Avispado sent an invalide stride");	

// 1.0.3 vp
a_load_granted_i_known :	assume property( disable iff(!rsn_i || kill_i) p_load_granted_i_known ) else $error("MQ sent unknown sew or sb_id"); 

// 1.0.4 vp
a_load_data_i_known :		assume property( disable iff(!rsn_i || kill_i) p_load_data_i_known ) else $error("MQ sent unknown sew or sb_id"); 

// 1.0.5 vp
a_sb_id_o :			assert property( disable iff(!rsn_i || kill_i) p_sb_id_o ) else $error("wrong sb_id in output");

// 1.0.6 vp
a_load_dvalid_known :		assert property( disable iff(!rsn_i || kill_i) p_load_dvalid_known ) else $error("an LMU output is unknown");

// 1.0.7 vp
a_dvalid_o :			assert property( disable iff(!rsn_i || kill_i) p_dvalid_o ) else $error("LMU did not compute any output");

// 1.0.8 vp
a_vstart_o :			assert property( disable iff(!rsn_i || kill_i) p_vstart_o ) else $error("wrong vstart_*");

// 1.0.9 vp
a_granted_ids : 		assume property( disable iff(!rsn_i || kill_i) p_granted_ids ) else $error("unallowed sb_id_i to the LMU");

// 1.0.10 vp
a_indexed_instr : 		assume property( disable iff(!rsn_i || kill_i) p_indexed_instr) else $error("issued an indexed with el_count!=1 or with mask");

// 1.0.11 vp
a_load_sync_end_i :		assume property( disable iff(!rsn_i || kill_i) p_load_sync_end_i) else $error("it didn't arrive a load_sync_end_i that was supposed to");

// 1.0.12 vp
a_load_grant_beh :		assume property( disable iff(!rsn_i || kill_i) p_load_grant_beh) else $error("issued 3 load_granted_i to the LMU without load_sync_end");

// 1.0.13 vp
a_load_sync_end_beh : 		assume property( disable iff(!rsn_i || kill_i) p_load_sync_end_beh) else $error("ended a load not actually issued");

// 1.0.14 vp
a_load_req_sync_end :		assume property( disable iff(!rsn_i || kill_i) p_load_req_sync_end) else $error("issued a new instruction simultaneously with a sync_end");

// 1.0.15 vp
a_el_count_sew_i : 		assume property( disable iff(!rsn_i || kill_i) p_el_count_sew_i ) else $error("Avispado sent a EL_COUNT!=1 with a stride!=+-1/2/3/4*sew"); 


`ifdef FUNCTIONAL

	// 1.1.1 vp 
	a_sb_correct :			assert property( disable iff(!rsn_i || kill_i) p_sb_correct ) else $error("LMU sent a output as dvalid_o = 1, for a non-valid load");	

	// 1.1.2 vp
	a_data_o :			assert property( disable iff(!rsn_i || kill_i) p_data_o ) else $error("wrong load_data_o");
		
	// 1.1.3 vp
	a_mask_o :			assert property( disable iff(!rsn_i || kill_i) p_mask_o ) else $error("wrong mask_o");

	// 1.1.4 vp
	a_el_ids_o :			assert property( disable iff(!rsn_i || kill_i) p_el_ids_o ) else $error("mismatch in element_ids_o");

	// 1.1.5 vp
	a_min_element_id_idx_o : 	assert property( disable iff(!rsn_i || kill_i) p_min_element_id_idx_o) else $error("wrong min_element_id_idx_o");

`endif

// 1.2.1 vp
a_rsn_o : 				assert property(p_rsn_o) else $error("rsn did not work");

// 1.2.2 vp
a_rsn_i : 				assume property(p_rsn_i) else $error("rsn input");

///////////////////////////////////////////////////////
/////////////////////// tasks /////////////////////////
///////////////////////////////////////////////////////
`ifdef FUNCTIONAL

	task check_sb_correct();

		
		if ( seq_id_i[32:29] == fifo[0].sb_id && !fifo[0].done ) begin
			SEW = 2**(3+fifo[0].SEW) ;
			STRIDE = fifo[0].STRIDE;
			is_indexed = fifo[0].is_indexed;
			sb_correct = 1;
		end
		else if ( seq_id_i[32:29] == fifo[1].sb_id && !fifo[1].done ) begin
			SEW = 2**(3+fifo[1].SEW) ;
			STRIDE = fifo[1].STRIDE;
			is_indexed = fifo[1].is_indexed;
			sb_correct = 1;
		end
		else begin
			sb_correct = 0;
		end
		if (sb_correct) begin
			EL_COUNT = seq_id_i[28:22];
			OFFSET = seq_id_i[21:16];
			EL_ID = seq_id_i[15:5];
			N_ELEMENTS = MEM_DATA_WIDTH/SEW;
			
			compute_data_o(SEW,STRIDE,EL_COUNT,OFFSET,EL_ID,N_ELEMENTS,is_indexed);
			compute_mask_o(SEW,EL_COUNT,EL_ID,N_ELEMENTS);
			compute_ids(SEW,EL_COUNT,EL_ID,N_ELEMENTS);
			compute_c_min_element_id_idx(SEW,EL_COUNT,EL_ID,N_ELEMENTS);

		end


	endtask : check_sb_correct

	task compute_data_o(int unsigned SEW, longint signed STRIDE, int unsigned EL_COUNT, int unsigned OFFSET, int unsigned EL_ID, int unsigned N_ELEMENTS, bit is_indexed);
		bit x[][];
		bit y[][];
		int unsigned j;
		int unsigned k;
		longint signed local_stride;

		local_stride=STRIDE;

		// step zero: sample the input, one byte at a time (SystemVerilog requires a constant width)
		x=new[N_ELEMENTS];
		y=new[N_ELEMENTS];

		foreach(x[i]) begin
			x[i]=new[SEW];
			y[i]=new[SEW];
		end
		

		for(k=0; k < N_ELEMENTS; k++) begin
			for(j=0;j < SEW; j++) begin
				x[N_ELEMENTS-1-k][SEW-j-1] = load_data_i[k*SEW+j];
			end
		end

		x_display0 = {>>{x}}; //debug signal

		// first step: take the stride into account
		
		if(!is_indexed && local_stride<0) begin
			foreach(x[i]) begin //if it's strided with negative stride, reverse the input
				y[N_ELEMENTS-1-i]=x[i];
			end	
		end 
		else if (is_indexed || (!is_indexed && local_stride>=0) ) begin 
			foreach(x[i]) begin //if it's indexed or strided with positive stride, do nothing
				y[i]=x[i];
			end
		end 
		
		x_display1 = {>>{y}}; //debug signal

		if (local_stride<0) local_stride = ( -1 ) * local_stride;
		local_stride = local_stride * 8 / SEW; // normalize from #of bytes to # of elements


		// second step: concatenate the data according to stride 
		// mask is not taken into account as there is no reason to out the output bits to 0: what we compare are the two outputs in AND with the mask_o	
		// initialize x to 0
		for(j=0;j<N_ELEMENTS;j++) begin
			for(k=0;k<SEW;k++) begin
				x[j][k] = 0;
			end
		end


		for (j=0; j<EL_COUNT; j++) begin
				x[(N_ELEMENTS-1-j)] = y[(N_ELEMENTS-1-j*local_stride-OFFSET)%N_ELEMENTS];
		end
	 
		 x_display2 = {>>{x}}; //debug signal

		// third step: shift the data according to EL_ID
		k = EL_ID % N_ELEMENTS;
		for (j=0; j<N_ELEMENTS; j++) begin
			y[(N_ELEMENTS-1-(k+j))%N_ELEMENTS] = x[(N_ELEMENTS-1-j)]; // "%n_elements" automatically manages the underflow 
		end

		/* we do the iterazion on all y to clean it from the old values computed in step 1, otherwise we could do it on only EL_COUNT but with a further previous initialization to 0*/

		computed_data_o = {>>{y}}; 


	endtask : compute_data_o


	task compute_mask_o(int unsigned SEW, int unsigned EL_COUNT, int unsigned EL_ID, int unsigned N_ELEMENTS);

		bit m_op [][];
		int unsigned m, n, k;
		
		m_op = new[N_ELEMENTS];

		foreach(m_op[k])
			m_op[k] = new[AVISPADO_LOAD_MASK_WIDTH/N_ELEMENTS]; 

		//init to 0
		for(m = 0; m < N_ELEMENTS; m++) begin
			for(n = 0; n < AVISPADO_LOAD_MASK_WIDTH/N_ELEMENTS; n++) 
				m_op[m][n] = 1'b0;
		end

		//assignment valid values to 1	
		k = 0;
		for(m = EL_ID; m < (EL_ID + EL_COUNT); m++) begin
			if ( !mask_valid_i || (mask_valid_i && mask_i[k]) ) begin
				for(n = 0; n < AVISPADO_LOAD_MASK_WIDTH/N_ELEMENTS; n++) begin
					m_op[N_ELEMENTS-1-(m%(N_ELEMENTS))][n] = 1'b1;
				end
			end
			k++;
		end
		
		m_result = {>>{m_op}};

	endtask : compute_mask_o


	task compute_ids(int unsigned SEW, int unsigned EL_COUNT, int unsigned EL_ID, int unsigned N_ELEMENTS);

		int unsigned f_v_e, i, j;
		
		// f_v_e is the index of the first 11-bit-element of computed_el_id_o where we have to put an EL_ID
		f_v_e = EL_ID % N_ELEMENTS; // find the first valid element 
		f_v_e = f_v_e * SEW / 8 ; // multiply it by the pace (number of bytes per element)
		
		// initialize to 0
		for(j=0;j<MAX_NUMBER_ELEMENTS;j++) begin
			computed_el_id_o[j] = '0;
		end

		for(j=0;j<EL_COUNT;j++) begin
			for(i=0;i<SEW/8;i++) begin
				computed_el_id_o[(f_v_e + i + (j*SEW/8))%MAX_NUMBER_ELEMENTS] = EL_ID + j;
			end
		end

	endtask : compute_ids


	task compute_big_mask_o();
		int j, k;
		bit bm[][];


		bm=new[MEM_DATA_WIDTH/8];

		foreach(bm[i]) begin
			bm[i]=new[8];
		end

		//init to 0
		for(k=0; k < MEM_DATA_WIDTH/8; k++) begin
			for(j=0;j < 8; j++) begin
				bm[k][j] = 0;
			end
		end


		//generate the mask at 512 bit
		for(k=0; k < MEM_DATA_WIDTH/8; k++) begin
			if(mask_o[k]) begin
				for(j=0; j < 8; j++) begin
					bm[MEM_DATA_WIDTH/8 -k -1][j] = 1;
				end
			end
		end

		big_mask = {>>{bm}};

	endtask: compute_big_mask_o


	task compute_c_min_element_id_idx(int unsigned SEW, int unsigned EL_COUNT, int unsigned EL_ID, int unsigned N_ELEMENTS);

		bit m_op [][];
		int unsigned m, n, k, min_el_id, f_v_e;
		int j,i;

		// computing the mask, as if the instruction was not masked
		f_v_e = EL_ID % N_ELEMENTS; // find the first valid element 
		f_v_e = f_v_e * SEW / 8 ; // multiply it by the pace (number of bytes per element)
		
		for(j=0;j<MAX_NUMBER_ELEMENTS;j++) begin // initialize to 0
			valid_bytes[j] = '0;
		end
		
		for(j=0;j<EL_COUNT;j++) begin // put to 1 the valid bits
			for(i=0;i<SEW/8;i++) begin
				valid_bytes[(f_v_e + i + (j*SEW/8))%MAX_NUMBER_ELEMENTS] = 1'b1;
			end
		end

		// computing min_el_id_idx
		foreach(valid_mins[i]) valid_mins[i]=0;
		foreach(c_min_element_id_idx[i]) c_min_element_id_idx[i]=0;

		for(j=0;j<N_LANES;j++) begin
			c_min_element_id_idx[j]=0;
			min_el_id = 2057;
			for(i=0;i<8;i++) begin
				if(valid_bytes[j*8+i]) begin
					if (computed_el_id_o[j*8+i]<min_el_id) begin
						min_el_id=computed_el_id_o[j*8+i];
						c_min_element_id_idx[j]=i;
					end 
					valid_mins[j]=1;
				end
			end
		end
		
		
		if(SEW==32) begin
			for(j=0;j<8;j++) begin
				c_min_element_id_idx_1[j]=c_min_element_id_idx[j]+1;
				c_min_element_id_idx_2[j]=c_min_element_id_idx[j]+2;
				c_min_element_id_idx_3[j]=c_min_element_id_idx[j]+3;
			end
		end

		if(SEW==16) begin
			for(j=0;j<8;j++) begin
				c_min_element_id_idx_1[j]=c_min_element_id_idx[j]+1;
				c_min_element_id_idx_2[j]=c_min_element_id_idx[j];
				c_min_element_id_idx_3[j]=c_min_element_id_idx[j]+1;
			end
		end

		if(SEW==8) begin
			for(j=0;j<8;j++) begin
				c_min_element_id_idx_1[j]=c_min_element_id_idx[j];
				c_min_element_id_idx_2[j]=c_min_element_id_idx[j];
				c_min_element_id_idx_3[j]=c_min_element_id_idx[j];
			end
		end

	endtask : compute_c_min_element_id_idx
	
`endif

endmodule: load_management_unit_checker 






