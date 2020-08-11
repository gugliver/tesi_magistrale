This documentation is an updated version of this [one](https://repo.hca.bsc.es/gitlab/EPI/RTL/Vector_Accelerator/-/wikis/VPU/Load-Management-Unit) at 27/05/2020.

[[_TOC_]]

# Load Management Unit

> :information_source:&emsp;Brief description

This module is in charge of handling the load operations, either strided and indexed.
Since the elements coming from memory are not guaranteed to arrive in order, a sequence ID
is sent by Avispado alongside the data.

This sequence ID contains sufficient information to allow the proper ordering of the incoming data, before sending it to the lanes.

This module is mainly made of three components: shifter, compactor and aligner.

The first component is in charge of eliminating the offset within the received line of data, meaning that it is possible to have the first valid element not in the LSB (or MSB in the case of negative stride).

The second component is in charge of getting rid of the stride, so concatenating the valid elements. When *stride=1*, the output of this component is the same as the input.

The last component is in charge of aligning the elements according to their corresponding lane and subbank.

This module is made of combinational logic.

## Include and package files

- EPI_pkg.sv

## Parameters

> :information_source:&emsp;Some parameters that ease future changes, default values are indicated at the end of each parameter.

- MEM_DATA_WIDTH: Data bus width for receiving data coming from Avispado. `512`
- SEQ_ID_WIDTH: Width of the sequence ID that identifies the data coming from Avispado. `33`
- MAX_NUMBER_ELEMENTS: This is the maximum number of elements that can be encoded in the chunk of data received (64 when SEW=8b). `64`
- AVISPADO_LOAD_MASK_WIDTH: Indicates the maximum number of mask bits that are received with the data. `64`
- NUM_LANES: Number of lanes. `8`

## Interface

The following table describes the interface to which this module is connected to. In a few words, this module is directly connected to the Avispado Interface and to the multilane wrapper.

> :information_source:&emsp;Input signal Coming From, Output signal Connected To


| **Signal**      |**Size(b)**|   **Type**   | **Coming From/Connected To** | **Description**
|:----------------|:---------|:------------------|:-----------------|:-----------------
| load_granted_i   |   1   | In           | Mem Queue | Indicates the memory queue is sending a Load instruction with a certain `sew_i` and `stride_i` 
| load_granted_sb_id_i   |   SB_WIDTH   | In           | Mem Queue | Indicates the id for the issued Load, can be issued up to 2 loads (i.e. LMU must support up to 2 inflights load)
| indexed_load_granted_i | 1 | In | Mem Queue | Flag to indicate that the granted load is indexed
| load_data_valid_i   |   1   | In           | Avispado | Indicates if the data in `load_data_i` bus is valid
| load_data_i   |   MEM_DATA_WIDTH   | In           | Avispado | Input data bus for receiving data coming from Avispado
| seq_id_i[32:0]   |   SEQ_ID_WIDTH   | In           | Avispado | Sequence ID identifying data contained in the bus `load_data_i`
| seq_id_i[4:0] | V_REG | In | Avispado | logical vector register where the data has to be written
| seq_id_i[15:5] | EL_ID | In | Avispado | destination element ID (see below)
| seq_id[21:16] | EL_OFF | In | Avispado | offset to identify the first valid data in load_data_i, according to the current SEW
| seq_id_i[28:22] | EL_COUNT | In | Avispado | number of valid elements
| seq_id_i[32:29] | SB_ID | In | Avispado | socreboard ID of the Load instruction
| mask_valid_i   |   1   | In           | Avispado | Indicates if the mask bits in `mask_i` bus is valid
| mask_i   |   AVISPADO_LOAD_MASK_WIDTH   | In           | Avispado | Mask bits belonging to the specific chunk of data received in `load_data_i`
| sew_i   |   3   | In           | Wrapper | Standard Element Width identifying the size of each vector element, sent with load_granted_i
| stride_i   |   64   | In           | Wrapper | Stride indicated in bytes, sent with load_granted_i
| load_data_o   |   MEM_DATA_WIDTH   | Out           | Wrapper | Output data bus for sending reordered data to the lanes
| load_dvalid_o   |   1   | Out           | Wrapper | Indicates if the data in `load_data_o` bus is valid
| mask_o   |   AVISPADO_LOAD_MASK_WIDTH   | Out           | Wrapper | Mask bits belonging to the specific chunk of data being sent in `load_data_o` (indicates valid bits, for every load instruction, not only masked)
| element_ids_o   |  MAX_NUMBER_ELEMENTS*EL_ID_WIDTH | Out           | Wrapper | Element IDs identifying each one of the elements contained in the chunk of data being sent in `load_data_o`
| sb_id_o   |   4   | Out           | Wrapper | Scoreboard ID identifying the instruction the data sent in `load_data_o` belongs to
| vstart_self_o   |   ADDR_WIDTH   | Out           | Wrapper | Element ID identifying the first valid element in the chunk of data received in `load_data_i`
| vstart_next_o   |   ADDR_WIDTH   | Out           | Wrapper | Element ID identifying the last valid element in the chunk of data received in `load_data_i`
| min_element_id_idx_o   |   NUM_LANES(8) * clog2(MASK_BANK_WORD(8))    | Out           | Wrapper | It is the index of the first valid element in elements_ids_o of each lane.



Principle of working
--------------------

There are two general types of load operations that are supported by this module.

The first type is strided loads, where the received vector elements are separated by a constant *stride*. Supported values for strided loads are 1, 2, 4, -1, -2, -4 times the SEW. It may happen that the stride is different from the supported values, in that case, EL_COUNT has to be equal to 1.

The other type of load operations is indexed, where the arrival of the elements is on a per-element basis, meaning that we get only one valid element per chunk of 512b.

Aditionally, any load operation can be masked or unmasked.

Since the memory system is not guaranteeing the in-order arrival of elements, a sequence ID containing the following information is sent alongside the data in order to identify each valid element and perform the reordering in case it is needed before sending the elements to the lanes and their corresponding Load Buffers.

* Virtual register: identifies the logical vector register to which the data should be written to.
* Element ID: element id of the first valid element contained in the chunk of data being transmitted.
* Element offset: identifies the position of the first valid element, and it is calculated according to the current SEW.
* Element count: indicates the number of valid elements being transmitted, bearing in mind that masked elements are also valid elements.
* Scoreboard ID: scoreboard ID of the load instruction that requested the data.

> :warning: **Element ID** 


**Element ID** is the variable used to do the last shift, to correctly align the data: each Vector has a variable number of elements according to the following table.

| **SEW**  | **ELEMENTS**
| ---------| --------------
| 64       | 256
| 32       | 512
| 16       | 1024
| 8        | 2048

So, each element can be addressed to with its Element ID, which will simply be its position in the Vector. As a consequence, for example, each element_id = n * (512/SEW) , with n between 0 and 31*(64/SEW), will indicate the first position of the 512-bit chunk of data.

> :warning:&emsp;In case any other stride is used, regardless the SEW, only one element per chunk of data is transmitted.

### Strided loads

The following example assumes a SEW of 32b, therefore there are up to 16 elements in the 512b cache line. Also, let's assume an LMUL=1, meaning that a load fetches up to 512 elements. The example shows a chunk of 512b of data transmitted from Avispado to the VPU, split into elements of 32b. Cells in blue indicate valid elements, along with a number representing the element ID. White cells represent invalid data that must be discarded.

* Stride: `-16` (-2 SEW)
* Virtual register: `A`
* Element ID: `491`
* Element offset: `5`
* Element count: `6`
* Scoreboard ID: `B`





![strided_ex](uploads/9be55080b82673b67147b033b845c61b/strided_ex.png)






The first step consists on identifying if the stride is either positive or negative. In the latter case, the cache line is reversed, keeping the correctness of the endianness of the elements.

Then, the cache line goes through the SHIFTER in order to eliminate the offset, as shown in the example, shifter step.

Afterwards, we have the first valid element at the beginning of the cache line, and by using the COMPACTOR, the stride between elements is eliminated. The result of this processing is shown in the above picture, Compactor step.

Finally, the elements have to be aligned according to the element mapping. This is done by left-shifting the first valid element to the correct lane and subbank.

The subbank is defined according to the element id. This is due in the case when **SEW < 64b**, we have more than one element mapped into a single **64b** bank (2 on this example). The blank spaces of the diagram may have any value (now it is 0) as they are masked by mask_o.

### Masked Strided Loads

As defined in the Avispado-VPU interface specs, Masked Strided load are Strided Load where some of the elements are not valid: with a certain EL_COUNT, mask_i[EL_COUNT-1:0] will indicate which ones of the elements are valid. When an element is not valid, it means it has to be not written in the VRF, so, out result will be the following: load_data_o will be as for a normal stride and the mask_o will oscurate the not-valid outputs.

![stridedmask_ex](uploads/de1d52e5501ee6032b8bf9500317686a/stridedmask_ex.jpg)

### Indexed loads

The following example assumes a SEW of 32b, LMUL=1 and an indexed load, the functionality is as follows.

* Indexed
* Virtual register: `A`
* Element ID: `42`
* Element offset: `5`
* Element count: `1`
* Scoreboard ID: `B`

![LMU_indexed](uploads/944df66409d1caccd2f5a5b0fa7ca6e9/LMU_indexed.jpg)

Since it is the case of an indexed load, the offset will indicate us the position of the valid element, **disregarding the stride**. Then, the output of the reversal module is going to be the same as the input. 

Afterwards, the cache line goes through the SHIFTER in order to eliminate the offset, as shown in the example.

Then, since we are only considering a single element, the COMPACTOR module processing will not have effect in the element received, keeping the valid element at the beginning of the cache line.

Finally, the element is aligned by left-shifting the first element to the correct lane and subbank. Also, when there is an Indexed Instruction, there must been mask_valid_i = 0.

### Mask generation

The LMU has to send byte enable signals to the multilane wrapper, so each lane is able to identify if the element received has to be written or not in the Load Buffer. 

A mask array is generated in accordance to the *Element count*. This is done in a per-byte basis, since the smallest SEW is 8b. Then, in case of a mask load operation, an *AND* operation is performed among the input mask and the mask array. Finally, this mask is the one that is sent to the multilane wrapper.

### Element IDs generation

The LMU is also in charge of generating the element ID of each valid element that is sent to the multilane wrapper. So, it is guaranteed that after the reordering of the elements, the element ID (or element IDs) identifying each one of the valid elements to be sent will be properly aligned and sent to the corresponding lane.

### Handshakes

The handshake protocol with the different components is as important as the data manipulation. The following is a simple example with stride equal to 1 and offset = 0 (so, no manipulation on the data in input), also, we don't focus on how long is the vector (VLEN) so the number of elements passed from Avispado is arbitrary fixed.

![load_management_unit](uploads/2e3926ec2bd2899372f3e704754bc2a0/load_management_unit.png)

As it can be observed, the flow is the following :
1.  up to 2 load are granted from the MU with the load_granted_i signal, and the information of sew and stride of the relative inst (identified with load_granted_sb_id_i) are passed.
2.  Avispado sends the data and the seq_id_i with its info ( offset, el_count, sb_id, vreg, el_id )
3. The next clock cycle the data is on the output for the Vector Lane
4. When a load is finished, another Load can be granted.


Testbench
---------

This module can be tested by using a standalone testbench which is located under the **tb/isa_tests/vl*** directory. In this testbench there are tests for all different stride possibilities: -1, -2, -4, 1, 2, 4, and all different SEW (8b, 16b, 32b, 64b). Also it can be stressed with its own UVM with the following command:

`python3 compile_and_sim_unit.py -u load_management_unit -t constrained_test`

Special cases
-------------

- [x] When receiving any other stride than the supported ones, regardless *SEW*, only one valid element per chunk of data is transmitted to the multilane wrapper.



