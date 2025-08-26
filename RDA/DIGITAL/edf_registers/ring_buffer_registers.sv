/* ###   interfaces   ###################################################### */

// BUF_VALID_COUNT
interface ring_buffer_registers_BUF_VALID_COUNT_if;
  logic[15:0] value;
  logic[11:0] VALID_COUNT, VALID_COUNT_in;

  modport master (
    input VALID_COUNT_in, 
    output value, VALID_COUNT
  );

  modport slave (
    input value, VALID_COUNT, 
    output VALID_COUNT_in
  );

endinterface : ring_buffer_registers_BUF_VALID_COUNT_if

// BUF_FREE
interface ring_buffer_registers_BUF_FREE_if;
  logic[15:0] value;
  logic[15:0] FREE, FREE_in;

  modport master (
    input FREE_in, 
    output value, FREE
  );

  modport slave (
    input value, FREE, 
    output FREE_in
  );

endinterface : ring_buffer_registers_BUF_FREE_if

// BUF_READ_POINTER
interface ring_buffer_registers_BUF_READ_POINTER_if;
  logic[15:0] value;
  logic[15:0] READ_POINTER, READ_POINTER_in;

  modport master (
    input READ_POINTER_in, 
    output value, READ_POINTER
  );

  modport slave (
    input value, READ_POINTER, 
    output READ_POINTER_in
  );

endinterface : ring_buffer_registers_BUF_READ_POINTER_if

// BUF_WRITE_POINTER
interface ring_buffer_registers_BUF_WRITE_POINTER_if;
  logic[15:0] value;
  logic[15:0] WRITE_POINTER, WRITE_POINTER_in;

  modport master (
    input WRITE_POINTER_in, 
    output value, WRITE_POINTER
  );

  modport slave (
    input value, WRITE_POINTER, 
    output WRITE_POINTER_in
  );

endinterface : ring_buffer_registers_BUF_WRITE_POINTER_if

// BUF_VALID_POINTER
interface ring_buffer_registers_BUF_VALID_POINTER_if;
  logic[15:0] value;
  logic[15:0] VALID_POINTER, VALID_POINTER_in;

  modport master (
    input VALID_POINTER_in, 
    output value, VALID_POINTER
  );

  modport slave (
    input value, VALID_POINTER, 
    output VALID_POINTER_in
  );

endinterface : ring_buffer_registers_BUF_VALID_POINTER_if



/*###   BUF_VALID_COUNT   ######################################################*/
module ring_buffer_registers_BUF_VALID_COUNT #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   ring_buffer_registers_BUF_VALID_COUNT_if.master ring_buffer_registers_BUF_VALID_COUNT);

   // BUF_VALID_COUNT : VALID_COUNT
   logic[11:0]  VALID_COUNT;


   always_comb begin
       VALID_COUNT = ring_buffer_registers_BUF_VALID_COUNT.VALID_COUNT_in;
   end

   assign ring_buffer_registers_BUF_VALID_COUNT.VALID_COUNT = VALID_COUNT;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {4'd0, VALID_COUNT} : '0;

   assign ring_buffer_registers_BUF_VALID_COUNT.value = {4'd0, VALID_COUNT};

endmodule : ring_buffer_registers_BUF_VALID_COUNT

/*###   BUF_FREE   ######################################################*/
module ring_buffer_registers_BUF_FREE #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   ring_buffer_registers_BUF_FREE_if.master ring_buffer_registers_BUF_FREE);

   // BUF_FREE : FREE
   logic[15:0]  FREE;


   always_comb begin
       FREE = ring_buffer_registers_BUF_FREE.FREE_in;
   end

   assign ring_buffer_registers_BUF_FREE.FREE = FREE;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {FREE} : '0;

   assign ring_buffer_registers_BUF_FREE.value = {FREE};

endmodule : ring_buffer_registers_BUF_FREE

/*###   BUF_READ_POINTER   ######################################################*/
module ring_buffer_registers_BUF_READ_POINTER #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   ring_buffer_registers_BUF_READ_POINTER_if.master ring_buffer_registers_BUF_READ_POINTER);

   // BUF_READ_POINTER : READ_POINTER
   logic[15:0]  READ_POINTER;


   always_comb begin
       READ_POINTER = ring_buffer_registers_BUF_READ_POINTER.READ_POINTER_in;
   end

   assign ring_buffer_registers_BUF_READ_POINTER.READ_POINTER = READ_POINTER;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {READ_POINTER} : '0;

   assign ring_buffer_registers_BUF_READ_POINTER.value = {READ_POINTER};

endmodule : ring_buffer_registers_BUF_READ_POINTER

/*###   BUF_WRITE_POINTER   ######################################################*/
module ring_buffer_registers_BUF_WRITE_POINTER #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   ring_buffer_registers_BUF_WRITE_POINTER_if.master ring_buffer_registers_BUF_WRITE_POINTER);

   // BUF_WRITE_POINTER : WRITE_POINTER
   logic[15:0]  WRITE_POINTER;


   always_comb begin
       WRITE_POINTER = ring_buffer_registers_BUF_WRITE_POINTER.WRITE_POINTER_in;
   end

   assign ring_buffer_registers_BUF_WRITE_POINTER.WRITE_POINTER = WRITE_POINTER;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {WRITE_POINTER} : '0;

   assign ring_buffer_registers_BUF_WRITE_POINTER.value = {WRITE_POINTER};

endmodule : ring_buffer_registers_BUF_WRITE_POINTER

/*###   BUF_VALID_POINTER   ######################################################*/
module ring_buffer_registers_BUF_VALID_POINTER #(
       parameter reg_addr=0,
       parameter addr_width=8
) (
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   ring_buffer_registers_BUF_VALID_POINTER_if.master ring_buffer_registers_BUF_VALID_POINTER);

   // BUF_VALID_POINTER : VALID_POINTER
   logic[15:0]  VALID_POINTER;


   always_comb begin
       VALID_POINTER = ring_buffer_registers_BUF_VALID_POINTER.VALID_POINTER_in;
   end

   assign ring_buffer_registers_BUF_VALID_POINTER.VALID_POINTER = VALID_POINTER;

   assign data_out = (reg_addr[addr_width-1:0] == addr && rd == 1'b1) ? {VALID_POINTER} : '0;

   assign ring_buffer_registers_BUF_VALID_POINTER.value = {VALID_POINTER};

endmodule : ring_buffer_registers_BUF_VALID_POINTER

/*###   Registers   ######################################################*/
module ring_buffer_registers #(
       parameter base_addr=0,
       parameter addr_width=8
) (
   clk_reset_if.slave clk_rst,
   input logic[addr_width-1:0] addr,
   input logic           rd,
   output logic[15:0]     data_out,
   // register interfaces
   ring_buffer_registers_BUF_VALID_COUNT_if.master ring_buffer_registers_BUF_VALID_COUNT,
   ring_buffer_registers_BUF_FREE_if.master ring_buffer_registers_BUF_FREE,
   ring_buffer_registers_BUF_READ_POINTER_if.master ring_buffer_registers_BUF_READ_POINTER,
   ring_buffer_registers_BUF_WRITE_POINTER_if.master ring_buffer_registers_BUF_WRITE_POINTER,
   ring_buffer_registers_BUF_VALID_POINTER_if.master ring_buffer_registers_BUF_VALID_POINTER
);

   logic[15:0] data_out_BUF_VALID_COUNT, data_out_BUF_FREE, data_out_BUF_READ_POINTER, data_out_BUF_WRITE_POINTER, data_out_BUF_VALID_POINTER;

   ring_buffer_registers_BUF_VALID_COUNT #( .reg_addr (base_addr + 'h0), .addr_width(addr_width) ) i_ring_buffer_registers_BUF_VALID_COUNT ( .data_out (data_out_BUF_VALID_COUNT), .*);
   ring_buffer_registers_BUF_FREE #( .reg_addr (base_addr + 'h2), .addr_width(addr_width) ) i_ring_buffer_registers_BUF_FREE ( .data_out (data_out_BUF_FREE), .*);
   ring_buffer_registers_BUF_READ_POINTER #( .reg_addr (base_addr + 'h8), .addr_width(addr_width) ) i_ring_buffer_registers_BUF_READ_POINTER ( .data_out (data_out_BUF_READ_POINTER), .*);
   ring_buffer_registers_BUF_WRITE_POINTER #( .reg_addr (base_addr + 'h9), .addr_width(addr_width) ) i_ring_buffer_registers_BUF_WRITE_POINTER ( .data_out (data_out_BUF_WRITE_POINTER), .*);
   ring_buffer_registers_BUF_VALID_POINTER #( .reg_addr (base_addr + 'ha), .addr_width(addr_width) ) i_ring_buffer_registers_BUF_VALID_POINTER ( .data_out (data_out_BUF_VALID_POINTER), .*);

   // output data assignment
   assign data_out = data_out_BUF_VALID_COUNT | data_out_BUF_FREE | data_out_BUF_READ_POINTER | data_out_BUF_WRITE_POINTER | data_out_BUF_VALID_POINTER;

endmodule : ring_buffer_registers
