`include "memory_interface.sv"
`include "mem_test.sv"
`include "axi_memory.sv"
module top();

  //memory signals

  logic           mem_en;
  logic           mem_we;
  logic [9:0]     mem_addr;
  logic [31:0]    mem_wdata;
  logic [31:0]    mem_rdata;

  logic ACLK;
  initial begin
	ACLK = 0;
	forever begin
	  #5ns ACLK = ~ACLK;
	end	
  end
  
  memory_interface  inter  (ACLK);
  axi4_memory       dut    (inter.dut);
  mem_test          tb     (inter.tb);
  mem_assert        check  (inter.dut);
  
endmodule  
  
  
  
  
