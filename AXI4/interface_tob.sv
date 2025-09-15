`include "axi4_interface.sv"
`include "Axi4_test.sv"
`include "axi4.sv"
module top();

  // axi4 signals
  
  bit             ARESETn;
  logic           AWVALID;
  logic           AWREADY;
  logic           WLAST;
  logic           RLAST;
  logic           WVALID;
  logic           WREADY;
  logic           RVALID;
  logic           RREADY;
  logic           ARREADY;
  logic           ARVALID;
  logic           BVALID;
  logic           BREADY;
  logic [15:0]    AWADDR;
  logic [7:0]     AWLEN;
  logic [2:0]     AWSIZE;
  logic [31:0]    WDATA;
  logic [31:0]    ARADDR;
  logic [31:0]    RDATA;
  logic [7:0]     ARLEN;
  logic [2:0]     ARSIZE;
  logic [1:0]     RRESP;
  logic [1:0]     BRESP;


  bit ACLK ;
  initial begin
	ACLK = 0;
	forever begin
	  #5ns ACLK = ~ACLK;
	end	
  end
  
  axi4_interface inter (ACLK);
  axi4 			     dut   (inter.dut);
  Axi4_test	     tb 	 (inter.tb);
  axi4_assert    check (inter.dut);
  
endmodule  
  
  
  
  
