interface axi4_interface (input bit ACLK);
	// axi4 signals
	bit        		ARESETn;
    logic        	AWVALID;
	logic        	AWREADY;
	logic        	WLAST;
	logic        	RLAST;
	logic        	WVALID;
	logic        	WREADY;
	logic        	RVALID;
	logic        	RREADY;
	logic        	ARREADY;
	logic        	ARVALID;
	logic        	BVALID;
	logic        	BREADY;
    logic [15:0]  	AWADDR;
    logic [7:0]     AWLEN;
    logic [2:0]     AWSIZE;
    logic [31:0]    WDATA;
	logic [15:0]    ARADDR;
	logic [31:0]    RDATA;
	logic [7:0]     ARLEN;
    logic [2:0]     ARSIZE;
	logic [1:0]     RRESP;
	logic [1:0]     BRESP;


	modport dut (
        input  	ACLK,
		input   ARESETn,

		// Write address channel
		input  	AWADDR,
		input  	AWLEN,
		input  	AWSIZE,
		input  	AWVALID,
		output 	AWREADY,

		// Write data channel
		input  	WDATA,
		input 	WVALID,
		input  	WLAST,
		output 	WREADY,

		// Write response channel
		output 	BRESP,
		output 	BVALID,
		input  	BREADY,

		// Read address channel
		input  	ARADDR,
		input  	ARLEN,
		input  	ARSIZE,
		input  	ARVALID,
		output 	ARREADY,

		// Read data channel
		output 	RDATA,
		output 	RRESP,
		output 	RVALID,
		output 	RLAST,
		input   RREADY
    );
	

    modport tb (
        input 	ACLK,
		output  ARESETn,

		// Write address channel
		output 	AWADDR,
		output 	AWLEN,
		output 	AWSIZE,
		output 	AWVALID,
		input  	AWREADY,

		// Write data channel
		output 	WDATA,
		output 	WVALID,
		output 	WLAST,
		input  	WREADY,

		// Write response channel
		input  	BRESP,
		input  	BVALID,
		output 	BREADY,

		// Read address channel
		output 	ARADDR,
		output 	ARLEN,
		output 	ARSIZE,
		output 	ARVALID,
		input  	ARREADY,

		// Read data channel
		input  	RDATA,
		input  	RRESP,
		input  	RVALID,
		input  	RLAST,
		output  RREADY
    );


endinterface