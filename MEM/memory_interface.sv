interface memory_interface (input bit ACLK);

	//memory signals

	logic           ARESETn;
	logic           mem_en;
    logic           mem_we;
    logic [9:0]     mem_addr;
    logic [31:0]    mem_wdata;
    logic [31:0]    mem_rdata;

	modport dut (
        input  	ACLK,
		input   ARESETn,
		input 	mem_en,
		input 	mem_we,
		input 	mem_addr,
		input 	mem_wdata,
		output 	mem_rdata
    );

	modport tb (
        input  	ACLK,
		output  ARESETn,
		output 	mem_en,
		output 	mem_we,
		output 	mem_addr,
		output 	mem_wdata,
		input 	mem_rdata
    );


endinterface