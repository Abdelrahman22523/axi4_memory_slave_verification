module axi4_memory #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 10,    // For 1024 locations
    parameter DEPTH = 1024
)(
    memory_interface.dut inter // modport of the interface
);

    // Memory array
    reg [DATA_WIDTH-1:0] memory [0:DEPTH-1];
    
    integer j;

    // Memory write and read logic
    always @(posedge inter.ACLK) begin
        if (!inter.ARESETn)
            inter.mem_rdata <= 0;
        else if (inter.mem_en) begin
            if (inter.mem_we)
                memory[inter.mem_addr] <= inter.mem_wdata;
            else
                inter.mem_rdata <= memory[inter.mem_addr];
        end
    end        

    // Initialize memory
    initial begin
        for (j = 0; j < DEPTH; j = j + 1)
            memory[j] = 0;
    end

endmodule
