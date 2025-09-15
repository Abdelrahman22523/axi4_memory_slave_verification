module axi4 #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    axi4_interface.dut inter
);

    // Internal memory signals
    reg mem_en, mem_we;
    reg [$clog2(MEMORY_DEPTH)-1:0] mem_addr;
    reg [DATA_WIDTH-1:0] mem_wdata;
    wire [DATA_WIDTH-1:0] mem_rdata;

    // Address and burst management
    reg [ADDR_WIDTH-1:0] write_addr, read_addr;
    reg [7:0] write_burst_len, read_burst_len;
    reg [7:0] write_burst_cnt, read_burst_cnt;
    reg [2:0] write_size, read_size;

    wire [ADDR_WIDTH-1:0] write_addr_incr, read_addr_incr;

    // Address increment calculation
    assign write_addr_incr = (1 << write_size);
    assign read_addr_incr  = (1 << read_size);

    // Address boundary check (4KB boundary = 12 bits)
    wire write_boundary_cross = ((inter.AWADDR & 12'hFFF) + ((inter.AWLEN + 1) << inter.AWSIZE)) > 12'hFFF;
    wire read_boundary_cross  = ((inter.ARADDR & 12'hFFF) + ((inter.ARLEN + 1) << inter.ARSIZE)) > 12'hFFF;

    // Address range check
    wire write_addr_valid = (write_addr >> 2) < MEMORY_DEPTH;
    wire read_addr_valid  = (read_addr >> 2) < MEMORY_DEPTH;

    // Memory instance
    axi4_memory #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH($clog2(MEMORY_DEPTH)),
        .DEPTH(MEMORY_DEPTH)
    ) mem_inst (
        .clk(inter.ACLK),
        .rst_n(inter.ARESETn),
        .mem_en(mem_en),
        .mem_we(mem_we),
        .mem_addr(mem_addr),
        .mem_wdata(mem_wdata),
        .mem_rdata(mem_rdata)
    );

    // FSM states
    reg [2:0] write_state;
    localparam W_IDLE = 3'd0,
               W_ADDR = 3'd1,
               W_DATA = 3'd2,
               W_RESP = 3'd3;

    reg [2:0] read_state;
    localparam R_IDLE = 3'd0,
               R_ADDR = 3'd1,
               R_DATA = 3'd2;

    always @(posedge inter.ACLK or negedge inter.ARESETn) begin
        if (!inter.ARESETn) begin
            // Reset all outputs
            inter.AWREADY <= 1'b1;
            inter.WREADY  <= 1'b0;
            inter.BVALID  <= 1'b0;
            inter.BRESP   <= 2'b00;

            inter.ARREADY <= 1'b1;
            inter.RVALID  <= 1'b0;
            inter.RRESP   <= 2'b00;
            inter.RDATA   <= {DATA_WIDTH{1'b0}};
            inter.RLAST   <= 1'b0;

            // Internal reset
            write_state <= W_IDLE;
            read_state  <= R_IDLE;

            mem_en      <= 1'b0;
            mem_we      <= 1'b0;
            mem_addr    <= {$clog2(MEMORY_DEPTH){1'b0}};
            mem_wdata   <= {DATA_WIDTH{1'b0}};

            write_addr        <= {ADDR_WIDTH{1'b0}};
            write_burst_len   <= 8'b0;
            write_burst_cnt   <= 8'b0;
            write_size        <= 3'b0;

            read_addr         <= {ADDR_WIDTH{1'b0}};
            read_burst_len    <= 8'b0;
            read_burst_cnt    <= 8'b0;
            read_size         <= 3'b0;

        end else begin
            // Default disables
            mem_en <= 1'b0;
            mem_we <= 1'b0;

            // ------------------------------------
            // Write Channel FSM
            // ------------------------------------
            case (write_state)
                W_IDLE: begin
                    inter.AWREADY <= 1'b1;
                    inter.WREADY  <= 1'b0;
                    inter.BVALID  <= 1'b0;

                    if (inter.AWVALID && inter.AWREADY) begin
                        write_addr      <= inter.AWADDR;
                        write_burst_len <= inter.AWLEN;
                        write_burst_cnt <= inter.AWLEN;
                        write_size      <= inter.AWSIZE;

                        inter.AWREADY   <= 1'b0;
                        write_state     <= W_ADDR;
                    end
                end

                W_ADDR: begin
                    inter.WREADY  <= 1'b1;
                    write_state   <= W_DATA;
                end

                W_DATA: begin
                    if (inter.WVALID && inter.WREADY) begin
                        if (write_addr_valid && !write_boundary_cross) begin
                            mem_en    <= 1'b1;
                            mem_we    <= 1'b1;
                            mem_addr  <= write_addr >> 2;
                            mem_wdata <= inter.WDATA;
                        end

                        if (inter.WLAST || write_burst_cnt == 0) begin

                            inter.WREADY <= 1'b0;
                            write_state  <= W_RESP;
                            inter.BRESP  <= (!write_addr_valid || write_boundary_cross) ? 2'b10 : 2'b00;
                            inter.BVALID <= 1'b1;

                        end else begin
                            write_addr     <= write_addr + write_addr_incr;
                            write_burst_cnt <= write_burst_cnt - 1'b1;
                        end
                    end
                end

                W_RESP: begin
                    if (inter.BREADY && inter.BVALID) begin
                        inter.BVALID  <= 1'b0;
                        inter.BRESP   <= 2'b00;
                        write_state   <= W_IDLE;
                    end
                end

                default: write_state <= W_IDLE;
            endcase

            // ------------------------------------
            // Read Channel FSM
            // ------------------------------------
            case (read_state)
                R_IDLE: begin
                    inter.ARREADY <= 1'b1;
                    inter.RVALID  <= 1'b0;
                    inter.RLAST   <= 1'b0;

                    if (inter.ARVALID && inter.ARREADY) begin
                        read_addr      <= inter.ARADDR;
                        read_burst_len <= inter.ARLEN;
                        read_burst_cnt <= inter.ARLEN;
                        read_size      <= inter.ARSIZE;

                        inter.ARREADY  <= 1'b0;
                        read_state     <= R_ADDR;
                    end
                end

                R_ADDR: begin
                    if (read_addr_valid && !read_boundary_cross) begin
                        mem_en    <= 1'b1;
                        mem_addr  <= read_addr >> 2;
                    end
                    read_state <= R_DATA;
                end

                R_DATA: begin
                    if (read_addr_valid && !read_boundary_cross) begin
                        inter.RDATA <= mem_rdata;
                        inter.RRESP <= 2'b00;
                    end else begin
                        inter.RDATA <= {DATA_WIDTH{1'b0}};
                        inter.RRESP <= 2'b10;
                    end

                    inter.RVALID <= 1'b1;
                    inter.RLAST  <= (read_burst_cnt == 0);

                    if (inter.RREADY && inter.RVALID) begin
                        inter.RVALID <= 1'b0;

                        if (read_burst_cnt > 0) begin
                            read_addr      <= read_addr + read_addr_incr;
                            read_burst_cnt <= read_burst_cnt - 1'b1;

                            if (read_addr_valid && !read_boundary_cross) begin
                                mem_en   <= 1'b1;
                                mem_addr <= (read_addr + read_addr_incr) >> 2;
                            end
                        end else begin
                            inter.RLAST  <= 1'b0;
                            read_state   <= R_IDLE;
                        end
                    end
                end

                default: read_state <= R_IDLE;
            endcase
        end
    end

endmodule
