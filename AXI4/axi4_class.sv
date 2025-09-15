class axi4_class;

  // Write signals
  rand logic [15:0] ADDR;
  rand logic [7:0]  LEN;   
  rand logic [2:0]  SIZE;
  rand logic [31:0] DATA;
  rand logic [1:0]  OPERATION;

  // Random delays for handshaking
  rand  logic [2:0] aw_valid_delay;
  rand  logic [2:0] w_valid_delay; 
  rand  logic [2:0] b_ready_delay;
  rand  logic [2:0] ar_valid_delay;
  rand  logic [2:0] r_ready_delay;

  // Constraints
  constraint OPERATION_C {
  OPERATION inside {[2'd1:2'd2]};
  }

  // Delay constraints
  constraint delay_ranges {
    aw_valid_delay inside {[0:7]};
    w_valid_delay  inside {[0:7]};
    b_ready_delay  inside {[0:7]};
    ar_valid_delay inside {[0:7]};  
    r_ready_delay  inside {[0:7]};
  }

  constraint fix_size {
    SIZE == 2;  // Fixed to 2 (4 bytes)
  }

  constraint aligned_address {
    ADDR[1:0] == 2'b00; // Aligned to 4-byte boundary
  }

  // Valid access constraint 
  constraint valid_range {
    ((ADDR >> 2) + (LEN + 1)) < 1024;  
  }

  // Invalid access constraint s  
  constraint invalid_access_c {
    ((ADDR >> 2) + (LEN + 1)) >= 1024;   
  }

  constraint LEN_range_c {
    LEN inside {[8'd0 : 8'd255]};
  }

  constraint LEN_corners_c {
    LEN inside {8'd0, 8'd1, 8'd127, 8'd128, 8'd254, 8'd255};
  }

  constraint addr_c {
    ADDR inside {[16'd0 : 16'd65535]};
  }

  constraint addr_corner_c {
    ADDR inside {16'd0, 16'd1024, 16'd2048, 16'd4092, 16'b1111_1111_1100}; // All 4-byte aligned
  }


constraint data_c1 {
  DATA inside {
    [32'd0          : 32'd255],
    [32'd256        : 32'd1023],
    [32'd1024       : 32'd4095],
    [32'd4096       : 32'd16383],
    [32'd16384      : 32'd32767]
  };
}

constraint data_c2 {
  DATA inside {
    [32'b0          : 32'b1],
    [32'd32768      : 32'd49151],
    [32'd49152      : 32'd65535],
    [32'd65536      : 32'd262143],
    [32'd262144     : 32'd1048575]
  };
}

constraint data_c3 {
  DATA inside {
    [32'b0          : 32'b1],
    [32'd1048576    : 32'd16777215],
    [32'd16777216   : 32'd268435455],
    [32'd268435456  : 32'd1073741823],
    [32'd1073741824 : 32'hFFFFFFFF]
  };
}

constraint data_corner_c {
  DATA inside {32'd0, 32'd1,  32'hFFFF_FFFF, 32'hAAAA_AAAA, 32'h1111_0000, 32'h0000_1111}; 
}

// Coverage
covergroup axi4_cov;

  // LEN coverage with corner bins
  coverpoint LEN {
    bins corner0   = {8'd0};
    bins corner1   = {8'd1};
    bins corner2   = {8'd127};
    bins corner3   = {8'd128};
    bins corner4   = {8'd254}; 
    bins corner5   = {8'd255};
    bins auto_bins[] = {[8'd0:8'd255]}; 
  }

  // ADDR coverage with corner bins
  coverpoint ADDR {
    bins corner0   = {16'd0};
    bins corner1   = {16'd1024};
    bins corner2   = {16'd2048};
    bins corner3   = {16'd4092};
    bins corner4   = {16'b1111_1111_1100};
    bins range_0   = { [16'd0       : 16'd255]   };
    bins range_1   = { [16'd256     : 16'd1023]  };
    bins range_2   = { [16'd1024    : 16'd4095]  };
    bins range_3   = { [16'd4096    : 16'd16383] };
    bins range_4   = { [16'd16384   : 16'd32767] };
    bins range_5   = { [16'd32768   : 16'd49151] };
    bins range_6   = { [16'd49152   : 16'd65535] };
  }

  // Fixed size coverage
  coverpoint SIZE {
    bins fixed_size = {2};
    illegal_bins others = default;
  }

  // DATA coverage with corner bins
  coverpoint DATA {
    bins corner0       = {32'd0};
    bins corner1       = {32'd1};
    bins corner2       = {32'hFFFF_FFFF};
    bins corner3       = {32'hAAAA_AAAA};
    bins corner4       = {32'h1111_0000}; 
    bins corner5       = {32'h0000_1111};
    bins range_0       = { [32'd0          : 32'd255] };
    bins range_1       = { [32'd256        : 32'd1023] };
    bins range_2       = { [32'd1024       : 32'd4095] };
    bins range_3       = { [32'd4096       : 32'd16383] };
    bins range_4       = { [32'd16384      : 32'd32767] };
    bins range_5       = { [32'd32768      : 32'd49151] };
    bins range_6       = { [32'd49152      : 32'd65535] };
    bins range_7       = { [32'd65536      : 32'd262143] };
    bins range_8       = { [32'd262144     : 32'd1048575] };
    bins range_9       = { [32'd1048576    : 32'd16777215] };
    bins range_10      = { [32'd16777216   : 32'd268435455] };
    bins range_11      = { [32'd268435456  : 32'd1073741823] };
    bins range_12      = { [32'd1073741824 : 32'hFFFFFFFF] };  
    }

  // Memory access bounds coverage
  coverpoint ((ADDR >> 2) + (LEN + 1)) {
    bins valid_access   = {[0:1024]};   // Fits within memory
    bins invalid_access = {[1025:$]};   // Exceeds memory
  }

  // Delay coverage
  coverpoint aw_valid_delay { bins all_values[] = {[0:7]}; }
  coverpoint w_valid_delay  { bins all_values[] = {[0:7]}; }
  coverpoint b_ready_delay  { bins all_values[] = {[0:7]}; }
  coverpoint ar_valid_delay { bins all_values[] = {[0:7]}; }
  coverpoint r_ready_delay  { bins all_values[] = {[0:7]}; }

  // Cross coverage
  cross LEN, ADDR;
  cross DATA, LEN;
  cross DATA, ADDR;
  cross aw_valid_delay, w_valid_delay;
  cross ar_valid_delay, r_ready_delay;

endgroup

  function void display();
    $display("ADDR = %0d, LEN = %0d, SIZE = %0d, Memory Access = %0d", 
            ADDR, LEN, SIZE, ((ADDR >> 2) + (LEN + 1)));
    $display("Delays - AW:%0d, W:%0d, B:%0d, AR:%0d, R:%0d",
            aw_valid_delay, w_valid_delay, b_ready_delay, ar_valid_delay, r_ready_delay);
  endfunction

  function new();
    axi4_cov = new();
  endfunction

endclass