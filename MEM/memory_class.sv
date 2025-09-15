class memory_class;
    // Memory signals
    rand logic        mem_en;
    rand logic        mem_we;
    rand logic [9:0]  mem_addr;
    rand logic [31:0] mem_wdata;

    // Constraint for memory enable
    constraint mem_en_const {
        mem_en dist {0 := 1, 1 := 9};
    }

    // Constraint for memory write enable
    constraint mem_we_const {
        if (mem_en)
            mem_we dist {0 := 6, 1 := 4};  // 0 = read, 1 = write
        else
            mem_we == 0;
    }
  
    // Address distribution constraint
    constraint addr_c {
        mem_addr inside {[10'd0 : 10'd1023]};
        };

    // Address corner case constraint
    constraint addr_corner_c {
        mem_addr inside {10'd0, 10'd1, 10'd7, 10'd15, 10'd31, 10'd63, 10'd127, 10'd255, 10'd511,
                        10'd1023, 10'b1010101010, 10'b0101010101, 10'b1111111111,10'b1111100000,
                        10'b0000011111};
    }


     constraint data_c1 {
      mem_wdata inside {
        [32'd0          : 32'd255],
        [32'd256        : 32'd1023],
        [32'd1024       : 32'd4095],
        [32'd4096       : 32'd16383],
        [32'd16384      : 32'd32767]
      };
    }

    constraint data_c2 {
      mem_wdata inside {
        [32'b0          : 32'b1],
        [32'd32768      : 32'd49151],
        [32'd49152      : 32'd65535],
        [32'd65536      : 32'd262143],
        [32'd262144     : 32'd1048575]
      };
    }

    constraint data_c3 {
      mem_wdata inside {
        [32'b0          : 32'b1],
        [32'd1048576    : 32'd16777215],
        [32'd16777216   : 32'd268435455],
        [32'd268435456  : 32'd1073741823],
        [32'd1073741824 : 32'hFFFFFFFF]
      };
    }

      constraint data_corner_c {
        mem_wdata inside {32'd0, 32'd1, 32'd7, 32'd15, 32'd31, 32'd63, 32'd127, 32'd255, 32'd511, 
                         32'd1023, 32'hFFFF_FFFF, 32'hAAAA_AAAA, 32'h5555_5555, 32'h1111_0000,
                         32'h0000_1111}; // Fixed: removed invalid constant
      }
      
        // Coverage group
    covergroup Memory_cov;
        option.per_instance = 1;

        mem_en_cp : coverpoint mem_en {
            bins disabled = {0};
            bins enabled  = {1};
        }

        mem_we_cp : coverpoint mem_we iff (mem_en) {
            bins read_op  = {0};
            bins write_op = {1};
        }

        mem_addr_cp : coverpoint mem_addr iff (mem_en) {
            bins corners[] = {10'd0, 10'd1, 10'd7, 10'd15, 10'd31, 10'd63, 10'd127, 10'd255,
                             10'd511, 10'd1023, 10'b1010101010, 10'b0101010101, 10'b1111111111,
                             10'b1111100000, 10'b0000011111};

            bins all_values[] = {[10'd0 : 10'd1023]};
        }

        mem_wdata_cp : coverpoint mem_wdata iff (mem_en && mem_we) {
            bins corners[] = {32'd0, 32'd1, 32'd7, 32'd15, 32'd31, 32'd63, 32'd127, 32'd255,
                             32'd511, 32'd1023, 32'hFFFF_FFFF, 32'hAAAA_AAAA, 32'h5555_5555,
                             32'h1111_0000, 32'h0000_1111};

            bins grp1_1 = {[32'd0          : 32'd255]};
            bins grp1_2 = {[32'd256        : 32'd1023]};
            bins grp1_3 = {[32'd1024       : 32'd4095]};
            bins grp1_4 = {[32'd4096       : 32'd16383]};
            bins grp1_5 = {[32'd16384      : 32'd32767]};

            bins grp2_1 = {[32'd32768      : 32'd49151]};
            bins grp2_2 = {[32'd49152      : 32'd65535]};
            bins grp2_3 = {[32'd65536      : 32'd262143]};
            bins grp2_4 = {[32'd262144     : 32'd1048575]};

            bins grp3_1 = {[32'd1048576    : 32'd16777215]};
            bins grp3_2 = {[32'd16777216   : 32'd268435455]};
            bins grp3_3 = {[32'd268435456  : 32'd1073741823]};
            bins grp3_4 = {[32'd1073741824 : 32'hFFFFFFFF]};
        }

    endgroup
    // Constructor
    function new();
        Memory_cov = new();
    endfunction

    // Post-randomize function with better formatting
    function void display();
        $display(">> post_randomize: en=%b, we=%b, addr=0x%03x(%0d), wdata=0x%08x", 
                mem_en, mem_we, mem_addr, mem_addr, mem_wdata);
    endfunction 
endclass