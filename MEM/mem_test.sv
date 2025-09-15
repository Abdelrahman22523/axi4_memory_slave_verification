`timescale 1ns/1ps
`include "memory_class.sv"

module mem_test (memory_interface.tb inter);
  memory_class stim;
  logic [31:0] golden_mem [0:1023];
  logic [31:0] actual_data;
  logic [31:0] expected_data;
  int cases = 0;
  int pass  = 0;
  int fail  = 0;
  int cov   = 0;
  
  initial begin
    // Initialize interface signals
    inter.mem_en     = 0;
    inter.mem_we     = 0;
    inter.mem_addr   = 0;
    inter.mem_wdata  = 0;
    inter.ARESETn    = 0;
    cases            = 0;
    
    // Create stimulus object
    stim = new();
    
    // Initialize golden memory
    for (int i = 0; i < 1024; i++)
      golden_mem[i] = 0;
    
    // Reset sequence
    repeat (2) @(posedge inter.ACLK);
    inter.ARESETn = 1;
    repeat (2) @(posedge inter.ACLK); // Allow reset to complete
    
    
    stim.addr_c.constraint_mode(1);
    stim.addr_corner_c.constraint_mode(0);
    stim.data_c1.constraint_mode(1);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end
    
    stim.addr_c.constraint_mode(1);
    stim.addr_corner_c.constraint_mode(0);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(1);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end
    
    stim.addr_c.constraint_mode(1);
    stim.addr_corner_c.constraint_mode(0);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(1);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end
    
    stim.addr_c.constraint_mode(1);
    stim.addr_corner_c.constraint_mode(0);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(1);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end

    stim.addr_c.constraint_mode(0);
    stim.addr_corner_c.constraint_mode(1);
    stim.data_c1.constraint_mode(1);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end

    stim.addr_c.constraint_mode(0);
    stim.addr_corner_c.constraint_mode(1);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(1);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end

    stim.addr_c.constraint_mode(0);
    stim.addr_corner_c.constraint_mode(1);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(1);
    stim.data_corner_c.constraint_mode(0);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end


    stim.addr_c.constraint_mode(0);
    stim.addr_corner_c.constraint_mode(1);
    stim.data_c1.constraint_mode(0);
    stim.data_c2.constraint_mode(0);
    stim.data_c3.constraint_mode(0);
    stim.data_corner_c.constraint_mode(1);
    repeat (10000) begin 
    cases++;
    generate_stimulus();
    golden_model();
    drive();
    collect();
    check();
    end


    cov = stim.Memory_cov.get_coverage();
    $display("=== Final Results ===");
    $display("Number of tests: %0d, Passed: %0d, Failed: %0d", cases, pass, fail);
    $display("Coverage achieved: %0d%%", cov);
    
    #200;
    $finish; 
  end
  

  
  task generate_stimulus();
    if (!stim.randomize()) begin
      $display("ERROR: Randomization failed at test case %0d", cases);
      $finish;
    end
  endtask
  
  task golden_model();
    if (stim.mem_en) begin
      if (stim.mem_we) begin
        // Write operation
        golden_mem[stim.mem_addr] = stim.mem_wdata;
        expected_data = 'x; // Don't expect read data on write
      end else begin
        // Read operation
        expected_data = golden_mem[stim.mem_addr];
      end
    end else begin
      // Memory disabled
      expected_data = 'x;
    end
  endtask

  
  task drive();
    // Drive stimulus to interface
    inter.mem_en    = stim.mem_en;
    inter.mem_we    = stim.mem_we;
    inter.mem_addr  = stim.mem_addr;
    inter.mem_wdata = stim.mem_wdata;
    
    // Sample coverage for stimulus
    stim.Memory_cov.sample();
    
    @(posedge inter.ACLK);
  endtask


  
  task collect();

    if (stim.mem_en && !stim.mem_we) 
    begin
      @(posedge inter.ACLK);
      actual_data = inter.mem_rdata;
    end else 
    begin
      actual_data = 'x;
    end
  endtask
  

  task check();
    if (stim.mem_en && !stim.mem_we) 
    begin
      if (actual_data !== expected_data) 
      begin
        $display("FAIL [%0d]: Addr=0x%03x, Expected=0x%08x, Got=0x%08x", 
                cases, stim.mem_addr, expected_data, actual_data);
        fail++;
      end else 
      begin
        pass++;
          $display("PASS [%0d]: Addr=0x%03x, Data=0x%08x", 
                  cases, stim.mem_addr, actual_data);
      end
    end else if (stim.mem_en && stim.mem_we) 
    begin
        $display("WRITE [%0d]: Addr=0x%03x, Data=0x%08x", 
                cases, stim.mem_addr, stim.mem_wdata);
    end
    $display("");
  endtask

  
endmodule