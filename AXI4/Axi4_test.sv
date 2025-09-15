`timescale 1ns/1ps
`include "axi4_class.sv"
`include "axi4_interface.sv"

module Axi4_test (axi4_interface.tb inter);

  axi4_class stim;
  logic [31:0] golden_mem [0:1023];
  logic [31:0] expected_queue[$];
  logic [31:0] actual_queue[$];
  logic [31:0] data[$];
  logic [1 :0] expected_response;
  logic [1 :0] actual_response;

  int cases = 0;
  int pass  = 0;
  int fail  = 0;
  real cov   = 0;


  bit range_mode [][2] = '{ '{1,0}, '{0,1} };   // valid, invalid range
  bit awlen_modes[][2] = '{ '{1,0}, '{0,1} };   // range, corners
  bit addr_modes [][2] = '{ '{1,0}, '{0,1} };   // range, corners
  bit data_modes [][4] = '{ '{1,0,0,0}, '{0,1,0,0}, '{0,0,1,0}, '{0,0,0,1} };

  initial begin
    stim = new();

    // Initialize golden memory
    for (int i = 0; i < 1024; i++)
      golden_mem[i] = 0;

    actual_queue.delete();
    expected_queue.delete();
    data.delete();
    reset();

    stim.delay_ranges.constraint_mode(1);
    stim.fix_size.constraint_mode(1);
    stim.aligned_address.constraint_mode(1);

    foreach (range_mode[m]) begin
    foreach (awlen_modes[i]) begin
    foreach (addr_modes[j]) begin
      foreach (data_modes[k]) begin

        stim.valid_range.constraint_mode(range_mode[m][0]);
        stim.invalid_access_c.constraint_mode(range_mode[m][1]);

        stim.LEN_range_c.constraint_mode(awlen_modes[i][0]);
        stim.LEN_corners_c.constraint_mode(awlen_modes[i][1]);

        stim.addr_c.constraint_mode(addr_modes[j][0]);
        stim.addr_corner_c.constraint_mode(addr_modes[j][1]);

        stim.data_c1.constraint_mode(data_modes[k][0]);
        stim.data_c2.constraint_mode(data_modes[k][1]);
        stim.data_c3.constraint_mode(data_modes[k][2]);
        stim.data_corner_c.constraint_mode(data_modes[k][3]);

        repeat (5100) begin
          cases++;
          clear_signals();
          generate_stimulus();
          golden_model();
          drive();
        end
      end
    end
    end
    end 

    cov = stim.axi4_cov.get_coverage();
    $display("=== Final Results ===");
    $display("Number of tests: %0d, Passed: %0d, Failed: %0d", cases, pass, fail);
    $display("Coverage achieved: %0.1f%%", cov);

    #200;
    $stop;
  end

  task reset();
    begin
      inter.ARESETn = 1'b1;
      @(negedge inter.ACLK);
      inter.ARESETn = 1'b0;
      @(negedge inter.ACLK);
      inter.ARESETn = 1'b1;
      @(negedge inter.ACLK);
    end
  endtask

  task clear_signals();
    inter.AWVALID = 0;
    inter.WVALID  = 0;
    inter.WLAST   = 0;
    inter.BREADY  = 0;
    inter.ARVALID = 0;
    inter.RREADY  = 0;
    inter.AWADDR  = 0;
    inter.AWLEN   = 0; 
    inter.AWSIZE  = 0;
    inter.WDATA   = 0;
    inter.ARADDR  = 0;
    inter.ARLEN   = 0; 
    inter.ARSIZE  = 0;
    expected_response = 2'b0;
    actual_response   = 2'b0;
    @(negedge inter.ACLK);
  endtask

  task generate_stimulus();
    data.delete();  
    stim.LEN     = 0;
    stim.ADDR    = 0;
    stim.SIZE    = 0;
    stim.DATA     = 0;
    stim.OPERATION = 0;
    stim.aw_valid_delay = 0;
    stim.w_valid_delay  = 0;
    stim.b_ready_delay  = 0;
    stim.ar_valid_delay = 0;
    stim.r_ready_delay  = 0; 

    assert(stim.randomize(ADDR, LEN, SIZE, OPERATION, aw_valid_delay, w_valid_delay,
          b_ready_delay, ar_valid_delay, r_ready_delay ))
      else $fatal("Address/Length/Operation randomization failed");
    
    if (stim.OPERATION == 2'd1) 
    begin
      for (int i = 0; i <= stim.LEN; i++) 
      begin  
        assert(stim.randomize(DATA))
          else $fatal("Data randomization failed for beat %0d", i);
        data[i] = stim.DATA;
        stim.axi4_cov.sample();
      end
    end
  endtask

  task golden_model();
    expected_queue.delete();
    if (((stim.ADDR >> stim.SIZE) + (stim.LEN + 1)) >= 1024) 
    begin
        expected_response = 2'b10;
    end else
    begin
      expected_response = 2'b00;
      if (stim.OPERATION == 2'd1) 
      begin
        for (int i = 0; i <= stim.LEN; i++) 
        begin
        golden_mem[(stim.ADDR >> 2) + i] = data[i];  
        end
      end else if (stim.OPERATION == 2'd2) 
      begin
        for (int i = 0; i <= stim.LEN; i++) 
        begin
        expected_queue[i] = golden_mem[(stim.ADDR >> 2) + i];  
        end
      end
    end
  endtask

  task drive();
    if (stim.OPERATION == 2'd2) 
    begin
      // Apply delay before starting read address phase
      repeat (stim.ar_valid_delay) @(negedge inter.ACLK);

      // Set up read address channel
      inter.ARADDR  = stim.ADDR;
      inter.ARLEN   = stim.LEN;
      inter.ARSIZE  = stim.SIZE;
      inter.ARVALID = 1'b1;

      // Wait for address acceptance
      repeat (20) @(negedge inter.ACLK)
        if (inter.ARREADY) break;
      inter.ARVALID = 0;

      collect();
    end else if (stim.OPERATION == 2'd1) 
    begin
        // Apply delay before starting write address phase
        repeat (stim.aw_valid_delay) @(negedge inter.ACLK);
        // Start write address transaction

        inter.AWADDR  = stim.ADDR;
        inter.AWLEN   = stim.LEN;
        inter.AWSIZE  = stim.SIZE;
        inter.AWVALID = 1'b1;

        // Wait for address acceptance
        repeat (20) @(negedge inter.ACLK)
          if (inter.AWREADY) break;
        inter.AWVALID = 1'b0;


        if (((stim.ADDR >> stim.SIZE) + (stim.LEN + 1)) >= 1024)  
        begin
            $display("TIME: $0t", $time);
            assert(stim.randomize(w_valid_delay))
              else $fatal("w_valid_delay randomization failed");
            repeat (stim.w_valid_delay) @(negedge inter.ACLK);
            stim.axi4_cov.sample();
            inter.WVALID = 1'b1;
            inter.WLAST  = 1;
            //@(negedge inter.ACLK);
            
            // Wait for write data acceptance
            repeat (20) @(negedge inter.ACLK)
            if (inter.WREADY) break;
            
            actual_response = inter.BRESP;
            inter.WVALID = 1'b0;
            inter.WLAST  = 0;

            // Apply delay before accepting write response
            repeat (stim.b_ready_delay) @(negedge inter.ACLK);
            inter.BREADY = 1'b1;
            repeat (20) @(negedge inter.ACLK)
            if (inter.BVALID) break;
            inter.BREADY = 0;
        end else
        begin

        // Apply delay before starting write data phase
        repeat (stim.w_valid_delay) @(negedge inter.ACLK);

        // Send burst data with proper handshaking
        for (int i = 0; i <= stim.LEN; i++) 
        begin
          inter.WDATA  = data[i];
          inter.WVALID = 1'b1;
          inter.WLAST  = (i == stim.LEN);
          
          // Wait for write data acceptance
          repeat (20) @(negedge inter.ACLK)
            if (inter.WREADY) break;
            
          inter.WVALID = 1'b0;
          // Generate random delay for each write data beat
          assert(stim.randomize(w_valid_delay)) 
            else $fatal("w_valid_delay randomization failed");
          repeat (stim.w_valid_delay) @(negedge inter.ACLK);
          stim.axi4_cov.sample();
        end
        actual_response = inter.BRESP;
        inter.WLAST  = 0;

        // Apply delay before accepting write response
        repeat (stim.b_ready_delay) @(negedge inter.ACLK);
        inter.BREADY = 1'b1;

        // Wait for write response
        repeat (20) @(negedge inter.ACLK)
          if (inter.BVALID) break;

        inter.BREADY = 0;
      end
      check();
    end
  endtask

  task collect();
      actual_queue.delete();
      // Start with RREADY high, then apply delay by temporarily deasserting
      inter.RREADY = 1'b1;
      
      for (int i = 0; i <= stim.LEN; i++) 
      begin
        // Apply r_ready_delay for each read beat
        if (stim.r_ready_delay > 0) 
        begin
          inter.RREADY = 1'b0;
          repeat (stim.r_ready_delay) @(negedge inter.ACLK);
          inter.RREADY = 1'b1;
        end

        // Generate random delay for each read beat
        assert(stim.randomize(r_ready_delay)) 
          else $fatal("r_ready_delay randomization failed");
        stim.axi4_cov.sample();

        if (i == stim.LEN && !inter.RLAST) begin
          $warning("RLAST not asserted on final beat");
        end

        // Wait for valid read data
        repeat (20) @(negedge inter.ACLK)
          if (inter.RVALID) break;

        actual_queue.push_back(inter.RDATA);
      end
      actual_response = inter.RRESP;
      inter.RREADY = 1'b0;
      check();
  endtask 

  task check();
    if (stim.OPERATION == 2'd1) 
    begin
      $display("Test %0d", cases);
      $display("Write Test");
      stim.display();

      if (actual_response == expected_response)
      begin
        pass++;
        $display("Test %0d PASSED", cases);
        $display("write Operation passed");
      end else
      begin
        fail++;
        $display("Test %0d FAILED Resopnse mismatch", cases);
        $display("write Operation failed");
      end
 
    end else
      if (stim.OPERATION == 2'd2) 
      begin
        $display("Test %0d", cases);
        $display("Read Test");
        stim.display();

        if (((stim.ADDR >> stim.SIZE) + (stim.LEN + 1)) >= 1024)    
        begin
            if (actual_response == expected_response) 
            begin
              pass++;
              $display("Test %0d PASSED", cases);
              $display("Read Operation passed");
              $display("Expected response: %2b, Actual response: %2b",
                       expected_response, actual_response);
            end else
            begin
              fail++;
              $display("Test %0d FAILED - Data|Resopnse mismatch", cases);
              $display("Read Operation failed");
              $display("Expected response: %2b, Actual response: %2b",
                       expected_response, actual_response);
            end
            $display("");
            return;
        end else
        begin

          if (actual_queue.size() != expected_queue.size()) 
          begin
          fail++;
          $display("Test %0d FAILED - Queue size mismatch", cases);
          $display("Read Operation failed");
          $display("Expected size: %0d, Actual size: %0d", 
                   expected_queue.size(), actual_queue.size());
          $display("");
          return;
          end

          if ((actual_queue == expected_queue) && (actual_response == expected_response)) 
          begin
            pass++;
            $display("Test %0d PASSED", cases);
            $display("Read Operation passed");
            $display("Expected response: %2b, Actual response: %2b",
                     expected_response, actual_response);

          end else 
          begin
            fail++;
            $display("Test %0d FAILED - Data|Resopnse mismatch", cases);
            $display("Read Operation failed");
            $display("Expected response: %2b, Actual response: %2b",
                     expected_response, actual_response);

            if (actual_response != expected_response) 
            begin
              $display("Expected response: %2b, Actual response: %2b",
                       expected_response, actual_response);
            end

            for (int i = 0; i < expected_queue.size(); i++) 
            begin
              if (expected_queue[i] != actual_queue[i]) 
              begin
                $display("  Beat[%0d]: Expected = %h, Actual = %h", 
                         i, expected_queue[i], actual_queue[i]);
              end
            end
        end
      end
    end
     $display("");
  endtask
endmodule


