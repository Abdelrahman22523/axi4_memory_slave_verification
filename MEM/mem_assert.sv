module mem_assert (memory_interface.dut inter);

    // Property 1: Write operations 
    property Write_prop;
        @(posedge inter.ACLK)
        disable iff (!inter.ARESETn)
        inter.mem_we |-> inter.mem_en;  // If mem_we is 1 , mem_en is must be 1
    endproperty

    A1: assert property (Write_prop)
        else $error("Write operation failed");
    C1: cover property (Write_prop);

    // Property 2: Read operation 
    property Read_prop;
        @(posedge inter.ACLK)
        disable iff (!inter.ARESETn)
        (inter.mem_en && !inter.mem_we) |=> !$isunknown(inter.mem_rdata);
    endproperty

    A2: assert property (Read_prop)
        else $error("Read operation failed");
    C2: cover property (Read_prop);

    // Property 3: Write enable 
    property enable_check;
        @(posedge inter.ACLK)
        disable iff (!inter.ARESETn)
        !inter.mem_en |-> !inter.mem_we;
    endproperty

    A3: assert property (enable_check)
        else $error("mem_we asserted when mem_en is low");
    C3: cover property (enable_check);

    // Property 4: Reset 
    property reset_prop;
        @(posedge inter.ACLK)
        !inter.ARESETn |=> (inter.mem_rdata == 0);
    endproperty

    A4: assert property (reset_prop)
        else $error("Reset protocol failed");
    C4: cover property (reset_prop);

    // Property 5: Memory operations
    property stable_signals;
        @(posedge inter.ACLK)
        disable iff (!inter.ARESETn)
        inter.mem_en |-> (inter.mem_we == 1'b0 || inter.mem_we == 1'b1); 
    endproperty

    A5: assert property (stable_signals)
        else $error("Invalid control signal values");
    C5: cover property (stable_signals);

    // Property 6: Address should be within valid range
    property valid_address;
        @(posedge inter.ACLK)
        disable iff (!inter.ARESETn)
        inter.mem_en |-> (inter.mem_addr < 1024);
    endproperty

    A6: assert property (valid_address)
        else $error("Invalid address");
    C6: cover property (valid_address);

endmodule