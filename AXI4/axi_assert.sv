module axi4_assert (axi4_interface.dut inter);
  
  // All outputs should be properly initialized after reset
  property reset_awready;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.AWREADY == 1'b1;
  endproperty
  A_RESET_AWREADY: assert property (reset_awready) 
    else $error("AWREADY not initialized to 1 after reset");
  C_RESET_AWREADY: cover property (reset_awready);

  property reset_wready;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.WREADY == 1'b0;
  endproperty
  A_RESET_WREADY: assert property (reset_wready)
    else $error("WREADY not initialized to 0 after reset");
  C_RESET_WREADY: cover property (reset_wready);

  property reset_bvalid;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.BVALID == 1'b0;
  endproperty
  A_RESET_BVALID: assert property (reset_bvalid)
    else $error("BVALID not initialized to 0 after reset");
  C_RESET_BVALID: cover property (reset_bvalid);

  property reset_arready;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.ARREADY == 1'b1;
  endproperty
  A_RESET_ARREADY: assert property (reset_arready)
    else $error("ARREADY not initialized to 1 after reset");
  C_RESET_ARREADY: cover property (reset_arready);

  property reset_rvalid;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.RVALID == 1'b0;
  endproperty
  A_RESET_RVALID: assert property (reset_rvalid)
    else $error("RVALID not initialized to 0 after reset");
  C_RESET_RVALID: cover property (reset_rvalid);

  property reset_rlast;
    @(posedge inter.ACLK) !inter.ARESETn |-> inter.RLAST == 1'b0;
  endproperty
  A_RESET_RLAST: assert property (reset_rlast)
    else $error("RLAST not initialized to 0 after reset");
  C_RESET_RLAST: cover property (reset_rlast);


  // AWREADY should go low after accepting address
  property awready_deassert;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.AWVALID && inter.AWREADY) |=> !inter.AWREADY;
  endproperty
  A_AWREADY_DEASSERT: assert property (awready_deassert)
    else $error("AWREADY should deassert after address handshake");
  C_AWREADY_DEASSERT: cover property (awready_deassert);

  // Address signals should remain stable when AWVALID is high
  property awaddr_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.AWVALID && !inter.AWREADY |=> $stable(inter.AWADDR);
  endproperty
  A_AWADDR_STABLE: assert property (awaddr_stable)
    else $error("AWADDR must remain stable when AWVALID is high");
  C_AWADDR_STABLE: cover property (awaddr_stable);

  property awlen_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.AWVALID && !inter.AWREADY |=> $stable(inter.AWLEN);
  endproperty
  A_AWLEN_STABLE: assert property (awlen_stable)
    else $error("AWLEN must remain stable when AWVALID is high");
  C_AWLEN_STABLE: cover property (awlen_stable);

  property awsize_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.AWVALID && !inter.AWREADY |=> $stable(inter.AWSIZE);
  endproperty
  A_AWSIZE_STABLE: assert property (awsize_stable)
    else $error("AWSIZE must remain stable when AWVALID is high");
  C_AWSIZE_STABLE: cover property (awsize_stable);


  // WDATA should remain stable when WVALID is high
  property wdata_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.WVALID && !inter.WREADY |=> $stable(inter.WDATA);
  endproperty
  A_WDATA_STABLE: assert property (wdata_stable)
    else $error("WDATA must remain stable when WVALID is high");
  C_WDATA_STABLE: cover property (wdata_stable);

  // WLAST should be asserted on the last data beat
  property wlast_on_last_beat;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.WVALID && inter.WREADY && inter.WLAST) |=> !inter.WREADY;
  endproperty
  A_WLAST_LAST_BEAT: assert property (wlast_on_last_beat)
    else $error("WREADY should deassert after WLAST");
  C_WLAST_LAST_BEAT: cover property (wlast_on_last_beat);

  // Write response must come after write data completion
  property write_order;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    $rose(inter.BVALID) |-> $past(inter.WVALID && inter.WREADY && inter.WLAST);
  endproperty
  A_WRITE_ORDER_DATA_RESP: assert property (write_order)
    else $error("Write response cannot start without data completion");
  C_WRITE_ORDER_DATA_RESP: cover property (write_order);

  // BVALID should be asserted after write data completion
  property bvalid_after_wlast;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.WVALID && inter.WREADY && inter.WLAST) |=> inter.BVALID;
  endproperty
  A_BVALID_AFTER_WLAST: assert property (bvalid_after_wlast)
    else $error("BVALID should be asserted after WLAST handshake");
  C_BVALID_AFTER_WLAST: cover property (bvalid_after_wlast);

  // BVALID should remain stable until BREADY
  property bvalid_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.BVALID && !inter.BREADY |=> inter.BVALID;
  endproperty
  A_BVALID_STABLE: assert property (bvalid_stable)
    else $error("BVALID must remain stable until handshake");
  C_BVALID_STABLE: cover property (bvalid_stable);

  // BRESP should remain stable when BVALID is high
  property bresp_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.BVALID && !inter.BREADY |=> $stable(inter.BRESP);
  endproperty
  A_BRESP_STABLE: assert property (bresp_stable)
    else $error("BRESP must remain stable when BVALID is high");
  C_BRESP_STABLE: cover property (bresp_stable);

  // BVALID should deassert after handshake
  property bvalid_deassert;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.BVALID && inter.BREADY) |=> !inter.BVALID;
  endproperty
  A_BVALID_DEASSERT: assert property (bvalid_deassert)
    else $error("BVALID should deassert after response handshake");
  C_BVALID_DEASSERT: cover property (bvalid_deassert);

  // ARREADY should go low after accepting address
  property arready_deassert;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.ARVALID && inter.ARREADY) |=> !inter.ARREADY;
  endproperty
  A_ARREADY_DEASSERT: assert property (arready_deassert)
    else $error("ARREADY should deassert after address handshake");
  C_ARREADY_DEASSERT: cover property (arready_deassert);

  // Read address signals should remain stable when ARVALID is high
  property araddr_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.ARVALID && !inter.ARREADY |=> $stable(inter.ARADDR);
  endproperty
  A_ARADDR_STABLE: assert property (araddr_stable)
    else $error("ARADDR must remain stable when ARVALID is high");
  C_ARADDR_STABLE: cover property (araddr_stable);

  property arlen_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.ARVALID && !inter.ARREADY |=> $stable(inter.ARLEN);
  endproperty
  A_ARLEN_STABLE: assert property (arlen_stable)
    else $error("ARLEN must remain stable when ARVALID is high");
  C_ARLEN_STABLE: cover property (arlen_stable);

  property arsize_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.ARVALID && !inter.ARREADY |=> $stable(inter.ARSIZE);
  endproperty
  A_ARSIZE_STABLE: assert property (arsize_stable)
    else $error("ARSIZE must remain stable when ARVALID is high");
  C_ARSIZE_STABLE: cover property (arsize_stable);


  // RVALID should be asserted after read address
  property rvalid_after_araddr;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.ARVALID && inter.ARREADY) |-> ##[1:3] inter.RVALID;
  endproperty
  A_RVALID_AFTER_ARADDR: assert property (rvalid_after_araddr)
    else $error("RVALID should be asserted within 3 cycles after read address");
  C_RVALID_AFTER_ARADDR: cover property (rvalid_after_araddr);

  // RVALID should remain stable until RREADY
  property rvalid_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.RVALID && !inter.RREADY |=> inter.RVALID;
  endproperty
  A_RVALID_STABLE: assert property (rvalid_stable)
    else $error("RVALID must remain stable until handshake");
  C_RVALID_STABLE: cover property (rvalid_stable);

  // RRESP should remain stable when RVALID is high
  property rresp_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.RVALID && !inter.RREADY |=> $stable(inter.RRESP);
  endproperty
  A_RRESP_STABLE: assert property (rresp_stable)
    else $error("RRESP must remain stable when RVALID is high");
  C_RRESP_STABLE: cover property (rresp_stable);

  // RLAST should remain stable when RVALID is high
  property rlast_stable;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.RVALID && !inter.RREADY |=> $stable(inter.RLAST);
  endproperty
  A_RLAST_STABLE: assert property (rlast_stable)
    else $error("RLAST must remain stable when RVALID is high");
  C_RLAST_STABLE: cover property (rlast_stable);

  // BRESP should be OKAY (00) or SLVERR (10)
  property bresp_valid_values;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.BVALID |-> (inter.BRESP == 2'b00 || inter.BRESP == 2'b10);
  endproperty
  A_BRESP_VALID_VALUES: assert property (bresp_valid_values)
    else $error("Invalid BRESP value: %b", inter.BRESP);
  C_BRESP_VALID_VALUES: cover property (bresp_valid_values);

  // RRESP should be OKAY (00) or SLVERR (10)
  property rresp_valid_values;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    inter.RVALID |-> (inter.RRESP == 2'b00 || inter.RRESP == 2'b10);
  endproperty
  A_RRESP_VALID_VALUES: assert property (rresp_valid_values)
    else $error("Invalid RRESP value: %b", inter.RRESP);
  C_RRESP_VALID_VALUES: cover property (rresp_valid_values);

  // 4KB boundary crossing should result in SLVERR for write
  property write_boundary;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.BVALID && 
     (((inter.AWADDR & 16'h0FFF) + ((inter.AWLEN + 1) << inter.AWSIZE)) > 16'h0FFF))
    |-> inter.BRESP == 2'b10;
  endproperty
  A_WRITE_BOUNDARY_ERROR: assert property (write_boundary)
    else $error("4KB boundary crossing should result in SLVERR");
  C_WRITE_BOUNDARY_ERROR: cover property (write_boundary);

  // Out of memory range should result in SLVERR for write
  property write_range;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.BVALID && ((inter.AWADDR >> 2) >= 1024))
    |-> inter.BRESP == 2'b10;
  endproperty
  A_WRITE_RANGE_ERROR: assert property (write_range)
    else $error("Out of range write should result in SLVERR");
  C_WRITE_RANGE_ERROR: cover property (write_range);

  // 4KB boundary crossing should result in SLVERR for read
  property read_boundary;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.RVALID && 
     (((inter.ARADDR & 16'h0FFF) + ((inter.ARLEN + 1) << inter.ARSIZE)) > 16'h0FFF))
    |-> inter.RRESP == 2'b10;
  endproperty
  A_READ_BOUNDARY_ERROR: assert property (read_boundary)
    else $error("4KB boundary crossing should result in SLVERR for read");
  C_READ_BOUNDARY_ERROR: cover property (read_boundary);

  // Out of memory range should result in SLVERR for read
  property read_range;
    @(posedge inter.ACLK) disable iff (!inter.ARESETn)
    (inter.RVALID && ((inter.ARADDR >> 2) >= 1024))
    |-> inter.RRESP == 2'b10;
  endproperty
  A_READ_RANGE_ERROR: assert property (read_range)
    else $error("Out of range read should result in SLVERR");
  C_READ_RANGE_ERROR: cover property (read_range);

endmodule