onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/inter/ACLK
add wave -noupdate /top/inter/WVALID
add wave -noupdate /top/inter/WREADY
add wave -noupdate /top/inter/WDATA
add wave -noupdate /top/inter/RVALID
add wave -noupdate /top/inter/RRESP
add wave -noupdate /top/inter/RREADY
add wave -noupdate /top/inter/RLAST
add wave -noupdate /top/inter/RDATA
add wave -noupdate /top/inter/BVALID
add wave -noupdate /top/inter/BREADY
add wave -noupdate /top/inter/AWVALID
add wave -noupdate /top/inter/AWSIZE
add wave -noupdate /top/inter/AWREADY
add wave -noupdate /top/inter/AWLEN
add wave -noupdate /top/inter/AWADDR
add wave -noupdate /top/inter/ARVALID
add wave -noupdate /top/inter/ARSIZE
add wave -noupdate /top/inter/ARREADY
add wave -noupdate /top/inter/ARLEN
add wave -noupdate /top/inter/ARESETn
add wave -noupdate /top/inter/ARADDR
add wave -noupdate /top/tb/cases
add wave -noupdate /top/tb/expected_response
add wave -noupdate /top/tb/actual_response
add wave -noupdate /top/tb/stim
add wave -noupdate /top/tb/golden_mem
add wave -noupdate /top/tb/pass
add wave -noupdate /top/tb/cov
add wave -noupdate /top/dut/DATA_WIDTH
add wave -noupdate /top/dut/ADDR_WIDTH
add wave -noupdate /top/dut/MEMORY_DEPTH
add wave -noupdate /top/dut/W_IDLE
add wave -noupdate /top/dut/W_ADDR
add wave -noupdate /top/dut/W_DATA
add wave -noupdate /top/dut/W_RESP
add wave -noupdate /top/dut/R_IDLE
add wave -noupdate /top/dut/R_ADDR
add wave -noupdate /top/dut/R_DATA
add wave -noupdate /top/dut/mem_en
add wave -noupdate /top/dut/mem_we
add wave -noupdate /top/dut/mem_addr
add wave -noupdate /top/dut/mem_wdata
add wave -noupdate /top/dut/mem_rdata
add wave -noupdate /top/dut/write_addr
add wave -noupdate /top/dut/read_addr
add wave -noupdate /top/dut/write_burst_len
add wave -noupdate /top/dut/read_burst_len
add wave -noupdate /top/dut/write_burst_cnt
add wave -noupdate /top/dut/read_burst_cnt
add wave -noupdate /top/dut/write_size
add wave -noupdate /top/dut/read_size
add wave -noupdate /top/dut/write_addr_incr
add wave -noupdate /top/dut/read_addr_incr
add wave -noupdate /top/dut/read_boundary_cross
add wave -noupdate /top/dut/read_addr_valid
add wave -noupdate -radix unsigned /top/tb/cases
add wave -noupdate -radix unsigned /top/tb/fail
add wave -noupdate /top/tb/expected_response
add wave -noupdate /top/tb/actual_response
add wave -noupdate /top/dut/write_addr_valid
add wave -noupdate /top/dut/write_boundary_cross
add wave -noupdate /top/inter/WLAST
add wave -noupdate /top/inter/BRESP
add wave -noupdate /top/dut/write_state
add wave -noupdate /top/dut/read_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {478400230 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {463126113 ps} {479526249 ps}
