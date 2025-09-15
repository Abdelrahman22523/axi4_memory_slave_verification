vlib work

vlog *.*v +cover -covercells

for {set i 0} {$i < 5} {incr i} {
    set seed [expr {int(rand() * 1000000)}]
    set ucdb_file "cov_run${i}.ucdb"
    
    puts "Running simulation $i with random seed: $seed"
    
    if {$i < 4} {
        vsim -voptargs=+acc work.top -coverage +ntb_random_seed=$seed -do "
            coverage save -onexit -du work.axi4 $ucdb_file
            add wave -radix hex /top/dut/*
            run -all
            quit -sim
        "
    } else {
        # For the last run, don't quit the simulation
        vsim -voptargs=+acc work.top -coverage +ntb_random_seed=$seed -do "
            coverage save -onexit -du work.axi4 $ucdb_file
            add wave -radix hex /top/dut/*
            run -all
        "
    }
}

vcover merge merged_cov.ucdb cov_run*.ucdb

vcover report merged_cov.ucdb -details -output cov_report.txt
vcover report merged_cov.ucdb -details -html -output cov_report
