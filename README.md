# axi4_memory_slave_verification
This project implements a custom SystemVerilog verification environment (without UVM) for a simplified AXI4 memory-mapped slave design.
The testbench models and verifies burst read/write transactions, address decoding, 4KB boundary compliance, and error response handling.

Key Features:
Direct SystemVerilog classes and interfaces for transaction-level modeling
Constrained-random stimulus for AXI4 protocol signals
Functional coverage to measure protocol feature exploration
Assertion-based verification for VALID/READY handshake compliance
Memory model with 4KB boundary enforcement
Simulation logs, waveforms, and coverage reports for validation results
The goal is to achieve 100% functional coverage, code coverage, and assertion coverage (with justified exclusions).
