SIM ?= icarus
TOPLEVEL_LANG ?= verilog

VERILOG_SOURCES += $(PWD)/register_file.v

# TOPLEVEL is the name of the toplevel module in your Verilog or VHDL file
TOPLEVEL = $(DUT)

# MODULE is the basename of the Python test file
MODULE = $(DUT)_tb

# include cocotb's make rules to take care of the simulator setup
include $(shell cocotb-config --makefiles)/Makefile.sim
