COQPROJECT?=_CoqProject

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: $(COQPROJECT)
	coq_makefile -docroot . -f $(COQPROJECT) -o Makefile.coq


SV2ROCQ_TOOL=../../tools/verilog2rocq.py --prefix Verification.VerilogArithmeticModule
MODULES_DIR=../../modules/verilog_arithmetic_module


verilog2rocq: rca cla
	# Half Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/00_HA/src/rtl/ha.v Adder/HA/ha_gen.v
	
	# Full Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/01_FA/src/rtl/fa.v Adder/FA/fa_gen.v

rca:	
	# Ripple Carry Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl Adder/RCA

cla:	
	# Carry Look-Ahead Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl Adder/CLA

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

