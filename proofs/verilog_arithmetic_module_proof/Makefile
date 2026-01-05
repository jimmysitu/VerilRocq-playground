COQPROJECT?=_CoqProject

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: $(COQPROJECT)
	coq_makefile -docroot . -f $(COQPROJECT) -o Makefile.coq


SV2ROCQ_TOOL=../../tools/verilog2rocq.py --prefix Verification.VerilogArithmeticModule
MODULES_DIR=../../modules/verilog_arithmetic_module


verilog2rocq:
	# Half Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/00_HA/src/rtl/ha.v Adder/HA/ha_gen.v
	
	# Full Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/01_FA/src/rtl/fa.v Adder/FA/fa_gen.v
	
	# Ripple Carry Adder
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl/fa.v Adder/RCA/fa_gen.v
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl/rca_04.v Adder/RCA/rca_04_gen.v
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl/rca_08.v Adder/RCA/rca_08_gen.v
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl/rca_16.v Adder/RCA/rca_16_gen.v
	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/02_RCA/src/rtl/rca_32.v Adder/RCA/rca_32_gen.v
	
#	# Carry Look-Ahead Adder
#	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl/fa.v Adder/CLA/fa_gen.v
#	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl/cla_04.v Adder/CLA/cla_04_gen.v
#	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl/cla_08.v Adder/CLA/cla_08_gen.v
#	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl/cla_16.v Adder/CLA/cla_16_gen.v
#	$(SV2ROCQ_TOOL) $(MODULES_DIR)/Adder/03_CLA/src/rtl/cla_32.v Adder/CLA/cla_32_gen.v


clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

