EBPF_SEMANTICS_DIR ?= linux-ebpf-semantics
BUILD_DIR := build
COQC ?= coqc
COQMAKEFILE ?= coq_makefile
COQCHK ?= coqchk
COQ_LOADPATH := \
	-R $(EBPF_SEMANTICS_DIR)/theories bpf.semantics \
	-Q $(BUILD_DIR) TrustNoBPF.Semantics
COQFLAGS := -q $(COQ_LOADPATH)

VOFILES := \
	$(BUILD_DIR)/AbstractDomain.vo \
	$(BUILD_DIR)/Concretization.vo \
	$(BUILD_DIR)/Transfer.vo \
	$(BUILD_DIR)/CompCertAssms.vo \
	$(BUILD_DIR)/KernelAssms.vo \
	$(BUILD_DIR)/IRLevelAssms.vo \
	$(BUILD_DIR)/Common.vo \
	$(BUILD_DIR)/MemoryLoad.vo \
	$(BUILD_DIR)/MemoryStoreImm.vo \
	$(BUILD_DIR)/MemoryStoreReg.vo \
	$(BUILD_DIR)/ArithmeticHelpers.vo \
	$(BUILD_DIR)/Arithmetic.vo \
	$(BUILD_DIR)/ControlFlow.vo \
	$(BUILD_DIR)/Calls.vo \
	$(BUILD_DIR)/GlobalSoundness.vo

.PHONY: all upstream check clean

ifeq ($(UPSTREAM_READY),1)
all: $(VOFILES)
else
# Re-enter make after the upstream build so dependency timestamps are fresh,
# including on the first build where no upstream .vo files existed yet.
all: upstream
	$(MAKE) UPSTREAM_READY=1 all

$(VOFILES): upstream
	$(MAKE) UPSTREAM_READY=1 $@
endif

# Build only the reusable theories; the upstream trace validator is separate.
# Run its dependency check on every invocation so upstream edits are noticed.
upstream:
	@test -f $(EBPF_SEMANTICS_DIR)/Makefile || { \
		echo "Missing eBPF semantics. Run: git submodule update --init semantics/linux-ebpf-semantics" >&2; exit 1; }
	$(MAKE) -C $(EBPF_SEMANTICS_DIR) CoqMakefile COQMAKEFILE="$(COQMAKEFILE)"
	$(MAKE) -C $(EBPF_SEMANTICS_DIR) -f CoqMakefile theories/ebpfBinSem.vo COQC="$(COQC)"

# Upstream .vo changes must invalidate our proofs as well.
ifeq ($(UPSTREAM_READY),1)
UPSTREAM_VOFILES := $(wildcard $(EBPF_SEMANTICS_DIR)/theories/*.vo)
$(VOFILES): $(UPSTREAM_VOFILES)
endif

check: all
	$(COQCHK) -silent $(COQ_LOADPATH) $(patsubst $(BUILD_DIR)/%.vo,TrustNoBPF.Semantics.%,$(VOFILES))

$(BUILD_DIR):
	mkdir -p $@

ifeq ($(UPSTREAM_READY),1)
$(BUILD_DIR)/AbstractDomain.vo: AbstractDomain.v | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.AbstractDomain -o $@ $<

$(BUILD_DIR)/Concretization.vo: Concretization.v $(BUILD_DIR)/AbstractDomain.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.Concretization -o $@ $<

$(BUILD_DIR)/Transfer.vo: Transfer.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.Transfer -o $@ $<

$(BUILD_DIR)/CompCertAssms.vo: CompCertAssms.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo $(BUILD_DIR)/Transfer.vo $(BUILD_DIR)/ArithmeticHelpers.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.CompCertAssms -o $@ $<

$(BUILD_DIR)/KernelAssms.vo: KernelAssms.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo $(BUILD_DIR)/Transfer.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.KernelAssms -o $@ $<

$(BUILD_DIR)/IRLevelAssms.vo: IRLevelAssms.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo $(BUILD_DIR)/Transfer.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.IRLevelAssms -o $@ $<

$(BUILD_DIR)/Common.vo: Common.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo $(BUILD_DIR)/Transfer.vo $(BUILD_DIR)/IRLevelAssms.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.Common -o $@ $<

$(BUILD_DIR)/MemoryLoad.vo: MemoryLoad.v $(BUILD_DIR)/AbstractDomain.vo $(BUILD_DIR)/Concretization.vo $(BUILD_DIR)/Transfer.vo $(BUILD_DIR)/CompCertAssms.vo $(BUILD_DIR)/KernelAssms.vo $(BUILD_DIR)/Common.vo $(BUILD_DIR)/Arithmetic.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.MemoryLoad -o $@ $<

$(BUILD_DIR)/MemoryStoreImm.vo: MemoryStoreImm.v $(BUILD_DIR)/Common.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.MemoryStoreImm -o $@ $<

$(BUILD_DIR)/MemoryStoreReg.vo: MemoryStoreReg.v $(BUILD_DIR)/Common.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.MemoryStoreReg -o $@ $<

$(BUILD_DIR)/ArithmeticHelpers.vo: ArithmeticHelpers.v $(BUILD_DIR)/Common.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.ArithmeticHelpers -o $@ $<

$(BUILD_DIR)/Arithmetic.vo: Arithmetic.v $(BUILD_DIR)/CompCertAssms.vo $(BUILD_DIR)/ArithmeticHelpers.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.Arithmetic -o $@ $<

$(BUILD_DIR)/ControlFlow.vo: ControlFlow.v $(BUILD_DIR)/CompCertAssms.vo $(BUILD_DIR)/Common.vo $(BUILD_DIR)/ArithmeticHelpers.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.ControlFlow -o $@ $<

$(BUILD_DIR)/Calls.vo: Calls.v $(BUILD_DIR)/Common.vo $(BUILD_DIR)/ArithmeticHelpers.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.Calls -o $@ $<

$(BUILD_DIR)/GlobalSoundness.vo: GlobalSoundness.v $(BUILD_DIR)/CompCertAssms.vo $(BUILD_DIR)/KernelAssms.vo $(BUILD_DIR)/IRLevelAssms.vo $(BUILD_DIR)/Arithmetic.vo $(BUILD_DIR)/MemoryLoad.vo $(BUILD_DIR)/MemoryStoreImm.vo $(BUILD_DIR)/MemoryStoreReg.vo $(BUILD_DIR)/ControlFlow.vo | $(BUILD_DIR)
	$(COQC) $(COQFLAGS) -top TrustNoBPF.Semantics.GlobalSoundness -o $@ $<
endif
clean:
	rm -rf $(BUILD_DIR)
	@if test -f $(EBPF_SEMANTICS_DIR)/CoqMakefile; then \
		$(MAKE) -C $(EBPF_SEMANTICS_DIR) -f CoqMakefile clean; fi
