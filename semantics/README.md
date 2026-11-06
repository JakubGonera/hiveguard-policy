# Overview
This directory contains the Rocq formalisation of local soundness theorem(s) for the instruction handling by abstract interpretation used in Rust verifier (main source in `bpf_verifier/core/src/verifier/transfer.rs`). The basis of the formalisation is the eBPF small-step semantic developed by Yaun et.al. (2026) which in turn uses CompCert memory model to describe the memory state of an eBPF configuration. The architecture of the proof is as follows:

- `AbstractDomain.v` contains transcription of structures describing abstract state in Rust implementation.
- `Concretization.v` defines the concretization relation. This relates abstract states that can be used in our verifier with concrete configurations, that is register states and memory contents, that are used to interpret an instruction in the concrete small-step semantics.
- `IRLevelAssms.v` collects the assumptions relating the Rust IR (built from user-level bytecode) to the kernel bytecode executed by the semantics: SSA freshness and instruction lowering.
- `CompCertAssms.v` collects the premises where CompCert's semantics is undefined and the hardware's is not.
- `Transfer.v, Common.v` and instruction specific files contain the Rocq definitions of the transfer functions (abstract operators) mirroring the Rust source, the statements of the soundness theorems for each transfer function, and associated lemmas and proofs.
- `GlobalSoundness.v` is the entry point: it states and proves soundness for whole programs and lists every assumption the result depends on.

On the high level, local soundness for us means "for any abstract state that a transfer function admits and any concrete state that concretizes it, a single small-step interpretation exists and its result concretizes the abstract state that results from the transfer function". `GlobalSoundness.v` chains these: a program the verifier accepts runs from any initial state its entry invariant describes without getting stuck before exit, and every state it reaches is described by an abstract state the verifier reached.

# Running Rocq
From a fresh checkout, run these commands at the repository root:

```sh
nix develop .#semantics
just semantics-build
just semantics-check
```

The lightweight `semantics` shell supplies Rocq 9.1, its matching standard
library, CompCert 3.18, and the build tools. `flake.lock` pins the package set
and the flake pins the CompCert source hash. Proof dependencies are opt-in:
the default `nix develop` shell and automatic directory-entry environment
(`direnv`) do not include or build Rocq/CompCert. Use `nix develop .#semantics`
(or `just semantics-shell`) only when working on these proofs.
The first invocation of the semantics shell may take time to download and
compile dependencies.

`just semantics-build` initializes the pinned
[`linux-ebpf-semantics`](https://github.com/OpenSourceVerif/linux-ebpf-semantics)
submodule in this directory, compiles its reusable theories with the same
toolchain, and then compiles our theories into `semantics/build/`.
`just semantics-check` also independently checks all compiled theories
with `coqchk`.

For a single theory, or when working without `just`, use:

```sh
git submodule update --init -- semantics/linux-ebpf-semantics
make -C semantics -j2
make -C semantics build/MemoryStoreImm.vo
coqchk -silent \
  -R semantics/linux-ebpf-semantics/theories bpf.semantics \
  -Q semantics/build TrustNoBPF.Semantics \
  TrustNoBPF.Semantics.MemoryStoreImm
```

To run without entering an interactive shell:

```sh
nix develop .#semantics -c just semantics-check
```

## Without Nix (opam)

Install the same toolchain (Rocq 9.1, CompCert 3.18) into a dedicated opam switch:

```sh
opam switch create trustnobpf-semantics ocaml-base-compiler.5.2.1
eval $(opam env --switch=trustnobpf-semantics)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.9.1.0 coq-compcert.3.18
```

`coq.9.1.0` is the compatibility package that pulls in `rocq-prover` and
`rocq-stdlib` and provides the `coqc`, `coq_makefile` and `coqchk` binaries
the Makefile expects. Then, from the repository root:

```sh
git submodule update --init -- semantics/linux-ebpf-semantics
make -C semantics -j2         # build
make -C semantics check       # build + coqchk
```

The tool paths can be overridden with `COQC=`, `COQMAKEFILE=` and `COQCHK=`
on the `make` command line.