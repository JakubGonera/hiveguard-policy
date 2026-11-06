"""eBPF-specific policy generation.

Uses the domain-agnostic `pdsl` DSL library to build a policy file from the
kernel proto descriptors. The hand-written predicates and built-in op
policies live in `builtins.pol`.
"""
