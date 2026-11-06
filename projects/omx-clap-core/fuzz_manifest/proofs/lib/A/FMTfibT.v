(* The ASan side of fuzz_manifest's asan_agrees and asan_halts, as one statement: every run of fm.asan from a
   valid entry on a valid input, at the target budget, realizes the trace set SPECX of fm's plain proof, without
   cuts (YK18.srealizes). The library shape is checksum_shape (ZTraceSpec.v): LLVMFuzzerTestOneInput returns 0,
   writes nothing and leaves the file system as it was. fm's plain side realizes SPECX at ag_shape checksum_shape,
   which has the same LIBK. The composition (FMTop.v) proves Statements.asan_agrees and Statements.asan_halts
   from TFIB_T; the relocated ASan core proves TFIB_T. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
#[local] Existing Instance YK11.fx0.

Definition tfibsegs0 : list Segment := Asan.M.loaded_segments.

Definition TFIB_T : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk tfibsegs0 brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    srealizes tfibsegs0
      (init_config tfibsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (SPECX (LS:=checksum_shape) inp).
