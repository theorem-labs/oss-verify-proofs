(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v:19-26, by way of proofs/libreac/fuzz_grant/lib/A/GrantTFIB.v (cold/port-grant 0bed23e5b69), for fuzz_preset's asan image: TFIB_T takes any trace set whose exits are 0 or 2, which is all that halts_budgets_of_srealizes (Reusable/HaltsKitB.v) asks; cgif's form, with the trace set SPECX at fuzz_preset's checksum_shape (lib/ZTraceSpec.v), is TFIB_T_specx and gives TFIB_T; module paths changed. *)
(* What the ASan side of fuzz_preset's asan_halts must prove (lib/A/AsanTop.v takes TFIB_T as its one hypothesis):
   from every valid start, the asan build at the 512 GiB limit realizes, with no cut (lib/Reusable/YK18.v srealizes),
   some trace set in which every exit has status 0 or 2 and no trace is killed by a signal.

   The class-full arm is reachable. TFIB_T has the five entry premises of the cgif form and nothing else: no bound on
   live bytes or event counts (the kind of cgif_file lib/YCfn.v:21-22, :38, which lives in cgif's proof of TFIB_T,
   tfib_lib_pre_x, not in TFIB_T), and no allocator regime, budget meter or mapped-bytes-per-class bound (the kind of
   cgif_rgb lib/YG01.v:200, :272 and YG0d.v:227, :233). srealizes needs every successor of every step covered
   (srz_node, node_ok), so a proof of TFIB_T must walk the branch where a size class of the runtime's primary allocator
   is full and the allocation returns 0 (allocator_may_return_null = 1), into the harness's refusal path, which ends
   in exit 0. TFIB_T asks only that every exit be 0 or 2. So a full class is an exit question here, not a trace
   question. TFIB_T_specx asks more, the trace set SPECX, and still admits the refusal path, because the harness
   call returns 0 and writes nothing, which SPECX's leaf LL 0 fs [] covers. Measured on the pinned asan build: the
   witness W (four-call header) fills a class in the second call and exits 0 with stdout 0\n0\n0\n0\n and a 0-byte
   stderr; all 28 runs over 7 inputs and 4 builds have identical stdout per input and empty stderr (measured by
   h-hpreset-7's lane on 2026-10-28, its note PORT-OOM-ROOM section 6).

   No extra argument. The halts statement grants only its 16 GiB premise on the asan run itself, and AsanTop.v uses it
   to re-limit 512 GiB to 16 GiB (Reusable/HaltsKitB.v halts_budgets_of_srealizes, Reusable/YQ05.v
   must_exit_in_scfg_relim_closed). The statement has no plain run, so it grants no plain premise that TFIB_T could
   take. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import ZTraceSpec.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition presetsegs0 : list Segment := Asan.M.loaded_segments.

Definition TFIB_T : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk presetsegs0 brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    exists T,
      srealizes presetsegs0
        (init_config presetsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp) T /\
      shape_ok Exits.ok_or_refused T.

(* cgif's form (cgif_file lib/YZ03.v:20-26; fuzz_grant lib/A/GrantTFIB.v), the trace set fixed to SPECX. *)
Definition TFIB_T_specx : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk presetsegs0 brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    srealizes presetsegs0
      (init_config presetsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (SPECX (LS:=checksum_shape) inp).

(* Exits 0 or 2: lib/ZTraceSpec.v's exit lemma for SPECX at checksum_shape, read as HaltsKitB's shape_ok (the two
   predicates on events are the same match). *)
Lemma preset_SPECX_shape_ok : forall inp, shape_ok Exits.ok_or_refused (SPECX (LS:=checksum_shape) inp).
Proof. intros inp. exact (checksum_SPECX_exits_allowed checksum_permitted inp). Qed.

Lemma TFIB_T_of_specx : TFIB_T_specx -> TFIB_T.
Proof.
  intros H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exists (SPECX (LS:=checksum_shape) inp).
  exact (conj (H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp) (preset_SPECX_shape_ok inp)).
Qed.
