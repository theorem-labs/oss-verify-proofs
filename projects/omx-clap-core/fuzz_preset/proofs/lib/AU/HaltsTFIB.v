(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v:19-26 (asan-ubsan image), by way of proofs/libreac/fuzz_grant/lib/A/GrantTFIB.v (a working branch 0bed23e5b69) and fuzz_preset's lib/A/HaltsTFIB.v (a working branch 7837446fad0), for fuzz_preset's asan-ubsan image: TFIB_T_AU_H takes any trace set whose exits are 0 or 2, which is all that halts_budgets_of_srealizes (Reusable/HaltsKitB.v) asks; cgif's form, with the trace set SPECX at fuzz_preset's checksum_shape (lib/ZTraceSpec.v), is TFIB_T_AU_H_specx and gives TFIB_T_AU_H; module paths and the image changed. *)
(* What the ASan side of fuzz_preset's asan_ubsan_halts must prove (lib/AU/HaltsTop.v takes TFIB_T_AU_H as its one
   hypothesis): from every valid start, the asan-ubsan build at the 512 GiB limit realizes, with no cut
   (lib/Reusable/YK18.v srealizes), some trace set in which every exit has status 0 or 2 and no trace is killed by a
   signal. This is lib/A/HaltsTFIB.v's TFIB_T, word for word but for the image (AsanUbsan instead of Asan).

   The class-full arm is reachable. TFIB_T_AU_H has the five entry premises of the cgif form and nothing else: no
   bound on live bytes or event counts and no allocator regime (those live in a proof of TFIB_T_AU_H, not in it). So
   a proof of it must walk the branch where a size class of the runtime's primary allocator is full and the
   allocation returns 0 (allocator_may_return_null = 1 in the image's options), into the harness's refusal path, which
   ends in exit 0. TFIB_T_AU_H asks only that every exit be 0 or 2, so a full class is an exit question here, not a
   trace question.

   No extra argument: the halts statement has no plain run, so it grants no plain premise that TFIB_T_AU_H could
   take; its 16 GiB premise is used by the re-limit in lib/AU/HaltsTop.v. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import ZTraceSpec.
(* presetsegsAU is a Theorem Labs lane's one definition (lib/AU/PresetTFIBAU.v), shared with the agrees side and the room export *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetTFIBAU.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Definition TFIB_T_AU_H : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk presetsegsAU brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    exists T,
      srealizes presetsegsAU
        (init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp) T /\
      shape_ok Exits.ok_or_refused T.

(* cgif's form (cgif_file lib/YZ03.v:20-26, the asan-ubsan image), the trace set fixed to SPECX. *)
Definition TFIB_T_AU_H_specx : Prop :=
  forall sp brk mbase rnd inp,
    valid_sp sp -> valid_brk presetsegsAU brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
    srealizes presetsegsAU
      (init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (SPECX (LS:=checksum_shape) inp).

Lemma presetAU_SPECX_shape_ok : forall inp, shape_ok Exits.ok_or_refused (SPECX (LS:=checksum_shape) inp).
Proof. intros inp. exact (checksum_SPECX_exits_allowed checksum_permitted inp). Qed.

Lemma TFIB_T_AU_H_of_specx : TFIB_T_AU_H_specx -> TFIB_T_AU_H.
Proof.
  intros H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exists (SPECX (LS:=checksum_shape) inp).
  exact (conj (H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp) (presetAU_SPECX_shape_ok inp)).
Qed.
