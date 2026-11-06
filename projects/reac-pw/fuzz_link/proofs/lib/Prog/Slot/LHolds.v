(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_grant: the plain side is fuzz_grant's proved realization (built as its lib/Prog/AgreeGrant.v and lib/AgreeFrame.v build it, at grant_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/AsanTop.v, with its module paths and module names changed; 61 of its 85 lines of code are new or changed and 90 lines of the source are left out. *)
(* The plain top glue: Statements.plain_halts from the slot's contract (lib/Prog/LLVMFuzzerTestOneInput_c.v)
   at the frame's own instance (lib/FrameSlotMF.v plain_halts_of_frame_slot_mf_mwrite: the T-form slot
   obligation at mf_shape, with src0_msyms, zlib_API, src0_sink_head, src0_sink, RA_LIB, EMPTY) and the
   printf lane's mwrite contract. What this file discharges: the four hypotheses the frame top asks of the
   slot's G and GI (G inside frame_G, GI local to G and the kept blocks, GI at the first call from the
   image, GI gives mf_gi) and the slot contract's bindings of this instance. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YH00 YH02 YI5b YI5c YL0g YL0i YL0k YL0s YI14 YI16 YI06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import
  ZTraceSpec ZComplete ZAllocator Img0 Contract FrameAPI FrameProof FrameSlotG SlotTopR SlotTopG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile MemFileRI StdioExitMF MemFileT06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MwriteExit FrameSlotMF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mwrite_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Lemma llvm_G_frame : forall a, in_globals llvm_G a -> in_globals frame_G a.
Proof. intros a H. exact H. Qed.

(* the three heads mf_gi reads: g_sink (0x74528), g_say (0x75530), ofl_head (0x95cc8), all in frame_G *)
Lemma llvm_G_heads : forall a, mf_head_addr link_mf a -> in_globals llvm_G a.
Proof.
  intros a H. unfold mf_head_addr in H. cbn in H. unfold in_globals, llvm_G, frame_G.
  destruct H as [H | [H | H]].
  - exists 0x74528, 8. split; [cbn; tauto | lia].
  - exists 0x75530, 8. split; [cbn; tauto | lia].
  - match type of H with ?lo <= _ < _ =>
      assert (E3 : lo = 0x95cc8) by reflexivity; rewrite E3 in H end.
    exists 0x95cc8, 8. split; [cbn; tauto | lia].
Qed.

(* one byte of memory, read through mbyte *)
Lemma byte1_frame : forall (m m' : word -> option byte) a b,
  mbyte rsegs m' a = mbyte rsegs m a -> bytes_at rsegs m a [b] -> bytes_at rsegs m' a [b].
Proof.
  intros m m' a b E (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
  pose proof (H2 0%nat Hi) as H.
  change (mbyte rsegs m (a + Z.of_nat 0) = nth_error [b] 0) in H.
  change (mbyte rsegs m' (a + Z.of_nat 0) = nth_error [b] 0).
  replace (a + Z.of_nat 0) with a in * by lia. rewrite E. exact H.
Qed.

Lemma la_in_G : in_globals llvm_G (0x743f8 + 300).
Proof. exists 0x743f8, 301. split; [cbn; tauto | lia]. Qed.

Lemma llvm_GI_local : G_local_T src0segs llvm_G (llvm_GI src0_msyms).
Proof.
  intros j T m m' Hfr [HG HN]. split.
  - exact (mf_gi_local src0_msyms link_mf llvm_G llvm_G_heads j T m m' Hfr HG).
  - apply (byte1_frame m m'); [|exact HN].
    rewrite <- ms_segs_rsegs. apply Hfr. left. exact la_in_G.
Qed.

Lemma la_rom : seg_rom rsegs (Z_to_bv 64 (0x743f8 + 300)) = Some (Z_to_bv 8 0).
Proof. vm_compute. reflexivity. Qed.

Lemma llvm_GI_init : forall mem, G_img src0segs llvm_G mem -> llvm_GI src0_msyms 0%nat [] mem.
Proof.
  intros mem Hi. split.
  - exact (link_mf_gi0 llvm_G llvm_G_heads mem Hi).
  - pose proof (Hi _ la_in_G) as E. replace src0segs with rsegs in E by reflexivity.
    split; [lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; lia|].
    intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k.
    change (mbyte rsegs mem (0x743f8 + 300 + Z.of_nat 0) = nth_error [Z_to_bv 8 0] 0).
    replace (0x743f8 + 300 + Z.of_nat 0) with (0x743f8 + 300) by lia. rewrite E. exact la_rom.
Qed.

Lemma llvm_GI_mf : forall j T m, llvm_GI src0_msyms j T m -> mf_gi src0_msyms link_mf T m.
Proof. intros j T m [H _]. exact H. Qed.

(* the frame's facts at its own instance (the first half of FrameSlotMF.frame_plain_mf_holds) *)
Lemma frame_facts_src0 : frame_facts_plain src0_msyms (@zlib_API) mf_shape src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|].
  split; [exact frame_G_facts|].
  split; [exact frame_RELRO_facts|].
  exact zlib_frame_allocator.
Qed.

(* plain_halts, from the slot's contract at the frame's instance and the printf lane's mwrite contract *)
Theorem plain_halts_of_slot :
  mwrite_contract ->
  LLVMFuzzerTestOneInput_contract src0_msyms (@zlib_API) src0_sink_head src0_sink ->
  Statements.plain_halts.
Proof.
  intros HMW HS.
  apply (plain_halts_of_frame_slot_mf_mwrite llvm_G (llvm_GI src0_msyms)
    llvm_G_frame llvm_GI_local llvm_GI_init llvm_GI_mf HMW).
  intros rc fx j Hj.
  exact (HS RA_LIB EMPTY frame_facts_src0 rc fx j Hj).
Qed.
