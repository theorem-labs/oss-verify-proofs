From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotGlue SlotCallees SlotIter SlotItBase SlotItSt SlotItA SlotItB SlotItBW SlotItCW SlotItC0 SlotItD SlotItE.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* One iteration of the message loop of the entry function (ubsan 0x14060): the loop head 0x140fc (ia_head) to
   send_message (ia_send, stA), strnlen and the three mallocs (ib_seg, stB), the word splitter, check_reply and
   check_arity to check_words's entry (seg_b2_spec, stBW), check_words (seg_cw, stC), check_refusal,
   check_round_trip, the three frees and the loop tail (seg_de). *)

Definition seg_b2_spec : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
         (ra empty : Z) (rc : RunCeil) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
         (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound),
    CF.Slot.frame_given_u B API LS SH SK ra empty -> cmd_callees B API -> harness_props ->
    lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b ->
    spZ rg = S ->
    forall m p n R0 c, stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
      SR rsegs c (stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).

Section Proof.
Hypothesis SEG_B2 : seg_b2_spec.

Lemma iter_spec_holds : iter_spec.
Proof.
  unfold iter_spec.
  intros B API LS SH SK ra empty rc S rg mem0 md0 L0 A0 p0 n0 pl b FG CC HP PRE RG2 m c HA.
  pose proof CC as (SMC & CWC & CRTC & RCC & CRPL & CAR & CRF & SNL & MEMC & SSP & SCSP).
  eapply SR_bind; [exact (ia_head B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 m c HA)|].
  intros c1 (p & n & R0 & H1).
  eapply SR_bind; [exact (ia_send B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2
                            (SMC rc) HP m p n R0 c1 H1)|].
  intros c2 H2.
  eapply SR_bind; [exact (ib_seg B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 SNL m p n R0 c2 H2)|].
  intros c3 H3.
  eapply SR_bind; [exact (SEG_B2 B API LS SH SK ra empty rc S rg mem0 md0 L0 A0 p0 n0 pl b FG CC HP PRE RG2
                            m p n R0 c3 H3)|].
  intros c4 H4.
  eapply SR_bind; [exact (seg_cw B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 (CWC rc)
                            m p n R0 c4 H4)|].
  intros c5 H5.
  exact (seg_de B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 CRF (CRTC rc) m p n R0 c5 H5).
Qed.

End Proof.
