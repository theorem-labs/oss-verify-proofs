(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput, UBSan build (ELF afc060e3cc9c, pinned
    1696d6c34ffd): its two theorems, 0x13e90 .. 0x141ec (the guard memset, "enp1s0", the inlined
    m_declared with m_split, reac_segconf_declared and check_declared).

    - [evt_V01_holds]: under the frame facts and the UBSan contracts of the six functions the body calls
      (lib/U/Prog/Seg/MainB.K_V01), the body is SegEvt.evt_V01 at the cut record every walk of main shares
      (lib/U/Prog/Seg/SegWalkMainA.CPseg, the U/Prog/seg_cuts.v predicates P_K13e90 and P_K141ec).
    - [seg_V01]: SegEnd.seg_V01_stmt at that record, by SegEvt.seg_V01_of_evt (the slot lifts the evt through
      Tac_seg.b1_seg_evt_e; evt_V01 is a seg_evt_e because reac_segconf_declared's strtol writes the errno cell).

    The walk itself is split over six files, against the interface lib/U/Prog/Seg/V01D.v:
      V01B.v      the frame bridge: FR + P_K13e90 -> V01D.V01_INNER, and V01D.V01_post -> seg_evt_e's post;
      V01Pre.v    0x13e90 .. 0x13f94  (the guard, the two "enp1s0" copies, the loop prologue);
      V01Loop.v   0x13f98 .. 0x13fcc  (the head and the join of the m_declared loop, by induction on the turns);
      V01Split.v  0x13fd0 .. 0x140c8  (m_split: strrchr, the digit loop, the parent loop, the mvlan buffer);
      V01Acc.v    0x140cc .. 0x1419c, 0x14254  (the duplicate loop, the append, the -1 exit);
      V01Tail.v   0x141ac .. 0x141e8  (reac_segconf_declared and check_declared).

    Part of the proof of LLVMFuzzerTestOneInput; no released proof of fuzz_segconf's LLVMFuzzerTestOneInput
    exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv SegEnd SegEvt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D SegWalkMainA MainB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01B V01Pre V01Loop V01Split V01Acc V01Tail.
Import ListNotations.
Open Scope Z_scope.

(** The five stretches, composed: the inner walk of the segment holds for every context the frame gives. *)
Lemma v01_inner : forall X : vctx, V01_geo X -> MainB.K_V01 -> V01_INNER X.
Proof.
  intros X G K.
  pose proof (v01_tail X G K) as T.
  pose proof (v01_split X G K) as S.
  pose proof (v01_acc X G K) as A.
  pose proof (v01_loop X G S A T) as H.
  exact (v01_pre X G K H T).
Qed.

Theorem evt_V01_holds :
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B APIf LS SH SK ra empty -> MainB.K_V01 ->
    evt_V01 B APIf ra empty SegWalkMainA.CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF K.
  apply (v01_evt_of_inner fx rc B APIf LS SH SK ra empty FF).
  intros X G. exact (v01_inner X G K).
Qed.

Theorem seg_V01 : seg_V01_stmt SegWalkMainA.CPseg MainB.K_V01.
Proof.
  apply (seg_V01_of_evt SegWalkMainA.CPseg MainB.K_V01).
  intros fx rc B APIf LS SH SK ra empty FF K.
  exact (evt_V01_holds fx rc B APIf LS SH SK ra empty FF K).
Qed.
