(* Carrying the loop's memory invariant (U/Prog/T/LLVMFuzzerTestOneInput_lh.v llvm_mem) across a callee whose
   footprint is at most its stack window [Sp - K, Sp) and the world (every evt callee contract of this unit posts
   that munch, with wmono, mem_inv, stk and wmem), and across a callee that fills one span of the world
   (memset / memcpy into a world field). The input buffer, the loop's frame [Sp, Sp + 240) and RELRO lie outside
   both intervals; the segment's footprint from m0 composes. The ubsan twin of the plain
   Prog/T/LLVMFuzzerTestOneInput_fr.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

Lemma lh_munch_add_world : forall a b m m', munch [(a, b)] m m' ->
  munch [(a, b); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m'.
Proof. intros a b m m' H x Hx. apply H. cbn [outside] in *. tauto. Qed.

(* A callee window [Sp - K, Sp) inside the segment's window [lo, Sp + 240): the segment's footprint composes. *)
Lemma lh_munch_seg : forall m0 m m' lo Sp K,
  munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  munch [(Sp - K, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  lo <= Sp - K -> 0 <= K ->
  munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m'.
Proof.
  intros m0 m m' lo Sp K H1 H2 HK HK0.
  eapply munch_trans; [exact H1|].
  eapply munch_weaken; [|exact H2].
  intros x Hx. cbn [outside] in *. unfold LH_FRAME in Hx. lia.
Qed.

(* RELRO (0x21ef8 + 0xd8) lies below the world, and below any window above the world. *)
Lemma lh_relro_munch : forall m m' a b, relro_img m ->
  munch [(a, b); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  W_BASE_UBSAN + W_LEN <= a -> relro_img m'.
Proof.
  intros m m' a b HR HM HA i Hi.
  unfold mrd. rewrite (HM (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - cbn [outside]. unfold wa.
    rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    unfold RELRO_BASE, RELRO_LEN, W_BASE_UBSAN, W_LEN in *.
    split; [lia|]. split; [lia | exact I].
Qed.

Section FR.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

Lemma llvm_frame_size : forall Sp j10 jio j60,
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  cells_size (llvm_frame regs0 Sp j10 jio j60) = 240%nat.
Proof.
  intros Sp j10 jio j60 H1 H2 H3. unfold llvm_frame, llvm_saved. reflexivity.
Qed.

Lemma llvm_mem_after_call : forall m0 Sp lo K B B' m m' j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= K <= LH_K ->
  munch [(Sp - K, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  wmono rsegs m m' ->
  mem_inv rsegs m' ->
  stk rsegs m' lo Sp ->
  wmem rsegs m' B' ->
  g_fail_next B' <= 1 ->
  llvm_mem data D regs0 m0 Sp lo B' m' j10 jio j60.
Proof.
  intros m0 Sp lo K B B' m m' j10 jio j60 HM HK MU WMO MI ST WM HFN'.
  unfold llvm_mem in HM |- *.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  pose proof (rw_cells_bound rsegs m Sp _ HRW) as HBF.
  rewrite (llvm_frame_size Sp j10 jio j60 HJ1 HJ2 HJ3) in HBF.
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HOW|].
  split.
  { eapply bytes_at_transport; [exact HD | exact MU |].
    cbn [disjoint_from]. unfold off_world in HOW. split; [lia | split; [exact HOW | exact I]]. }
  split; [exact HSP|]. split; [exact ST|]. split; [exact HLO|]. split; [exact HSP2|]. split; [exact HWL|].
  split; [exact MI|].
  split; [eapply lh_relro_munch; [exact HRO | exact MU | lia]|].
  split; [exact WM|]. split; [exact HFN'|].
  split; [eapply lh_munch_seg; [exact HMU | exact MU | lia | lia]|].
  split; [exact (wmono_trans rsegs _ _ _ HWMO WMO)|].
  split; [exact HJ1|]. split; [exact HJ2|]. split; [exact HJ3|].
  eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
  rewrite (llvm_frame_size Sp j10 jio j60 HJ1 HJ2 HJ3).
  cbn [disjoint_from]. unfold W_BASE_UBSAN, W_LEN in *. split; [lia | split; [lia | exact I]].
Qed.

(* A callee that only fills a span inside the world (memset / memcpy on a world field): its munch is that span. *)
Lemma lh_munch_span_in_world : forall X n m m', munch [(X, X + n)] m m' ->
  W_BASE_UBSAN <= X -> X + n <= W_BASE_UBSAN + W_LEN ->
  forall A, munch [(A, A); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m'.
Proof.
  intros X n m m' HM H1 H2 A x Hx. apply HM.
  cbn [outside] in *. destruct Hx as (_ & Hw & _). split; [lia | exact I].
Qed.

(* The invariant after such a callee: the world is the model's upd B k src. *)
Lemma llvm_mem_after_fill : forall m0 Sp lo B m m' k n src j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(W_BASE_UBSAN + k, W_BASE_UBSAN + k + n)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (W_BASE_UBSAN + k) [CB (Z.to_nat n) src] ->
  0 <= k -> 0 <= n -> k + n <= W_LEN ->
  g_fail_next (upd B k src) <= 1 ->
  llvm_mem data D regs0 m0 Sp lo (upd B k src) m' j10 jio j60.
Proof.
  intros m0 Sp lo B m m' k n src j10 jio j60 HM MU WMO MI CZ Hk Hn Hkn HFN'.
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & _ & HSTK & HLO & _ & HWL & _ & _ & HWM & _).
  assert (MUw : munch [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m').
  { replace (Sp - 0) with Sp by lia.
    apply (lh_munch_span_in_world (W_BASE_UBSAN + k) n m m'); [exact MU | lia | lia]. }
  eapply (llvm_mem_after_call m0 Sp lo 0 B (upd B k src) m m');
    [exact HM | unfold LH_K; lia | exact MUw | exact WMO | exact MI | | | exact HFN'].
  - eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |].
    cbn [disjoint_from]. unfold W_BASE_UBSAN, W_LEN in *. split; [lia | exact I].
  - exact (wm_fill rsegs W_BASE_UBSAN m m' B (W_BASE_UBSAN + k) k n src HWM MU WMO CZ eq_refl Hk Hn Hkn).
Qed.

End FR.
