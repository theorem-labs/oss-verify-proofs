(* Carrying the op loop's memory invariant (LLVMFuzzerTestOneInput_lh.v llvm_mem) across a callee whose footprint
   is at most its stack window [Sp - K, Sp) and the world: every callee contract of this unit has that post (its
   munch, wmono, mem_inv, stk and wmem; a callee that touches only its window, as settle, is widened by
   munch_add_world). The loop's own frame [Sp, Sp + LLVM_FRAME), the input buffer and RELRO lie outside both
   intervals, so each is carried by the kit's transport lemma. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

Lemma munch_add_world : forall a b m m', munch [(a, b)] m m' ->
  munch [(a, b); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m'.
Proof. intros a b m m' H x Hx. apply H. cbn [outside] in *. tauto. Qed.

(* RELRO (0x213c8 + 0x98) is below the world and below any window above the world. *)
Lemma relro_munch_hi : forall m m' a b, relro_img m ->
  munch [(a, b); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  W_BASE_PLAIN + W_LEN <= a -> relro_img m'.
Proof.
  intros m m' a b HR HM HA i Hi.
  unfold mrd. rewrite (HM (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - cbn [outside]. unfold wa.
    rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    unfold RELRO_BASE, RELRO_LEN, W_BASE_PLAIN, W_LEN in *.
    split; [lia|]. split; [lia | exact I].
Qed.

Section FR.
Context (data : Z) (D : list byte).

Lemma llvm_mem_after_call : forall Sp lo K B B' m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' ->
  mem_inv rsegs m' ->
  stk rsegs m' lo Sp ->
  wmem rsegs m' B' ->
  g_fail_next B' <= 1 ->
  llvm_mem data D Sp lo B' m0 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.
Proof.
  intros Sp lo K B B' m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 HM HK MU WMO MI ST WM HFN'.
  unfold llvm_mem in HM |- *.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                  & HFN & HJ1 & HJ2 & HRW).
  split; [ (* the footprint, extended *)
    eapply munch_trans; [exact HMU0|];
    intros x Hx; apply MU; cbn [outside] in Hx |- *;
      unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in Hx, HK; destruct Hx as (Hx1 & Hx2 & _);
      split; [lia | split; [exact Hx2 | exact I]] |].
  split; [eapply wmono_trans; [exact HWMO0 | exact WMO]|].
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  assert (HSPpos : 0 <= lo /\ W_BASE_PLAIN + W_LEN <= lo)
    by (unfold W_BASE_PLAIN, W_LEN in HOWS |- *; lia).
  unfold off_window in HOWIN. rewrite unsigned_lit in HOWIN by lia.
  pose proof (rw_cells_bound rsegs m Sp _ HRW) as HBF.
  split; [eapply bytes_at_transport; [exact HD | exact MU | cbn [disjoint_from];
            unfold off_world in HOW; split; [lia | split; [exact HOW | exact I]]]|].
  split; [exact HSP|]. split; [exact ST|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWOS|]. split; [exact HOWS|]. split; [exact HOW|].
  split; [unfold off_window; rewrite unsigned_lit by lia; exact HOWIN|].
  split; [exact MI|].
  split; [eapply relro_munch_hi; [exact HRO | exact MU | lia]|].
  split; [exact WM|]. split; [exact HFN'|]. split; [exact HJ1|]. split; [exact HJ2|].
  eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
  unfold llvm_frame_consts, llvm_saved in HBF |- *.
  cbn [disjoint_from cells_size csize app] in HBF |- *.
  split; [lia|]. split; [lia | exact I].
Qed.

(* A callee that only fills a span inside the world (memset / memcpy on a world field): its munch is that span,
   which lies inside the world, so the window-and-world form covers it. *)
Lemma munch_span_in_world : forall X n m m', munch [(X, X + n)] m m' ->
  W_BASE_PLAIN <= X -> X + n <= W_BASE_PLAIN + W_LEN ->
  forall A, munch [(A, A); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m'.
Proof.
  intros X n m m' HM H1 H2 A x Hx. apply HM.
  cbn [outside] in *. destruct Hx as (_ & Hw & _). split; [lia | exact I].
Qed.

(* The invariant after such a callee: the world is the model's upd B k src. *)
Lemma llvm_mem_after_fill : forall Sp lo B m0 m m' k n src ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  munch [(W_BASE_PLAIN + k, W_BASE_PLAIN + k + n)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (W_BASE_PLAIN + k) [CB (Z.to_nat n) src] ->
  0 <= k -> 0 <= n -> k + n <= W_LEN ->
  g_fail_next (upd B k src) <= 1 ->
  llvm_mem data D Sp lo (upd B k src) m0 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.
Proof.
  intros Sp lo B m0 m m' k n src ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    HM MU WMO MI CZ Hk Hn Hkn HFN'.
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & HSTK & HLO & _ & _ & HOWS & _ & _ & _ & _ & HWM & _).
  assert (MUw : munch [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m').
  { replace (Sp - 0) with Sp by lia.
    apply (munch_span_in_world (W_BASE_PLAIN + k) n m m'); [| lia | lia].
    replace (W_BASE_PLAIN + k + n) with (W_BASE_PLAIN + k + n) by lia. exact MU. }
  eapply (llvm_mem_after_call Sp lo 0 B (upd B k src) m0 m m');
    [exact HM | unfold LLVM_LOOP_K; lia | exact MUw | exact WMO | exact MI | | | exact HFN'].
  - eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |].
    cbn [disjoint_from]. split; [lia | exact I].
  - exact (wm_fill rsegs W_BASE_PLAIN m m' B (W_BASE_PLAIN + k) k n src HWM MU WMO CZ eq_refl Hk Hn Hkn).
Qed.

End FR.
