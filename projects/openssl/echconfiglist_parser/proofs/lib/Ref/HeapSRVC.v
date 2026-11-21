(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the run instance the library is closed at, [HRv], and
   its laws.  [HRv] is [HeapSRRun.hsr_run] over [MallocSR.HS] with [HeapSRRun.hsr_vc]'s
   additions: the overlay holds no byte of the vDSO/vvar pair [[vlo, vhi)] and every client block
   lies apart from it (heap relation), the pair stays the launch's reserved pair (kernel
   relation), and the auxv bound is at most [State.TASK_SIZE] (auxv relation).
     - A heap call carries [run_inv] through its own tree ([MallocSRI], [MallocSRI_x]): a machine
       step keeps the clean window, because no segment of the binary holds a byte at or above
       0x311000 ([VdsoClean.msteps_clean], [RMallocRep.ref_find_segment_none]); an mm node keeps
       it and the reserved pair ([MmVdso.mm_node_vc], once per entry of the pair).
     - The reach of [HRv] is over the run's list: the call's reach over the binary's list is
       lifted by [RunTail.sreach_lift_tail].
     - A block a call returns meets no byte of the window: every byte of it is writable (the
       post's [rw_cells]), and no byte of a clean window is ([VdsoClean.wview_none_of_clean]).
       That needs a non-empty window ([HWlt]): a block may straddle the point of an empty one.
     - A client write keeps the window clean: every interval of an [rclient_write_ok] list lies
       at or above [hceil], below 0x311000, or inside a client block, and each misses the window.
   Every other law is [MallocSR_closed]'s.  [HRbin] is [HRv] with the reach over the binary's own
   segments ([MainDefs.hsr_bin HRv]): the free that stays on them ([free_bin_vc]). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret Scfg SReach.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface HeapSRRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import MallocSR MallocSR_closed MallocSRI MallocSRI_x.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require RMallocRep.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require KLink.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section VC.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image rsegs = None.
  Variables vlo vmid vhi : Z.
  Hypothesis HW : 0x311000 <= vlo /\ vlo <= vmid /\ vmid <= vhi /\ vhi <= hceil.
  (* the window is not empty: a returned block's distance from it ([blk_off]) *)
  Hypothesis HWlt : vlo < vhi.

  Definition HRv : HeapSR_iface.hsr := hsr_vc vlo vmid vhi (hsr_run tail MallocSR.HS).

  (** * The window and the binary's segments *)

  (* no segment of the binary holds a byte of the window *)
  Lemma vc_nw_win : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment rsegs (bv_unsigned x) 1 = Some s -> seg_writable s = false.
  Proof.
    intros x s Hx Hf. pose proof HW as (W1 & W2 & W3 & W4).
    rewrite (RMallocRep.ref_find_segment_none (bv_unsigned x) 1) in Hf by lia. discriminate Hf.
  Qed.

  (* a range of at least one byte, every byte of it writable under a clean window, misses the
     window *)
  Lemma vc_new_off : forall m' A k n, vclean vlo vhi m' -> wr_at rsegs m' A k -> 1 <= n -> n <= k ->
    A + n <= vlo \/ vhi <= A.
  Proof.
    intros m' A k n VC (HA & HAk & HWr) Hn Hk.
    pose proof HW as (W1 & W2 & W3 & W4). pose proof HWlt as W5. pose proof hceil_lt_2p64 as Hc.
    destruct (Z_le_gt_dec (A + n) vlo) as [L1|L1]; [left; exact L1|].
    destruct (Z_le_gt_dec vhi A) as [L2|L2]; [right; exact L2|].
    exfalso.
    assert (EX : exists x, A <= x < A + n /\ vlo <= x < vhi).
    { destruct (Z_le_gt_dec A vlo) as [L3|L3]; [exists vlo | exists A]; lia. }
    destruct EX as (x & Hx & Hxw).
    apply (HWr (x - A) ltac:(lia)).
    replace (A + (x - A)) with x by lia.
    apply (wview_none_of_clean rsegs vlo vhi vc_nw_win m' _ VC).
    rewrite (wa_unsigned x) by lia. exact Hxw.
  Qed.

  (* every interval a client may write misses the window *)
  Lemma vc_outside_off : forall LB W (x : Z), Forall (blk_off vlo vhi) LB ->
    Forall (rclient_write_ok LB) W -> vlo <= x < vhi -> outside W x.
  Proof.
    intros LB W x FB FW Hx. pose proof HW as (W1 & W2 & W3 & W4).
    induction FW as [|iv W' Hiv _ IH]; [exact I|].
    destruct iv as [lo hi]. cbn [outside]. split; [|exact IH].
    unfold rclient_write_ok in Hiv. cbn [fst snd] in Hiv.
    destruct Hiv as [H1|[(H2a & H2b & _)|(b & Hb & H3 & H4)]].
    - lia.
    - lia.
    - destruct (proj1 (Forall_forall _ _) FB b Hb) as [O|O]; lia.
  Qed.

  Lemma vc_lb_remove_sub : forall p LB b, In b (hs_lb_remove MallocSR.HS p LB) -> In b LB.
  Proof.
    intros p LB b Hb. destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LR & _).
    destruct LR as (_ & _ & LR3). exact (LR3 p LB b Hb).
  Qed.

  (** * The invariant through a heap call's tree *)

  Theorem run_inv_ms : INV_MS (run_inv vlo vmid vhi).
  Proof.
    intros ms ms' mo Hm HI. destruct HI as [VC PI].
    split; [exact (msteps_clean rsegs vlo vhi vc_nw_win ms ms' Hm VC) | exact PI].
  Qed.

  Theorem run_inv_node : INV_NODE (run_inv vlo vmid vhi).
  Proof.
    intros n ms mo rsp mo' evs AT HH MI SF NS HI.
    pose proof HW as (W1 & W2 & W3 & W4).
    destruct HI as [VC [P1 P2]].
    assert (C1 : vc_cfg vlo vmid (mkCfg ms mo)).
    { split; [intros x Hx; exact (VC x ltac:(lia)) | exact P1]. }
    assert (C2 : vc_cfg vmid vhi (mkCfg ms mo)).
    { split; [intros x Hx; exact (VC x ltac:(lia)) | exact P2]. }
    destruct (mm_node_vc vlo vmid rsegs n ms mo rsp mo' evs AT HH MI SF NS C1) as [V1 Q1].
    destruct (mm_node_vc vmid vhi rsegs n ms mo rsp mo' evs AT HH MI SF NS C2) as [V2 Q2].
    split; [| split; [exact Q1 | exact Q2]].
    intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) vmid) as [L|L].
    - exact (V1 x ltac:(lia)).
    - exact (V2 x ltac:(lia)).
  Qed.

  (** * Reaches *)

  (* a reach of [HSI run_inv] from a state with the binary's backing is a reach of [HRv] *)
  Lemma vc_lift_run : forall (Q Q' : config -> Prop) c,
    hs_SR (HSI (run_inv vlo vmid vhi)) Q c ->
    ms_rom (cfg_ms c) = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom rsegs ->
    run_inv vlo vmid vhi c ->
    (forall c', Q c' -> run_inv vlo vmid vhi c' -> Q' c') ->
    hs_SR HRv Q' c.
  Proof.
    intros Q Q' c S Hr RI K.
    change (run_inv vlo vmid vhi c -> sreach rsegs (fun c' => Q c' /\ run_inv vlo vmid vhi c') c) in S.
    change (sr_run tail Q' c). unfold sr_run.
    eapply sreach_mono; [exact (sreach_lift_tail rsegs tail Hnx Hnw Hvi _ c (S RI) Hr)|].
    intros c' (c0 & E & HQ & HI). exists c0. split; [exact E | exact (K c0 HQ HI)].
  Qed.

  (* a reach over the binary's list from a state with its backing is a reach of [HRv] *)
  Lemma vc_lift_plain : forall (Q : config -> Prop) c, sreach rsegs Q c ->
    ms_rom (cfg_ms c) = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom rsegs ->
    hs_SR HRv Q c.
  Proof.
    intros Q c S Hr. change (sr_run tail Q c). unfold sr_run.
    exact (sreach_lift_tail rsegs tail Hnx Hnw Hvi Q c S Hr).
  Qed.

  (** * The posts: [HSI run_inv]'s with [run_inv] where they arrive are [HRv]'s *)

  Lemma vc_malloc_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo,
    Forall (blk_off vlo vhi) LB -> 1 <= n -> hs_rauxv_ok HRv m B ->
    forall c, HeapSR_iface.malloc_sr_post (HSI (run_inv vlo vmid vhi))
                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c ->
    run_inv vlo vmid vhi c ->
    HeapSR_iface.malloc_sr_post HRv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo FB Hn AUXv c HP RI.
    pose proof AUXv as [_ TB].
    unfold HeapSR_iface.malloc_sr_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & p & s'
                    & E & K & MP & MI & ST & ER & AU & PR & RR & RH & CE).
    destruct RI as [VC PI].
    assert (VC' : vclean vlo vhi m') by (rewrite E in VC; exact VC).
    pose proof CE as [_ WR].
    pose proof (vc_new_off m' A _ n VC' WR Hn) as NO.
    assert (OFF : blk_off vlo vhi (p, A, n))
      by (exact (NO ltac:(first [cbn [cells_size csize]; lia | simpl; lia]))).
    assert (FB2 : Forall (blk_off vlo vhi) ((p, A, n) :: LB)) by (constructor; [exact OFF | exact FB]).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', A, junk, p, s'.
    split; [exact E|]. split; [exact (conj K PI)|]. split; [exact MP|]. split; [exact MI|].
    split; [exact ST|]. split; [exact ER|]. split; [exact (conj AU TB)|]. split; [exact PR|].
    split; [exact RR|]. split; [exact (conj RH (conj VC' FB2)) | exact CE].
  Qed.

  Lemma vc_free_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo,
    Forall (blk_off vlo vhi) LB -> hs_rauxv_ok HRv m B ->
    forall c, HeapSR_iface.free_sr_post (HSI (run_inv vlo vmid vhi))
                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo c ->
    run_inv vlo vmid vhi c ->
    HeapSR_iface.free_sr_post HRv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo FB AUXv c HP RI.
    pose proof AUXv as [_ TB].
    unfold HeapSR_iface.free_sr_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s'
                    & E & K & MP & MI & ST & ER & AU & PR & RH).
    destruct RI as [VC PI].
    assert (VC' : vclean vlo vhi m') by (rewrite E in VC; exact VC).
    assert (FB' : Forall (blk_off vlo vhi) (hs_lb_remove MallocSR.HS p LB)).
    { apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) FB). exact (vc_lb_remove_sub p LB b Hb). }
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', s'.
    split; [exact E|]. split; [exact (conj K PI)|]. split; [exact MP|]. split; [exact MI|].
    split; [exact ST|]. split; [exact ER|]. split; [exact (conj AU TB)|].
    split; [exact PR | exact (conj RH (conj VC' FB'))].
  Qed.

  Lemma vc_realloc_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo,
    Forall (blk_off vlo vhi) LB -> 1 <= n' -> hs_rauxv_ok HRv m B ->
    forall c, HeapSR_iface.realloc_sr_post (HSI (run_inv vlo vmid vhi))
                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo c ->
    run_inv vlo vmid vhi c ->
    HeapSR_iface.realloc_sr_post HRv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo FB Hn AUXv c HP RI.
    pose proof AUXv as [_ TB].
    unfold HeapSR_iface.realloc_sr_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A' & junk & p' & s'
                    & E & K & MP & MI & ST & ER & AU & PR & RR & RH & CE).
    destruct RI as [VC PI].
    assert (VC' : vclean vlo vhi m') by (rewrite E in VC; exact VC).
    pose proof CE as [_ WR].
    pose proof (vc_new_off m' A' _ n' VC' WR Hn) as NO.
    assert (OFF : blk_off vlo vhi (p', A', n'))
      by (exact (NO ltac:(first [cbn [cells_size csize]; lia | simpl; lia]))).
    assert (FB2 : Forall (blk_off vlo vhi) ((p', A', n') :: hs_lb_remove MallocSR.HS p LB)).
    { constructor; [exact OFF|]. apply Forall_forall. intros b Hb.
      apply (proj1 (Forall_forall _ _) FB). exact (vc_lb_remove_sub p LB b Hb). }
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', A', junk, p', s'.
    split; [exact E|]. split; [exact (conj K PI)|]. split; [exact MP|]. split; [exact MI|].
    split; [exact ST|]. split; [exact ER|]. split; [exact (conj AU TB)|]. split; [exact PR|].
    split; [exact RR|]. split; [exact (conj RH (conj VC' FB2)) | exact CE].
  Qed.

  Lemma vc_aalloc_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n lo B m mo,
    Forall (blk_off vlo vhi) LB -> 1 <= n -> hs_rauxv_ok HRv m B ->
    forall c, HeapSR_iface.aalloc_sr_post (HSI (run_inv vlo vmid vhi))
                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n lo B m mo c ->
    run_inv vlo vmid vhi c ->
    HeapSR_iface.aalloc_sr_post HRv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n lo B m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n lo B m mo FB Hn AUXv c HP RI.
    pose proof AUXv as [_ TB].
    unfold HeapSR_iface.aalloc_sr_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & p & s'
                    & E & K & MP & MI & ST & ER & AU & PR & RR & AM & RH & CE).
    destruct RI as [VC PI].
    assert (VC' : vclean vlo vhi m') by (rewrite E in VC; exact VC).
    pose proof CE as [_ WR].
    pose proof (vc_new_off m' A _ n VC' WR Hn) as NO.
    assert (OFF : blk_off vlo vhi (p, A, n))
      by (exact (NO ltac:(first [cbn [cells_size csize]; lia | simpl; lia]))).
    assert (FB2 : Forall (blk_off vlo vhi) ((p, A, n) :: LB)) by (constructor; [exact OFF | exact FB]).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', A, junk, p, s'.
    split; [exact E|]. split; [exact (conj K PI)|]. split; [exact MP|]. split; [exact MI|].
    split; [exact ST|]. split; [exact ER|]. split; [exact (conj AU TB)|]. split; [exact PR|].
    split; [exact RR|]. split; [exact AM|]. split; [exact (conj RH (conj VC' FB2)) | exact CE].
  Qed.

  (** * The fields of [heap_sr_hyps_x HRv] *)

  Lemma vc_SR_laws : HeapSR_iface.SR_laws HRv.
  Proof.
    assert (L : HeapSR_iface.SR_laws (hsr_run tail MallocSR.HS)).
    { eapply SR_laws_run; first [eassumption | (intros ? ? HQ; exact HQ)]. }
    exact L.
  Qed.

  Lemma vc_KREL_laws : HeapSR_iface.KREL_laws HRv.
  Proof. intros s mo HK. destruct HK as [K _]. exact (KM_halted_lazy s mo K). Qed.

  Lemma vc_MPRES_laws : HeapSR_iface.MPRES_laws HRv.
  Proof. destruct heap_sr_hyps_closed as (_ & _ & L3 & _). exact L3. Qed.

  Lemma vc_alloc_ok_of_live : HeapSR_iface.alloc_ok_of_live HRv.
  Proof.
    intros s LB m n HR0. destruct HR0 as [HR _].
    destruct heap_sr_hyps_closed as (_ & _ & _ & L4 & _). exact (L4 s LB m n HR).
  Qed.

  Lemma vc_RHEAP_frame : HeapSR_iface.RHEAP_frame HRv.
  Proof.
    unfold HeapSR_iface.RHEAP_frame, RMalloc_iface_stmt.RHEAP_frame_stmt.
    intros s LB m m' W HR0 MU WM FW. destruct HR0 as (HR & VC & FB).
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & RF & _).
    assert (VC' : vclean vlo vhi m').
    { intros x Hx. rewrite (MU x (vc_outside_off LB W (bv_unsigned x) FB FW Hx)). exact (VC x Hx). }
    exact (conj (RF s LB m m' W HR MU WM FW) (conj VC' FB)).
  Qed.

  Lemma vc_RHEAP_block_range : HeapSR_iface.RHEAP_block_range HRv.
  Proof.
    unfold HeapSR_iface.RHEAP_block_range, RMalloc_iface_stmt.RHEAP_block_range_stmt.
    intros s LB m b HR0 Hb. destruct HR0 as [HR _].
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & L6 & _). exact (L6 s LB m b HR Hb).
  Qed.

  Lemma vc_RHEAP_blocks_disjoint : HeapSR_iface.RHEAP_blocks_disjoint HRv.
  Proof.
    unfold HeapSR_iface.RHEAP_blocks_disjoint, RMalloc_iface_stmt.RHEAP_blocks_disjoint_stmt.
    intros s LB m b1 b2 HR0. destruct HR0 as [HR _].
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & L7 & _). exact (L7 s LB m b1 b2 HR).
  Qed.

  Lemma vc_RHEAP_blocks_nodup : HeapSR_iface.RHEAP_blocks_nodup HRv.
  Proof.
    unfold HeapSR_iface.RHEAP_blocks_nodup, RMalloc_iface_stmt.RHEAP_blocks_nodup_stmt.
    intros s LB m HR0. destruct HR0 as [HR _].
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & L8 & _). exact (L8 s LB m HR).
  Qed.

  (* the auxv bound never changes, so its [TASK_SIZE] conjunct is the premise's *)
  Lemma vc_rauxv_frame : HeapSR_iface.rauxv_frame HRv.
  Proof.
    unfold HeapSR_iface.rauxv_frame, RMalloc_iface_stmt.rauxv_ok_frame_stmt.
    intros m m' B W AU0 MU WM FW. destruct AU0 as [AU TB].
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _).
    exact (conj (L9 m m' B W AU MU WM FW) TB).
  Qed.

  Lemma vc_lb_remove_laws : HeapSR_iface.lb_remove_laws HRv.
  Proof. destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LR & _). exact LR. Qed.

  Lemma vc_malloc : HeapSR_iface.malloc_sr_stmt HRv.
  Proof.
    unfold HeapSR_iface.malloc_sr_stmt, HeapSR_iface.malloc_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv mo
           HR0 KR0 AOK AUX0 HB ST CLO LO ERR MI TP A0 HN.
    destruct HR0 as (HR & VC & FB). destruct KR0 as (KMs & PI). pose proof AUX0 as [AUX _].
    pose proof (malloc_sr_I phase2 (run_inv vlo vmid vhi) run_inv_ms run_inv_node) as MS0.
    unfold HeapSR_iface.malloc_sr_stmt, HeapSR_iface.malloc_sr_stmt_at in MS0.
    pose proof (MS0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv mo
                    HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 HN) as S0.
    apply (vc_lift_run _ _ _ S0); [reflexivity | exact (conj VC PI) |].
    exact (vc_malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo FB (proj1 HN) AUX0).
  Qed.

  Lemma vc_free : HeapSR_iface.free_sr_stmt HRv.
  Proof.
    unfold HeapSR_iface.free_sr_stmt, HeapSR_iface.free_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv mo
           HR0 KR0 HIN AUX0 HB ST CLO LO ERR MI TP A0.
    destruct HR0 as (HR & VC & FB). destruct KR0 as (KMs & PI). pose proof AUX0 as [AUX _].
    pose proof (free_sr_I phase2 (run_inv vlo vmid vhi) run_inv_ms run_inv_node) as FS.
    unfold HeapSR_iface.free_sr_stmt, HeapSR_iface.free_sr_stmt_at in FS.
    pose proof (FS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv mo
                   HR KMs HIN AUX HB ST CLO LO ERR MI TP A0) as S0.
    apply (vc_lift_run _ _ _ S0); [reflexivity | exact (conj VC PI) |].
    exact (vc_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo FB AUX0).
  Qed.

  (* [free(NULL)] reads nothing of the heap: [MallocSR]'s reach, lifted *)
  Lemma vc_free_null : HeapSR_iface.free_null_sr_stmt HRv.
  Proof.
    unfold HeapSR_iface.free_null_sr_stmt, HeapSR_iface.free_null_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo HH HL.
    destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FN).
    apply vc_lift_plain; [| reflexivity].
    exact (FN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo HH HL).
  Qed.

  Lemma vc_realloc : HeapSR_iface.realloc_sr_stmt HRv.
  Proof.
    unfold HeapSR_iface.realloc_sr_stmt, HeapSR_iface.realloc_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n n' lo B pre errv mo
           HR0 KR0 HIN AOK BA LEN AUX0 HB ST CLO LO ERR MI TP A0 A1 HN.
    destruct HR0 as (HR & VC & FB). destruct KR0 as (KMs & PI). pose proof AUX0 as [AUX _].
    pose proof (realloc_sr_I phase2 (run_inv vlo vmid vhi) run_inv_ms run_inv_node) as RS.
    unfold HeapSR_iface.realloc_sr_stmt, HeapSR_iface.realloc_sr_stmt_at in RS.
    pose proof (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n n' lo B pre errv mo
                   HR KMs HIN AOK BA LEN AUX HB ST CLO LO ERR MI TP A0 A1 HN) as S0.
    apply (vc_lift_run _ _ _ S0); [reflexivity | exact (conj VC PI) |].
    exact (vc_realloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo FB (proj1 HN) AUX0).
  Qed.

  Lemma vc_aalloc : HeapSR_iface.aalloc_sr_stmt HRv.
  Proof.
    unfold HeapSR_iface.aalloc_sr_stmt, HeapSR_iface.aalloc_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB al n lo B errv mo
           HR0 KR0 AOK AUX0 HB ST CLO LO ERR MI TP A0 A1 AL N1 N2.
    destruct HR0 as (HR & VC & FB). destruct KR0 as (KMs & PI). pose proof AUX0 as [AUX _].
    pose proof (aalloc_sr_I phase2 (run_inv vlo vmid vhi) run_inv_ms run_inv_node) as AAS.
    unfold HeapSR_iface.aalloc_sr_stmt, HeapSR_iface.aalloc_sr_stmt_at in AAS.
    pose proof (AAS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB al n lo B errv mo
                    HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 A1 AL N1 N2) as S0.
    apply (vc_lift_run _ _ _ S0); [reflexivity | exact (conj VC PI) |].
    exact (vc_aalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n lo B m mo FB N1 AUX0).
  Qed.

  Lemma vc_rauxv_elim : HeapSR_iface.rauxv_elim HRv.
  Proof.
    intros m B AU0. destruct AU0 as [AU _].
    destruct heap_sr_hyps_x_closed as (_ & _ & _ & X3 & _). exact (X3 m B AU).
  Qed.

  Lemma vc_statics : HeapSR_iface.statics_of_RHEAP HRv.
  Proof.
    intros s LB m HR0. destruct HR0 as [HR _].
    destruct heap_sr_hyps_x_closed as (_ & _ & _ & _ & X4 & _). exact (X4 s LB m HR).
  Qed.

  Lemma vc_perm : HeapSR_iface.RHEAP_perm_law HRv.
  Proof.
    intros s LB LB' m HR0 P. destruct HR0 as (HR & VC & FB).
    destruct heap_sr_hyps_x_closed as (_ & _ & _ & _ & _ & X5 & _).
    assert (FB' : Forall (blk_off vlo vhi) LB').
    { apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) FB).
      eapply Permutation_in; [apply Permutation_sym; exact P | exact Hb]. }
    exact (conj (X5 s LB LB' m HR P) (conj VC FB')).
  Qed.

  Lemma vc_slack : HeapSR_iface.RHEAP_slack_law HRv.
  Proof.
    intros s LB m p A n HR0. destruct HR0 as [HR _].
    destruct heap_sr_hyps_x_closed as (_ & _ & _ & _ & _ & _ & X6). exact (X6 s LB m p A n HR).
  Qed.

  Theorem heap_sr_hyps_x_vc : HeapSR_iface.heap_sr_hyps_x HRv.
  Proof.
    unfold HeapSR_iface.heap_sr_hyps_x, HeapSR_iface.heap_sr_hyps.
    split; [split; [exact vc_SR_laws|] |].
    - split; [exact vc_KREL_laws|]. split; [exact vc_MPRES_laws|]. split; [exact vc_alloc_ok_of_live|].
      split; [exact vc_RHEAP_frame|]. split; [exact vc_RHEAP_block_range|].
      split; [exact vc_RHEAP_blocks_disjoint|]. split; [exact vc_RHEAP_blocks_nodup|].
      split; [exact vc_rauxv_frame|]. split; [exact vc_lb_remove_laws|].
      split; [exact vc_malloc|]. split; [exact vc_free | exact vc_free_null].
    - split; [exact vc_realloc|]. split; [exact vc_aalloc|]. split; [exact vc_rauxv_elim|].
      split; [exact vc_statics|]. split; [exact vc_perm | exact vc_slack].
  Qed.

  (** * The reach over the binary's own list *)

  (* the reach over the binary's own list, everything else HRv's: convertible to MainDefs.hsr_bin HRv *)
  Definition HRbin : HeapSR_iface.hsr :=
    {| hs_SR := sreach rsegs; hs_KREL := hs_KREL HRv; hs_MPRES := hs_MPRES HRv; hs_RHEAP := hs_RHEAP HRv;
       hs_rauxv_ok := hs_rauxv_ok HRv; hs_lb_remove := hs_lb_remove HRv; hs_alloc_ok := hs_alloc_ok HRv;
       hs_LIVE_MAX := hs_LIVE_MAX HRv; hs_LIVE_CNT_MAX := hs_LIVE_CNT_MAX HRv;
       hs_LIVE_BIG_MAX := hs_LIVE_BIG_MAX HRv; hs_canary := hs_canary HRv |}.

  Lemma vc_bin_run : forall (Q Q' : config -> Prop) c,
    hs_SR (HSI (run_inv vlo vmid vhi)) Q c -> run_inv vlo vmid vhi c ->
    (forall c', Q c' -> run_inv vlo vmid vhi c' -> Q' c') -> hs_SR HRbin Q' c.
  Proof.
    intros Q Q' c S RI K.
    change (run_inv vlo vmid vhi c -> sreach rsegs (fun c' => Q c' /\ run_inv vlo vmid vhi c') c) in S.
    change (sreach rsegs Q' c).
    eapply sreach_mono; [exact (S RI)|]. intros c' [HQ HI]. exact (K c' HQ HI).
  Qed.

  Theorem free_bin_vc : HeapSR_iface.free_sr_stmt HRbin.
  Proof.
    unfold HeapSR_iface.free_sr_stmt, HeapSR_iface.free_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv mo
           HR0 KR0 HIN AUX0 HB ST CLO LO ERR MI TP A0.
    destruct HR0 as (HR & VC & FB). destruct KR0 as (KMs & PI). pose proof AUX0 as [AUX _].
    pose proof (free_sr_I phase2 (run_inv vlo vmid vhi) run_inv_ms run_inv_node) as FS.
    unfold HeapSR_iface.free_sr_stmt, HeapSR_iface.free_sr_stmt_at in FS.
    pose proof (FS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv mo
                   HR KMs HIN AUX HB ST CLO LO ERR MI TP A0) as S0.
    apply (vc_bin_run _ _ _ S0); [exact (conj VC PI) |].
    intros c' HQ HI.
    exact (vc_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo FB AUX0 c' HQ HI).
  Qed.

  (** * The kernel relation and the fields no step changes *)

  Theorem krel_vm_vc : forall s mo mo', hs_KREL HRv s mo -> m_halted mo' = m_halted mo -> m_vm_lazy mo' = m_vm_lazy mo ->
    m_vm_materialized mo' = m_vm_materialized mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo ->
    m_channel_reader mo' = m_channel_reader mo -> hs_KREL HRv s mo'.
  Proof.
    intros s mo mo' HK Hh Hl Hm Hv Hk Hr. destruct HK as (K & P1 & P2).
    change (MallocSR.KM s mo' /\ (mm_vinv vlo vmid mo' /\ mm_vinv vmid vhi mo')).
    split; [| split].
    - apply (KM_vm s mo mo' K).
      + destruct K as (L & _ & KL & _). destruct (KLink.kb_minv _ _ _ KL) as [M1 [M2 M3]].
        split; [rewrite Hl; exact M1 | split; [rewrite Hm; exact M2 | rewrite Hr; exact M3]].
      + rewrite Hh. exact (proj1 (KM_halted_lazy s mo K)).
      + exact Hk.
      + exact Hv.
    - apply (mm_vinv_frame vlo vmid mo mo');
        [exact Hk | rewrite Hv; reflexivity | rewrite Hv; reflexivity | rewrite Hv; reflexivity | exact P1].
    - apply (mm_vinv_frame vmid vhi mo mo');
        [exact Hk | rewrite Hv; reflexivity | rewrite Hv; reflexivity | rewrite Hv; reflexivity | exact P2].
  Qed.
End VC.
