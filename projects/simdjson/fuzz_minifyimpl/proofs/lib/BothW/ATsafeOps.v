(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree RSim RSimProg AsanOK.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation atot := (atotal aokS apost).


Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition CHMAX : Z := LSBYTES + 12296 * SMAX + 2 * (Q_MAX + Q_CACHE).
(* [comment removed for export] *)
Definition COSTP (c : Z) : Z := 9 * (size_of_class c + 128) + 8.
Definition COSTS (n : Z) : Z := sec_map_size n + sec_map_size n / 8 + sec_map_size n / 4 + 24576.
Definition COSTF : Z := COSTP K_BATCH_CLASS.
Definition COSTM (n : Z) : Z := if is_primary n then COSTP (class_id (needed_size n)) else COSTS n.

Section OpsM.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Variable NLK : Z.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK + NMAXZ * 4096 <= LIMIT.
Hypothesis HNLK : 0 <= NLK.
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation KI := (ATsafeAlloc.KI Abase NLK).
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation TS := (TS NMAX).
Local Notation LW := (ATsafeEv.LW SB PA).
Local Notation PHI := (ATsafeEv.PHI).

(* [comment removed for export] *)
Definition GH (mf : Z -> Z) (st : astate) : Prop :=
  forall c, 1 <= c <= 31 ->
    0 <= mf c
    /\ cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st) <= mf c
    /\ c_allocated_user (get_cls st c) <= size_of_class c * (mf c + SLK c).

(* [comment removed for export] *)
Definition JJ (Y : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  fun RNG A s mo =>
    AI Y s mo /\ aps_atop s = ATOP
    /\ RNG = fp_ok (m_vm_lazy mo) A /\ a_space_beg (aps_m s) = SB /\ a_ptr_array (aps_m s) = PA /\ 0 <= v /\
    exists G k mf, QOK G (aps_m s) /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k /\ GH mf (aps_m s)
      /\ 8 * (EAGER0 + CBM mf + CHMAX) + v <= 8 * NLK
      /\ 4096 * k + cpot (PHI mf (aps_m s)) + v <= 4096 * NMAXZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_of_AMI : forall RESV ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros RESV ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact M9| split; [exact M6| exact M10]].
Qed.

Lemma cntP_nbatch_nonneg : forall c st, 0 <= cntP c (all_chunks [] [] st) /\ 0 <= nbatch c (qbatches [] st).
Proof. intros. split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. Qed.

(* [comment removed for export] *)
Lemma LW_of_INV : forall RESV st mo mf, INV RESV ATOP [] [] st mo -> GH mf st ->
  (forall c, 1 <= c <= 31 -> 0 <= mf c) -> a_space_beg st = SB -> a_ptr_array st = PA ->
  LW mf st.
Proof.
  intros RESV st mo mf [HA HM] HG Hm0 ESB EPA. pose proof HA as (HC & _ & _ & _ & _ & _ & Hres & _).
  split; [exact ESB|]. split; [exact EPA|]. split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. destruct X as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  destruct (HG c Hc) as (G0 & G1 & G2). pose proof (size_of_class_pos c Hc) as [S1 S2]. pose proof (SLK_nonneg c Hc) as SL.
  pose proof (MS_nonneg mf Hm0) as MS0. pose proof (cntP_nbatch_nonneg c st) as [N1 N2].
  assert (CV : cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st) + c_count (get_cls st c) + c_num_freed (get_cls st c) <= mf c + SLK c).
  { destruct (Z_le_dec (cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st) + c_count (get_cls st c) + c_num_freed (get_cls st c)) (mf c + SLK c)) as [|NE]; [assumption| exfalso].
    assert (size_of_class c * (mf c + SLK c + 1) <= size_of_class c * (cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st) + c_count (get_cls st c) + c_num_freed (get_cls st c)))
      by (apply Z.mul_le_mono_nonneg_l; lia). nia. }
  unfold cls_lw, UCAP, FCAP, FCNT. unfold K_USER_MAP, K_FREEARR_MAP in *. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma HH_eq : forall st c, AINV ATOP [] [] st -> 1 <= c <= 31 ->
  HH c (get_cls st c) = size_of_class c * (cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st)).
Proof.
  intros st c HA Hc. pose proof HA as (HC & _). pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C10 & _). unfold HH, stk. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gsum_le : forall (f g : Z -> Z), (forall c, 1 <= c <= 31 -> f c <= g c) -> gsum f <= gsum g.
Proof.
  intros f g H. unfold gsum.
  assert (G : forall l, (forall x, In x l -> 1 <= x <= 31) -> fold_right (fun c acc => f c + acc) 0 l <= fold_right (fun c acc => g c + acc) 0 l).
  { induction l as [|x l IH]; intros Hl; cbn; [lia|]. pose proof (H x (Hl x (or_introl eq_refl))). specialize (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). lia. }
  apply G. intros x Hx. apply In_CLASSES. exact Hx.
Qed.
Lemma gsum_add : forall (f g : Z -> Z), gsum (fun c => f c + g c) = gsum f + gsum g.
Proof. intros f g. unfold gsum. induction CLASSES as [|x l IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma gsum_ext : forall (f g : Z -> Z), (forall c, 1 <= c <= 31 -> f c = g c) -> gsum f = gsum g.
Proof. intros f g H. pose proof (gsum_le f g ltac:(intros; rewrite H; auto; lia)). pose proof (gsum_le g f ltac:(intros; rewrite H; auto; lia)). lia. Qed.

(* [comment removed for export] *)
Lemma gsum_cntP : forall l, Forall (chunk_wf ATOP) l -> gsum (fun c => cntP c l) = nprim l.
Proof.
  induction l as [|ch l IH]; intros HW.
  - rewrite nprim_nonneg || idtac. unfold nprim. cbn [List.filter]. rewrite (@zlen_nil achunk).
    unfold gsum. induction CLASSES; cbn; [reflexivity|]. rewrite cntP_nil. lia.
  - apply Forall_cons_iff in HW as [Hch HW]. rewrite nprim_cons, <- (IH HW).
    rewrite (gsum_ext (fun c => cntP c (ch :: l)) (fun c => (if is_prim_of c ch then 1 else 0) + cntP c l)) by (intros; apply cntP_cons).
    rewrite gsum_add. f_equal.
    destruct ch as [c0 n0|mb ms n0]; cbn [is_primb is_prim_of].
    + cbn in Hch. destruct Hch as [Hn0 Hc0]. pose proof (primary_class_facts n0 ltac:(lia)) as PF.
      assert (HP : is_primary n0 = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia). specialize (PF HP). cbv zeta in PF. rewrite <- Hc0 in PF.
      destruct PF as (R1 & _). assert (Hc1 : 1 <= c0 <= 31) by lia.
      (* [comment removed for export] *)
      unfold gsum. assert (ND := NoDup_CLASSES). assert (IN : In c0 CLASSES) by (apply In_CLASSES; lia).
      revert ND IN. generalize CLASSES. induction l0 as [|x l0 IHl]; intros ND IN; [destruct IN|]. cbn. apply List.NoDup_cons_iff in ND as [Hni Hnd].
      destruct IN as [->|IN].
      * rewrite Z.eqb_refl. assert (Z0 : fold_right (fun c acc => (if c0 =? c then 1 else 0) + acc) 0 l0 = 0).
        { clear IHl. revert Hni Hnd. induction l0 as [|y l0 IH2]; intros Hni Hnd; cbn; [reflexivity|]. apply List.NoDup_cons_iff in Hnd as [Hni2 Hnd2].
          destruct (Z.eqb_spec c0 y) as [<-|NE]; [exfalso; apply Hni; left; reflexivity|]. rewrite IH2; [lia| | exact Hnd2]. intros F; apply Hni; right; exact F. }
        rewrite Z0. lia.
      * destruct (Z.eqb_spec c0 x) as [<-|NE]; [contradiction|]. rewrite (IHl Hnd IN). lia.
    + unfold gsum. induction CLASSES; cbn; [reflexivity|]. lia.
Qed.

Lemma gsum_nbatch : forall bs, gsum (fun c => nbatch c bs) = zlen bs.
Proof.
  intros bs. unfold gsum, nbatch.
  assert (H : forall l, List.NoDup l -> In K_BATCH_CLASS l -> fold_right (fun c acc => (if c =? K_BATCH_CLASS then zlen bs else 0) + acc) 0 l = zlen bs).
  { induction l as [|x l IH]; intros ND IN; [destruct IN|]. cbn. apply List.NoDup_cons_iff in ND as [Hni Hnd]. destruct IN as [->|IN].
    - rewrite Z.eqb_refl. assert (Z0 : fold_right (fun c acc => (if c =? K_BATCH_CLASS then zlen bs else 0) + acc) 0 l = 0).
      { clear IH. revert Hni Hnd. induction l as [|y l IH2]; intros Hni Hnd; cbn; [reflexivity|]. apply List.NoDup_cons_iff in Hnd as [Hni2 Hnd2].
        destruct (Z.eqb_spec y K_BATCH_CLASS) as [->|NE]; [exfalso; apply Hni; left; reflexivity|]. rewrite IH2; [lia| | exact Hnd2]. intros F; apply Hni; right; exact F. }
      rewrite Z0. lia.
    - destruct (Z.eqb_spec x K_BATCH_CLASS) as [->|NE]; [contradiction|]. rewrite (IH Hnd IN). lia. }
  apply H; [apply NoDup_CLASSES| apply In_CLASSES; unfold K_BATCH_CLASS; lia].
Qed.

Lemma nprimq_qchunks : forall bs, nprimq bs = nprim (qchunks bs) + zlen bs.
Proof. induction bs as [|b bs IH]; [cbn; rewrite (@zlen_nil abatch); unfold nprim; cbn; rewrite (@zlen_nil achunk); lia|]. cbn [nprimq]. rewrite qchunks_cons, nprim_app, zlen_cons, IH. lia. Qed.

(* [comment removed for export] *)
Lemma QT_bound : forall RESV st mo mf, INV RESV ATOP [] [] st mo -> GH mf st -> (forall c, 1 <= c <= 31 -> 0 <= mf c) ->
  forall c, 1 <= c <= 31 -> stk (get_cls st c) + QT st + 1 <= MS mf + 1.
Proof.
  intros RESV st mo mf HI HG Hm0 c Hc. pose proof HI as [HA HM]. pose proof HA as (HC & HW & _).
  (* [comment removed for export] *)
  assert (PC : forall c', 1 <= c' <= 31 -> cntP c' (qchunks (qbatches [] st)) + nbatch c' (qbatches [] st) + stk (get_cls st c') <= mf c' + SLK c' /\ 0 <= stk (get_cls st c')).
  { intros c' Hc'. pose proof (HC c' Hc') as X. unfold cls_inv in X. cbv zeta in X. destruct X as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
    destruct (HG c' Hc') as (G0 & G1 & G2). pose proof (size_of_class_pos c' Hc') as [S1 S2].
    unfold all_chunks in *. cbn [app] in *. rewrite cntP_app in C10, G1. pose proof (cntP_nonneg c' (live_chunks st)).
    unfold stk. split; [| lia].
    destruct (Z_le_dec (cntP c' (qchunks (qbatches [] st)) + nbatch c' (qbatches [] st) + (c_count (get_cls st c') + c_num_freed (get_cls st c'))) (mf c' + SLK c')) as [|NE]; [assumption| exfalso].
    assert (size_of_class c' * (mf c' + SLK c' + 1) <= size_of_class c' * (cntP c' (live_chunks st) + cntP c' (qchunks (qbatches [] st)) + nbatch c' (qbatches [] st) + c_count (get_cls st c') + c_num_freed (get_cls st c')))
      by (apply Z.mul_le_mono_nonneg_l; lia). nia. }
  assert (SUM : gsum (fun c' => cntP c' (qchunks (qbatches [] st)) + nbatch c' (qbatches [] st)) + gsum (fun c' => stk (get_cls st c')) <= MS mf).
  { unfold MS. rewrite <- gsum_add. apply gsum_le. intros c' Hc'. pose proof (PC c' Hc'). lia. }
  rewrite gsum_add, gsum_nbatch, gsum_cntP in SUM.
  2:{ unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [_ HW]. exact HW. }
  assert (QTE : QT st = nprim (qchunks (qbatches [] st)) + zlen (qbatches [] st)) by (unfold QT, qbatches; cbn [app]; apply nprimq_qchunks).
  pose proof (gsum_ge (fun c' => stk (get_cls st c')) c Hc ltac:(intros c' Hc'; exact (proj2 (PC c' Hc')))). cbv beta in H. lia.
Qed.

(* [comment removed for export] *)
Lemma CH_tight : forall AT pc st QB, AINV AT [] [] st -> live_budget_list (pc ++ live_chunks st) -> Forall (chunk_wf AT) pc ->
  bsum (qbatches [] st) <= QB -> 0 <= QB <= 2^31 ->
  zsum2 (CH pc [] st) <= LSBYTES + 12296 * SMAX + 2 * QB.
Proof.
  intros AT pc st QB HA (L1 & L2 & L3) HWpc HQ HQB.
  destruct HA as (HC & HW & HBW & _).
  unfold CH, all_chunks in *. cbn [app] in *. rewrite app_assoc, !secs_app, !zsum2_app.
  apply Forall_app in HW as [HWl HWq].
  assert (HWA : Forall (chunk_wf AT) (pc ++ live_chunks st)) by (apply Forall_app; split; assumption).
  destruct (secs_bounds (pc ++ live_chunks st) HWA) as (A1 & A2 & A3).
  destruct (secs_bounds _ HWq) as (Q1 & Q2 & Q3). pose proof (qchunks_secbytes _ HBW).
  rewrite secs_app, zsum2_app, zlen_app in *. unfold qbatches in *. cbn [app] in *.
  pose proof (zlen_nonneg (secs pc)). pose proof (zlen_nonneg (secs (live_chunks st))). pose proof (zlen_nonneg (secs (qchunks (a_qloc st ++ a_qglob st)))).
  unfold SMAX, HB in *. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition upd (mf : Z -> Z) (k : Z) : Z -> Z := fun c => if c =? k then mf c + 1 else mf c.

Lemma gsum_ind : forall k x, 1 <= k <= 31 -> gsum (fun c => if c =? k then x else 0) = x.
Proof.
  intros k x Hk. unfold gsum.
  assert (H : forall l, List.NoDup l -> In k l -> fold_right (fun c acc => (if c =? k then x else 0) + acc) 0 l = x).
  { induction l as [|y l IH]; intros ND IN; [destruct IN|]. cbn. apply List.NoDup_cons_iff in ND as [Hni Hnd]. destruct IN as [->|IN].
    - rewrite Z.eqb_refl. assert (Z0 : fold_right (fun c acc => (if c =? k then x else 0) + acc) 0 l = 0).
      { clear IH. revert Hni Hnd. induction l as [|z l IH2]; intros Hni Hnd; cbn; [reflexivity|]. apply List.NoDup_cons_iff in Hnd as [Hni2 Hnd2].
        destruct (Z.eqb_spec z k) as [->|NE]; [exfalso; apply Hni; left; reflexivity|]. rewrite IH2; [lia| | exact Hnd2]. intros F; apply Hni; right; exact F. }
      rewrite Z0. lia.
    - destruct (Z.eqb_spec y k) as [->|NE]; [contradiction|]. rewrite (IH Hnd IN). lia. }
  apply H; [apply NoDup_CLASSES| apply In_CLASSES; exact Hk].
Qed.

Lemma MS_upd : forall mf k, 1 <= k <= 31 -> MS (upd mf k) = MS mf + 1.
Proof.
  intros mf k Hk. unfold MS, upd.
  rewrite (gsum_ext (fun c => (if c =? k then mf c + 1 else mf c) + SLK c) (fun c => (mf c + SLK c) + (if c =? k then 1 else 0))) by (intros c Hc; destruct (c =? k); lia).
  rewrite gsum_add, gsum_ind by exact Hk. reflexivity.
Qed.

Lemma CBM_upd : forall mf k, 1 <= k <= 31 -> CBM (upd mf k) = CBM mf + size_of_class k + 128.
Proof.
  intros mf k Hk. unfold CBM. pose proof (MS_upd mf k Hk) as EM.
  rewrite (gsum_ext (fun c => UCAP (upd mf k) c + FCAP (upd mf k) c) (fun c => (UCAP mf c + FCAP mf c) + ((if c =? k then size_of_class k + 4 else 0) + 4))).
  2:{ intros c Hc. unfold UCAP, FCAP, FCNT. rewrite EM. unfold upd. destruct (Z.eqb_spec c k) as [->|NE]; lia. }
  rewrite (gsum_add (fun c => UCAP mf c + FCAP mf c) (fun c => (if c =? k then size_of_class k + 4 else 0) + 4)).
  rewrite (gsum_add (fun c => if c =? k then size_of_class k + 4 else 0) (fun _ => 4)).
  rewrite (gsum_ind k (size_of_class k + 4) Hk).
  assert (G4 : gsum (fun _ => 4) = 124) by (vm_compute; reflexivity). rewrite G4. lia.
Qed.

Lemma PHI_upd : forall mf k st, 1 <= k <= 31 -> PHI (upd mf k) st = PHI mf st + size_of_class k + 128.
Proof. intros. unfold ATsafeEv.PHI. rewrite CBM_upd by assumption. lia. Qed.

Lemma upd_ge : forall mf k c, mf c <= upd mf k c. Proof. intros. unfold upd. destruct (c =? k); lia. Qed.
Lemma GH_mono : forall mf mf' st, GH mf st -> (forall c, mf c <= mf' c) -> GH mf' st.
Proof.
  intros mf mf' st H HM c Hc. destruct (H c Hc) as (A & B & C). pose proof (HM c). pose proof (size_of_class_pos c Hc). split; [lia|]. split; [lia| nia].
Qed.
Lemma GH_nonneg : forall mf st, GH mf st -> forall c, 1 <= c <= 31 -> 0 <= mf c.
Proof. intros mf st H c Hc. exact (proj1 (H c Hc)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qbytes_AI : forall Y s mo, AI Y s mo -> bsum (qbatches [] (aps_m s)) <= Q_MAX + Q_CACHE.
Proof.
  intros Y s mo ((HA & _) & _ & Hq1 & Hq2 & _). unfold qbatches. cbn [app]. rewrite bsum_app.
  destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). lia.
Qed.

Lemma CH_now : forall Y s mo, AI Y s mo -> zsum2 (CH [] [] (aps_m s)) <= CHMAX.
Proof.
  intros Y s mo HAI. pose proof HAI as ((HA & HM) & _). pose proof (qbytes_AI _ _ _ HAI) as HQ.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LB).
  pose proof (CH_tight (aps_atop s) [] (aps_m s) (Q_MAX + Q_CACHE) HA ltac:(cbn [app]; apply (proj1 (live_budget_list_iff _)); exact LB) ltac:(constructor) HQ
                ltac:(unfold Q_MAX, Q_CACHE; lia)).
  unfold CHMAX. lia.
Qed.

(* [comment removed for export] *)
Lemma HLB_of_HISTOK : forall RESV Y st mo n, INV RESV ATOP [] [] st mo -> Permutation Y (live_pairs st) -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st).
Proof.
  intros RESV Y st mo n HI HPY Hn HH mb ms.
  set (dummy := mkch n 70368744177664 (sec_map_size n)).
  assert (Hwf : chunk_wf ATOP dummy).
  { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
    - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
    - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
      unfold KHIGH. unfold REQMAX in Hn. atop_facts. repeat split; try lia. }
  apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
  apply (live_budget_of_HISTOK (ATOP:=ATOP)).
  + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
    apply Forall_app in HW as [HWl _]. exact HWl.
  + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
    fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY.
Qed.

Lemma CH_next : forall Y s mo n, AI Y s mo -> aps_atop s = ATOP -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  zsum2 (CH [] [] (aps_m s)) + (if is_primary n then 0 else sec_map_size n) <= CHMAX.
Proof.
  intros Y s mo n HAI HAT Hn HH. pose proof HAI as ((HA & HM) & HPY & Hq1 & Hq2 & _). pose proof (qbytes_AI _ _ _ HAI) as HQ. rewrite HAT in HA, HM.
  pose proof (HLB_of_HISTOK _ Y _ mo n (conj HA HM) HPY Hn HH 70368744177664 (sec_map_size n)) as HLB.
  set (dummy := mkch n 70368744177664 (sec_map_size n)) in HLB.
  assert (Hwf : chunk_wf ATOP dummy).
  { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
    - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
    - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
      unfold KHIGH. unfold REQMAX in Hn. atop_facts. repeat split; try lia. }
  pose proof (CH_tight ATOP [dummy] (aps_m s) (Q_MAX + Q_CACHE) HA ltac:(cbn [app]; exact HLB) ltac:(constructor; [exact Hwf| constructor]) HQ
                ltac:(unfold Q_MAX, Q_CACHE; lia)) as HT.
  rewrite CH_cons, zsum2_app in HT. unfold CHMAX. unfold dummy, mkch in HT. destruct (is_primary n); cbn [sec_of zsum2 snd] in HT; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma JJ_acct : forall Y v RNG A s mo, JJ Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Proof.
  intros Y v RNG A s mo HJ. pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & G & k & mf & HQ & HAB & HGA & HBU & Hk & HGH & HB1 & HB2).
  pose proof HAI as ((HA & HM) & _). rewrite HAT in HM, HA.
  pose proof (LW_of_INV _ _ _ mf (conj HA HM) HGH (GH_nonneg _ _ HGH) HSB' HPA') as HL.
  pose proof (PHI_nonneg SB PA mf _ HL) as P0. pose proof (cpot_nonneg _ P0).
  pose proof (commit_bytes_LW SB PA mf _ HL) as CB.
  pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)) as NL. pose proof (CH_now _ _ _ HAI) as CHB.
  eapply (KI_acct_ok NMAX Abase NLK HLIM 0 G A k mo); [| lia].
  split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TS_alift : forall {R X} (t : AM R) (s : APS) RNG A mo (Q1 : postT R) (Q : postM (St:=APS) X) (f : R -> X * APS),
  TS RNG A (aembed ATOP t) mo (EQ Q1) ->
  (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 r RNG' A' mo' -> Q (fst (f r)) RNG' A' (snd (f r)) mo') ->
  TS RNG A (ebind (aembed ATOP t) (fun r => Ret (Ok (f r)))) mo (MQ Q).
Proof.
  intros R X t s RNG A mo Q1 Q f H HQ. eapply TS_ebind; [exact H|].
  intros r RNG' A' mo' HA H1. apply TS_ret_ok; [exact HA|]. cbn. apply HQ; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cnt_after_malloc : forall st st' ch c,
  a_live st' = <[a_next st := ch]> (a_live st) -> (a_live st) !! (a_next st) = None ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  cntP c (all_chunks [] [] st') = (if is_prim_of c ch then 1 else 0) + cntP c (all_chunks [] [] st)
  /\ nbatch c (qbatches [] st') = nbatch c (qbatches [] st).
Proof.
  intros st st' ch c Hl Hn Hq1 Hq2. unfold all_chunks, qbatches. cbn [app]. rewrite Hq1, Hq2. split; [|reflexivity].
  rewrite !cntP_app. unfold live_chunks. rewrite Hl.
  rewrite (cntP_perm c _ _ (Permutation_map snd (map_to_list_insert (a_live st) (a_next st) ch Hn))). cbn [map snd]. rewrite cntP_cons. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_malloc : forall Y v n,
  0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JJ Y v RNG A s mo /\ COSTM n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JJ ((q, n) :: Y) (v - COSTM n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HH. unfold amalloc_M.
  apply TSM_bind_get; [| intros RNG A s mo [HJ _]; eapply JJ_acct; exact HJ].
  intros s0.
  set (kc := class_id (needed_size n)).
  set (extra := if is_primary n then 0 else sec_map_size n).
  eapply TSM_bind with (Q1 := fun x RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX /\ COSTM n <= v /\
     exists G' b' k' mf, let mf' := (if is_primary n then upd mf kc else mf) in
        RPm SB PA mf' (aps_m s0) (mrel n) G' b' x /\ malloc_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) n x mo /\ minv (strip mo) /\ m_halted mo = None
        /\ KI b' G' A k' mo /\ 4096 * k' + cpot b' + (v - COSTM n) <= 4096 * NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A
        /\ GH mf (aps_m s0) /\ AINV ATOP [] [] (aps_m s0)
        /\ 8 * (EAGER0 + CBM mf' + CHMAX) + (v - COSTM n) <= 8 * NLK).
  - (* [comment removed for export] *)
    intros RNG A s mo (-> & HJ & Hnv). destruct s0 as [st so RESV atp cl].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & G & k & mf & HQ & HAB & HGA & HBU & Hk & HGH & HB1 & HB2).
    cbn [aps_m] in HSB', HPA', HQ, HGH, HB2. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    pose proof HI as [HA HM]. pose proof (GH_nonneg _ _ HGH) as Hm0.
    pose proof (primary_class_facts n ltac:(lia)) as PCF.
    assert (Hkc : is_primary n = true -> 1 <= kc <= 31) by (intros EP; specialize (PCF EP); cbv zeta in PCF; subst kc; lia).
    set (mf' := if is_primary n then upd mf kc else mf).
    assert (Hm0' : forall c, 1 <= c <= 31 -> 0 <= mf' c) by (intros c Hc; subst mf'; pose proof (Hm0 c Hc); destruct (is_primary n); [unfold upd; destruct (c =? kc)|]; lia).
    assert (HGH' : GH mf' st) by (subst mf'; destruct (is_primary n); [eapply GH_mono; [exact HGH| intros; apply upd_ge]| exact HGH]).
    assert (DCBM : CBM mf' = CBM mf + (if is_primary n then size_of_class kc + 128 else 0)).
    { subst mf'. destruct (is_primary n) eqn:EP; [rewrite CBM_upd by (apply Hkc; reflexivity); lia| lia]. }
    assert (DPHI : PHI mf' st = PHI mf st + (if is_primary n then size_of_class kc + 128 else 0)) by (unfold ATsafeEv.PHI; rewrite DCBM; lia).
    (* [comment removed for export] *)
    assert (Hex : 0 <= extra <= 2^31 /\ (is_primary n = false -> 64512 < n /\ sec_map_size n = extra)).
    { subst extra. destruct (is_primary n) eqn:EP; [lia|]. pose proof (not_primary_large n ltac:(lia) EP).
      pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)). unfold REQMAX in Hn. lia. }
    assert (HCOST : 8 * (if is_primary n then size_of_class kc + 128 else 0) <= COSTM n
                    /\ 4096 * gcost (if is_primary n then [] else [sec_map_size n]) + cpot (PHI mf' st + extra) <= cpot (PHI mf st) + COSTM n).
    { pose proof (LW_of_INV _ _ _ mf HI HGH Hm0 HSB' HPA') as HL0. pose proof (PHI_nonneg SB PA mf _ HL0) as P0.
      rewrite DPHI. unfold COSTM. subst extra kc. destruct (is_primary n) eqn:EP.
      - cbn [gcost]. pose proof (size_of_class_pos (class_id (needed_size n)) (Hkc eq_refl)) as [S1 S2]. unfold COSTP, cpot.
        pose proof (Z.div_mod (7 * PHI mf st) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * PHI mf st) 32 ltac:(lia)).
        pose proof (Z.div_mod (7 * (PHI mf st + (size_of_class (class_id (needed_size n)) + 128) + 0)) 32 ltac:(lia)).
        pose proof (Z.mod_pos_bound (7 * (PHI mf st + (size_of_class (class_id (needed_size n)) + 128) + 0)) 32 ltac:(lia)). lia.
      - cbn [gcost]. destruct Hex as [_ HX]. destruct (HX eq_refl) as [NL ES]. pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)) as SBn.
        unfold COSTS, pcost, cpot. set (M := sec_map_size n) in *.
        pose proof (Z.div_mod (7 * PHI mf st) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * PHI mf st) 32 ltac:(lia)).
        pose proof (Z.div_mod (7 * (PHI mf st + 0 + M)) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (PHI mf st + 0 + M)) 32 ltac:(lia)).
        pose proof (Z.div_mod M 4096 ltac:(lia)). pose proof (Z.mod_pos_bound M 4096 ltac:(lia)).
        pose proof (Z.div_mod M 32768 ltac:(lia)). pose proof (Z.mod_pos_bound M 32768 ltac:(lia)).
        pose proof (Z.div_mod M 8 ltac:(lia)). pose proof (Z.mod_pos_bound M 8 ltac:(lia)).
        pose proof (Z.div_mod M 4 ltac:(lia)). pose proof (Z.mod_pos_bound M 4 ltac:(lia)). lia. }
    destruct HCOST as [HC1 HC2].
    (* [comment removed for export] *)
    pose proof (LW_of_INV _ _ _ mf' HI HGH' Hm0' HSB' HPA') as HL.
    pose proof (PHI_nonneg SB PA mf' _ HL) as P0'.
    pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)) as NL0. pose proof (CH_next _ _ _ n HAI eq_refl Hn HH) as CHB. cbn [aps_m] in CHB.
    assert (HK : KI (PHI mf' st + extra) G A k mo).
    { split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold ATsafeEv.PHI in *; subst extra; lia|].
      split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk]. }
    assert (HNF : next_fresh st) by (destruct HA as (_ & _ & _ & _ & _ & _ & _ & NF & _); exact NF).
    eapply (TS_alift (amalloc ATOP RESV st n) (mkAPS st so RESV ATOP cl) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP cl))).
    + eapply (TS_aembed NMAX SB PA Abase NLK HLIM (amalloc ATOP RESV st n) (RPm SB PA mf' st (mrel n))
                (fun r mo' => malloc_post st n r mo' /\ FR mo mo') _ G _ A k (4096 * NMAXZ - (v - COSTM n)) mo).
      * apply atotal_FR. apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)). eapply HLB_of_HISTOK; eauto.
      * subst extra. apply (evq_amalloc SB PA mf' Hm0'); [exact HL| exact HQ| exact HNF| lia|].
        intros EP. cbv zeta. subst mf' kc. rewrite EP. rewrite (HH_eq _ _ HA (Hkc EP)).
        destruct (HGH _ (Hkc EP)) as (_ & G1 & _). unfold upd. rewrite Z.eqb_refl.
        pose proof (size_of_class_pos _ (Hkc EP)). nia.
      * exact HK.
      * destruct (is_primary n); constructor; [lia| constructor].
      * subst extra. pose proof (cpot_nonneg _ P0'). lia.
      * lia.
    + intros r RNG' A' mo' HA' HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hnv|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k', mf. cbv zeta. fold kc. fold mf'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact HGH|]. split; [exact HA|]. rewrite DCBM. lia.
  - (* [comment removed for export] *)
    intros x. eapply TSM_bind; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|].
    intros []. apply TSM_ret. intros RNG A s mo (HA & s1 & -> & _ & -> & HAT0 & HP). split; [exact HA|].
    destruct HP as (HPY & Hq1 & Hq2 & Hnv & G' & b' & k' & mf & HRP & HMP & Hmi & Hh & HK & Hkv & -> & HGH & HI0 & HB1).
    cbv zeta in HRP, HB1.
    destruct s0 as [st so RESV atp cl]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv] in HMP, HRP, HPY, Hq1, Hq2, HGH, HI0.
    destruct x as [st' op]. destruct HMP as (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4). cbn [fst snd] in *.
    subst op. exists (a_next st). split; [reflexivity|]. split; [| unfold REQMAX in Hn; lia].
    destruct HRP as (HL' & HQ' & HREL & HPB). pose proof HK as (_ & Hb' & _ & HAB & HGA & HBU & Hk0).
    set (mf' := if is_primary n then upd mf kc else mf) in *.
    assert (Hkc : is_primary n = true -> 1 <= kc <= 31).
    { intros EP. pose proof (primary_class_facts n ltac:(lia) EP) as PCF. cbv zeta in PCF. subst kc. lia. }
    (* [comment removed for export] *)
    pose proof HI2 as [HA2 HM2].
    assert (WF2 : chunk_wf ATOP ch).
    { destruct HA2 as (_ & HW2 & _). unfold all_chunks, live_chunks in HW2. cbn [app] in HW2. rewrite Hlive in HW2.
      apply Forall_app in HW2 as [HW2 _]. eapply (proj1 (Forall_forall _ _) HW2). apply in_map_iff. exists (a_next st, ch). split; [reflexivity|].
      apply list_elem_of_In. apply elem_of_map_to_list. apply lookup_insert_eq. }
    assert (CNT : forall c, 1 <= c <= 31 -> cntP c (all_chunks [] [] st') + nbatch c (qbatches [] st')
                                          = (if is_primary n then (if c =? kc then 1 else 0) else 0) + (cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st))).
    { intros c Hc. destruct (cnt_after_malloc st st' ch c Hlive Hnone Eq3 Eq4) as [-> ->].
      destruct ch as [c0 n0|mb ms n0]; cbn [is_prim_of]; cbn in Hsz; subst n0.
      - cbn in WF2. destruct WF2 as [Hn0 Hc0]. assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
        rewrite EP. subst kc. rewrite <- Hc0. rewrite (Z.eqb_sym c c0). lia.
      - cbn in WF2. destruct WF2 as (Hn0 & _). rewrite (large_not_primary n ltac:(lia)). lia. }
    split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [lia|]]]]]].
    + (* [comment removed for export] *)
      unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split.
      * unfold live_pairs. rewrite Hlive.
        eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
        cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
      * rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
    + exists G', k', mf'. cbn [aps_m aset_m]. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0|]. split; [| split; [exact HB1|]].
      * (* [comment removed for export] *)
        intros c Hc. destruct (HGH c Hc) as (G0 & G1 & G2). pose proof (size_of_class_pos c Hc) as [S1 S2]. pose proof (SLK_nonneg c Hc) as SL. rewrite (CNT c Hc).
        unfold mrel in HREL. subst mf' kc. destruct (is_primary n) eqn:EP.
        -- unfold upd. destruct HREL as (RO & RH & RA & RD & RS). destruct (Z.eqb_spec c (class_id (needed_size n))) as [->|NE].
           ++ split; [lia|]. split; [lia|]. rewrite (HH_eq _ _ HI0 (Hkc eq_refl)) in RD. destruct RD as [RD|RD]; [rewrite RD; nia| nia].
           ++ rewrite (RO c NE). split; [lia|]. split; [lia| exact G2].
        -- rewrite (HREL c). split; [lia|]. split; [lia| exact G2].
      * (* [comment removed for export] *)
        pose proof (cpot_mono (PHI mf' st') b' ltac:(split; [apply (PHI_nonneg SB PA mf'); exact HL'| exact HPB])). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_free : forall Y v q n,
  TSM (fun RNG A s mo => JJ ((q, n) :: Y) v RNG A s mo /\ COSTF <= v) (afree_M q) (fun _ RNG A s mo => JJ Y (v - COSTF) RNG A s mo).
Proof.
  intros Y v q n. unfold afree_M.
  apply TSM_bind_get; [| intros RNG A s mo [HJ _]; eapply JJ_acct; exact HJ].
  intros s0.
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\ COSTF <= v /\
     exists G' b' k' mf, let mf' := upd mf K_BATCH_CLASS in
        RPst SB PA mf' (aps_m s0) frel G' b' st' /\ free_post (RESV:=aps_resv s0) (ATOP:=ATOP) (aps_m s0) q st' mo /\ minv (strip mo) /\ m_halted mo = None
        /\ KI b' G' A k' mo /\ 4096 * k' + cpot b' + (v - COSTF) <= 4096 * NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A
        /\ GH mf (aps_m s0) /\ AINV ATOP [] [] (aps_m s0)
        /\ 8 * (EAGER0 + CBM mf' + CHMAX) + (v - COSTF) <= 8 * NLK
        /\ Permutation ((q, n) :: Y) (live_pairs (aps_m s0))).
  - intros RNG A s mo (-> & HJ & Hnv). destruct s0 as [st so RESV atp cl].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & G & k & mf & HQ & HAB & HGA & HBU & Hk & HGH & HB1 & HB2).
    cbn [aps_m] in HSB', HPA', HQ, HGH, HB2. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    pose proof HI as [HA HM]. pose proof (GH_nonneg _ _ HGH) as Hm0. pose proof batch_K as HK24.
    assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    set (mf' := upd mf K_BATCH_CLASS).
    assert (Hm0' : forall c, 1 <= c <= 31 -> 0 <= mf' c) by (intros c Hc; subst mf'; pose proof (Hm0 c Hc); unfold upd; destruct (c =? K_BATCH_CLASS); lia).
    assert (HGH' : GH mf' st) by (subst mf'; eapply GH_mono; [exact HGH| intros; apply upd_ge]).
    assert (DCBM : CBM mf' = CBM mf + size_of_class K_BATCH_CLASS + 128) by (subst mf'; apply CBM_upd; exact HK24).
    assert (DPHI : PHI mf' st = PHI mf st + size_of_class K_BATCH_CLASS + 128) by (unfold ATsafeEv.PHI; rewrite DCBM; lia).
    assert (S24 : size_of_class K_BATCH_CLASS = 8192) by (vm_compute; reflexivity).
    pose proof (LW_of_INV _ _ _ mf HI HGH Hm0 HSB' HPA') as HL0. pose proof (PHI_nonneg SB PA mf _ HL0) as P0.
    pose proof (LW_of_INV _ _ _ mf' HI HGH' Hm0' HSB' HPA') as HL. pose proof (PHI_nonneg SB PA mf' _ HL) as P0'.
    pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)) as NL0. pose proof (CH_now _ _ _ HAI) as CHB. cbn [aps_m] in CHB.
    assert (HC : 8 * (size_of_class K_BATCH_CLASS + 128) <= COSTF /\ cpot (PHI mf' st + 0) <= cpot (PHI mf st) + COSTF).
    { rewrite DPHI, S24. unfold COSTF, COSTP, cpot. rewrite S24.
      pose proof (Z.div_mod (7 * PHI mf st) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * PHI mf st) 32 ltac:(lia)).
      pose proof (Z.div_mod (7 * (PHI mf st + 8192 + 128 + 0)) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (PHI mf st + 8192 + 128 + 0)) 32 ltac:(lia)). lia. }
    destruct HC as [HC1 HC2].
    assert (HK : KI (PHI mf' st + 0) G A k mo).
    { split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold ATsafeEv.PHI in *; lia|].
      split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk]. }
    eapply (TS_alift (afree st (Some q)) (mkAPS st so RESV ATOP cl) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP cl))).
    + eapply (TS_aembed NMAX SB PA Abase NLK HLIM (afree st (Some q)) (RPst SB PA mf' st frel)
                (fun st' mo' => free_post (RESV:=RESV) (ATOP:=ATOP) st q st' mo' /\ FR mo mo') [] G _ A k (4096 * NMAXZ - (v - COSTF)) mo).
      * apply atotal_FR. eapply (afree_core (ATOP:=ATOP)); eauto.
      * apply (evq_afree SB PA mf' Hm0'); [exact HL| exact HQ| |].
        -- rewrite (HH_eq _ _ HA HK24). destruct (HGH _ HK24) as (_ & G1 & _). subst mf'. unfold upd. rewrite Z.eqb_refl. rewrite S24 in *. lia.
        -- intros c Hc. pose proof (QT_bound _ _ _ mf HI HGH Hm0 c Hc). subst mf'. rewrite MS_upd by exact HK24. lia.
      * exact HK.
      * constructor.
      * cbn [gcost]. lia.
      * lia.
    + intros r RNG' A' mo' HA' HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hnv|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k', mf. cbv zeta. fold mf'. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact HGH|]. split; [exact HA|]. split; [rewrite DCBM; lia| exact HPY].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & Hnv & HP).
    destruct HP as (G' & b' & k' & mf & HRP & HFP & Hmi & Hh & HK & Hkv & -> & HGH & HA0 & HB1 & HPY).
    cbv zeta in HRP, HB1.
    destruct s0 as [st so RESV atp cl]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HFP, HPY, HRP, HGH, HA0.
    destruct HFP as (HI2 & Hlive & Hnext & Hq1' & Hq2').
    destruct HRP as (HL' & HQ' & HREL & HPB). pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
    set (mf' := upd mf K_BATCH_CLASS) in *. pose proof batch_K as HK24.
    assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    pose proof HI2 as [HA2 HM2].
    split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [lia|]]]]]].
    * unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split.
      -- unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
         eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
         change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
           with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
         apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
      -- split; [exact Hq1'|]. split; [exact Hq2'|]. split; [exact Hmi| exact Hh].
    * exists G', k', mf'. cbn [aps_m aset_m]. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0|]. split; [| split; [exact HB1|]].
      -- (* [comment removed for export] *)
         intros c Hc. destruct (HGH c Hc) as (G0 & G1 & G2). pose proof (size_of_class_pos c Hc) as [S1 S2]. pose proof (SLK_nonneg c Hc) as SL.
         destruct (HREL c Hc) as (R1 & R2 & R3).
         rewrite (HH_eq _ _ HA2 Hc) in R1. rewrite (HH_eq _ _ HA0 Hc) in R1, R3.
         assert (E' : mf' c = mf c + (if c =? K_BATCH_CLASS then 1 else 0)) by (subst mf'; unfold upd; destruct (c =? K_BATCH_CLASS); lia).
         split; [destruct (c =? K_BATCH_CLASS); lia|]. split.
         ++ destruct (Z_le_dec (cntP c (all_chunks [] [] st') + nbatch c (qbatches [] st')) (mf' c)) as [|NE]; [assumption| exfalso].
            assert (size_of_class c * (mf' c + 1) <= size_of_class c * (cntP c (all_chunks [] [] st') + nbatch c (qbatches [] st'))) by (apply Z.mul_le_mono_nonneg_l; lia).
            rewrite E' in *. destruct (c =? K_BATCH_CLASS); nia.
         ++ destruct R3 as [R3|[-> R3]]; [rewrite R3; rewrite E'; destruct (c =? K_BATCH_CLASS); nia|].
            rewrite E', Z.eqb_refl. nia.
      -- pose proof (cpot_mono (PHI mf' st') b' ltac:(split; [apply (PHI_nonneg SB PA mf'); exact HL'| exact HPB])). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_annot : forall Y v q cap old new,
  In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  TSM (JJ Y v) (aannot_M q cap old new) (fun _ RNG A s mo => JJ Y v RNG A s mo).
Proof.
  intros Y v q cap old new Hin Hold Hnew Hmin. unfold aannot_M.
  apply TSM_bind_get; [| intros RNG A s mo HJ; eapply JJ_acct; exact HJ].
  intros s0.
  eapply TSM_bind with (Q1 := fun st' RNG A s mo => s = s0 /\ aps_atop s0 = ATOP /\
     exists G' b' k' mf, RPst SB PA mf (aps_m s0) crel_n G' b' st' /\ (st' = aps_m s0 /\ INV (aps_resv s0) (aps_atop s0) [] [] (aps_m s0) mo) /\ minv (strip mo) /\ m_halted mo = None
                      /\ KI b' G' A k' mo /\ 4096 * k' + cpot b' + v <= 4096 * NMAXZ /\ RNG = fp_ok (m_vm_lazy mo) A /\ 0 <= v
                      /\ GH mf (aps_m s0) /\ 8 * (EAGER0 + CBM mf + CHMAX) + v <= 8 * NLK
                      /\ Permutation Y (live_pairs (aps_m s0)) /\ a_qloc_bytes (aps_m s0) <= Q_CACHE /\ a_qglob_bytes (aps_m s0) <= Q_MAX).
  - intros RNG A s mo (-> & HJ). destruct s0 as [st so RESV atp cl].
    pose proof HJ as (HAI & HAT & -> & HSB' & HPA' & Hv & G & k & mf & HQ & HAB & HGA & HBU & Hk & HGH & HB1 & HB2).
    cbn [aps_m] in HSB', HPA', HQ, HGH, HB2. cbn [aps_atop] in HAT. subst atp. unfold alift. cbn [aps_m aps_resv aps_atop].
    pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_resv aps_atop] in HI, HPY, Hq1, Hq2.
    pose proof HI as [HA HM]. pose proof (GH_nonneg _ _ HGH) as Hm0.
    assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
    destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
    pose proof (LW_of_INV _ _ _ mf HI HGH Hm0 HSB' HPA') as HL. pose proof (PHI_nonneg SB PA mf _ HL) as P0.
    pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)) as NL0. pose proof (CH_now _ _ _ HAI) as CHB. cbn [aps_m] in CHB.
    assert (HK : KI (PHI mf st + 0) G A k mo).
    { split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold ATsafeEv.PHI in *; lia|].
      split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk]. }
    eapply (TS_alift (aannotate st q cap old new) (mkAPS st so RESV ATOP cl) _ A mo _ _ (fun r => (r, mkAPS st so RESV ATOP cl))).
    + eapply (TS_aembed NMAX SB PA Abase NLK HLIM (aannotate st q cap old new) (RPst SB PA mf st crel_n)
                (fun st' mo' => (st' = st /\ INV RESV ATOP [] [] st mo') /\ FR mo mo') [] G _ A k (4096 * NMAXZ - v) mo).
      * apply atotal_FR. eapply (aannotate_core RESV ATOP); eauto.
      * eapply (evq_aannotate SB PA mf); [exact HL| exact HQ| exact Hl| lia].
      * exact HK.
      * constructor.
      * cbn [gcost]. replace (PHI mf st + 0) with (PHI mf st) by lia. lia.
      * lia.
    + intros r RNG' A' mo' HA' HP. cbn [fst snd aps_m aps_atop]. split; [reflexivity|]. split; [reflexivity|].
      destruct HP as (G' & b' & k' & H1 & [H2 HF] & H3 & H4 & H5 & H6).
      exists G', b', k', mf. split; [exact H1|]. split; [exact H2|].
      destruct HF as (F1 & _ & _ & F4). split; [apply F1; exact Hmi|]. split; [rewrite F4; exact Hh|].
      split; [exact H3|]. split; [lia|]. split; [exact H6|]. split; [exact Hv|]. split; [exact HGH|]. split; [exact HB1|]. split; [exact HPY|]. split; [exact Hq1| exact Hq2].
  - intros st'. eapply TSM_post; [apply TSM_upd; intros RNG A s mo [HA _]; exact HA|]. cbv beta.
    intros [] RNG A s mo HA (s1 & -> & _ & -> & HAT0 & HP).
    destruct HP as (G' & b' & k' & mf & HRP & [-> HI2] & Hmi & Hh & HK & Hkv & -> & Hv & HGH & HB1 & HPY & Hq1 & Hq2).
    destruct s0 as [st so RESV atp cl]. cbn [aps_atop] in HAT0. subst atp. cbn [aps_m aps_resv aps_atop] in HI2, HPY, Hq1, Hq2, HRP, HGH.
    destruct HRP as (HL' & HQ' & _ & HPB). pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
    split; [| split; [reflexivity| split; [reflexivity| split; [exact (proj1 HL')| split; [exact (proj1 (proj2 HL'))| split; [exact Hv|]]]]]].
    * unfold AI. cbn [aps_m aset_m aps_so aps_resv aps_atop]. split; [exact HI2|]. split; [exact HPY|].
      split; [exact Hq1|]. split; [exact Hq2|]. split; [exact Hmi| exact Hh].
    * exists G', k', mf. cbn [aps_m aset_m]. split; [exact HQ'|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU|]. split; [exact Hk0|]. split; [exact HGH|]. split; [exact HB1|].
      pose proof (cpot_mono (PHI mf st) b' ltac:(split; [apply (PHI_nonneg SB PA mf); exact HL'| exact HPB])). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma JJ_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JJ Y v RNG A s mo -> JJ Y' v RNG A s mo.
Proof. intros Y Y' v RNG A s mo HP (HAI & H). split; [eapply AI_perm; [exact HP| exact HAI]| exact H]. Qed.

Lemma JJ_so : forall Y v RNG A s mo w, JJ Y v RNG A s mo -> JJ Y v RNG A (aset_so w s) mo.
Proof. intros Y v RNG A [st so RESV atp cl] mo w (HAI & H). split; [apply AI_so; exact HAI| exact H]. Qed.

Lemma JJ_cl : forall Y v RNG A s mo w, JJ Y v RNG A s mo -> JJ Y v RNG A (aset_cl w s) mo.
Proof. intros Y v RNG A [st so RESV atp cl] mo w (HAI & H). split; [apply AI_cl; exact HAI| exact H]. Qed.

Lemma JJ_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JJ Y v RNG A s mo -> JJ Y v' RNG A s mo.
Proof.
  intros Y v v' RNG A s mo Hv (HAI & HAT & HR & HSB' & HPA' & _ & G & k & mf & HQ & HAB & HGA & HBU & Hk & HGH & HB1 & HB2).
  split; [exact HAI|]. split; [exact HAT|]. split; [exact HR|]. split; [exact HSB'|]. split; [exact HPA'|]. split; [lia|].
  exists G, k, mf. repeat (split; [assumption|]). split; lia.
Qed.

Lemma JJ_nonneg : forall Y v RNG A s mo, JJ Y v RNG A s mo -> 0 <= v.
Proof. intros Y v RNG A s mo (_ & _ & _ & _ & _ & Hv & _). exact Hv. Qed.

Lemma AMI_with_tid : forall RESV atop ch st t mo, AMI RESV atop ch st (with_tid t mo) <-> AMI RESV atop ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.

Lemma JJ_model : forall Y v RNG A s mo, JJ Y v RNG A s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y v RNG A s mo (HAI & _). exact (AI_model _ _ _ HAI). Qed.

(* [comment removed for export] *)
Lemma JJ_io : forall n Y v RNG A s mo rsp mo' evs,
  io_node n -> nstep n mo rsp mo' evs -> JJ Y v RNG A s mo -> JJ Y v RNG A s mo'.
Proof.
  intros n Y v RNG A s mo rsp mo' evs Hio Hst HJ.
  pose proof HJ as (HAI & HAT & HR & Hrest). pose proof (AI_model _ _ _ HAI) as [HMA Hh].
  destruct (asan_ok_MI2 n mo rsp mo' evs Hst Hio HMA Hh) as [HMA' Hh']. pose proof (proj1 HMA') as Hmi'.
  destruct (nstep_io_shape n mo rsp mo' evs Hio Hst) as [-> | [(f & ->) | (t & ->)]].
  - exact HJ.
  - split; [apply AI_fds; [exact HAI| exact HMA'| exact Hh']|]. split; [exact HAT|]. split; [exact HR| exact Hrest].
  - split; [| split; [exact HAT| split; [exact HR| exact Hrest]]].
    destruct s as [st so RESV atp cl]. destruct HAI as ([HA HM] & HP & Hq1 & Hq2 & _). unfold AI. cbn [aps_m aps_resv aps_atop] in *.
    split; [split; [exact HA| apply AMI_with_tid; exact HM]|]. split; [exact HP|]. split; [exact Hq1|]. split; [exact Hq2|].
    split; [exact Hmi'| exact Hh'].
Qed.
End OpsM.
End CANSEC1.
