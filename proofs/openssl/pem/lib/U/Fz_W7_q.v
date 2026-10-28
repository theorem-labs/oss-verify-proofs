(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun KStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_W1_defs Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_lems.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_f Fz_W7_w Fz_W7_p.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_app_intro : forall (l1 l2 : list bptr), List.NoDup l1 -> List.NoDup l2 -> (forall q, In q l1 -> ~ In q l2) -> List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 N1 N2 D; [exact N2|]. cbn [app]. inversion N1; subst. constructor.
  - intros X. apply in_app_iff in X. destruct X as [X|X]; [contradiction| exact (D a ltac:(left; reflexivity) X)].
  - apply IH; [assumption| exact N2| intros q Hq; exact (D q ltac:(right; exact Hq))].
Qed.

Lemma nodup_blocks_of_ids : forall (l : list block), List.NoDup (map blk_id l) -> List.NoDup l.
Proof. intros l H. exact (NoDup_map_inv _ _ H). Qed.

(* [comment removed for export] *)
Lemma cl_own_length `{CE__ : Ceiling} `{RN__ : RunRnd} : forall LBall LB (L : @clist bptr),
  cl_own LBall LB L -> length LBall = (length L + length LB)%nat.
Proof.
  intros LBall LB L (CLB & HP & HM). rewrite (Permutation_length HP), length_app.
  rewrite <- (length_map blk_id CLB), HM, length_map. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mbio_ids `{CE__ : Ceiling} `{RN__ : RunRnd} : forall (m : mem) LBall L K BI meth len max off q,
  mbio_rep m LBall L K BI meth len max off -> mbio_T K q -> In q (map blk_id LBall).
Proof.
  intros m LBall L K BI meth len max off q [BM MB] Tq.
  destruct MB as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DOPT).
  destruct Tq as [->|[->|[->|[->|KD]]]].
  - apply in_map_iff. exists (k_bi K, BI, 128). split; [reflexivity| exact (proj1 OWNB)].
  - apply in_map_iff. exists (k_bb K, BB, 16). split; [reflexivity| exact (proj1 OWNbb)].
  - apply in_map_iff. exists (k_bm K, BM, 32). split; [reflexivity| exact (proj1 OWNbm)].
  - apply in_map_iff. exists (k_rp K, RP, 32). split; [reflexivity| exact (proj1 OWNrp)].
  - rewrite KD in DOPT. destruct DOPT as (D & nm & junk & OWND & _). apply in_map_iff. exists (q, D, max). split; [reflexivity| exact (proj1 OWND)].
Qed.

(* [comment removed for export] *)
Lemma cells4 `{CE__ : Ceiling} `{RN__ : RunRnd} : forall (m : mem) A (a b c d : word),
  rw_cells usegs m A [C8 a] -> rw_cells usegs m (A + 8) [C8 b] -> rw_cells usegs m (A + 16) [C8 c] -> rw_cells usegs m (A + 24) [C8 d] ->
  rw_cells usegs m A [C8 a; C8 b; C8 c; C8 d].
Proof.
  intros m A a b c d Ha Hb Hc Hd.
  apply (proj2 (rw_cells_app usegs m A [C8 a] [C8 b; C8 c; C8 d])). split; [exact Ha|]. cbn [cells_size csize Nat.add]. replace (Z.of_nat 8) with 8 by reflexivity.
  apply (proj2 (rw_cells_app usegs m (A + 8) [C8 b] [C8 c; C8 d])). split; [exact Hb|]. cbn [cells_size csize Nat.add]. replace (Z.of_nat 8) with 8 by reflexivity.
  replace (A + 8 + 8) with (A + 16) by lia.
  apply (proj2 (rw_cells_app usegs m (A + 16) [C8 c] [C8 d])). split; [exact Hc|]. cbn [cells_size csize Nat.add]. replace (Z.of_nat 8) with 8 by reflexivity.
  replace (A + 16 + 8) with (A + 24) by lia. exact Hd.
Qed.

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  (* [comment removed for export] *)
  Lemma perm_after_call : forall s LB2 LB L2 m2 sp2 tp lo B s3 LB3 L3 m3 sp3 (ADD L0 : @clist bptr) (NEW : list block),
    cstate s LB2 LB L2 m2 sp2 tp lo B -> cstate s3 LB3 LB L3 m3 sp3 tp lo B ->
    Permutation L2 (ADD ++ L0) ->
    (forall b, In b LB3 <-> In b LB2 \/ In b NEW) -> (forall b, In b NEW -> ~ In (blk_id b) (map blk_id LB2)) -> List.NoDup (map blk_id NEW) ->
    (forall q nm, In (q, nm) L2 -> In (q, nm) L3) -> (forall b, In b NEW -> In (blk_id b, blk_size b) L3) ->
    Permutation L3 ((ADD ++ bents NEW) ++ L0).
  Proof.
    intros s LB2 LB L2 m2 sp2 tp lo B s3 LB3 L3 m3 sp3 ADD L0 NEW CST2 CST3 PERM2 LBIFF FRESH NDN LINCL NEWL.
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [NDB2 NDL2]. pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [NDB3 NDL3].
    pose proof CST2 as (_ & CO2 & _). pose proof CST3 as (_ & CO3 & _).
    (* [comment removed for export] *)
    assert (IDS2 : forall q, In q (map fst L2) -> In q (map blk_id LB2)).
    { intros q Hq. destruct CO2 as (CLB & HP & HM). rewrite <- HM in Hq.
      eapply Permutation_in; [apply Permutation_map; apply Permutation_sym; exact HP|]. rewrite map_app. apply in_or_app. left. exact Hq. }
    (* [comment removed for export] *)
    assert (PT : Permutation ((ADD ++ bents NEW) ++ L0) (bents NEW ++ L2)).
    { rewrite <- app_assoc. eapply perm_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_sym. exact PERM2. }
    eapply perm_trans; [| apply Permutation_sym; exact PT].
    apply pigeonhole.
    - exact NDL3.
    - rewrite map_app, map_fst_bents. apply nodup_app_intro; [exact NDN| exact NDL2|].
      intros q Hq HL. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). exact (FRESH b Hb (IDS2 _ HL)).
    - intros [q nm] He. apply in_app_iff in He. destruct He as [He|He].
      + apply in_bents in He. destruct He as (b & Hb & <- & <-). exact (NEWL b Hb).
      + exact (LINCL q nm He).
    - (* [comment removed for export] *)
      pose proof (cl_own_length _ _ _ CO2) as LEN2. pose proof (cl_own_length _ _ _ CO3) as LEN3.
      assert (PB : Permutation LB3 (LB2 ++ NEW)).
      { apply Permutation.NoDup_Permutation.
        - exact (nodup_blocks_of_ids _ NDB3).
        - apply nodup_blocks_of_ids. rewrite map_app. apply nodup_app_intro; [exact NDB2| exact NDN|].
          intros q Hq HN. apply in_map_iff in HN. destruct HN as (b & <- & Hb). exact (FRESH b Hb Hq).
        - intros x. rewrite in_app_iff. exact (LBIFF x). }
      pose proof (Permutation_length PB) as LENB. rewrite length_app in LENB. rewrite length_app, length_bents. lia.
  Qed.

  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Local Notation w7_comI := (w7_com libenv).
  Local Notation f7_invI := (f7_inv libenv errst_live).
  Local Notation pw_invI := (pw_inv libenv errst_live).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w7_pem_step : forall en st2 LB2 L2 m2 K BI blen bmax st3 LB3 L3 m3 v,
    w7_comI en st2 LB2 L2 m2 (mbk_ents K bmax) ->
    mbio_rep m2 LB2 L2 K BI M_MEM blen bmax 0 ->
    (forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> ~ mbio_T K q) -> (forall b, In b (w_LBL en) -> ~ mbio_T K (blk_id b)) ->
    blen = zlength (w_d en) - 1 ->
    cstate st3 LB3 (w_LB en) L3 m3 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe (fun q => mbio_T K q \/ q = w_pe en) [] (w_SP en + -64 + 32) st2 LB2 L2 m2 st3 LB3 L3 m3 ->
    pem_read_res libenv errst_live K BI M_MEM blen bmax 0 (w_SP en + -64) (w_E en) (w_LBL en) LB2 L2 v LB3 L3 m3 ->
    exists ret boff' top bot strs, v = wz ret /\ 0 <= boff' <= blen /\ (length strs <= 2)%nat /\
      ((ret = 0 /\ f7_invI en st3 LB3 L3 m3 K BI blen bmax boff' top bot strs [] /\ exists lw, rw_cells usegs m3 (w_SP en + -64) [C8 lw; C8 (wz 0); C8 (wz 0); C8 (wz 0)])
       \/ (ret = 1 /\ exists (qd qh qn : bptr) (DT dlen HD nh NM nn : Z) (bd bh bn : list byte),
              pw_invI en st3 LB3 L3 m3 K BI blen bmax boff' top bot blen boff' strs qd qh qn DT dlen HD nh NM nn bd bh bn)).
  Proof.
    intros en st2 LB2 L2 m2 K BI blen bmax st3 LB3 L3 m3 v COM2 MB2 KFR KL EBLEN CST3 FRM3 R3.
    destruct R3 as (ret & boff' & top & bot & strs & news & -> & BOFF & MB3 & LE3 & LIVE3 & LEN2 & SL3 & NDSN & NSZ & OUT & LBIFF & NEWFRESH & LINCL).
    pose proof COM2 as (CST2 & FR0 & LE2 & INCL0 & INCL2 & NPL & INE2 & INL2 & PERM2 & SAVED2 & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLN & NDE & REL).
    assert (EK2 : forall q, mbio_T K q -> In q (map blk_id LB2)) by (intros q Tq; exact (mbio_ids _ _ _ _ _ _ _ _ _ _ MB2 Tq)).
    assert (IDS0 : forall q, In q (map blk_id (w_LBall en)) -> In q (map blk_id LB2)).
    { intros q Hq. pose proof FR0 as (_ & [KB0 _] & _). destruct (bptr_eq_dec q (w_pe en)) as [->|NE].
      - apply in_map_iff. exists (w_pe en, w_E en, 904). split; [reflexivity| exact INE2].
      - apply in_map_iff in Hq. destruct Hq as (b0 & Eb & Hb0). apply in_map_iff. exists b0. split; [exact Eb|]. apply KB0; [exact Hb0| rewrite Eb; intros E; exact (NE (eq_sym E))]. }
    assert (IDSL : forall q, In q (map fst (w_L en)) -> In q (map blk_id (w_LBall en))).
    { intros q Hq. change (map blk_ptr (w_CLB en)) with (map blk_id (w_CLB en)) in REL. apply w_pe_in_gen. rewrite REL. exact Hq. }
    exists ret, boff', top, bot, strs. split; [reflexivity|]. split; [clear - BOFF; lia|]. split; [exact LEN2|].
    assert (CORE : (forall b, In b news -> In (blk_id b, blk_size b) L3) -> f7_invI en st3 LB3 L3 m3 K BI blen bmax boff' top bot strs news).
    { intros NEWL.
      assert (NEWL' : forall b, In b (strs ++ news) -> In (blk_id b, blk_size b) L3).
      { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (proj1 (Forall_forall _ _) SL3 b Hb))| exact (NEWL b Hb)]. }
      split.
      { eapply (com7_callg libenv); [exact COM2| exact CST3| exact FRM3| clear; lia| | | exact LE3| apply LBIFF; left; exact INE2| exact (LINCL _ _ INL2)| intros b Hb; apply LBIFF; left; exact (INCL2 b Hb)|].
        - intros q Hq NE [X| ->]; [exact (KFR q Hq X)| exact (NE eq_refl)].
        - intros b Hb [X|X]; [exact (KL b Hb X)| exact (NPL b Hb X)].
        - rewrite <- bents_app. eapply perm_after_call; [exact CST2| exact CST3| exact PERM2| exact LBIFF| exact NEWFRESH| exact NDSN| exact LINCL| exact NEWL']. }
      split; [exact MB3|]. split; [exact LIVE3|]. split; [exact LEN2|].
      split; [apply Forall_forall; intros b Hb; apply LBIFF; right; apply in_or_app; left; exact Hb|]. split; [exact SL3|].
      split; [apply Forall_forall; intros b Hb; split; [apply LBIFF; right; apply in_or_app; right; exact Hb| exact (NEWL b Hb)]|].
      split; [exact KFR|]. split; [exact KL|].
      split; [intros b Hb X; exact (NEWFRESH b Hb (EK2 _ X))|]. split; [exact NDSN|].
      split; [intros b Hb [X|X]; apply (NEWFRESH b Hb); [exact (IDS0 _ X)| exact (IDS0 _ (IDSL _ X))]|].
      intros b Hb X. apply in_map_iff in X. destruct X as (b' & Eb & Hb'). apply (NEWFRESH b' Hb'). rewrite Eb. apply in_map. exact (INCL2 b Hb). }
    destruct OUT as [(-> & -> & O1 & O2 & O3 & (lw & O4))|(-> & qn & qh & qd & NM & HD & DT & nn & nh & dlen & bn & bh & bd & -> & OWNN & OWNH & OWND & NN & NH & DLEN & O1 & O2 & O3 & O4
                                                    & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC)].
    - left. split; [reflexivity|]. split; [apply CORE; intros b []|]. exists lw. exact (cells4 _ _ _ _ _ _ O4 O3 O2 O1).
    - right. split; [reflexivity|]. exists qd, qh, qn, DT, dlen, HD, nh, NM, nn, bd, bh, bn.
      split; [apply CORE; intros b [<-|[<-|[<-|[]]]]; cbn [blk_id blk_size fst snd]; [exact (proj2 OWND)| exact (proj2 OWNH)| exact (proj2 OWNN)]|].
      split; [exact (cells4 _ _ _ _ _ _ O4 O3 O2 O1)|].
      split; [exact NN|]. split; [exact NH|]. split; [exact DLEN|].
      split; [exact LBN|]. split; [exact NMC|]. split; [exact NUL|]. split; [exact LBH|]. split; [exact HDC|]. split; [exact NULH|]. split; [exact LBD|]. split; [exact DTC|].
      split; [apply Forall_forall; intros b Hb; exact (proj2 (proj1 (Forall_forall _ _) SL3 b Hb))|].
      split; [exact EBLEN|]. split; [clear - BOFF; lia|]. unfold news_sz in NSZ. cbn [fold_right blk_size snd] in NSZ. clear - NSZ. lia.
  Qed.
End W7.
