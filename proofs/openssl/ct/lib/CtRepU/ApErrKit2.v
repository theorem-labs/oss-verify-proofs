(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section SegBase. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
Variables (s0 : PState) (m0 : mem) (OW : list block) (st : ap_st bptr) (E : ap_env) (bo : Z * Z) (LB K : list block) (SP lo B : Z).

Definition seg_base (sX : PState) (OWc : list block) (mb : mem) : Prop :=
  RHEAP sX (OWc ++ LB) mb /\ rauxv_ok mb B /\ lx_pres LB SP LIBW_AP m0 mb
  /\ ap_rest mb OW E bo (as_cnf st) /\ (forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OWc ++ LB))
  /\ data_cells mb OW st /\ (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OWc ++ LB))
  /\ kept K m0 mb /\ (forall b, In b K -> In b OWc)
  /\ In (p_es E, e_es E, 904) OWc
  /\ ps_so sX = ps_so s0 /\ ps_fa sX = ps_fa s0.

(* [comment removed for export] *)
Definition seg_writable (OWc : list block) (p : bptr) : Prop :=
  ~ In p (map blk_id (rest_blocks OW E (as_cnf st))) /\ (forall i q k, get_data i st = Some (q, k) -> q <> p) /\ ~ In p (map blk_id K).

Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis GLO : GLOBALS_TOP <= lo.
Hypothesis SPB : lo <= SP <= B.
Hypothesis IDS : ids_ok E st.
Hypothesis AS0 : exists mI, ap_state st mI OW E bo.
Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

Lemma es_writable : forall OWc, seg_writable OWc (p_es E).
Proof using AS0 IDS KIDS.
  clear CEIL GLO SPB. intros OWc. split; [|split].
  - destruct AS0 as [mI AS]. eapply es_not_rest; [exact AS|exact IDS].
  - intros i q k Hd ->. exact (ids_data_es_ne E st i (p_es E) k IDS Hd eq_refl).
  - eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto.
Qed.

(* [comment removed for export] *)
Lemma seg_base_munch : forall sX OWc mb mc W,
  seg_base sX OWc mb -> munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ iv = (3355012, 3355016)
                    \/ (exists p A n, In (p, A, n) OWc /\ seg_writable OWc p /\ A <= fst iv /\ snd iv <= A + n)) W ->
  seg_base sX OWc mc.
Proof using CEIL GLO SPB.
  intros sX OWc mb mc W (HEAP & AUX & LX & AR & RB & DC & DIN & KP & KOW & IES & SO & FA) MU WM HW.
  assert (INCL : forall b, In b OWc -> In b (OWc ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  unfold GLOBALS_TOP in GLO.
  destruct (seg_close sX OWc LB W mb mc lo SP B HEAP AUX CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP' & AUX' & LX').
  { eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & HIn & _ & H1 & H2)]]; cbn [fst snd] in *.
    - left. cbn. lia. - right. left. exact H. - right. right. exists p, A, n. split; [exact HIn|cbn; lia]. }
  split; [exact HEAP'|]. split; [exact AUX'|]. split; [eapply lx_pres_trans; [exact LX|exact LX']|].
  split.
  { eapply rest_of_munch; [exact AR|exact MU|exact WM|]. intros a Ha. apply seg_outside.
    pose proof (lib_addr_where sX (OWc ++ LB) mb (rest_blocks OW E (as_cnf st)) a HEAP RB Ha) as C.
    eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & HIn & (W1 & _ & _) & H1 & H2)]]; cbn [fst snd] in *.
    - lia.
    - injection H as -> ->. lia.
    - pose proof (blk_bounds sX (OWc ++ LB) mb p A n HEAP (INCL _ HIn)) as (B1 & B2 & B3 & B4 & B5).
      destruct Ha as [Hs|([[p' A'] n'] & Hb & Hr)].
      + destruct C as [C|C]; [lia|]. unfold LIBW_HX in Hs. cbn [rin_ivs fst snd] in Hs. lia.
      + cbn [blk_addr blk_size fst snd] in Hr.
        assert (Hp : p <> p') by (intros ->; apply W1; change p' with (blk_id (p', A', n')); apply in_map; exact Hb).
        pose proof (blk_disjoint sX (OWc ++ LB) mb p A n p' A' n' HEAP (INCL _ HIn) (RB _ Hb) Hp) as D. lia. }
  split; [exact RB|]. split.
  { eapply (data_cells_of_munch sX (OWc ++ LB) W mb mc); [exact DC|exact DIN|exact HEAP|exact CEIL|exact MU|exact WM|].
    eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & HIn & (_ & W2 & _) & H1 & H2)]]; cbn [fst snd] in *.
    - left. lia. - right. left. exact H. - right. right. exists p, A, n. split; [apply INCL; exact HIn|]. split; [exact W2|lia]. }
  split; [exact DIN|]. split.
  { eapply kept_trans; [exact KP|]. eapply (kept_of_munch sX (OWc ++ LB) W mb mc K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
    eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(p & A & n & HIn & (_ & _ & W3) & H1 & H2)]]; cbn [fst snd] in *.
    - left. lia. - right. left. exact H. - right. right. exists p, A, n. split; [apply INCL; exact HIn|]. split; [exact W3|lia]. }
  split; [exact KOW|]. split; [exact IES|]. split; [exact SO|exact FA].
Qed.

(* [comment removed for export] *)
Lemma seg_base_free : forall sX sY OWc mb mc od SP',
  seg_base sX OWc mb ->
  (forall q n, od = Some (q, n) -> In q (map blk_id OWc) /\ seg_writable OWc q /\ q <> p_es E) ->
  rheap_pres (lremove od (OWc ++ LB)) SP' mb mc -> SP' <= SP -> RHEAP sY (lremove od (OWc ++ LB)) mc -> rauxv_ok mc B ->
  ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
  seg_base sY (lremove od OWc) mc.
Proof.
  intros sX sY OWc mb mc od SP' (HEAP & AUX & LX & AR & RB & DC & DIN & KP & KOW & IES & SO & FA) Hod HP' HSP HEAP' AUX' SO' FA'.
  pose proof (LH_nodup _ _ _ HEAP) as ND.
  assert (QI : forall q n, od = Some (q, n) -> In q (map blk_id OWc)) by (intros q n H; exact (proj1 (Hod q n H))).
  rewrite (lremove_app od OWc LB ND QI) in HP', HEAP'.
  assert (HP : rheap_pres (lremove od OWc ++ LB) SP mb mc) by (eapply rheap_pres_weaken; [exact HP'|exact HSP|intros b Hb; exact Hb]).
  assert (INCL : forall b, In b OWc -> In b (OWc ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  assert (RB' : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (lremove od OWc ++ LB)).
  { rewrite <- (lremove_app od OWc LB ND QI). apply rest_blocks_lremove; [exact RB|]. intros q n H. exact (proj1 (proj1 (proj2 (Hod q n H)))). }
  assert (DIN' : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (lremove od OWc ++ LB)).
  { intros i q k Hd. rewrite <- (lremove_app od OWc LB ND QI). apply lremove_keep; [eapply DIN; exact Hd|].
    intros q' n' H. cbn. exact (proj1 (proj2 (proj1 (proj2 (Hod q' n' H)))) i q k Hd). }
  assert (KOW' : forall b, In b K -> In b (lremove od OWc)).
  { intros b Hb. apply (K_lremove K OWc od KOW); [|exact Hb]. intros q n H. exact (proj2 (proj2 (proj1 (proj2 (Hod q n H))))). }
  split; [exact HEAP'|]. split; [exact AUX'|]. split.
  { eapply lx_pres_trans; [exact LX|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP|lia|]. intros b Hb. apply in_app_iff. right. exact Hb. }
  split; [eapply rest_of_heap_pres; [exact AR|exact HP|exact RB']|]. split; [exact RB'|].
  split; [eapply data_cells_heap_pres; [exact DC|exact HP|exact DIN']|]. split; [exact DIN'|].
  split; [eapply kept_trans; [exact KP|eapply kept_of_heap_pres; [exact HP|intros b Hb; apply in_app_iff; left; apply KOW'; exact Hb]]|].
  split; [exact KOW'|]. split.
  { apply lremove_keep; [exact IES|]. intros q n H. cbn. apply not_eq_sym. exact (proj2 (proj2 (Hod q n H))). }
  split; [rewrite SO'; exact SO|rewrite FA'; exact FA].
Qed.

(* [comment removed for export] *)
Lemma seg_base_malloc : forall sX sY OWc mb mc p A n SP',
  seg_base sX OWc mb ->
  rheap_pres (OWc ++ LB) SP' mb mc -> SP' <= SP -> RHEAP sY ((p, A, n) :: OWc ++ LB) mc -> rauxv_ok mc B ->
  ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
  seg_base sY ((p, A, n) :: OWc) mc.
Proof.
  intros sX sY OWc mb mc p A n SP' (HEAP & AUX & LX & AR & RB & DC & DIN & KP & KOW & IES & SO & FA) HP' HSP HEAP' AUX' SO' FA'.
  assert (HP : rheap_pres (OWc ++ LB) SP mb mc) by (eapply rheap_pres_weaken; [exact HP'|exact HSP|intros b Hb; exact Hb]).
  split; [exact HEAP'|]. split; [exact AUX'|]. split.
  { eapply lx_pres_trans; [exact LX|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP|lia|]. intros b Hb. apply in_app_iff. right. exact Hb. }
  split; [eapply rest_of_heap_pres; [exact AR|exact HP|exact RB]|]. split; [intros b Hb; right; apply RB; exact Hb|].
  split; [eapply data_cells_heap_pres; [exact DC|exact HP|exact DIN]|]. split; [intros i q k Hd; right; eapply DIN; exact Hd|].
  split; [eapply kept_trans; [exact KP|eapply kept_of_heap_pres; [exact HP|intros b Hb; apply in_app_iff; left; apply KOW; exact Hb]]|].
  split; [intros b Hb; right; apply KOW; exact Hb|]. split; [right; exact IES|]. split; [rewrite SO'; exact SO|rewrite FA'; exact FA].
Qed.

(* [comment removed for export] *)
Lemma seg_base_crypto_statics : forall sX OWc mb, seg_base sX OWc mb -> crypto_statics mb.
Proof. intros sX OWc mb (_ & _ & _ & AR & _). destruct AR as (_ & _ & (CS & _) & _). exact CS. Qed.

Lemma seg_base_heap : forall sX OWc mb, seg_base sX OWc mb -> RHEAP sX (OWc ++ LB) mb.
Proof. intros sX OWc mb (H & _). exact H. Qed.

Lemma seg_base_es : forall sX OWc mb, seg_base sX OWc mb -> In (p_es E, e_es E, 904) OWc.
Proof. intros sX OWc mb (_ & _ & _ & _ & _ & _ & _ & _ & _ & IES & _). exact IES. Qed.

Lemma seg_base_aux : forall sX OWc mb, seg_base sX OWc mb -> rauxv_ok mb B.
Proof. intros sX OWc mb (_ & AUX & _). exact AUX. Qed.

Lemma seg_base_kow : forall sX OWc mb, seg_base sX OWc mb -> forall b, In b K -> In b OWc.
Proof. intros sX OWc mb (_ & _ & _ & _ & _ & _ & _ & _ & KOW & _). exact KOW. Qed.

(* [comment removed for export] *)
Lemma fresh_writable : forall sX OWc mb p,
  seg_base sX OWc mb -> ~ In p (map blk_id (OWc ++ LB)) -> forall OWd, seg_writable OWd p.
Proof.
  intros sX OWc mb p (HEAP & AUX & LX & AR & RB & DC & DIN & KP & KOW & IES & SO & FA) NI OWd. split; [|split].
  - intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply in_map. apply RB. exact Hb.
  - intros i q k Hd ->. apply NI. change p with (blk_id (p, badr OW p, k)). apply in_map. eapply DIN. exact Hd.
  - intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply in_map. apply in_app_iff. left. apply KOW. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma seg_base_intro : forall mb,
  RHEAP s0 (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB SP LIBW_AP m0 mb -> ap_state st mb OW E bo -> data_cells mb OW st ->
  kept K m0 mb -> (forall b, In b K -> In b OW) ->
  seg_base s0 OW mb.
Proof.
  intros mb HEAP AUX LX AS DC KP KOW.
  assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  pose proof (proj1 (ap_state_split _ _ _ _ _) AS) as [AR _].
  pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & IES & _ & _ & _ & _ & _ & OD). unfold ES_SIZE in IES.
  split; [exact HEAP|]. split; [exact AUX|]. split; [exact LX|]. split; [exact AR|].
  split; [intros b Hb; apply INCL; eapply rest_blocks_OW; [exact AR|exact Hb]|]. split; [exact DC|].
  split; [intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|].
  split; [exact KP|]. split; [exact KOW|]. split; [exact IES|]. split; reflexivity.
Qed.

End SegBase.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Gain. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
Lemma ids_ok_add : forall E st st' p n,
  Permutation (st_blocks st') ((p, n) :: st_blocks st) -> ~ In p (es_ids st ++ env_ids E) ->
  (as_top st' < ERR_NUM)%nat -> (as_bottom st' < ERR_NUM)%nat -> marks_sub st' st -> ids_ok E st -> ids_ok E st'.
Proof.
  intros E st st' p n HP NI T B' MS (ND & _ & _ & MK). split; [|split; [exact T|split; [exact B'|eapply marks_ok_sub; [exact MS|exact MK]]]].
  unfold es_ids in *. eapply Permutation_NoDup; [apply Permutation_app_tail; apply Permutation_map; apply Permutation_sym; exact HP|].
  cbn [map fst app]. constructor; [exact NI|exact ND].
Qed.

(* [comment removed for export] *)
Definition ids_in (E : ap_env) st (OW : list block) : Prop := forall q, In q (es_ids st ++ env_ids E) -> In q (map blk_id OW).

Lemma ids_in_intro : forall st m OW E bo, ap_state st m OW E bo -> ids_in E st OW.
Proof.
  intros st m OW E bo AS q Hq. pose proof AS as (HE & _ & _ & HC & _ & _ & _ & (_ & _ & F1 & F2 & F3)).
  apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
  - unfold es_ids, st_blocks in Hq. rewrite !map_app, !in_app_iff in Hq.
    assert (FM : forall l, Forall (optb_ok OW) l -> In q (map fst (fm l)) -> In q (map blk_id OW)).
    { intros l Hl Hin. apply in_map_iff in Hin. destruct Hin as ([q' n] & E1 & Hin). cbn in E1. subst q'.
      induction l as [|o l IH]; [destruct Hin|]. apply Forall_cons_iff in Hl. destruct Hl as [Ho Hl].
      rewrite fm_cons in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [|apply IH; assumption].
      destruct o as [[q' n']|]; [|destruct Hin]. destruct Hin as [Hin|[]]. injection Hin as -> ->. cbn in Ho. destruct Ho as [Ho _].
      change q with (blk_id (q, badr OW q, n)). apply in_map. exact Ho. }
    destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [apply (FM _ F1 Hq)|apply (FM _ F2 Hq)|apply (FM _ F3 Hq)|].
    destruct (as_cnf st) as [[[lk lh] bk]|]; cbn [ap_statics_cnf cnf_blocks map fst In] in HC, Hq; [|destruct Hq].
    destruct HC as (_ & _ & _ & _ & _ & _ & I1 & I2 & I3 & _).
    destruct Hq as [<-|[<-|[<-|[]]]]; [change lk with (blk_id (lk, badr OW lk, SZ_OBJ_LOCK))|change lh with (blk_id (lh, badr OW lh, SZ_ADDED))|change bk with (blk_id (bk, badr OW bk, SZ_ADDED_BUCKETS))]; apply in_map; assumption.
  - destruct HE as (HF & _ & _). unfold env_ids in Hq. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map.
    exact (proj1 (Forall_forall _ _) HF b Hb).
Qed.

(* [comment removed for export] *)
Lemma ids_in_remove : forall E st st' OW q n,
  ids_ok E st -> Permutation ((q, n) :: st_blocks st') (st_blocks st) -> ids_in E st OW -> ids_in E st' (lb_remove q OW).
Proof.
  intros E st st' OW q n (ND & _ & _) HP HI q' Hq'.
  assert (Hin : In q' (es_ids st ++ env_ids E)).
  { apply in_app_iff in Hq'. apply in_app_iff. destruct Hq' as [H|H]; [left|right; exact H].
    unfold es_ids in *. apply in_map_iff in H. destruct H as (b & <- & Hb). apply in_map. eapply Permutation_in; [exact HP|]. right. exact Hb. }
  assert (NE : q' <> q).
  { intros ->. unfold es_ids in ND, Hq'.
    assert (ND' : List.NoDup (q :: map fst (st_blocks st') ++ env_ids E)).
    { change (q :: map fst (st_blocks st') ++ env_ids E) with (map fst ((q, n) :: st_blocks st') ++ env_ids E).
      eapply Permutation_NoDup; [|exact ND]. apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact HP. }
    cbn in ND'. apply NoDup_cons_iff in ND'. exact (proj1 ND' Hq'). }
  pose proof (HI q' Hin) as H. apply in_map_iff in H. destruct H as (b & <- & Hb). apply in_map. apply lb_remove_In. split; [exact Hb|exact NE].
Qed.

Lemma ids_in_cons : forall E st OW b, ids_in E st OW -> ids_in E st (b :: OW).
Proof. intros E st OW b HI q Hq. cbn. right. apply HI. exact Hq. Qed.

Lemma ids_in_add : forall E st st' OW p A n,
  Permutation (st_blocks st') ((p, n) :: st_blocks st) -> ids_in E st OW -> ids_in E st' ((p, A, n) :: OW).
Proof.
  intros E st st' OW p A n HP HI q Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq]; [|cbn; right; apply HI; apply in_app_iff; right; exact Hq].
  unfold es_ids in Hq. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). pose proof (Permutation_in _ HP Hb) as [<-|H]; [cbn; left; reflexivity|].
  cbn. right. apply HI. apply in_app_iff. left. unfold es_ids. apply in_map. exact H.
Qed.

(* [comment removed for export] *)
Lemma fresh_not_ids : forall E st OW LB p, ids_in E st OW -> ~ In p (map blk_id (OW ++ LB)) -> ~ In p (es_ids st ++ env_ids E).
Proof. intros E st OW LB p HI NI H. apply NI. rewrite map_app. apply in_app_iff. left. apply HI. exact H. Qed.

(* [comment removed for export] *)
Lemma upd_ext : forall {X} (l1 l2 : list X) i v,
  length l1 = length l2 -> (forall j, j <> i -> nth_error l1 j = nth_error l2 j) -> upd l1 i v = upd l2 i v.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] i v HL HJ; cbn in HL; try discriminate; [reflexivity|].
  destruct i as [|i]; cbn.
  - f_equal. apply nth_error_ext. intros j. exact (HJ (S j) ltac:(lia)).
  - pose proof (HJ 0%nat ltac:(lia)) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH; [lia|]. intros j Hj. exact (HJ (S j) ltac:(lia)).
Qed.

Lemma upd_upd_same : forall {X} (l : list X) i v w, upd (upd l i v) i w = upd l i w.
Proof. induction l as [|x l IH]; intros [|i] v w; cbn; [reflexivity|reflexivity|reflexivity|]. rewrite IH. reflexivity. Qed.

End Gain.
