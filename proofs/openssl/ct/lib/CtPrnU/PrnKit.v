(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG ApBase ApState.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_bio_push W_bio_write W_obj_lookup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma disjoint_from_forall : forall W a n, Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof. induction W as [|[x y] W IH]; intros a n H; cbn; [exact I|]. apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [lia| apply IH; exact H2]. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma other_not_rest : forall st E OW (pb : bptr),
  ~ In pb (es_ids st ++ env_ids E) -> ~ In pb (map blk_id (rest_blocks OW E (as_cnf st))) /\ pb <> p_es E.
Proof.
  intros st E OW pb NI. rewrite in_app_iff in NI. split.
  - rewrite rest_ids, in_app_iff. intros [H|H].
    + apply NI. right. rewrite env_ids_unfold. cbn [In] in H |- *. tauto.
    + apply NI. left. apply cnf_ids_in_es_ids. exact H.
  - intros ->. apply NI. right. rewrite env_ids_unfold. cbn. tauto.
Qed.

(* [comment removed for export] *)
Lemma blk_off_static : forall s L m p A n a, RHEAP s L m -> In (p, A, n) L -> A <= a < A + n -> a < alloc_ceiling /\ (a < 0x10000 \/ 0x355000 <= a).
Proof. intros s L m p A n a HEAP HIn Ha. pose proof (blk_bounds s L m p A n HEAP HIn) as (B1 & B2 & B3 & B4 & B5). lia. Qed.

(* [comment removed for export] *)
Lemma ap_state_of_munch_bio : forall st mb mc OW E bo s L W lo (pb : bptr) PB nB,
  ap_state st mb OW E bo -> ids_ok E st -> RHEAP s L mb -> (forall b, In b OW -> In b L) ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  In (pb, PB, nB) OW -> ~ In pb (es_ids st ++ env_ids E) ->
  munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016) \/ (PB <= fst iv /\ snd iv <= PB + nB)) W ->
  ap_state st mc OW E bo.
Proof.
  intros st mb mc OW E bo s L W lo pb PB nB AS IDS HEAP HL CEIL GLO HBIN NI MU WM HW.
  destruct (other_not_rest st E OW pb NI) as [NR NES].
  pose proof (proj1 (ap_state_split _ _ _ _ _) AS) as [AR ER].
  apply ap_state_split. split.
  - eapply rest_of_munch; [exact AR| exact MU| exact WM|]. intros a Ha. apply seg_outside. eapply Forall_impl; [| exact HW].
    intros [x y] [H|[H|[Hx Hy]]]; cbn [fst snd] in *.
    + eapply (rest_outside_stack s L mb); try eassumption.
    + injection H as -> ->. pose proof (lib_addr_where s L mb OW a HEAP HL ltac:(destruct Ha as [Ha|(b & Hb & Hr)]; [left; exact Ha| right; exists b; split; [eapply rest_blocks_OW; [exact AR| exact Hb]| exact Hr]])) as C.
      unfold GLOBALS_TOP in GLO. lia.
    + intros Hin. eapply (rest_outside_block s L mb OW E bo (as_cnf st) pb PB nB a); try eassumption; [apply HL; exact HBIN| lia].
  - destruct ER as (SH & EAT & F1 & F2 & F3). split; [exact SH|]. split; [| split; [exact F1| split; [exact F2| exact F3]]].
    pose proof AR as (HE & _). destruct (env_in E OW HE) as (IES & _).
    apply es_at_raw. eapply es_raw_transport; [apply es_at_raw; exact EAT| apply g_len_of; exact SH| exact MU| exact WM|].
    pose proof (blk_bounds s L mb _ _ _ HEAP (HL _ IES)) as (B1 & B2 & B3 & B4 & B5). unfold ES_SIZE in *.
    assert (NE : pb <> p_es E) by exact NES.
    pose proof (blk_disjoint s L mb pb PB nB (p_es E) (e_es E) 904 HEAP (HL _ HBIN) (HL _ IES) NE) as DJ.
    clear - HW B1 B2 B3 B4 B5 DJ CEIL GLO. unfold GLOBALS_TOP in GLO.
    induction W as [|[x y] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
    split; [| apply IH; exact H2]. cbn [fst snd] in H1. destruct H1 as [H1|[H1|[H1 H1']]]; [lia| injection H1 as -> ->; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma data_cells_of_munch_bio : forall st mb mc OW E s L W lo (pb : bptr) PB nB,
  data_cells mb OW st -> ap_state st mb OW E (0, 0) \/ (exists bo, ap_state st mb OW E bo) -> RHEAP s L mb -> (forall b, In b OW -> In b L) ->
  alloc_ceiling <= lo -> In (pb, PB, nB) OW -> ~ In pb (es_ids st ++ env_ids E) ->
  munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016) \/ (PB <= fst iv /\ snd iv <= PB + nB)) W ->
  data_cells mc OW st.
Proof.
  intros st mb mc OW E s L W lo pb PB nB DC AS HEAP HL CEIL HBIN NI MU WM HW.
  assert (OD : Forall (optb_ok OW) (as_data st)).
  { destruct AS as [AS|[bo AS]]; destruct (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD); exact OD. }
  eapply (data_cells_of_munch s L W mb mc OW st lo); [exact DC| | exact HEAP| exact CEIL| exact MU| exact WM|].
  - intros i q k Hd. apply HL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)).
  - eapply Forall_impl; [| exact HW]. intros iv [H|[H|[H H']]]; [left; exact H| right; left; exact H| right; right].
    exists pb, PB, nB. split; [apply HL; exact HBIN|]. split; [| split; [exact H| exact H']].
    intros i q k Hd ->. apply NI. apply in_app_iff. left. eapply es_ids_data. exact Hd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pn_pre (s : PState) st (m : mem) (OW LB : list block) (E : ap_env) (bo : Z * Z) (NB : list block)
    (q lo B : Z) (errv canary : word) : Prop :=
  RHEAP s (NB ++ OW ++ LB) m /\ ap_state st m OW E bo /\ ids_ok E st /\ data_cells m OW st
  /\ rauxv_ok m B /\ q <= B /\ B < 2^63
  /\ stk ctusegs m lo q /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= q
  /\ rw_cells ctusegs m 3355012 [C4 errv] /\ ssp_cells m canary /\ mem_inv ctusegs m.

(* [comment removed for export] *)
Definition pn_acc (LB : list block) (SP : Z) (K : list block) (s0 s : PState) (m0 m : mem) : Prop :=
  lx_pres LB SP LIBW_AP m0 m /\ kept K m0 m /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0.

Lemma pn_acc_refl : forall LB SP K s m, pn_acc LB SP K s s m m.
Proof. intros. split; [apply lx_pres_refl|]. split; [intros a _ _; reflexivity|]. split; reflexivity. Qed.

Lemma pn_acc_trans : forall LB SP K s0 s1 s2 m0 m1 m2,
  pn_acc LB SP K s0 s1 m0 m1 -> pn_acc LB SP K s1 s2 m1 m2 -> pn_acc LB SP K s0 s2 m0 m2.
Proof.
  intros until m2. intros (L1 & K1 & S1 & F1) (L2 & K2 & S2 & F2).
  split; [eapply lx_pres_trans; [exact L1| exact L2]|]. split; [eapply kept_trans; [exact K1| exact K2]|]. split; congruence.
Qed.

Lemma errno_addr_lit : errno_addr (wz RATP) = 3355012.
Proof. unfold errno_addr, RATP, MallocRep.wz. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pn_pre_of_ap : forall s st m OW LB E bo (sp : word) lo B errv canary stack,
  ap_pre s st m OW LB E bo sp lo B errv canary stack -> 0 <= stack ->
  pn_pre s st m OW LB E bo [] (bv_unsigned sp) lo B errv canary /\ lo <= bv_unsigned sp - stack /\ bv_unsigned sp mod 16 = 0.
Proof.
  intros until stack. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15) ST0.
  rewrite errno_addr_lit in A12. unfold pn_pre. cbn [app].
  assert (LOQ : lo <= bv_unsigned sp) by lia.
  split; [repeat (split; [assumption|]); exact A14|]. split; [exact A11| exact A15].
Qed.

(* [comment removed for export] *)
Lemma ap_pre_of_pn : forall s st m OW LB E bo (sp : word) lo B errv canary,
  pn_pre s st m OW LB E bo [] (bv_unsigned sp) lo B errv canary -> bv_unsigned sp mod 16 = 0 ->
  ap_pre s st m OW LB E bo sp lo B errv canary 0.
Proof.
  intros until canary. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & LO & A12 & A13 & A14) SP16. cbn [app] in A1.
  unfold ap_pre. rewrite errno_addr_lit. repeat (split; [first [assumption| lia]|]). exact SP16.
Qed.

(* [comment removed for export] *)
Lemma pn_seg_bio : forall s st mb mc OW LB E bo NB q q' lo B errv canary W SP (pbio : bptr) out K,
  pn_pre s st mb OW LB E bo NB q lo B errv canary ->
  In (pbio, out, BIO_SIZE) OW -> ~ In pbio (es_ids st ++ env_ids E) ->
  munch W mb mc -> wmono ctusegs mb mc ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ (out <= fst iv /\ snd iv <= out + BIO_SIZE)) W ->
  lo <= SP <= B -> q' <= B -> lo <= q' ->
  mem_inv ctusegs mc -> stk ctusegs mc lo q' ->
  (forall b, In b K -> In b (NB ++ OW ++ LB) /\ blk_id b <> pbio) ->
  pn_pre s st mc OW LB E bo NB q' lo B errv canary /\ lx_pres LB SP LIBW_AP mb mc /\ kept K mb mc.
Proof.
  intros until K. intros (HEAP & AS & IDS & DC & AUX & QB & B63 & ST & CEIL & GLO & LOQ & ERR & SSP & MI) HBIN NI MU WM HW SPB QB' LOQ' MI' ST' HK.
  unfold BIO_SIZE in *.
  assert (INCL : forall b, In b OW -> In b (NB ++ OW ++ LB)) by (intros b Hb; apply in_app_iff; right; apply in_app_iff; left; exact Hb).
  pose proof (INCL _ HBIN) as HBL.
  pose proof (blk_bounds s _ mb _ _ _ HEAP HBL) as (B1 & B2 & B3 & B4 & B5).
  assert (SEG : Forall (seg_iv (NB ++ OW) lo SP) W).
  { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[H1 H2]]; [left; split; assumption|].
    right. right. exists pbio, out, 128. split; [apply in_app_iff; right; exact HBIN|]. split; assumption. }
  rewrite app_assoc in HEAP.
  destruct (seg_close s (NB ++ OW) LB W mb mc lo SP B HEAP AUX CEIL GLO SPB MU WM SEG) as (HEAP' & AUX' & LX). rewrite <- app_assoc in HEAP, HEAP'.
  assert (HW3 : Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016) \/ (out <= fst iv /\ snd iv <= out + 128)) W).
  { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[H1 H2]]; [left; exact H1| right; right; split; assumption]. }
  split; [| split; [exact LX|]].
  - split; [exact HEAP'|]. split.
    { eapply (ap_state_of_munch_bio st mb mc OW E bo s (NB ++ OW ++ LB) W lo pbio out 128); try eassumption. }
    split; [exact IDS|]. split.
    { eapply (data_cells_of_munch_bio st mb mc OW E s (NB ++ OW ++ LB) W lo pbio out 128); try eassumption. right. exists bo. exact AS. }
    split; [exact AUX'|]. split; [exact QB'|]. split; [exact B63|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact GLO|]. split; [exact LOQ'|].
    split.
    { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply disjoint_from_forall.
      eapply Forall_impl; [| exact HW]. intros [x y] [[H1 H2]|[H1 H2]]; cbn [fst snd] in *; unfold GLOBALS_TOP in GLO; lia. }
    split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP'| exact MI'].
  - eapply (kept_of_munch s (NB ++ OW ++ LB) W mb mc K lo); [exact HEAP| intros b Hb; exact (proj1 (HK b Hb))| exact CEIL| exact MU|].
    eapply Forall_impl; [| exact HW3]. intros iv [H|[H|[H H']]]; [left; exact H| right; left; exact H| right; right].
    exists pbio, out, 128. split; [exact HBL|]. split; [| split; assumption].
    intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). exact (proj2 (HK b Hb) Eb).
Qed.

(* [comment removed for export] *)
Lemma pn_node : forall s s' st mb mc OW LB E bo NB NB' q lo B (errv errv' canary : word) SP K,
  pn_pre s st mb OW LB E bo NB q lo B errv canary ->
  rheap_pres (OW ++ LB) q mb mc ->
  RHEAP s' (NB' ++ OW ++ LB) mc -> mem_inv ctusegs mc -> stk ctusegs mc lo q -> rw_cells ctusegs mc 3355012 [C4 errv'] -> rauxv_ok mc B ->
  ps_so s' = ps_so s -> ps_fa s' = ps_fa s ->
  q <= SP -> (forall b, In b K -> In b (OW ++ LB)) ->
  pn_pre s' st mc OW LB E bo NB' q lo B errv' canary /\ pn_acc LB SP K s s' mb mc.
Proof.
  intros until K. intros (HEAP & AS & IDS & DC & AUX & QB & B63 & ST & CEIL & GLO & LOQ & ERR & SSP & MI) HP HEAP' MI' ST' ERR' AUX' SO FA QSP HK.
  assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
  split.
  - split; [exact HEAP'|]. split; [eapply ap_state_heap_pres; [exact AS| exact HP| exact INCL]|]. split; [exact IDS|].
    split; [eapply data_cells_heap_pres; [exact DC| exact HP| intros i q' k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q' k OD Hd))]|].
    split; [exact AUX'|]. split; [exact QB|]. split; [exact B63|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact GLO|]. split; [exact LOQ|].
    split; [exact ERR'|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP'| exact MI'].
  - split; [eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| exact QSP| intros b Hb; apply in_app_iff; right; exact Hb| intros a Ha; exact Ha]|].
    split; [eapply kept_of_heap_pres; [exact HP| intros b Hb; apply HK; exact Hb]|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_drop_nb : forall NB OW LB q mb mc, rheap_pres (NB ++ OW ++ LB) q mb mc -> rheap_pres (OW ++ LB) q mb mc.
Proof. intros. eapply rheap_pres_weaken; [eassumption| lia| intros b Hb; apply in_app_iff; right; exact Hb]. Qed.

(* [comment removed for export] *)
Lemma rheap_pres_but_other : forall s L' L2 OW LB q X mb mc (g : bptr) G n,
  rheap_pres_but L' q X mb mc -> X = (G, G + n) ->
  RHEAP s L2 mc -> (forall b, In b L' -> In b L2) -> In (g, G, n) L' -> (forall b, In b (OW ++ LB) -> In b L') -> ~ In g (map blk_id (OW ++ LB)) ->
  alloc_ceiling <= q ->
  rheap_pres (OW ++ LB) q mb mc.
Proof.
  intros s L' L2 OW LB q X mb mc g G n HP -> HEAP HL2 HG HL NI CQ a Ha Hc. apply (HP a Ha).
  - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; exact Hc| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
  - cbn [fst snd]. pose proof (blk_bounds s L2 mc g G n HEAP (HL2 _ HG)) as (B1 & B2 & B3 & B4 & B5).
    destruct Hc as [Hc|[[Hc1 Hc2]|(b & Hb & Hr)]]; [lia| lia|].
    destruct b as [[p A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
    assert (NE : g <> p) by (intros ->; apply NI; apply in_map_iff; exists (p, A', n'); split; [reflexivity| exact Hb]).
    pose proof (blk_disjoint s L2 mc g G n p A' n' HEAP (HL2 _ HG) (HL2 _ (HL _ Hb)) NE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma null_meth_of_img : forall m, mem_inv ctusegs m -> ap_img m -> null_meth_cells m.
Proof.
  intros m MI IMG. unfold null_meth_cells, NULL_METHOD, BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz.
  split.
  - eapply W_obj_lookup.ro_cells_recast.
    + apply (ap_img_ro_cells m (2978032 + 16) 16); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity].
    + cbn. tauto.
    + bytes_lit_eq.
  - eapply W_obj_lookup.ro_cells_recast.
    + apply (ap_img_ro_cells m (2978032 + 48) 8); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity].
    + cbn. tauto.
    + bytes_lit_eq.
Qed.

End WithCeiling0.
