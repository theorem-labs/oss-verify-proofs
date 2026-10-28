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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApErrKit ApErrKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs1 cs2,
  rw_cells ctusegs m A cs1 -> cells_wf cs2 -> cells_bytes cs2 = cells_bytes cs1 -> cells_size cs2 = cells_size cs1 -> rw_cells ctusegs m A cs2.
Proof. intros m A cs1 cs2 [[W B] R] W2 EB ES. split; [split; [exact W2|rewrite EB; exact B]|rewrite ES; exact R]. Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_of : forall m A cs, rw_cells ctusegs m A cs -> rw_cells ctusegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact W|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.

(* [comment removed for export] *)
Lemma fm_nodup_slots : forall (l : list (option (bptr * Z))) i j p n q k,
  List.NoDup (map fst (fm l)) -> nth i l None = Some (p, n) -> nth j l None = Some (q, k) -> i <> j -> p <> q.
Proof.
  induction l as [|o l IH]; intros i j p n q k ND Hi Hj NE; [destruct i; discriminate|].
  rewrite fm_cons, map_app in ND.
  destruct i as [|i], j as [|j]; cbn [nth] in Hi, Hj; [congruence| | |].
  - subst o. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros ->. apply NI. change q with (fst (q, k)). apply in_map. eapply fm_in. exact Hj.
  - subst o. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros ->. apply NI. change q with (fst (q, n)). apply in_map. eapply fm_in. exact Hi.
  - eapply (IH i j); [|exact Hi|exact Hj|lia]. destruct o as [[r z]|]; cbn in ND; [apply NoDup_cons_iff in ND; exact (proj2 ND)|exact ND].
Qed.

Section More. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
Lemma ids_ok_nodup_arrays : forall E st, ids_ok E st ->
  List.NoDup (map fst (fm (as_file st))) /\ List.NoDup (map fst (fm (as_func st))) /\ List.NoDup (map fst (fm (as_data st))).
Proof.
  intros E st (ND & _ & _). unfold es_ids, st_blocks in ND. rewrite !map_app in ND.
  pose proof (List.NoDup_app_remove_r _ _ ND) as ND1. pose proof (List.NoDup_app_remove_r _ _ ND1) as NF.
  pose proof (List.NoDup_app_remove_l _ _ ND1) as N2. pose proof (List.NoDup_app_remove_r _ _ N2) as NN.
  pose proof (List.NoDup_app_remove_l _ _ N2) as N3. pose proof (List.NoDup_app_remove_r _ _ N3) as ND'.
  split; [exact NF|]. split; [exact NN|exact ND'].
Qed.

(* [comment removed for export] *)
Lemma es_wr_tb0 : forall m A g, es_raw m A g -> g_len g ->
  store_ok ctusegs m (wa (A + 896)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + 896)) (le8 (wz 0))) A (set_g_bot 0 (set_g_top 0 g)).
Proof.
  intros m A g H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM in *.
  pose proof (rw_cells_CB_of _ _ _ HT) as HT8. cbn [cells_size csize cells_bytes cbytes Nat.add] in HT8. rewrite app_nil_r in HT8.
  split. { exact (rw_cells_store_ok_at _ m (A + 896) _ 0%nat _ 8 (wa (A + 896)) HT8 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)). }
  unfold es_raw, set_g_top, set_g_bot. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot].
  unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 0%nat _ (C8 (wz 0)) HT8 eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 0) with (A + 896) in W by lia.
  eapply rw_cells_recast; [exact W|cbn; tauto|vm_compute; reflexivity|reflexivity].
Qed.
End More.

Section SegData. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Implicit Types st : ap_st bptr.
Variables (s0 : PState) (m0 : mem) (OW : list block) (st : ap_st bptr) (E : ap_env) (bo : Z * Z) (LB K : list block) (SP lo B : Z).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis GLO : GLOBALS_TOP <= lo.
Hypothesis SPB : lo <= SP <= B.
Hypothesis IDS : ids_ok E st.
Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

(* [comment removed for export] *)
Lemma seg_base_store_data : forall sX OWc mb mc i pd nd x y junk',
  seg_base s0 m0 OW st E bo LB K SP B sX OWc mb -> get_data i st = Some (pd, nd) -> In (pd, badr OW pd, nd) OWc ->
  lo <= x -> y <= SP ->
  munch [(x, y); (badr OW pd, badr OW pd + 1)] mb mc -> wmono ctusegs mb mc ->
  rw_cells ctusegs mc (badr OW pd) [CB (Z.to_nat nd) junk'] ->
  seg_base s0 m0 OW st E bo LB K SP B sX OWc mc.
Proof.
  intros sX OWc mb mc i pd nd x y junk' (HEAP & AUX & LX & AR & RB & DC & DIN & KP & KOW & IES & SO & FA) GD HIn Hx Hy MU WM HC.
  assert (INCL : forall b, In b OWc -> In b (OWc ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  unfold GLOBALS_TOP in GLO. pose proof (proj1 (proj1 DC i pd nd GD)) as ND1.
  destruct (seg_close sX OWc LB _ mb mc lo SP B HEAP AUX CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP' & AUX' & LX').
  { constructor; [left; cbn; lia|]. constructor; [right; right; exists pd, (badr OW pd), nd; split; [exact HIn|cbn; lia]|constructor]. }
  split; [exact HEAP'|]. split; [exact AUX'|]. split; [eapply lx_pres_trans; [exact LX|exact LX']|].
  split.
  { eapply (rest_of_seg' sX (OWc ++ LB) _ mb mc); [exact AR|exact HEAP|exact RB|exact CEIL|unfold GLOBALS_TOP; lia|exact MU|exact WM|].
    constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HIn|].
    split; [eapply data_not_rest; [exact IDS|exact GD]|cbn; lia]. }
  split; [exact RB|]. split.
  { eapply (data_cells_store1 sX (OWc ++ LB) mb mc); [exact DC|exact DIN|apply INCL; exact HIn|exact ND1|exact HEAP|exact CEIL|exact Hx|exact MU|exact WM|exact HC]. }
  split; [exact DIN|]. split.
  { eapply kept_trans; [exact KP|]. eapply (kept_of_munch sX (OWc ++ LB) _ mb mc K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
    constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HIn|].
    split; [eapply K_not_es; [exact KIDS|]; eapply es_ids_data; exact GD|cbn; lia]. }
  split; [exact KOW|]. split; [exact IES|]. split; [exact SO|exact FA].
Qed.
End SegData.
