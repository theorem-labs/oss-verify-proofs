(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_artP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_lb_lf (st : rtstate) (LB : list (Z * Z)) (LF : list fframe) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 _ a18 a19 a20 a21 a22 _ b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 LF a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Permutation_filter' : forall {A} (f : A -> bool) (l l' : list A),
  Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
  - constructor.
  - cbn. destruct (f x); [apply perm_skip; exact IH| exact IH].
  - cbn. destruct (f y); destruct (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma zsum_perm : forall l l', Permutation l l' -> zsum l = zsum l'.
Proof.
  intros l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; unfold zsum in *; cbn in *; try lia.
Qed.

Lemma existsb_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros A f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn; try congruence.
  destruct (f y), (f x); reflexivity.
Qed.

Lemma Permutation_in' : forall {A} (l l' : list A) x, Permutation l l' -> In x l' -> In x l.
Proof. intros A l l' x H Hx. eapply Permutation_in; [apply Permutation_sym; exact H| exact Hx]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section P.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool)
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (LB LB' : list (Z * Z)) (LF LF' : list fframe).
Hypothesis PB : Permutation LB LB'.
Hypothesis PF : Permutation LF LF'.
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 LF a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5.
Let st' := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 LF' a18 a19 a20 a21 a22 LB' b1 b2 b3 b4 b5.

Lemma all_blocks_perm : Permutation (all_blocks st) (all_blocks st').
Proof. unfold all_blocks. cbn [st_lb st_qpend st st']. apply Permutation_app_tail. exact PB. Qed.

Lemma used_cptrs_perm : forall c, Permutation (used_cptrs st c) (used_cptrs st' c).
Proof.
  intros c. unfold used_cptrs. apply Permutation_app_head. apply Permutation_app_tail.
  unfold live_cptrs, lb_prim. cbn [st_lb st st']. apply Permutation_map. apply Permutation_filter'. exact PB.
Qed.

Lemma flag_val_perm : forall k pos, flag_val st' k pos = flag_val st k pos.
Proof.
  intros k pos. unfold flag_val, flag_live. cbn [st_lf st_fs st st'].
  rewrite (existsb_perm _ LF LF' PF). reflexivity.
Qed.

Lemma RTREP_perm : forall m, RTREP st m -> RTREP st' m.
Proof.
  intros m HR. constructor; try (exact (rr_link st m HR)); try (exact (rr_consts st m HR)); try (exact (rr_alloc st m HR));
    try (exact (rr_rinfo st m HR)); try (exact (rr_regions st m HR)); try (exact (rr_avail st m HR)); try (exact (rr_cache st m HR));
    try (exact (rr_thread st m HR)); try (exact (rr_quar st m HR)); try (exact (rr_batches st m HR)); try (exact (rr_ptrarr st m HR));
    try (exact (rr_depot st m HR)); try (exact (rr_ia st m HR)); try (exact (rr_lowshadow st m HR)).
  - (* [comment removed for export] *) intros A n Hin. exact (rr_live st m HR A n (Permutation_in' LB LB' _ PB Hin)).
  - (* [comment removed for export] *) destruct (rr_fs st m HR) as (V1 & V2 & H3 & H4 & H5 & H6 & H7).
    split; [exact V1|]. split; [exact V2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split.
    + intros k pos Hk Hp. rewrite flag_val_perm. exact (H6 k pos Hk Hp).
    + intros F k Hin. exact (H7 F k (Permutation_in' LF LF' _ PF Hin)).
Qed.

Lemma RTWF_perm : RTWF st -> RTWF st'.
Proof.
  intros WF. constructor.
  - destruct (wf_base_ok st WF); constructor; assumption.
  - intros c Hc. pose proof (wf_class_ok st WF c Hc) as WC. pose proof (used_cptrs_perm c) as PU.
    constructor; try (exact (wc_alloc_nonneg st c WC)); try (exact (wc_alloc_carved st c WC)); try (exact (wc_alloc_mapped st c WC));
      try (exact (wc_mapped_align st c WC)); try (exact (wc_mapped_max st c WC)); try (exact (wc_fa_nonneg st c WC));
      try (exact (wc_fa_align st c WC)); try (exact (wc_fa_max st c WC)); try (exact (wc_num_freed st c WC)); try (exact (wc_cache_max st c WC)).
    + intros k Hk. exact (wc_used_carved st c WC k (Permutation_in' _ _ _ PU Hk)).
    + eapply Permutation_NoDup; [exact PU| exact (wc_used_nodup st c WC)].
    + unfold zlen. rewrite <- (Permutation_length PU). exact (wc_used_all st c WC).
    + exact (wc_residue st c WC).
    + exact (wc_delta st c WC).
    + exact (wc_exh st c WC).
  - pose proof (wf_blocks_ok st WF) as WB. constructor.
    + intros b Hb. exact (wk_block st WB b (Permutation_in' _ _ _ all_blocks_perm Hb)).
    + eapply Permutation_NoDup; [apply Permutation_map; exact all_blocks_perm| exact (wk_nodup st WB)].
  - pose proof (wf_sec_ok st WF) as WS. constructor; try (exact (ws_nodup st WS)); try (exact (ws_nres st WS)).
    + intros e He. destruct (ws_entry st WS e He) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      destruct E4 as [E4|E4]; [left; eapply Permutation_in; [exact all_blocks_perm| exact E4]| right; exact E4].
    + intros e He. destruct (ws_spend st WS e He) as [S1 S2]. split; [exact S1|]. intros HB. apply S2.
      eapply Permutation_in; [apply Permutation_sym; exact all_blocks_perm| exact HB].
    + exact (ws_spend_nodup st WS).
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - pose proof (wf_fs_ok st WF) as WFF. constructor.
    + eapply Permutation_NoDup; [apply Permutation_map; exact PF| exact (wff_nodup st WFF)].
    + intros F k Hin. exact (wff_frame st WFF F k (Permutation_in' LF LF' _ PF Hin)).
Qed.

Lemma RTMODEL_perm : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.

Lemma rt_prov_perm : rt_prov st' = rt_prov st.
Proof.
  assert (E9 : prov_l24 st' = prov_l24 st).
  { unfold prov_l24, lb_prim. cbn [st_lb st st']. unfold zlen.
    rewrite (Permutation_length (Permutation_filter' (fun b : Z * Z => bprim (snd b) && (pclass (snd b) =? 24)) _ _ PB)). reflexivity. }
  unfold rt_prov. rewrite E9. unfold prov_live. cbn [st_lb st st'].
  rewrite (zsum_perm _ _ (Permutation_map (fun b : Z * Z => fp (snd b) + rp (snd b)) PB)). reflexivity.
Qed.
End P.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem artd_perm : forall sp0 SPB LB LB' LF LF' TRS B m mo g,
  ARTd sp0 SPB LB LF TRS B m mo g -> Permutation LB LB' -> Permutation LF LF' -> ARTd sp0 SPB LB' LF' TRS B m mo g.
Proof.
  intros sp0 SPB LB LB' LF LF' TRS B m mo g (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW) PB PF.
  exists (set_lb_lf st LB' LF'). destruct st. cbn in Hsp0, HLB, HLF, HTRS. subst. cbn [set_lb_lf].
  split; [eapply RTREP_perm; [exact PB| exact PF| exact HR]|]. split; [eapply RTWF_perm; [exact PB| exact PF| exact WF]|]. split; [exact HM|].
  split; [exact HO|]. split; [exact HB|]. split; [exact HG|]. split; [exact HFR|]. repeat (split; [reflexivity|]). split; [exact HQ|]. split; [exact HB0|]. split; [| split; [exact HSPB| exact HSW]].
  erewrite rt_prov_perm; [exact HB1| exact PB].
Qed.


End CeilWrap.
End RT_artP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
Import RT_artP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nthz_updz_len : forall {A} (l : list A) i x, length (updz l i x) = length l.
Proof. intros. apply updz_length. Qed.

Lemma filter_cons_true : forall {A} (f : A -> bool) x l, f x = true -> List.filter f (x :: l) = x :: List.filter f l.
Proof. intros A f x l H. cbn. rewrite H. reflexivity. Qed.
Lemma filter_cons_false : forall {A} (f : A -> bool) x l, f x = false -> List.filter f (x :: l) = List.filter f l.
Proof. intros A f x l H. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section POP.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (c k : Z) (pre : list Z).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Let st' := mkRT a1 a2 a3 a4 a5 (updz a6 c pre) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 ((c, k) :: b1) b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis HC : cch st c = pre ++ [k].
Hypothesis HAP : b1 = [].    (* [comment removed for export] *)

Lemma len_cache : length a6 = 32%nat.
Proof. exact (wb_len_cache st (wf_base_ok st WF)). Qed.

Lemma cch_pop_same : cch st' c = pre.
Proof. unfold cch. cbn [st_cache st']. apply nthz_updz_same. unfold zlen. rewrite len_cache. unfold KNUMCLASSES in *. lia. Qed.
Lemma cch_pop_other : forall c', c' <> c -> cch st' c' = cch st c'.
Proof. intros c' Hc'. unfold cch. cbn [st_cache st st']. apply nthz_updz_other. lia. Qed.
Lemma rg_pop : forall c', rg st' c' = rg st c'. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma apend_pop_same : apend_cptrs st' c = k :: apend_cptrs st c.
Proof. unfold apend_cptrs. cbn [st_apend st st']. rewrite filter_cons_true by (cbn; apply Z.eqb_refl). reflexivity. Qed.
Lemma apend_pop_other : forall c', c' <> c -> apend_cptrs st' c' = apend_cptrs st c'.
Proof. intros c' Hc'. unfold apend_cptrs. cbn [st_apend st st']. rewrite filter_cons_false by (cbn; apply Z.eqb_neq; lia). reflexivity. Qed.
Lemma qelems_pop : qelems st' = qelems st. Proof. reflexivity. Qed.
Lemma qall_pop : qall st' = qall st. Proof. reflexivity. Qed.
Lemma all_blocks_pop : all_blocks st' = all_blocks st. Proof. reflexivity. Qed.
Lemma live_pop : forall c', live_cptrs st' c' = live_cptrs st c'. Proof. reflexivity. Qed.
Lemma quar_pop : forall c', quar_cptrs st' c' = quar_cptrs st c'. Proof. reflexivity. Qed.
Lemma qpend_pop : forall c', qpend_cptrs st' c' = qpend_cptrs st c'. Proof. reflexivity. Qed.
Lemma batch_pop : forall c', batch_cptrs st' c' = batch_cptrs st c'. Proof. reflexivity. Qed.
Lemma ncarved_pop : forall c', ncarved st' c' = ncarved st c'. Proof. reflexivity. Qed.
Lemma carved_pop : forall c' j, carved_cptr st' c' j <-> carved_cptr st c' j. Proof. intros. reflexivity. Qed.

Lemma perm_mid : forall (P M A : list Z) (x : Z), Permutation (P ++ M ++ x :: A) ((P ++ [x]) ++ M ++ A).
Proof.
  intros. rewrite <- (app_assoc P [x] (M ++ A)). apply Permutation_app_head. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma used_pop_same : Permutation (used_cptrs st' c) (used_cptrs st c).
Proof.
  unfold used_cptrs, avail_cptrs. rewrite rg_pop, cch_pop_same, live_pop, quar_pop, qpend_pop, batch_pop, apend_pop_same, HC.
  set (F := r_fa (rg st c)). set (A := apend_cptrs st c).
  set (L1 := live_cptrs st c). set (L2 := quar_cptrs st c). set (L3 := qpend_cptrs st c). set (L4 := batch_cptrs st c).
  replace (L1 ++ L2 ++ L3 ++ L4 ++ k :: A) with ((L1 ++ L2 ++ L3 ++ L4) ++ k :: A) by (rewrite <- !app_assoc; reflexivity).
  replace (L1 ++ L2 ++ L3 ++ L4 ++ A) with ((L1 ++ L2 ++ L3 ++ L4) ++ A) by (rewrite <- !app_assoc; reflexivity).
  rewrite (app_assoc F pre [k]). apply perm_mid.
Qed.
Lemma used_pop_other : forall c', c' <> c -> used_cptrs st' c' = used_cptrs st c'.
Proof.
  intros c' Hc'. unfold used_cptrs, avail_cptrs. rewrite rg_pop, cch_pop_other, live_pop, quar_pop, qpend_pop, batch_pop, apend_pop_other by lia. reflexivity.
Qed.
Lemma navail_pop_same : navail st' c = navail st c - 1.
Proof. unfold navail, avail_cptrs. rewrite rg_pop, cch_pop_same, HC, !zlen_app, zlen_cons, zlen_nil. lia. Qed.
Lemma navail_pop_other : forall c', c' <> c -> navail st' c' = navail st c'.
Proof. intros c' H. unfold navail, avail_cptrs. rewrite rg_pop, cch_pop_other by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RTWF_pop : RTWF st'.
Proof.
  pose proof (wf_base_ok st WF) as WB.
  constructor.
  - destruct WB; constructor; try assumption.
    + cbn [st_cache st']. rewrite updz_length. assumption.
    + split; [apply (proj1 wb_class0)|]. rewrite cch_pop_other by lia. apply (proj2 wb_class0).
    + intros Hu c'. exfalso. cbn [st_cache_inited st'] in Hu. pose proof (wb_uninit Hu c) as E. fold st in E. rewrite HC in E. destruct pre; discriminate.
  - intros c' Hc'. pose proof (wf_class_ok st WF c' Hc') as WC. destruct (Z.eq_dec c' c) as [->|NE].
    + destruct WC; constructor; rewrite ?rg_pop, ?ncarved_pop; try assumption.
      * rewrite cch_pop_same. rewrite HC, zlen_app, zlen_cons, zlen_nil in wc_cache_max. lia.
      * intros j Hj. apply carved_pop. apply wc_used_carved. eapply Permutation_in; [exact used_pop_same| exact Hj].
      * eapply Permutation_NoDup; [apply Permutation_sym; exact used_pop_same| exact wc_used_nodup].
      * unfold zlen in *. rewrite (Permutation_length used_pop_same). exact wc_used_all.
    + destruct WC; constructor; rewrite ?rg_pop, ?ncarved_pop, ?cch_pop_other, ?used_pop_other by lia; try assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    + cbn [st_apend st_qpend st'] in *. cbn [st_apend st_qpend st] in wq_inflight. rewrite HAP. unfold zlen in *. cbn [length]. lia.
    + intros ck [<-|Hin]; [cbn; unfold KNUMCLASSES; lia| exact (wq_apend ck Hin)].
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma provU_pop_same : provU st' c <= provU st c + 2 * csize c.
Proof.
  unfold provU, delta. rewrite rg_pop, navail_pop_same. pose proof (csize_pos c ltac:(lia)). lia.
Qed.
Lemma provU_pop_other : forall c', c' <> c -> provU st' c' = provU st c'.
Proof. intros c' H. unfold provU, delta. rewrite rg_pop, navail_pop_other by lia. reflexivity. Qed.
Lemma provF_pop : forall c', provF st' c' = provF st c'.
Proof. intros. unfold provF, fa_cap. rewrite rg_pop, ncarved_pop. reflexivity. Qed.

Lemma zsum_cons : forall x l, zsum (x :: l) = x + zsum l. Proof. reflexivity. Qed.
Lemma zsum_map_ext : forall (f g : Z -> Z) l, (forall y, In y l -> f y = g y) -> zsum (map f l) = zsum (map g l).
Proof.
  intros f g l H. induction l as [|y l IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons.
  rewrite (H y ltac:(left; reflexivity)), IH; [reflexivity|]. intros z Hz. apply H. right. exact Hz.
Qed.
Lemma zsum_map_le : forall (f g : Z -> Z) l d x, (forall y, In y l -> y <> x -> f y = g y) -> f x <= g x + d -> 0 <= d ->
  List.NoDup l -> zsum (map f l) <= zsum (map g l) + d.
Proof.
  intros f g l d x Hfg Hx Hd ND. induction l as [|y l IH]; [cbn; unfold zsum; cbn; lia|].
  inversion ND as [|y' l' Hni ND']; subst. cbn [map]. rewrite !zsum_cons.
  destruct (Z.eq_dec y x) as [->|NE].
  - rewrite (zsum_map_ext f g l); [lia|]. intros z Hz. apply Hfg; [right; exact Hz|]. intros ->. exact (Hni Hz).
  - rewrite (Hfg y ltac:(left; reflexivity) NE).
    specialize (IH ltac:(intros w Hw Hne; apply Hfg; [right; exact Hw| exact Hne]) ND'). lia.
Qed.

Lemma classes_nodup : List.NoDup classes.
Proof. unfold classes. apply Finite.Injective_map_NoDup; [intros x y H; lia| apply seq_NoDup]. Qed.

Lemma prov_classes_pop : prov_classes st' <= prov_classes st + 2 * csize c.
Proof.
  unfold prov_classes. apply (zsum_map_le _ _ classes (2 * csize c) c).
  - intros y Hy Hne. rewrite provU_pop_other, provF_pop by exact Hne. reflexivity.
  - rewrite provF_pop. pose proof provU_pop_same. lia.
  - pose proof (csize_pos c ltac:(lia)). lia.
  - apply classes_nodup.
Qed.

Lemma rt_prov_pop : rt_prov st' <= rt_prov st + 2 * csize c.
Proof.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_depot st' = prov_depot st) by reflexivity.
  assert (E8 : prov_slots st' = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 st' = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb st' = prov_emb st) by reflexivity.   (* [comment removed for export] *)
  unfold rt_prov. rewrite E2, E3, E4, E5, E6, E7, E8, E9, E10. pose proof prov_classes_pop. lia.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_pop : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_pop : forall m mo g, GWIN st m mo g -> GWIN st' m mo g.
Proof. intros m mo g H. exact H. Qed.
End POP.


End CeilWrap.
