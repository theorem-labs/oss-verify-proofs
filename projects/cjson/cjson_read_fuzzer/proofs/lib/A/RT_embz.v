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
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RT_emb.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rg_set_exh (r : region_st) : region_st :=
  mkRegion (r_allocated r) (r_mapped r) (r_mapped_fa r) true (r_fa r).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TR.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EXH.
Variable cls : Z.
Hypothesis Hcls : 1 <= cls <= 31.
(* [comment removed for export] *)
Hypothesis HX : r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls.
Let stE := mkRT a1 a2 a3 (updz a4 cls (rg_set_exh (rg st cls))) a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.

Lemma exh_rg : forall c, rg stE c = if c =? cls then rg_set_exh (rg st cls) else rg st c.
Proof.
  intros c. unfold rg. cbn [st_regions stE st]. pose proof (wb_len_regions st (wf_base_ok st WF)) as L. cbn [st_regions st] in L.
  destruct (Z.eqb_spec c cls) as [->|NE].
  - apply nthz_updz_same. unfold zlen. rewrite L. lia.
  - rewrite nthz_updz_other by lia. reflexivity.
Qed.
Lemma exh_proj : forall c,
  r_allocated (rg stE c) = r_allocated (rg st c) /\ r_mapped (rg stE c) = r_mapped (rg st c)
  /\ r_mapped_fa (rg stE c) = r_mapped_fa (rg st c) /\ r_fa (rg stE c) = r_fa (rg st c).
Proof. intros c. rewrite exh_rg. destruct (Z.eqb_spec c cls) as [->|NE]; [cbn; repeat split; reflexivity| repeat split; reflexivity]. Qed.
Lemma exh_exhausted : forall c, r_exhausted (rg stE c) = if c =? cls then true else r_exhausted (rg st c).
Proof. intros c. rewrite exh_rg. destruct (c =? cls); reflexivity. Qed.

(* [comment removed for export] *)
Lemma exh_ncarved : forall c, ncarved stE c = ncarved st c.
Proof. intros c. unfold ncarved. rewrite (proj1 (exh_proj c)). reflexivity. Qed.
Lemma exh_num_freed : forall c, num_freed stE c = num_freed st c.
Proof. intros c. unfold num_freed. rewrite (proj2 (proj2 (proj2 (exh_proj c)))). reflexivity. Qed.
Lemma exh_fa_cap : forall c, fa_cap stE c = fa_cap st c.
Proof. intros c. unfold fa_cap. rewrite (proj1 (proj2 (proj2 (exh_proj c)))). reflexivity. Qed.
Lemma exh_cch : forall c, cch stE c = cch st c. Proof. reflexivity. Qed.
Lemma exh_carved : forall c k, carved_cptr stE c k <-> carved_cptr st c k.
Proof. intros c k. unfold carved_cptr. rewrite exh_ncarved. reflexivity. Qed.
Lemma exh_avail : forall c, avail_cptrs stE c = avail_cptrs st c.
Proof. intros c. unfold avail_cptrs. rewrite (proj2 (proj2 (proj2 (exh_proj c)))). reflexivity. Qed.
Lemma exh_used : forall c, used_cptrs stE c = used_cptrs st c.
Proof. intros c. unfold used_cptrs. rewrite exh_avail. reflexivity. Qed.
Lemma exh_navail : forall c, navail stE c = navail st c.
Proof. intros c. unfold navail. rewrite exh_avail. reflexivity. Qed.
Lemma exh_all_blocks : all_blocks stE = all_blocks st. Proof. reflexivity. Qed.
Lemma exh_qall : qall stE = qall st. Proof. reflexivity. Qed.
Lemma exh_rt_ranges : rt_ranges stE = rt_ranges st. Proof. reflexivity. Qed.
Lemma exh_rt_loose : rt_loose stE = rt_loose st. Proof. reflexivity. Qed.
Lemma exh_b_cptr : forall A n, b_cptr stE A n = b_cptr st A n. Proof. reflexivity. Qed.
Lemma exh_cptr_addr : forall c k, cptr_addr stE c k = cptr_addr st c k. Proof. reflexivity. Qed.

Lemma nexh_exh : nexh stE = (if r_exhausted (rg st cls) then nexh st else nexh st + 1).
Proof.
  unfold nexh. cbn [st_regions stE st]. pose proof (wb_len_regions st (wf_base_ok st WF)) as L. cbn [st_regions st] in L.
  rewrite count_exh_updz by (unfold zlen; rewrite L; lia). unfold rg. cbn [st_regions st r_exhausted rg_set_exh].
  destruct (r_exhausted (nthz a4 cls region0)); lia.
Qed.
Lemma nexh_exh_ge : nexh st <= nexh stE <= nexh st + 1.
Proof. rewrite nexh_exh. destruct (r_exhausted (rg st cls)); lia. Qed.

Lemma RTWF_exh : RTWF stE.
Proof.
  pose proof (wf_base_ok st WF) as WB.
  constructor.
  - destruct WB; constructor; try assumption.
    + cbn [st_regions stE]. rewrite updz_length. exact wb_len_regions.
    + destruct wb_class0 as [C1 C2]. split; [| exact C2]. rewrite exh_rg. replace (0 =? cls) with false by (symmetry; apply Z.eqb_neq; lia). exact C1.
    + pose proof nexh_exh_ge. unfold emb_sz in *. cbn [st_tls stE st] in *. unfold EMB_MSG in *. lia.
  - intros c Hc. pose proof (wf_class_ok st WF c Hc) as WC. pose proof (exh_proj c) as (P1 & P2 & P3 & P4).
    destruct WC; constructor; rewrite ?P1, ?P2, ?P3, ?exh_ncarved, ?exh_num_freed, ?exh_cch, ?exh_used; try assumption.
    + intros k Hk. apply exh_carved. exact (wc_used_carved k Hk).
    + (* [comment removed for export] *) rewrite exh_exhausted. destruct (Z.eqb_spec c cls) as [->|NE]; [intros _; exact HX| exact wc_exh].
  - pose proof (wf_blocks_ok st WF) as WK. constructor; [| exact (wk_nodup st WK)].
    intros b Hb. exact (wk_block st WK b Hb).
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - pose proof (wf_quar_ok st WF) as WQ. destruct WQ; constructor; try assumption.
    intros b Hb. destruct (wq_batch b Hb) as [Q1 (k & Q2 & Q3)]. split; [exact Q1|]. exists k. split; [apply exh_carved; exact Q2| exact Q3].
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma prov_classes_exh : prov_classes stE = prov_classes st.
Proof.
  unfold prov_classes. f_equal. apply map_ext. intros c.
  unfold provU, provF, delta. pose proof (exh_proj c) as (P1 & P2 & P3 & P4). rewrite P1, P2, exh_navail, exh_fa_cap, exh_ncarved. reflexivity.
Qed.
Lemma rt_prov_exh : rt_prov stE = rt_prov st.
Proof.
  assert (E2 : prov_nb stE = prov_nb st) by reflexivity.
  assert (E3 : prov_q stE = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stE = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stE = prov_live st) by reflexivity.
  assert (E6 : prov_quar stE = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stE = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stE = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 stE = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stE = prov_emb st) by reflexivity.
  unfold rt_prov. rewrite prov_classes_exh, E2, E3, E4, E5, E6, E7, E8, E9, E10. reflexivity.
Qed.
Lemma RTMODEL_exh : forall mo, RTMODEL st mo -> RTMODEL stE mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_exh : forall m mo g, GWIN st m mo g -> GWIN stE m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_exh : forall g, SWIN st g -> SWIN stE g.
Proof. intros g H. exact H. Qed.
Lemma QUIET_exh : QUIET st -> QUIET stE.
Proof. intros H. exact H. Qed.
End EXH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NEW.
Variables (d sz : Z).
Hypothesis Hd0 : emb_d st = 0.
Hypothesis Hal : d mod 4096 = 0.
Hypothesis Hblk : ablk d (d + EMB_CAP).   (* [comment removed for export] *)
Hypothesis Hhi : d + EMB_CAP <= CEIL.
Hypothesis FRESH : forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d.
Hypothesis Hsz : 0 <= sz <= EMB_MSG * nexh st.
Let tlsN := mkTLS (tl_dtls_block a20) (tl_dtls_w a20) d sz.
Let stN := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 tlsN (a21 ++ [(d, EMB_CAP)]) a22 LB AP SP QP b4 b5.

Lemma embN_d : emb_d stN = d. Proof. reflexivity. Qed.
Lemma embN_sz : emb_sz stN = sz. Proof. reflexivity. Qed.
Lemma embN_nexh : nexh stN = nexh st. Proof. reflexivity. Qed.
Lemma embN_dtls_same : dtls_same st stN. Proof. split; reflexivity. Qed.
Lemma embN_loose0_ext : loose0_ext st stN. Proof. exists [(d, EMB_CAP)]. reflexivity. Qed.
Lemma embN_all_blocks : all_blocks stN = all_blocks st. Proof. reflexivity. Qed.
Lemma embN_rg : forall c, rg stN c = rg st c. Proof. reflexivity. Qed.
Lemma embN_cch : forall c, cch stN c = cch st c. Proof. reflexivity. Qed.
Lemma embN_used : forall c, used_cptrs stN c = used_cptrs st c. Proof. reflexivity. Qed.
Lemma d_ne0 : d <> 0. Proof. pose proof (ablk_lin _ _ Hblk) as X. unfold AIMG_HI in X. lia. Qed.

Lemma embN_rt_ranges_eq : rt_ranges stN =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21)
  ++ (d, d + EMB_CAP) :: (map (fun e => (fst e, fst e + smapsize (snd e))) a9
      ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof.
  unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot stN]. rewrite map_app. cbn [map app fst snd].
  rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.
Lemma rt_ranges_split0 : rt_ranges st =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21)
  ++ (map (fun e => (fst e, fst e + smapsize (snd e))) a9
      ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof. unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot st]. cbn [app]. rewrite <- ?app_assoc. reflexivity. Qed.
Lemma embN_rt_ranges : Permutation (rt_ranges stN) ((d, d + EMB_CAP) :: rt_ranges st).
Proof. rewrite embN_rt_ranges_eq, rt_ranges_split0. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma embN_In_ranges : forall r, In r (rt_ranges stN) <-> r = (d, d + EMB_CAP) \/ In r (rt_ranges st).
Proof.
  intros r. split; intros H.
  - apply (Permutation_in _ embN_rt_ranges) in H. destruct H as [E|H]; [left; symmetry; exact E| right; exact H].
  - eapply Permutation_in; [apply Permutation_sym; exact embN_rt_ranges|]. destruct H as [->|H]; [left; reflexivity| right; exact H].
Qed.
Lemma embN_rt_loose : forall e, In e (rt_loose stN) <-> e = (d, EMB_CAP) \/ In e (rt_loose st).
Proof.
  intros e. unfold rt_loose. cbn [st_loose0 st_sec st_depot stN st]. rewrite !in_app_iff. cbn [In]. split; intros H.
  - destruct H as [[H|[H|[]]]|H]; [right; left; exact H| left; symmetry; exact H| right; right; exact H].
  - destruct H as [->|[H|H]]; [left; right; left; reflexivity| left; left; exact H| right; exact H].
Qed.

#[using="Hsz FRESH Hhi Hblk Hal Hd0 WF st"] Lemma RTWF_embN : RTWF stN.
Proof.
  pose proof (wf_base_ok st WF) as WB. pose proof d_ne0 as NZ.
  constructor.
  - destruct WB; constructor; try assumption.
    + (* [comment removed for export] *) intros r Hr. apply embN_In_ranges in Hr as [->|Hr]; [cbn [fst snd]; unfold CEIL, EMB_CAP in *; blia| exact (wb_ranges r Hr)].
    + (* [comment removed for export] *) rewrite embN_rt_ranges_eq. apply pwdj_insert; [rewrite <- rt_ranges_split0; exact wb_pwdj|].
      rewrite <- rt_ranges_split0. apply Forall_forall. intros r Hr. cbn [fst snd]. destruct (FRESH r Hr); lia.
    + cbn [st_t st_loose0 stN]. apply in_or_app. left. exact wb_t_loose.
    + cbn [st_fs st_loose0 stN]. apply in_or_app. left. exact wb_fs_loose.
    + destruct wb_ctx_loose as (b & k & L1 & L2 & L3). exists b, k. split; [cbn [st_loose0 stN]; apply in_or_app; left; exact L1| split; assumption].
    + destruct wb_dtls_loose as (b & k & L1 & L2 & L3). exists b, k. cbn [st_tls stN tlsN tl_dtls_block] in *.
      split; [cbn [st_loose0 stN]; apply in_or_app; left; exact L1| split; assumption].
    + (* [comment removed for export] *) intros _. cbn [emb_d st_tls st_loose0 stN tlsN tl_emb_d]. apply in_or_app. right. left. reflexivity.
    + (* [comment removed for export] *) intros _. unfold emb_d. cbn [st_tls st_ctx stN tlsN tl_emb_d].
      destruct wb_ctx_loose as (b & k & L1 & L2 & L3). cbn [st_ctx st] in L2, L3.
      destruct (FRESH (b, b + k) ltac:(unfold rt_ranges; do 2 right; apply in_or_app; left; apply in_map_iff; exists (b, k); auto)); cbn [fst snd] in *; lia.
    + (* [comment removed for export] *) intros _. rewrite embN_d.
      assert (ED : tl_dtls_block (st_tls stN) = tl_dtls_block (st_tls st)) by reflexivity. rewrite ED.
      destruct wb_dtls_loose as (b & k & L1 & L2 & L3).
      destruct (FRESH (b, b + k) ltac:(unfold rt_ranges; do 2 right; apply in_or_app; left; apply in_map_iff; exists (b, k); auto)); cbn [fst snd] in *; lia.
    + (* [comment removed for export] *) change (emb_d stN = 0 -> emb_sz stN = 0). rewrite embN_d. intros E. (lia_on Hd0 wb_sp0 wb_nres NZ E).
  - intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma rt_prov_embN : rt_prov stN = rt_prov st - EMB_CAP.
Proof.
  assert (E1 : prov_classes stN = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stN = prov_nb st) by reflexivity.
  assert (E3 : prov_q stN = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stN = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stN = prov_live st) by reflexivity.
  assert (E6 : prov_quar stN = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stN = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stN = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 stN = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stN = prov_emb st - EMB_CAP).
  { unfold prov_emb. rewrite embN_d, Hd0. cbn [Z.eqb]. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact d_ne0). lia. }
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. lia.
Qed.

Lemma RTMODEL_embN : forall mo, RTMODEL st mo -> d + EMB_CAP <= 2^64 ->
  RTMODEL stN (mm_add_map (wz d) (wz EMB_CAP) mo).
Proof.
  intros mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) HB.
  assert (U1 : bv_unsigned (wz d) = d) by (unfold wz; apply unsigned_lit; pose proof (ablk_lin _ _ Hblk) as X; unfold AIMG_HI, EMB_CAP in *; lia).
  assert (U2 : bv_unsigned (wz EMB_CAP) = EMB_CAP) by (unfold wz; apply unsigned_lit; unfold EMB_CAP; lia).
  unfold RTMODEL. rewrite mm_add_map_vmmaps. cbn [vm_maps vm_limit st_pbase st_pa st_sec stN st].
  split; [right; exact M1|]. split; [right; exact M2|]. split; [right; exact M3|]. split; [right; exact M4|].
  split; [| split; [| split; [| split]]].
  - intros e He. apply embN_rt_loose in He as [->|He]; [left; reflexivity| right; exact (M5 e He)].
  - (* [comment removed for export] *) right; exact M6.
  - intros x Hx. rewrite mm_add_map_lzf. exact (M7 x Hx).
  - exact M8.
  - intros e He x Hx. unfold sec_plain in *.
    change (m_vm_lazy (mm_add_map (wz d) (wz EMB_CAP) mo)) with (m_vm_lazy mo).
    change (vm_noaccess (m_vmmaps (mm_add_map (wz d) (wz EMB_CAP) mo))) with (vm_noaccess (m_vmmaps mo)).
    exact (M9 e He x Hx).
Qed.
Lemma GWIN_embN_map : forall m mo g, GWIN st m mo g -> GWIN stN m (mm_add_map (wz d) (wz EMB_CAP) mo) g.
Proof. intros m mo g H x Hw Hz Hr. rewrite mm_add_map_lzf in Hz. exact (H x Hw Hz Hr). Qed.
Lemma GWIN_embN : forall m mo g, GWIN st m mo g -> GWIN stN m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_embN : forall g, SWIN st g -> SWIN stN g.
Proof. intros g H. exact H. Qed.
Lemma QUIET_embN : QUIET st -> QUIET stN.
Proof. intros H. exact H. Qed.
End NEW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section APP.
Variable sz : Z.
Hypothesis Hd : emb_d st <> 0.
Hypothesis Hsz : 0 <= sz <= EMB_MSG * nexh st.
Let tlsA := mkTLS (tl_dtls_block a20) (tl_dtls_w a20) (tl_emb_d a20) sz.
Let stA := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 tlsA a21 a22 LB AP SP QP b4 b5.

Lemma embA_d : emb_d stA = emb_d st. Proof. reflexivity. Qed.
Lemma embA_sz : emb_sz stA = sz. Proof. reflexivity. Qed.
Lemma embA_nexh : nexh stA = nexh st. Proof. reflexivity. Qed.
Lemma embA_dtls_same : dtls_same st stA. Proof. split; reflexivity. Qed.
Lemma embA_loose0_ext : loose0_ext st stA. Proof. apply loose0_ext_of_eq. reflexivity. Qed.
Lemma embA_rt_ranges : rt_ranges stA = rt_ranges st. Proof. reflexivity. Qed.
Lemma embA_rt_loose : rt_loose stA = rt_loose st. Proof. reflexivity. Qed.

Lemma RTWF_embA : RTWF stA.
Proof.
  pose proof (wf_base_ok st WF) as WB.
  constructor.
  - destruct WB; constructor; try assumption.
    + change (emb_d stA = 0 -> emb_sz stA = 0). rewrite embA_d. intros E. exfalso. exact (Hd E).
  - intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.
Lemma rt_prov_embA : rt_prov stA = rt_prov st.
Proof.
  assert (E1 : prov_classes stA = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stA = prov_nb st) by reflexivity.
  assert (E3 : prov_q stA = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stA = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stA = prov_live st) by reflexivity.
  assert (E6 : prov_quar stA = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stA = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stA = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 stA = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stA = prov_emb st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. reflexivity.
Qed.
Lemma RTMODEL_embA : forall mo, RTMODEL st mo -> RTMODEL stA mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_embA : forall m mo g, GWIN st m mo g -> GWIN stA m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_embA : forall g, SWIN st g -> SWIN stA g.
Proof. intros g H. exact H. Qed.
Lemma QUIET_embA : QUIET st -> QUIET stA.
Proof. intros H. exact H. Qed.
End APP.
End TR.

(* [comment removed for export] *)
Section NCT.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.

(* [comment removed for export] *)
Lemma RTREP_nc_emb : forall d sz l m,
  RTREP_nc st m ->
  RTREP_nc (mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 (mkTLS (tl_dtls_block a20) (tl_dtls_w a20) d sz) l a22 LB AP SP QP b4 b5) m.
Proof. intros d sz l m H. destruct a20. exact H. Qed.

(* [comment removed for export] *)
Lemma RTREP_nc_exh : forall cls m, 1 <= cls <= 31 ->
  let stE := mkRT a1 a2 a3 (updz a4 cls (rg_set_exh (rg st cls))) a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 in
  RTREP_nc st m ->
  (exists jr je js, rw_cells asegs m (rinfo st cls) (rinfo_cells stE cls jr je js)) ->
  RTREP_nc stE m.
Proof.
  intros cls m Hcls stE (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16) HL.
  pose proof (exh_proj a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 WF cls Hcls) as PJ. fold st stE in PJ.
  pose proof (exh_rg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 WF cls Hcls) as RG. fold st stE in RG.
  pose proof (exh_num_freed a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 WF cls Hcls) as NF. fold st stE in NF.
  pose proof (exh_avail a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 WF cls Hcls) as AV. fold st stE in AV.
  unfold RTREP_nc.
  split; [exact X1|]. split; [exact X3|].
  split.
  { (* [comment removed for export] *) destruct X4 as [V H]. split; [exact V|]. intros c Hc.
    destruct (Z.eq_dec c cls) as [->|NE]; [exact HL|].
    destruct (H c Hc) as (jr & je & js & RC). exists jr, je, js.
    unfold rinfo_cells in *. rewrite RG. replace (c =? cls) with false by (symmetry; apply Z.eqb_neq; exact NE). rewrite NF. exact RC. }
  split.
  { (* [comment removed for export] *) intros c Hc. pose proof (X5 c Hc) as R5. cbn zeta in *. destruct (PJ c) as (P1 & P2 & P3 & P4).
    rewrite P1, P2, P3, P4, NF. exact R5. }
  split. { (* [comment removed for export] *) intros c k Hc Hk. rewrite AV in Hk. exact (X6 c k Hc Hk). }
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; assumption.
Qed.
End NCT.

End CeilWrap.
End RT_emb.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kit RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0.
Import RT_emb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition WOK_consts_rest (W : list (Z * Z)) : Prop :=
  disjoint_from W A_SHADOW_OFF_CELL 8 /\ disjoint_from W A_UAR_OPTION 4 /\ disjoint_from W A_AFLAGS 120
  /\ disjoint_from W A_CFLAGS 288 /\ disjoint_from W A_PAGESIZE_CACHED 8 /\ disjoint_from W A_KHIGHMEMEND 8
  /\ disjoint_from W A_KMIDMEMBEG 8 /\ disjoint_from W A_KMIDMEMEND 8 /\ disjoint_from W A_ASAN_INITED 3
  /\ disjoint_from W A_MCS 4 /\ disjoint_from W A_CAN_POISON 1 /\ disjoint_from W A_TSD_KEY_INITED 1
  /\ disjoint_from W A_TSD_KEY 4 /\ disjoint_from W A_MAY_RETURN_NULL 2 /\ disjoint_from W A_ALLOC_OOM 1
  /\ disjoint_from W A_DYING 4 /\ disjoint_from W A_VERBOSITY 4 /\ disjoint_from W A_MFHOOKS 80
  /\ disjoint_from W A_LSAN_DISABLE 4 /\ disjoint_from W A_IA_INITED 4 /\ disjoint_from W AHOOKS 24
  /\ disjoint_from W A_LIBC_PAGESIZE 8 /\ disjoint_from W A_MU_GLOBALS 8 /\ disjoint_from W A_GLOBALS_REGD 8
  /\ disjoint_from W A_TPCG_INITED 1
  /\ disjoint_from W A_TOOLNAME 8 /\ disjoint_from W A_PRINTF_CB 8.
Lemma WOK_consts_rest_of : forall W, WOK_consts W -> WOK_consts_rest W.
Proof. intros W H. unfold WOK_consts, WOK_consts_rest in *. tauto. Qed.
Lemma WOK_consts_rest_app : forall W1 W2, WOK_consts_rest W1 -> WOK_consts_rest W2 -> WOK_consts_rest (W1 ++ W2).
Proof.
  unfold WOK_consts_rest. intros W1 W2 H1 H2.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; (apply disjoint_from_app; split; tauto).
Qed.

(* [comment removed for export] *)
Section EZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (W : list (Z * Z)) (elo ehi : Z).
(* [comment removed for export] *)
Hypothesis HBA : ablk elo ehi.
Hypothesis Hz : forall a sz, (a + sz <= A_EMB \/ A_EMB + 56 <= a) -> a + sz <= CEIL -> (a + sz <= elo \/ ehi <= a) -> disjoint_from W a sz.
Lemma Hlow : forall a sz, a + sz <= A_EMB -> disjoint_from W a sz.
Proof. intros a sz H. pose proof alloc_ceiling_range as ACR. apply Hz; [left; exact H| unfold CEIL, A_EMB in *; lia| left; unfold A_EMB in *; blia]. Qed.
(* [comment removed for export] *)
Lemma Himg : forall a sz, A_EMB + 56 <= a -> a + sz <= AIMG_HI -> disjoint_from W a sz.
Proof. intros a sz H1 H2. pose proof alloc_ceiling_range as ACR. apply Hz; [right; exact H1| unfold CEIL, AIMG_HI in *; lia| left; blia]. Qed.
(* [comment removed for export] *)
Lemma Hband : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. pose proof alloc_ceiling_range as ACR.
  apply Hz; [right; unfold A_EMB, KLOWSHADOW_BEG in *; lia| unfold CEIL, KHIGHMEM_BEG in *; lia| destruct (ablk_disj_band _ _ HBA); [right| left]; lia].
Qed.
(* [comment removed for export] *)
Lemma Hhigh : forall a sz, (a + sz <= AIMG_LO \/ AIMG_HI <= a) -> a + sz <= CEIL -> (a + sz <= elo \/ ehi <= a) -> disjoint_from W a sz.
Proof. intros a sz H1 H2 H3. apply Hz; [unfold A_EMB, AIMG_LO, AIMG_HI in *; lia| exact H2| exact H3]. Qed.
(* [comment removed for export] *)
Hypothesis HBLK : (forall r, In r (rt_ranges st) -> ehi <= fst r \/ snd r <= elo)
               \/ (emb_d st <> 0 /\ elo = emb_d st /\ ehi = emb_d st + EMB_CAP).
Local Abbreviation P := (st_pbase st).

(* [comment removed for export] *)
Lemma blk_disj : forall r, In r (rt_ranges st) -> r <> (elo, ehi) -> ehi <= fst r \/ snd r <= elo.
Proof.
  intros r Hr NE. destruct HBLK as [F|(Hd & E1 & E2)]; [exact (F r Hr)|].
  assert (HB : In (emb_d st, emb_d st + EMB_CAP) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (emb_d st, EMB_CAP).
    split; [reflexivity| exact (wb_emb_loose st (wf_base_ok st WF) Hd)]. }
  rewrite E1, E2 in NE |- *.
  destruct (pwdj_In _ _ _ (wb_pwdj st (wf_base_ok st WF)) Hr HB) as [E|D]; [exfalso; exact (NE E)|]. cbn [fst snd] in D. lia.
Qed.
(* [comment removed for export] *)
Lemma EZrange : forall r a sz, In r (rt_ranges st) -> r <> (elo, ehi) -> fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.
Proof.
  intros r a sz Hr NE H1 H2. (nelimp (wb_ranges st (wf_base_ok st WF) r Hr) 4%nat; intros R1 R2 R3 R4).
  apply Hhigh; [blia| unfold CEIL; lia|]. destruct (blk_disj r Hr NE); lia.
Qed.
(* [comment removed for export] *)
Lemma EZrange_len : forall r a sz, In r (rt_ranges st) -> snd r - fst r <> EMB_CAP -> fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.
Proof.
  intros r a sz Hr HL H1 H2. apply (EZrange r); try assumption. intros E. apply HL. rewrite E. cbn [fst snd].
  destruct HBLK as [F|(Hd & E1 & E2)]; [| lia].
  exfalso. (nelimp (wb_ranges st (wf_base_ok st WF) r Hr) 4%nat; intros R1 R2 R3 R4). destruct (F r Hr); rewrite E in *; cbn [fst snd] in *; lia.
Qed.

Lemma EZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. apply (EZrange_len (P, P + PRIM_RES_SIZE)); [left; reflexivity| cbn; unfold PRIM_RES_SIZE, EMB_CAP; lia| cbn; lia| cbn; lia].
Qed.
Lemma EZpa : forall a sz, st_pa st <= a -> a + sz <= st_pa st + PTRARR_RES_SIZE -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. apply (EZrange_len (st_pa st, st_pa st + PTRARR_RES_SIZE)); [right; left; reflexivity| cbn; unfold PTRARR_RES_SIZE, EMB_CAP; lia| cbn; lia| cbn; lia].
Qed.
(* [comment removed for export] *)
Lemma EZloose_sz : forall b k a sz, In (b, k) (st_loose0 st) -> k <> EMB_CAP -> b <= a -> a + sz <= b + k -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin Hk H1 H2. apply (EZrange_len (b, b + k)); [| cbn; lia| cbn; lia| cbn; lia].
  unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (b, k). auto.
Qed.
(* [comment removed for export] *)
Lemma EZtail : forall r a sz,
  In r (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
        ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
        ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))) ->
  fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.
Proof.
  intros r a sz Hr H1 H2.
  assert (HR : In r (rt_ranges st)) by (rewrite rt_ranges_tail; cbn [app]; do 2 right; apply in_or_app; right; exact Hr).
  (nelimp (wb_ranges st (wf_base_ok st WF) r HR) 4%nat; intros R1 R2 R3 R4).
  apply Hhigh; [blia| unfold CEIL; lia|]. destruct HBLK as [F|(Hd & E1 & E2)]; [destruct (F r HR); lia|].
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. (nelim PW 3%nat; intros _ _ PW).
  pose proof (pwdj_app_disj _ _ (emb_d st, emb_d st + EMB_CAP) r PW
                ltac:(apply in_map_iff; exists (emb_d st, EMB_CAP); split; [reflexivity| exact (wb_emb_loose st (wf_base_ok st WF) Hd)]) Hr) as D.
  cbn [fst snd] in D. lia.
Qed.
Lemma EZsec : forall e a sz, In e (st_sec st) -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz He H1 H2. apply (EZtail (fst e, fst e + smapsize (snd e))); [| cbn; lia| cbn; lia].
  apply in_or_app. left. apply in_map_iff. exists e. auto.
Qed.
Lemma EZnb : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Proof.
  intros b a sz Hb H1 H2. apply (EZtail (b, b + NODEBLOCK_SIZE)); [| cbn; lia| cbn; lia].
  apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists b. auto.
Qed.
Lemma EZsh : forall x k, 0 <= x -> 0 <= k -> x + 8 * k <= CEIL -> disjoint_from W (SH x) k.
Proof.
  intros x k H0 Hk Hx. pose proof alloc_ceiling_range as ACR. apply Hband; unfold SH, SHADOW_OFFSET, CEIL, KLOWSHADOW_BEG, KHIGHMEM_BEG in *; Z.div_mod_to_equations; lia.
Qed.
Lemma EZsh2 : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2. pose proof alloc_ceiling_range as ACR. apply Hband; unfold SH, SHADOW_OFFSET, CEIL, KLOWSHADOW_BEG, KHIGHMEM_BEG in *; Z.div_mod_to_equations; lia.
Qed.

Local Ltac lowmid := first [ apply Hlow; unfold A_EMB; lia | apply Himg; unfold A_EMB, AIMG_HI; lia | apply Hband; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia ].

(* [comment removed for export] *)
Lemma EZ_link : WOK_link W.
Proof.
  split; [intros a v Hin; destruct (alink_range a v Hin); lowmid| unfold A_GLOBREC_LO, A_GLOBREC_HI; lowmid].
Qed.
Lemma EZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.
Lemma EZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. lowmid. Qed.
Lemma EZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. lowmid.
Qed.

(* [comment removed for export] *)
Lemma EZ_rinfo : WOK_rinfo st W.
Proof.
  intros c Hc. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc.
  apply EZprim; unfold rinfo; lia.
Qed.
Lemma EZ_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply EZprim; lia.
  - apply EZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.
Lemma EZ_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  (nelim (carved_chunk st WF c k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *.
  apply EZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma EZt : forall a sz, st_t st <= a -> a + sz <= st_t st + 4096 -> disjoint_from W a sz.
Proof. intros a sz H1 H2. eapply (EZloose_sz (st_t st) 4096); [exact (wb_t_loose st (wf_base_ok st WF))| unfold EMB_CAP; lia| exact H1| exact H2]. Qed.
Lemma EZ_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply EZt; unfold pcaddr, acache, T_ACACHE; lia.
  - intros i Hi. apply EZt; unfold pcaddr, acache, T_ACACHE; lia.
Qed.
Lemma EZ_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply EZt; lia|].
  split; [apply EZt; unfold qcache_t, T_QCACHE; lia|].
  split; [apply EZt; unfold T_UNWINDING; lia|].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelim (loose0_range st WF _ _ CL1) 4%nat; intros R1 R2 R3 R4).
  assert (CL : In (cb, cb + ck) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (cb, ck). auto. }
  assert (CTX : forall a sz, st_ctx st <= a -> a + sz <= st_ctx st + 160 -> disjoint_from W a sz).
  { intros a sz H1 H2. apply Hhigh; [blia| unfold CEIL; lia|].
    destruct HBLK as [F|(Hd & E1 & E2)]; [destruct (F _ CL); cbn [fst snd] in *; lia|].
    destruct (wb_emb_ctx st (wf_base_ok st WF) Hd); lia. }
  split; [apply CTX; unfold CTX_TID; lia|].
  split; [apply CTX; unfold CTX_THREAD; lia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|].
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). (nelim (loose0_range st WF _ _ DL1) 4%nat; intros Q1 Q2 Q3 Q4).
  assert (DL : In (db, db + dk) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (db, dk). auto. }
  apply Hhigh; [blia| unfold CEIL; lia|].
  destruct HBLK as [F|(Hd & E1 & E2)]; [destruct (F _ DL); cbn [fst snd] in *; lia|].
  destruct (wb_emb_dtls st (wf_base_ok st WF) Hd); lia.
Qed.

(* [comment removed for export] *)
Lemma EZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in K. olin_all.
  pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. destruct (bprim n) eqn:EP.
    - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply EZprim; lia.
    - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). eapply (EZsec (b_lo A n, n)); [exact S1| cbn [fst]; lia| cbn [fst snd]; lia]. }
  apply WOK_block_intro.
  - intros a sz Ha Hs. apply OBJ; lia.
  - unfold sh_tot. assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    assert (ASZ : 0 <= asz n).
    { destruct (bprim n) eqn:EP; [(nelim (prim_facts n EP) 5%nat; intros _ _ F3 F4 F5); rewrite F5 | (nelim (sec_facts n EP) 6%nat; intros _ _ F3 _ F5 _); rewrite F5]; Z.div_mod_to_equations; lia. }
    apply EZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n EP) 3%nat; intros _ F2 _). rewrite F2. cbn. lia.
Qed.
Lemma EZ_live : WOK_live st W.
Proof. intros A n Hin. apply EZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma EZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply EZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma EZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply EZprim; lia.
  - intros i Hi. apply EZprim; lia.
  - apply EZsh; [lia| lia| unfold CEIL; lia].
Qed.

(* [comment removed for export] *)
Lemma EZ_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). apply EZpa; lia.
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    destruct e as [mb n]. destruct (ws_entry st (wf_sec_ok st WF) _ HE) as (E1 & _). (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _).
    pose proof (usz_le_rounded8 n) as (U1 & _).
    eapply (EZsec (mb, n)); [exact HE| cbn [fst]; lia| cbn [fst snd]; unfold usz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma EZ_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. lowmid.
  - lowmid.
  - intros k Hk. lowmid.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    apply (EZnb b); [exact Hb| Z.div_mod_to_equations; lia| unfold NODEBLOCK_SIZE; Z.div_mod_to_equations; lia].
  - lowmid.
  - intros b Hb. lowmid.
Qed.

(* [comment removed for export] *)
Lemma EZ_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply (EZloose_sz (st_fs st) FS_TOTAL); [exact FL| unfold FS_TOTAL, EMB_CAP; lia| exact H1| exact H2]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X1 X2 _). pose proof (fsz_12 k Hk) as (FZ & _).
    assert (8 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    apply OBJ; unfold FS_FRAMES_OFF in *; lia.
Qed.

(* [comment removed for export] *)
Lemma EZ_consts_rest : WOK_consts_rest W.
Proof.
  unfold WOK_consts_rest.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, ATP in *.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.

Theorem ez_others : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m -> RTREP_nc st m'.
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  unfold RTREP_nc.
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact EZ_link]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| exact EZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| exact EZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| exact EZ_regions]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| exact EZ_avail]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| exact EZ_cache]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| exact EZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| exact EZ_live]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| exact EZ_quar]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| exact EZ_batches]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| exact EZ_ptrarr]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact EZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact EZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| exact EZ_ia]|].
  tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| exact EZ_lowshadow].
Qed.

(* [comment removed for export] *)
Lemma ez_consts_rest : forall m m', munch W m m' -> wmono asegs m m' -> R_consts_rest st m -> R_consts_rest st m'.
Proof.
  intros m m' MU WM H. unfold R_consts_rest in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27). (* [comment removed for export] *)
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, ATP in *.
  Local Ltac trc MU WM H := first [ eapply (roT W _ _ MU _ _ H) | eapply (rwT W _ _ MU WM _ _ H) ]; cbn -[Z.add Z.mul Z.le Z.lt Z.sub disjoint_from]; lowmid.
  split; [trc MU WM H1|]. split; [trc MU WM H2|]. split; [trc MU WM H3|]. split; [trc MU WM H4|]. split; [trc MU WM H5|]. split; [trc MU WM H6|].
  split; [trc MU WM H7|]. split; [trc MU WM H8|]. split; [trc MU WM H9|]. split; [trc MU WM H10|]. split; [trc MU WM H11|]. split; [trc MU WM H12|].
  split; [trc MU WM H13|]. split; [trc MU WM H14|]. split; [exists oom; trc MU WM H15|]. split; [trc MU WM H16|]. split; [trc MU WM H17|].
  split; [trc MU WM H18|]. split; [trc MU WM H19|]. split; [trc MU WM H20|]. split; [trc MU WM H21|]. split; [trc MU WM H22|]. split; [trc MU WM H23|]. split; [trc MU WM H24|].
  split; [trc MU WM H25|]. split; [trc MU WM H26|]. trc MU WM H27.
Qed.
End EZ.

(* [comment removed for export] *)
Definition ez_ok (elo ehi : Z) (iv : Z * Z) : Prop :=
  CEIL <= fst iv \/ (A_EMB <= fst iv /\ snd iv <= A_EMB + 56) \/ (elo <= fst iv /\ snd iv <= ehi).
Lemma ez_z_of : forall W elo ehi, Forall (ez_ok elo ehi) W ->
  forall a sz, (a + sz <= A_EMB \/ A_EMB + 56 <= a) -> a + sz <= CEIL -> (a + sz <= elo \/ ehi <= a) -> disjoint_from W a sz.
Proof.
  intros W elo ehi HW a sz H1 H2 H3. induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H4 H5]; subst. cbn. split; [| apply IH; exact H5].
  unfold ez_ok in H4. cbn [fst snd] in H4. unfold CEIL, A_EMB in *. lia.
Qed.
(* [comment removed for export] *)
Lemma ez_ok_stack : forall elo ehi lo hi, CEIL <= lo -> ez_ok elo ehi (lo, hi).
Proof. intros. left. cbn. assumption. Qed.
Lemma ez_ok_cells : forall elo ehi lo hi, A_EMB <= lo -> hi <= A_EMB + 56 -> ez_ok elo ehi (lo, hi).
Proof. intros. right; left. cbn. auto. Qed.
Lemma ez_ok_block : forall elo ehi lo hi, elo <= lo -> hi <= ehi -> ez_ok elo ehi (lo, hi).
Proof. intros. right; right. cbn. auto. Qed.



End CeilWrap.
