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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_p_absf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma csize_le64k' : forall c, 1 <= c <= 30 -> csize c <= 65536.
Proof.
  intros c Hc'.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by (clear -Hc'; lia).
  clear Hc'. repeat (destruct H as [->|H]; [vm_compute; discriminate|]). subst. vm_compute. discriminate.
Qed.
Lemma slack_ok' : forall c, 1 <= c <= 30 -> 64 + 2 * (nrefill c * csize c) - 2 * csize c <= 2048 /\ nrefill c <= 8 /\ 1 <= nrefill c.
Proof.
  intros c Hc'.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by (clear -Hc'; lia).
  clear Hc'. repeat (destruct H as [->|H]; [vm_compute; repeat split; discriminate|]). subst. vm_compute. repeat split; discriminate.
Qed.

Section PF.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls : Z) (um : bool).
Let r := rg st cls.
Let S := csize cls.
Let nf := num_freed st cls.
Definition r_f : region_st :=
  mkRegion (r_allocated r) (r_mapped r + (if um then 262144 else 0)) (r_mapped_fa r) (r_exhausted r) (r_fa r).
Let st' := mkRT a1 a2 a3 (updz a4 cls r_f) true a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.

Hypothesis WF : RTWF st.
Hypothesis WX : wf_pd st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
(* [comment removed for export] *)
Hypothesis HUM : um = true -> nf < nrefill cls /\ r_mapped r < r_allocated r + (nrefill cls - nf) * S /\ r_mapped r + 262144 <= KFREEARRAY_OFF.

Lemma Hcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma Hc1 : 1 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma WC : wf_class st cls. Proof. exact (wf_class_ok st WF cls Hcls). Qed.
Lemma ES : S = csize cls. Proof. reflexivity. Qed.
Lemma Er : r = rg st cls. Proof. reflexivity. Qed.
Lemma Spos : 32 <= S <= 65536.
Proof. rewrite ES. split; [apply csize_pos; lia| apply csize_le64k'; lia]. Qed.
Lemma nrange : 1 <= nrefill cls <= 8 /\ nrefill cls * S <= 65536.
Proof.
  rewrite ES. unfold nrefill, cmaxcount, clampz. pose proof Spos as SP. rewrite ES in SP.
  pose proof (Z.le_max_l 1 (Z.min 8 (1024 / csize cls))) as M1. pose proof (Z.le_min_l 8 (1024 / csize cls)) as M2.
  pose proof (Z.le_min_r 8 (1024 / csize cls)) as M3.
  rewrite (Z.mul_comm 2), Z.div_mul by lia.
  assert (D : csize cls * (1024 / csize cls) <= 1024) by (apply Z.mul_div_le; lia).
  assert (D0 : 0 <= 1024 / csize cls) by (apply Z.div_pos; lia).
  destruct (Z_le_gt_dec (Z.min 8 (1024 / csize cls)) 1).
  - rewrite Z.max_l by lia. lia.
  - rewrite Z.max_r by lia. split; [lia|]. nia.
Qed.

Lemma len_regions : length a4 = 32%nat. Proof. exact (wb_len_regions st (wf_base_ok st WF)). Qed.

(* [comment removed for export] *)
Lemma rg_same : rg st' cls = r_f.
Proof. unfold rg. cbn [st_regions st']. apply nthz_updz_same. unfold zlen. rewrite len_regions. unfold KNUMCLASSES in *. lia. Qed.
Lemma rg_other : forall c, c <> cls -> rg st' c = rg st c.
Proof. intros c H. unfold rg. cbn [st_regions st st']. apply nthz_updz_other. lia. Qed.
Lemma cch_all : forall c, cch st' c = cch st c. Proof. reflexivity. Qed.
Lemma rbeg_same : forall c, rbeg st' c = rbeg st c. Proof. reflexivity. Qed.
Lemma fabeg_same : forall c, fabeg st' c = fabeg st c. Proof. reflexivity. Qed.
Lemma rinfo_same : forall c, rinfo st' c = rinfo st c. Proof. reflexivity. Qed.
Lemma cptr_addr_same : forall c k, cptr_addr st' c k = cptr_addr st c k. Proof. reflexivity. Qed.
Lemma pcaddr_same : forall c, pcaddr st' c = pcaddr st c. Proof. reflexivity. Qed.
Lemma all_blocks_same : all_blocks st' = all_blocks st. Proof. reflexivity. Qed.
Lemma qall_same : qall st' = qall st. Proof. reflexivity. Qed.
Lemma apend_same : forall c, apend_cptrs st' c = apend_cptrs st c. Proof. reflexivity. Qed.
Lemma rt_ranges_same : rt_ranges st' = rt_ranges st. Proof. reflexivity. Qed.
Lemma rt_loose_same : rt_loose st' = rt_loose st. Proof. reflexivity. Qed.

Lemma alloc_same : forall c, r_allocated (rg st' c) = r_allocated (rg st c).
Proof. intros c. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite rg_same; reflexivity| rewrite rg_other by exact NE; reflexivity]. Qed.
Lemma fam_same : forall c, r_mapped_fa (rg st' c) = r_mapped_fa (rg st c).
Proof. intros c. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite rg_same; reflexivity| rewrite rg_other by exact NE; reflexivity]. Qed.
Lemma fa_same : forall c, r_fa (rg st' c) = r_fa (rg st c).
Proof. intros c. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite rg_same; reflexivity| rewrite rg_other by exact NE; reflexivity]. Qed.
Lemma exhf_same : forall c, r_exhausted (rg st' c) = r_exhausted (rg st c).
Proof. intros c. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite rg_same; reflexivity| rewrite rg_other by exact NE; reflexivity]. Qed.
Lemma mapped_same' : r_mapped (rg st' cls) = r_mapped r + (if um then 262144 else 0).
Proof. rewrite rg_same. reflexivity. Qed.
Lemma mapped_other : forall c, c <> cls -> r_mapped (rg st' c) = r_mapped (rg st c).
Proof. intros c NE. rewrite rg_other by exact NE. reflexivity. Qed.

Lemma ncarved_all : forall c, ncarved st' c = ncarved st c.
Proof. intros c. unfold ncarved. rewrite alloc_same. reflexivity. Qed.
Lemma num_freed_all : forall c, num_freed st' c = num_freed st c.
Proof. intros c. unfold num_freed. rewrite fa_same. reflexivity. Qed.
Lemma fa_cap_all : forall c, fa_cap st' c = fa_cap st c.
Proof. intros c. unfold fa_cap. rewrite fam_same. reflexivity. Qed.
Lemma carved_iff : forall c k, carved_cptr st' c k <-> carved_cptr st c k.
Proof. intros c k. unfold carved_cptr. rewrite ncarved_all. tauto. Qed.
Lemma avail_all : forall c, avail_cptrs st' c = avail_cptrs st c.
Proof. intros c. unfold avail_cptrs. rewrite fa_same, cch_all. reflexivity. Qed.
Lemma used_all : forall c, used_cptrs st' c = used_cptrs st c.
Proof. intros c. unfold used_cptrs. rewrite avail_all. reflexivity. Qed.
Lemma navail_all : forall c, navail st' c = navail st c.
Proof. intros c. unfold navail. rewrite avail_all. reflexivity. Qed.
Lemma navail_old : navail st cls = nf.
Proof. unfold navail, avail_cptrs. unfold nf, num_freed. rewrite HC0, app_nil_r. reflexivity. Qed.

Lemma nexh_same : nexh st' = nexh st.
Proof.
  unfold nexh. cbn [st_regions st st']. rewrite count_exh_updz by (unfold zlen; rewrite len_regions; unfold KNUMCLASSES in *; lia).
  cbn [r_exhausted r_f]. replace (nthz a4 cls region0) with r by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma um_facts : um = true -> r_mapped r < r_allocated r + S /\ r_mapped r + 262144 <= KFREEARRAY_OFF.
Proof.
  intros E. destruct (HUM E) as (M0 & M1 & M2). split; [| exact M2].
  destruct (WX cls Hc1) as [DEL _]. rewrite <- Er in DEL. change (csize cls) with S in DEL.
  assert (NF0 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg). pose proof Spos as SP.
  pose proof nrange as [N1 N2]. destruct DEL as [D|[D1 D2]]; [exact D|]. exfalso.
  assert ((nrefill cls - nf) * S <= nrefill cls * S) by (apply Z.mul_le_mono_nonneg_r; lia). clear -M1 D1 N2 N1 H. nia.
Qed.

Lemma wf_pd_f : wf_pd st'.
Proof.
  intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE]; [| rewrite rg_other by exact NE; exact (WX c Hc')].
  rewrite rg_same. unfold r_f. cbn [r_allocated r_mapped r_exhausted].
  destruct (WX cls Hc1) as [DEL EXH]. rewrite <- Er in DEL, EXH. change (csize cls) with S in DEL, EXH |- *.
  pose proof (wc_alloc_mapped st cls WC) as AM. rewrite <- Er in AM. pose proof Spos. pose proof um_facts as UF.
  destruct um; [| rewrite Z.add_0_r; exact (conj DEL EXH)].
  destruct (UF eq_refl) as [M1 M2]. split; [right; lia|].
  intros E. destruct (EXH E) as [X1 X2]. exfalso. unfold KFREEARRAY_OFF in *. lia.
Qed.

Lemma RTWF_f : RTWF st'.
Proof.
  pose proof (wf_base_ok st WF) as WB. pose proof Spos as SP.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_alloc_nonneg st cls WC) as A0.
  pose proof (wc_mapped_align st cls WC) as MA. pose proof (wc_mapped_max st cls WC) as MM. pose proof (wc_residue st cls WC) as RS.
  pose proof um_facts as UF. pose proof carved_iff as CI. pose proof nexh_same as NX.
  pose proof ncarved_all as E1. pose proof cch_all as E2. pose proof num_freed_all as E3. pose proof used_all as E4. pose proof alloc_same as E5.
  pose proof fam_same as E6. pose proof fa_same as E7. pose proof mapped_same' as E8. pose proof mapped_other as E9. pose proof rg_other as E10.
  rewrite <- Er in *.
  change (csize cls) with S in RS.
  constructor.
  - destruct WB; constructor; try assumption.
    + cbn [st_regions st']. rewrite updz_length. assumption.
    + split; [rewrite E10 by lia; apply (proj1 wb_class0)| rewrite E2; apply (proj2 wb_class0)].
    + intros Hu. exfalso. cbn in Hu. discriminate.
    + change (emb_sz st') with (emb_sz st). rewrite NX. exact wb_emb_sz.
  - intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE].
    + destruct (wf_class_ok st WF cls Hc'); constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8; rewrite <- ?Er in *; try assumption.
      * destruct um; lia.
      * destruct um; [rewrite Z.add_mod, MA by lia; reflexivity| rewrite Z.add_0_r; exact MA].
      * destruct um; [destruct (UF eq_refl); lia| rewrite Z.add_0_r; exact MM].
      * intros k Hk. apply CI. exact (wc_used_carved k Hk).
      * change (csize cls) with S. destruct um; [destruct (UF eq_refl); lia| rewrite Z.add_0_r; exact RS].
      * (* [comment removed for export] *) intros _. pose proof (proj1 (wf_pd_f cls Hc1)) as D.
        rewrite ?rg_same in D. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_f] in D. rewrite <- ?Er in D. exact D.
      * (* [comment removed for export] *) pose proof (proj2 (wf_pd_f cls Hc1)) as D.
        rewrite ?rg_same in D. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_f] in D. rewrite <- ?Er in D.
        rewrite ?rg_same. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_f]. rewrite <- ?Er. exact D.
    + destruct (wf_class_ok st WF c Hc'); constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E9, ?E10 by exact NE; try assumption.   (* [comment removed for export] *)
      intros k Hk. apply CI. exact (wc_used_carved k Hk).
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    intros b Hb. destruct (wq_batch b Hb) as [C (k & CK & E)]. split; [exact C| exists k; split; [apply CI; exact CK| exact E]].
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.


(* [comment removed for export] *)
Lemma provU_other : forall c, c <> cls -> provU st' c = provU st c.
Proof. intros c H. unfold provU, delta. rewrite rg_other, navail_all by exact H. reflexivity. Qed.
Lemma provF_all : forall c, provF st' c = provF st c.
Proof. intros c. unfold provF. rewrite fa_cap_all, ncarved_all. reflexivity. Qed.
Lemma provU_step : provU st' cls + (if um then LUMPU else 0) <= provU st cls.
Proof.
  unfold provU, delta. rewrite navail_all, navail_old, mapped_same', alloc_same. rewrite <- Er.
  pose proof nrange as [N1 N2]. pose proof Spos as SP. pose proof (slack_ok' cls Hc) as (SL1 & SL2 & SL3). change (csize cls) with S in SL1 |- *.
  pose proof (wc_num_freed st cls WC) as NF. pose proof (wc_alloc_mapped st cls WC) as AM. rewrite <- Er in AM.
  assert (NF0 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  unfold Nmax. change (csize cls) with S. unfold LUMPU, FAPROV.
  set (Q := 2^18 / S) in *. assert (Q0 : 0 <= Q) by (subst Q; apply Z.div_pos; lia).
  destruct um; [| rewrite !Z.add_0_r; lia].
  destruct (HUM eq_refl) as (M0 & M1 & M2).
  assert ((nrefill cls - nf) * S <= nrefill cls * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  replace (r_mapped r - r_allocated r <? nrefill cls * S) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (r_mapped r + 262144 - r_allocated r <? nrefill cls * S) with false by (symmetry; apply Z.ltb_ge; lia).
  assert (SNF : 0 <= 2 * S * nf /\ 2 * S * nf <= 2 * S * (nrefill cls - 1)) by (split; [nia| apply Z.mul_le_mono_nonneg_l; lia]).
  lia.
Qed.

Lemma zsum_map_le'' : forall (f g : Z -> Z) l d x, (forall y, In y l -> y <> x -> f y = g y) -> f x + d <= g x ->
  List.NoDup l -> In x l -> zsum (map f l) + d <= zsum (map g l).
Proof.
  intros f g l d x Hfg Hx ND IN. induction l as [|y l IH]; [destruct IN|].
  inversion ND as [|y' l' Hni ND']; subst. cbn [map]. rewrite !zsum_cons.
  destruct (Z.eq_dec y x) as [->|NE].
  - rewrite (zsum_map_ext f g l); [clear -Hx; lia|]. intros z Hz. apply Hfg; [right; exact Hz|]. intros ->. exact (Hni Hz).
  - rewrite (Hfg y ltac:(left; reflexivity) NE). destruct IN as [E|IN]; [exfalso; exact (NE E)|].
    specialize (IH ltac:(intros w Hw Hne; apply Hfg; [right; exact Hw| exact Hne]) ND' IN). clear -IH. lia.
Qed.

Lemma prov_classes_f : prov_classes st' + (if um then LUMPU else 0) <= prov_classes st.
Proof.
  unfold prov_classes.
  apply (zsum_map_le'' (fun c => provU st' c + provF st' c) (fun c => provU st c + provF st c) classes _ cls).
  - intros y Hy Hne. rewrite provU_other, provF_all by exact Hne. reflexivity.
  - pose proof provU_step. rewrite provF_all. lia.
  - apply classes_nodup.
  - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
Qed.

Lemma rt_prov_f : rt_prov st' + (if um then LUMPU else 0) <= rt_prov st.
Proof.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_depot st' = prov_depot st) by reflexivity.
  assert (E8 : prov_slots st' = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 st' = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb st' = prov_emb st) by reflexivity.
  unfold rt_prov. rewrite E2, E3, E4, E5, E6, E7, E8, E9, E10. pose proof prov_classes_f. lia.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_f : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_f : forall m mo g, GWIN st m mo g -> GWIN st' m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_f : forall g, SWIN st g -> SWIN st' g.
Proof. intros g H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variables (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis HR : RTREP st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis HW : Forall (pz_ok st cls) W.
Let rb := rbeg st cls.
Let fb := fabeg st cls.
Let alloc := r_allocated r.
Let mapped := r_mapped r.
Let mapped' := r_mapped r + (if um then 262144 else 0).
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells asegs m' (rinfo st cls) (rinfo_cells st' cls jr je js).
(* [comment removed for export] *)
Hypothesis VU : um = true -> vis m' (rb + mapped) (rb + mapped + 262144) /\ rw_cells asegs m' (SH (rb + mapped)) (zcells (zrep SV_HEAP_LEFT_RZ 32768)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells asegs m' (pcaddr st c) [W4 (zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Hypothesis PCO : forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells asegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

Lemma RF : KHIGHMEM_BEG <= rb /\ rb mod 8 = 0 /\ alloc mod 8 = 0 /\ mapped mod 8 = 0 /\ 0 <= alloc <= mapped /\ mapped <= KFREEARRAY_OFF /\ rb + KREGIONSIZE <= CEIL.
Proof.
  pose proof (region_facts st WF cls Hcls) as X. cbn zeta in X. destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold rb, alloc, mapped, r. unfold CEIL. repeat split; try lia; assumption.
Qed.

Lemma tail_shadow_f : rw_cells asegs m' (SH (rb + alloc)) (zcells (zrep SV_HEAP_LEFT_RZ ((mapped' - alloc) / 8))).
Proof.
  pose proof RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
  destruct (pz_others st WF cls Hc W HW m m' MU WM HR) as (_ & _ & _ & RG & _).
  destruct (RG cls Hcls) as (_ & _ & _ & _ & _ & TL). fold r in TL. change (rbeg st cls) with rb in TL. change (r_allocated r) with alloc in TL. change (r_mapped r) with mapped in TL.
  unfold mapped'. change (r_mapped r) with mapped. pose proof VU as VU'. destruct um.
  - destruct (VU' eq_refl) as [_ SHU].
    replace ((mapped + 262144 - alloc) / 8) with ((mapped - alloc) / 8 + 32768) by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    rewrite zrep_split, zcells_app' by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    apply rw_cells_app. split; [exact TL|]. rewrite zcells_zrep_size by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    replace (SH (rb + alloc) + (mapped - alloc) / 8) with (SH (rb + mapped)); [exact SHU|].
    rewrite !rt_SH_aligned_add by exact X2. clear -X3 X4 X5. Z.div_mod_to_equations. lia.
  - rewrite Z.add_0_r. exact TL.
Qed.

Lemma RTREP_f : RTREP st' m'.
Proof.
  pose proof RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7). pose proof Spos as SP.
  destruct (pz_others st WF cls Hc W HW m m' MU WM HR) as (Y1 & Y2 & Y3 & Y5 & Y6 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16).
  pose proof tail_shadow_f as TS. pose proof VU as VU'. pose proof rg_other as RGO. pose proof rg_same as RGS. pose proof avail_all as AVA. pose proof cch_all as CCA.
  constructor.
  - exact Y1.
  - exact Y2.
  - exact Y3.
  - (* [comment removed for export] *) split.
    { pose proof (proj1 (rr_rinfo st m HR)) as VR. pose proof (ris_range st WF) as (Z1 & Z2 & Z3 & Z4). change (ris st') with (ris st).
      destruct RINFO as (jr0 & je0 & js0 & RC0).
      assert (E128 : Z.of_nat (cells_size (rinfo_cells st' cls jr0 je0 js0)) = 128).
      { destruct RC0 as [[Wf _] _]. cbn in Wf. unfold rinfo_cells. cbn [cells_size Cells.csize].
        destruct Wf as (_ & _ & _ & _ & _ & _ & _ & _ & L1 & _ & L2 & L3 & _). lia. }
      assert (RL : rinfo st cls = ris st + 128 * cls) by reflexivity.
      destruct (stk_split asegs m (ris st) (rinfo st cls) (ris st + 4096) VR ltac:(rewrite RL; lia)) as [VA VB].
      destruct (stk_split asegs m (rinfo st cls) (rinfo st cls + 128) (ris st + 4096) VB ltac:(rewrite RL; lia)) as [_ VC].
      apply (stk_merge asegs m' _ (rinfo st cls)); [| | rewrite RL; lia].
      - eapply stk_transport_disjoint; [exact VA| exact MU| exact WM|].
        pose proof (cls_facts st WF cls Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
        apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia.
      - apply (stk_merge asegs m' _ (rinfo st cls + 128)); [| | rewrite RL; lia].
        + pose proof (stk_of_rw_cells asegs m' _ _ RC0) as SR. rewrite E128 in SR. exact SR.
        + eapply stk_transport_disjoint; [exact VC| exact MU| exact WM|].
          pose proof (cls_facts st WF cls Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
          apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, KNUMCLASSES in *; lia. }
    intros c Hc'. change (rinfo st' c) with (rinfo st c). destruct (Z.eq_dec c cls) as [->|NE]; [exact RINFO|].
    destruct (proj2 (rr_rinfo st m HR) c Hc') as (jr & je & js & RC). exists jr, je, js.
    replace (rinfo_cells st' c jr je js) with (rinfo_cells st c jr je js) by (unfold rinfo_cells; rewrite RGO by exact NE; unfold num_freed; rewrite RGO by exact NE; reflexivity).
    exact (pz_rinfo_other st WF cls Hc W HW m m' c jr je js MU WM Hc' NE RC).
  - (* [comment removed for export] *) intros c Hc'. change (rbeg st' c) with (rbeg st c). change (fabeg st' c) with (fabeg st c).
    destruct (Z.eq_dec c cls) as [->|NE].
    2:{ unfold num_freed. rewrite RGO by exact NE. exact (Y5 c Hc'). }
    rewrite RGS. unfold num_freed. rewrite RGS. cbn [r_allocated r_mapped r_mapped_fa r_fa r_f]. fold rb fb. change (r_mapped r + (if um then 262144 else 0)) with mapped'. fold alloc.
    destruct (Y5 cls Hcls) as (V1 & V2 & V3 & V4 & EN & TL). fold r rb fb in V1, V2, V3, V4, EN, TL |- *.
    change (r_mapped r) with mapped in V1, V2.
    split; [| split; [| split; [exact V3| split; [exact V4| split; [exact EN|]]]]].
    + unfold mapped'. change (r_mapped r) with mapped. destruct um; [| rewrite Z.add_0_r; exact V1]. destruct (VU' eq_refl) as [VU1 _]. replace (rb + (mapped + 262144)) with (rb + mapped + 262144) by lia. eapply stk_merge; [exact V1| exact VU1| lia].
    + unfold mapped'. change (r_mapped r) with mapped. destruct um; [| rewrite Z.add_0_r; exact V2]. destruct (VU' eq_refl) as [_ SHU].
      apply zcells_zrep_to_CB in SHU; [| lia]. apply (stk_of_rw_cellsZ _ _ _ 32768) in SHU; [| cbn; lia].
      replace (SH rb + (mapped + 262144) / 8) with (SH (rb + mapped) + 32768) by (rewrite rt_SH_aligned_add by exact X2; clear -X4 X5; Z.div_mod_to_equations; lia).
      replace (SH rb + mapped / 8) with (SH (rb + mapped)) in V2 by (rewrite rt_SH_aligned_add by exact X2; reflexivity).
      eapply stk_merge; [exact V2| exact SHU| pose proof (rt_SH_mono rb (rb + mapped) ltac:(lia)); lia].
    + exact TS.
  - (* [comment removed for export] *) intros c k Hc' Hk. change (cptr_addr st' c k) with (cptr_addr st c k).
    rewrite AVA, apend_same in Hk. exact (Y6 c k Hc' Hk).
  - (* [comment removed for export] *) intros c Hc'. change (pcaddr st' c) with (pcaddr st c).
    assert (PM : pc_max_count st' c = (if c =? 0 then 0 else cmaxcount c)) by (unfold pc_max_count; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    assert (PS' : pc_class_size st' c = (if c =? 0 then 0 else csize c)) by (unfold pc_class_size; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    rewrite PM, PS', CCA. split; [exact (PCH c Hc')|]. intros i Hi. exact (PCO c i Hc' Hi).
  - exact Y8.
  - exact Y9.
  - exact Y10.
  - exact Y11.
  - exact Y12.
  - exact Y13.
  - exact Y14.
  - exact Y15.
  - exact Y16.
Qed.
End PF.


End CeilWrap.
End RTW_p_absf.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_p_pop2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_map OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_efa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_libo OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
(* [comment removed for export] *)
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].

(* [comment removed for export] *)
Lemma pop_tail : forall (x1 sp gp tp y5 y6 y7 x9 x10 x11 x12 x14 x15 y16 y17 x18 x20 s6v s7 s8 s9 s10 s11 y28 y29 y30 y31 : word) (s6 s5 s4 s3 s2 s1 s0 ra : word) (mtx sem : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc S alloc mapped' nf N lo : Z) (jr je js : list byte) (exh : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells asegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells asegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] ->
  rw_cells asegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
  0 < S <= 65536 -> 0 <= alloc -> 0 <= N -> alloc + N * S <= mapped' -> mapped' <= KFREEARRAY_OFF -> 0 <= nf -> 4 * (nf + N) <= 2^29 ->
  evt asegs (fun ms2 => exists (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) m2,
      ms2 = MS (mkR ra sp gp tp z5 z6 z7 s0 s1 (wz 1) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31) F (ret_pc ra) fc None m2 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp)
      /\ rw_cells asegs m2 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + N))]
      /\ rw_cells asegs m2 (Rc + 32) [C8 (Z_to_bv 64 (alloc + N * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js])
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp y5 y6 y7 (wz Rc) x9 x10 x11 x12 (wz alloc) x14 x15 y16 y17
             x18 (wz N) x20 (wz S) s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x372c8) fc None m (seg_rom asegs)).
Proof.
  intros until exh. intros MI ST CEIL LO FR RIa RIb HR1 HR2 HS Ha HN HNS Hmx Hnf Htf.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, pop_frame in *. cbv beta delta [wz] in *.
  assert (NS0 : 0 <= N * S) by nia.
  lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  do 8 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. nexists 15%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact RIa| exact RIb].
Qed.

(* [comment removed for export] *)
Lemma pop_G : forall (sp gp tp y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 s6v s7 s8 s9 s10 s11 y28 y29 y30 y31 : word) (s6 s5 s4 s3 s2 s1 s0 ra : word) (mtx sem : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc RB S alloc mapped' nf N lo : Z) (jr je js : list byte) (exh : Z) (dpre : list word),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells asegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells asegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] ->
  rw_cells asegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> KHIGHMEM_BEG <= RB -> RB + 2^32 <= alloc_ceiling -> RB + 2^32 <= Rc ->
  32 <= S <= 65536 -> 0 <= alloc <= mapped' -> mapped' <= KFREEARRAY_OFF -> 0 <= nf -> 4 * (nf + N) <= 2^29 ->
  N = (mapped' - alloc) / S -> length dpre = Z.to_nat N ->
  u32arr asegs m (RB + KFREEARRAY_OFF + 4 * nf) dpre ->
  evt asegs (fun ms2 => exists (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) m2,
      ms2 = MS (mkR ra sp gp tp z5 z6 z7 s0 s1 (wz 1) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31) F (ret_pc ra) fc None m2 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RB + KFREEARRAY_OFF + 4 * nf, RB + KFREEARRAY_OFF + 4 * nf + 4 * N); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp)
      /\ rw_cells asegs m2 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + N))]
      /\ rw_cells asegs m2 (Rc + 32) [C8 (Z_to_bv 64 (alloc + N * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js]
      /\ u32arr asegs m2 (RB + KFREEARRAY_OFF + 4 * nf) (fill_vals alloc S (Z.to_nat N)))
    (MS (mkR (wz 0x37280) (wz (bv_unsigned sp + -64)) gp tp y5 y6 y7 (wz Rc) (wz (nf + N)) (wz 1) y11 y12 y13 y14 y15 y16 y17
             (wz RB) (wz N) (wz (mapped' - alloc)) (wz S) s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x37280) fc None m (seg_rom asegs)).
Proof.
  intros until dpre. intros MI ST CEIL LO FR RIa RIb HR1 HR2 HB1 HB2 HBR HS Ham Hmx Hnf Htf HN LD DST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, pop_frame in *. cbv beta delta [wz] in *.
  assert (NR : 0 <= N /\ N * S <= mapped' - alloc /\ mapped' - alloc < N * S + S).
  { subst N. split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod (mapped' - alloc) S ltac:(lia)). pose proof (Z.mod_pos_bound (mapped' - alloc) S ltac:(lia)). nia. }
  (nelim NR 3%nat; intros N0 N1 N2).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    assert (NZ : N = 0) by (cut_on [HS Ham HN RSP N0 N1 N2 K0] nia). clear HN. subst N.
    eapply evt_mono; [eapply pop_tail; [exact MI| exact ST| exact CEIL| exact LO| exact FR| exact RIa| exact RIb| ..]; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF; idtac; lia|].
    cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 -> MU WM MI2 ST2 RIa2 RIb2).
    nexists 15%nat. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. subfp. }
    split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact RIa2|]. split; [exact RIb2|].
    destruct dpre; [| cbn in LD; lia]. cbn [fill_vals Z.to_nat rev map seq].
    eapply (u32arr_transport asegs _ m m2); [exact DST| exact MU| exact WM| cbn [disjoint_from]; rewrite fill_vals_length; lia].
  - (* [comment removed for export] *)
    assert (NP : 0 < N) by nia.
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (RB + 3758096384 + 4 * nf + 4 * N)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 12 (Z_to_bv 64 (alloc + 0 * S)) ltac:(f_equal; lia).
    rewrite <- (app_nil_r dpre) in DST. change ([] : list word) with (fill_vals alloc S (Z.to_nat 0)) in DST.
    eapply (fill_loop (Z.to_nat N) 0 N (RB + 3758096384 + 4 * nf) S alloc dpre);
      [lia| lia| lia| lia| lia| unfold KFREEARRAY_OFF in *; lia| unfold AIMG_HI; lia| exact LD| exact DST| exact MI|].
    intros m' ARR2 MU2 WM2 MI2 x14 x15. replace (alloc + 0 * S) with alloc by lia.
    transport_after_call asegs m m' MU2 WM2.
    eapply evt_mono; [eapply pop_tail; [exact MI2| exact ST| exact CEIL| exact LO| exact FR| exact RIa| exact RIb| ..]; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF; idtac; lia|].
    cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 -> MU WM MI3 ST2 RIa2 RIb2).
    nexists 15%nat. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU]]; subfp. }
    split; [eapply wmono_trans; [exact WM2| exact WM]|]. split; [exact MI3|]. split; [exact ST2|]. split; [exact RIa2|]. split; [exact RIb2|].
    eapply (u32arr_transport asegs _ m' m2); [exact ARR2| exact MU| exact WM|].
    cbn [disjoint_from]. rewrite fill_vals_length. lia.
Qed.

(* [comment removed for export] *)
Lemma pop_X : forall (sp gp tp x5 x6 x7 x15 x16 x17 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc stt c q alloc mapped RB : Z) (jr je js : list byte) (a1v : word),
  mem_inv asegs m ->
  ro_cells asegs m 0xa6c40 [C4 (Z_to_bv 64 4294967295)] ->
  rw_cells asegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 -> 0 <= q -> csize c * q <= 262144 -> 0 <= alloc <= mapped ->
  mapped < alloc + csize c * q -> mapped = KFREEARRAY_OFF ->
  evt asegs (fun ms1 =>
      ms1 = MS (mkR (wz 0x370a0) sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz 0) (wz (KFREEARRAY_OFF + 1)) (wz c) (wz (mapped + 262144)) (wz q) x15 x16 x17
                    (wz RB) (wz 262144) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x373b4) fc None m (seg_rom asegs))
    (MS (mkR (wz 0x370a0) sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) a1v (wz c) (wz alloc) (wz q) x15 x16 x17
             (wz RB) (wz (alloc + csize c * q)) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x3718c) fc None m (seg_rom asegs)).
Proof.
  intros until a1v. intros MI AC40 RIb HR1 HR2 Hc Hq QS Ham LT EXH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *. cbv beta delta [wz] in *. idtac.
  pose proof (csize_pos c ltac:(lia)) as CP.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite zb_lxor_ones by lia; rewrite land_align18 by (apply Z.mod_pos_bound; lia); Z.div_mod_to_equations; lia).
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst mapped. cbv delta [mkR]. reflexivity.
Qed.

Definition LUMP : Z := 294912.        (* [comment removed for export] *)
Definition POP_STACK : Z := 1264.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition p1_W (lo sp Rc T D Nv Ufa : Z) (fm : bool) : list (Z * Z) :=
  [(lo, sp); (Rc + 16, Rc + 24); (Rc + 24, Rc + 32); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69); (T + 2872, T + 2888); (D, D + 4 * Nv)]
  ++ (if fm then [(Ufa, Ufa + 262144); (SH Ufa, SH Ufa + 32768)] else []).

(* [comment removed for export] *)
Lemma spin_or_lscps_evt : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) mo g (Q : machine_state -> Prop) ms,
  evt asegs Q ms ->
  (forall ms', Q ms' -> if spin then evt asegs (jself asegs) ms' else LSCPS asegs P ms' mo g) ->
  if spin then evt asegs (jself asegs) ms else LSCPS asegs P ms mo g.
Proof. intros spin P mo g Q ms EV K. destruct spin. - eapply evt_cut; [exact EV| exact K]. - eapply lscps_evt_then; [exact EV| exact K]. Qed.

Section P1.
  Hypothesis PS : poison_shadow_spec.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : word -> option byte) (mo1 : Model) (G1 : list (Z * Z)) (R1 : Z) (st : rtstate)
            (Rc RB S alloc mapped1 nf fam lo : Z) (tj1 tj2 mtx sem : word) (jr je js : list byte) (exh1 : Z).
  Let Nv := (mapped1 - alloc) / S.
  Let n := nf + Nv.
  Let nm := (4 * n + 262143) / 262144 * 262144.
  Let Ufa := RB + KFREEARRAY_OFF + fam.
  Let D := RB + KFREEARRAY_OFF + 4 * nf.
  Let fam' := if fam <? 4 * n then nm else fam.
  Hypothesis HC1 : mmap_consts m1.
  Hypothesis IC1 : icpt_cells m1.
  Hypothesis PC1 : poison_cells m1.
  Hypothesis LC1 : leafc st m1.
  Hypothesis WF : RTWF st.
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -64).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + POP_STACK <= bv_unsigned sp.
  Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra).
  Hypothesis RIa1 : rw_cells asegs m1 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)].
  Hypothesis RI241 : rw_cells asegs m1 (Rc + 24) [C8 (Z_to_bv 64 fam)].
  Hypothesis RIb1 : rw_cells asegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped1); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh1); CB 3 je; CB 56 js].
  Hypothesis A56 : ro_cells asegs m1 0xa6c50 [C1 (Z_to_bv 8 0)].
  Hypothesis TST1 : rw_cells asegs m1 (st_t st + 2872) [C8 tj1; C8 tj2].
  Hypothesis VFA1 : stk asegs m1 (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam).
  Hypothesis HRc : KHIGHMEM_BEG <= Rc /\ Rc + 128 <= alloc_ceiling /\ (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) /\ (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st)
                   /\ RB + 2^32 <= Rc.
  Hypothesis HRB : KHIGHMEM_BEG <= RB /\ RB + 2^32 <= alloc_ceiling /\ RB mod 65536 = 0
                   /\ (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) /\ (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st).
  Hypothesis HS : 32 <= S <= 65536.
  Hypothesis Hm1 : 0 <= alloc <= mapped1 /\ mapped1 <= KFREEARRAY_OFF /\ mapped1 - alloc <= S + 524288.
  Hypothesis Hnf : 0 <= nf <= 8 /\ 4 * nf <= fam.
  Hypothesis Hfam : 0 <= fam /\ fam mod 262144 = 0 /\ fam <= 2^29.
  Hypothesis LZS1 : fam < 4 * n -> forall x : word, SH Ufa <= bv_unsigned x < SH Ufa + 32768 -> lzf mo1 x = true.
  Hypothesis HVIS1 : fam < 4 * n -> forall x : word, SH Ufa <= bv_unsigned x < SH Ufa + 32768 -> lzf mo1 x = true -> in_winb G1 x = true -> m1 x <> None.
  Hypothesis SITE1 : fam < 4 * n -> mmap_fixed_site mo1 Ufa 262144.
  Hypothesis HR1 : fam < 4 * n -> LUMP <= R1.

  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs).

  #[using="Hfam Hnf Hm1 HS HRB HRc fam' D Ufa nm n fam nf RB Rc st ACEIL"] Lemma Nv_bound : 0 <= Nv <= 16385 /\ Nv * S <= mapped1 - alloc.
  Proof.
    subst Nv. (nelimp Hm1 3%nat; intros A1 A2 A3).
    split. { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. (cut_on [HRc HRB HS Hm1 Hnf Hfam A1 A2 A3] nia). }
    pose proof (Z.mul_div_le (mapped1 - alloc) S ltac:(lia)). lia.
  Qed.

  Lemma pop_P1 : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) (x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 : word),
    (* [comment removed for export] *)
    True ->
    (* [comment removed for export] *)
    (forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 (m' : word -> option byte) (tj1' tj2' : word),
       mem_inv asegs m' -> munch (p1_W lo (bv_unsigned sp) Rc (st_t st) D Nv Ufa (fam <? 4 * n)) m1 m' -> wmono asegs m1 m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + Nv))] ->
       rw_cells asegs m' (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
       rw_cells asegs m' (Rc + 32) [C8 (Z_to_bv 64 (alloc + Nv * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped1); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells asegs m' (st_t st + 2872) [C8 tj1'; C8 tj2'] ->
       stk asegs m' (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam') ->
       u32arr asegs m' D (fill_vals alloc S (Z.to_nat Nv)) ->
       (if fam <? 4 * n then rw_cells asegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       LSCPS asegs P (RET 1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m')
             (if fam <? 4 * n then mm_commit (wz Ufa) (wz 262144) mo1 else mo1)
             (mkG (if fam <? 4 * n then (SH Ufa, SH Ufa + 32768) :: G1 else G1) (R1 - (if fam <? 4 * n then LUMP else 0)))) ->
    LSCPS asegs P
      (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) x9 (wz A_ALLOC) x11 x12 (wz alloc) x14 x15 x16 x17
               (wz RB) x19 (wz mapped1) (wz S) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x37260) fc None m1 (seg_rom asegs)) mo1 (mkG G1 R1).
  Proof.
    intros spin P x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 _ K1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [CEIL LO2]. pose proof CEIL as CEILn. idtac. unfold POP_STACK in LO2.
    (nelimp HRc 5%nat; intros RC1 RC2 RC3 RC4 RC5). (nelimp HRB 5%nat; intros RB1 RB2 RB3 RB4 RB5). (nelimp Hm1 3%nat; intros A1 A2 A3). destruct Hnf as [N1 N2]. (nelimp Hfam 3%nat; intros F1 F2 F3).
    pose proof RC2 as RC2n. idtac. pose proof RB2 as RB2n. idtac. unfold KHIGHMEM_BEG, AIMG_HI in RC1, RB1. olin_all. unfold KFREEARRAY_OFF in *.
    pose proof Nv_bound as [NB1 NB2].
    assert (EUfa : Ufa = RB + 3758096384 + fam) by reflexivity. assert (ED : D = RB + 3758096384 + 4 * nf) by reflexivity.
    assert (ENv : Nv = (mapped1 - alloc) / S) by reflexivity. assert (En : n = nf + Nv) by reflexivity.
    assert (E64 : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (unfold wz; apply unsigned_lit; lia).
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply pop_C; [exact MI1| exact RIa1| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| lia| lia| lia| lia]. }
    cbv beta. intros ms1 ->. fold Nv. fold n.
    assert (Hn4 : 4 * n <= fam + 262144) by (subst n; lia).
    eapply (efa_spec PS) with (st := st) (fam := fam) (lo := lo) (tj1 := tj1) (tj2 := tj2) (spin := spin) (n := n);
      [exact HC1| exact IC1| exact PC1| exact LC1| exact WF| exact TP| exact MI1| rewrite E64; exact ST1| rewrite E64; unfold EFA_STACK; lia
      | exact RI241| exact A56| exact TST1| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia
      | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; try assumption; try (lia_on HRc HRB HS Hm1 RC5 RB1 RB3 N1); clear -RB3; Z.div_mod_to_equations; lia
      | subst n; (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1)| repeat split; lia| exact HOK
      | intros LT; replace ((4 * n + 262143) / 262144 * 262144 - fam) with 262144 by (clear -LT F1 F2 Hn4; Z.div_mod_to_equations; lia); exact (SITE1 LT)
      | | | ..].
    1,2: assert (SZ8 : (fam < 4 * n /\ ((4 * n + 262143) / 262144 * 262144 - fam) / 8 = 32768) \/ (4 * n + 262143) / 262144 * 262144 <= fam)
           by (destruct (Z_lt_le_dec fam (4 * n)) as [LT|GE]; [left; split; [exact LT| clear -LT F1 F2 Hn4; Z.div_mod_to_equations; (lia_on F2 Hn4 LT H H0 H4 H5 H9)]
                                                                | right; clear -GE F1 F2 N1 NB1; subst n; Z.div_mod_to_equations; nia]).
    { intros x Hx. destruct SZ8 as [[LT E]|GE]; [rewrite E in Hx; exact (LZS1 LT x Hx)|]. exfalso. clear -Hx GE. Z.div_mod_to_equations. lia. }
    { intros x Hx. destruct SZ8 as [[LT E]|GE]; [rewrite E in Hx; exact (HVIS1 LT x Hx)|]. exfalso. clear -Hx GE. Z.div_mod_to_equations. lia. }
    { unfold LUMP in HR1. intros LT. pose proof (HR1 LT). clear -H LT F1 F2 Hn4. Z.div_mod_to_equations. lia. }
    all: cbv beta delta [wz]; cbv delta [wz] in E64; rewrite ?E64.
    all: replace (ret_pc (Z_to_bv 64 225920)) with (Z_to_bv 64 225920 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    - (* [comment removed for export] *)
      intros GE y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 RI2.
      pose proof FR1 as FR2. eapply (rw_cells_transport asegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia].
      pose proof RIa1 as RIa2. eapply (rw_cells_transport asegs _ m1 m2) in RIa2; [| exact MU2| exact WM2| cbn; lia].
      pose proof RIb1 as RIb2. eapply (rw_cells_transport asegs _ m1 m2) in RIb2; [| exact MU2| exact WM2| cbn; lia].
      pose proof TST1 as TST2. eapply (rw_cells_transport asegs _ m1 m2) in TST2; [| exact MU2| exact WM2| cbn; pose proof (t_range st WF); unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HRB HS Hm1 CEILn RC3 RC4 RC5 RB4 RB5 N1 RC2n RB2n H)].
      pose proof VFA1 as VFA2. eapply (stk_transport_disjoint asegs _ m1 m2) in VFA2; [| exact MU2| exact WM2| cbn; lia].
      (* [comment removed for export] *)
      destruct (stk_split asegs m2 _ D _ VFA2 ltac:(subst D n; lia)) as [VL VR0].
      destruct (stk_split asegs m2 _ (D + 4 * Nv) _ VR0 ltac:(subst D n; lia)) as [VM VR].
      (nelim (stk_carve asegs m2 D (D + 4 * Nv) (Z.to_nat (4 * Nv)) VM ltac:(lia)) 3%nat; intros _ junk JK).
      replace (D + 4 * Nv - Z.of_nat (Z.to_nat (4 * Nv))) with D in JK by (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1).
      destruct (p_u32arr_of_u8arr asegs m2 D junk (Z.to_nat Nv) (u8arr_of_rw_cells asegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { pose proof (rw_cells_bound asegs m2 D _ JK). cbn [cells_size Cells.csize] in H. destruct JK as [[WFj _] _]. cbn in WFj. (lia_on HRc HRB HS Hm1 RC5 RB1 N1 WFj). }
      eapply lscps_evt_then.
      { eapply (pop_G sp gp tp) with (lo := lo) (nf := nf) (N := Nv) (dpre := dpre);
          [exact MI2| exact ST2| exact CEIL| lia| exact FR2| exact RIa2| exact RIb2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RB2| exact RC5
          | exact HS| lia| unfold KFREEARRAY_OFF; lia| lia| subst n; lia| reflexivity| exact LD| unfold KFREEARRAY_OFF; exact DST]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 23%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 -> MU3 WM3 MI3 ST3 RIa3 RIb3 FILL).
      unfold KFREEARRAY_OFF in MU3, FILL.
      subst fam'. assert (EF : (fam <? 4 * n) = false) by (apply Z.ltb_ge; lia). rewrite !EF in K1. rewrite ?EF.
      cbv beta iota delta [wz] in K1. rewrite Z.sub_0_r in K1.
      eapply (K1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 tj1 tj2); [exact MI3| | eapply wmono_trans; [exact WM2| exact WM3]| exact ST3| exact RIa3| | exact RIb3| | | exact FILL| exact I].
      + unfold p1_W. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subfp.
      + eapply (rw_cells_transport asegs _ m2 m3); [exact RI2| exact MU3| exact WM3| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 RC2n NB1)].
      + eapply (rw_cells_transport asegs _ m2 m3); [exact TST2| exact MU3| exact WM3| cbn; pose proof (t_range st WF); unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HRB HS Hm1 CEILn RC3 RC4 RC5 RB4 RB5 N1 F3 RC2n RB2n NB1 EF H)].
      + unfold KFREEARRAY_OFF.
        apply (stk_merge asegs m3 _ D); [| | subst D n; (lia_on HRc HRB HS Hm1 Hnf RC5 RB1 N1)].
        { eapply (stk_transport_disjoint asegs _ m2 m3); [exact VL| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 RC2n)]. }
        apply (stk_merge asegs m3 _ (D + 4 * Nv)); [| | subst D n; lia].
        { pose proof (stk_of_rw_cells asegs m3 D _ (rw_cells_of_u8arr asegs _ _ _ (p_u8arr_of_u32arr asegs _ _ _ FILL))) as SF.
          cbn [cells_size Cells.csize] in SF. rewrite Nat.add_0_r, u32s_length, fill_vals_length in SF.
          replace (D + Z.of_nat (4 * Z.to_nat Nv)) with (D + 4 * Nv) in SF by (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1). exact SF. }
        eapply (stk_transport_disjoint asegs _ m2 m3); [exact VR| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 F3 RC2n)].
    - (* [comment removed for export] *) exact I.
    - (* [comment removed for export] *)
      intros LT y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 tj1' tj2' MI2 MU2 WM2 ST2 RI2 STU SHP TST2. unfold KFREEARRAY_OFF in *.
      assert (SZV : (4 * n + 262143) / 262144 * 262144 - fam = 262144) by (clear -LT F1 F2 Hn4; Z.div_mod_to_equations; lia).
      rewrite !SZV in *. change (262144 / 8) with 32768 in *.
      assert (F0 : fam = 0) by (clear -LT F1 F2 N1 NB1; subst n; Z.div_mod_to_equations; nia).
      pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
      assert (SHR : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296).
      { unfold SH, SHADOW_OFFSET. clear -RB1 RB2n F1 F3. Z.div_mod_to_equations. lia. }
      assert (SHR' : SH Ufa + 32768 <= 17594333495296) by exact SHR.
      pose proof FR1 as FR2. eapply (rw_cells_transport asegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; (lia_on HRc LO2 CEILn F0 TR SHR)].
      pose proof RIa1 as RIa2. eapply (rw_cells_transport asegs _ m1 m2) in RIa2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof RIb1 as RIb2. eapply (rw_cells_transport asegs _ m1 m2) in RIb2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof VFA1 as VFA2. eapply (stk_transport_disjoint asegs _ m1 m2) in VFA2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof (stk_merge asegs m2 _ _ _ VFA2 STU ltac:(lia)) as VALL.
      destruct (stk_split asegs m2 _ D _ VALL ltac:(subst D n; lia)) as [VL VR0].
      destruct (stk_split asegs m2 _ (D + 4 * Nv) _ VR0 ltac:(subst D n; lia)) as [VM VR].
      (nelim (stk_carve asegs m2 D (D + 4 * Nv) (Z.to_nat (4 * Nv)) VM ltac:(lia)) 3%nat; intros _ junk JK).
      replace (D + 4 * Nv - Z.of_nat (Z.to_nat (4 * Nv))) with D in JK by (lia_on HRc HRB HS Hm1 RC5 RB1 NB1 LT F0).
      destruct (p_u32arr_of_u8arr asegs m2 D junk (Z.to_nat Nv) (u8arr_of_rw_cells asegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { pose proof (rw_cells_bound asegs m2 D _ JK). cbn [cells_size Cells.csize] in H. destruct JK as [[WFj _] _]. cbn in WFj. (lia_on HRc HRB HS Hm1 RC5 RB1 N2 LT F0 WFj). }
      eapply lscps_evt_then.
      { eapply (pop_G sp gp tp) with (lo := lo) (nf := nf) (N := Nv) (dpre := dpre);
          [exact MI2| exact ST2| exact CEIL| lia| exact FR2| exact RIa2| exact RIb2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RB2| exact RC5
          | exact HS| lia| unfold KFREEARRAY_OFF; lia| lia| subst n; lia| reflexivity| exact LD| unfold KFREEARRAY_OFF; exact DST]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 23%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 -> MU3 WM3 MI3 ST3 RIa3 RIb3 FILL).
      unfold KFREEARRAY_OFF in MU3, FILL.
      subst fam'. assert (EF : (fam <? 4 * n) = true) by (apply Z.ltb_lt; lia). rewrite !EF in K1.
      cbv beta iota delta [wz] in K1. unfold LUMP in K1. replace (R1 - 262144 - 32768) with (R1 - 294912) by lia.
      eapply (K1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 tj1' tj2'); [exact MI3| | eapply wmono_trans; [exact WM2| exact WM3]| exact ST3| exact RIa3| | exact RIb3| | | exact FILL|].
      + unfold p1_W. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subfp.
      + eapply (rw_cells_transport asegs _ m2 m3); [exact RI2| exact MU3| exact WM3| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n Hn4 LT F0 TR EF)].
      + sepM. sepM. eapply (rw_cells_transport asegs _ m2 m3); [exact TST2| exact MU3| exact WM3| cbn; (lia_on HRc HRB CEILn N1 SZV F0 TR)].
      + unfold KFREEARRAY_OFF.
        apply (stk_merge asegs m3 _ D); [| | subst D n; (lia_on HRc HRB HS Hm1 RC5 RB1 N1 N2 LT SZV F0 EF)].
        { eapply (stk_transport_disjoint asegs _ m2 m3); [exact VL| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N2 RC2n LT F0)]. }
        apply (stk_merge asegs m3 _ (D + 4 * Nv)); [| | subst D n; clear -Hn4 N1 NB1 F1; Z.div_mod_to_equations; (lia_on N1 NB1)].
        { pose proof (stk_of_rw_cells asegs m3 D _ (rw_cells_of_u8arr asegs _ _ _ (p_u8arr_of_u32arr asegs _ _ _ FILL))) as SF.
          cbn [cells_size Cells.csize] in SF. rewrite Nat.add_0_r, u32s_length, fill_vals_length in SF.
          replace (D + Z.of_nat (4 * Z.to_nat Nv)) with (D + 4 * Nv) in SF by (lia_on HRc HRB HS Hm1 RC5 RB1 NB1 LT F0 EF). exact SF. }
        try replace (RB + 3758096384 + nm) with (RB + 3758096384 + fam + 262144) by (subst nm; lia).
        try replace (RB + 3758096384 + (4 * n + 262143) / 262144 * 262144) with (RB + 3758096384 + fam + 262144) by lia.
        eapply (stk_transport_disjoint asegs _ m2 m3); [exact VR| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0)].
      + eapply (rw_cells_transport asegs _ m2 m3); [exact SHP| exact MU3| exact WM3| cbn [disjoint_from cells_size Cells.csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 LT F0 SHR' EF)].
  Qed.
End P1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prf_W (lo sp Rc T stt U : Z) (um : bool) : list (Z * Z) :=
  [(lo, sp); (Rc + 48, Rc + 56); (T + 2872, T + 2888); (stt + 24, stt + 32)] ++ (if um then [(U, U + 262144); (SH U, SH U + 32768)] else []).
Definition pop_W (lo sp Rc T stt U D Nv Ufa : Z) (um fm : bool) : list (Z * Z) :=
  prf_W lo sp Rc T stt U um ++ [(Rc + 16, Rc + 24); (Rc + 24, Rc + 32); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69); (D, D + 4 * Nv)]
  ++ (if fm then [(Ufa, Ufa + 262144); (SH Ufa, SH Ufa + 32768)] else []).

Section POPW.
  Hypothesis PS : poison_shadow_spec.
  Variables (sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Let ra : word := wz 0x370a0.
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate)
            (S Rc stt c q alloc mapped nf fam lo : Z) (tj1 tj2 sa mtx sem : word) (jr je js : list byte) (exhb : bool).
  Let RB := S + c * 2^32.
  Let total := alloc + csize c * q.
  Let U := RB + mapped.
  Let Ufa := RB + KFREEARRAY_OFF + fam.
  Let D := RB + KFREEARRAY_OFF + 4 * nf.
  Let exh := if exhb then 1 else 0.
  Hypothesis HC : mmap_consts m.
  Hypothesis IC : icpt_cells m.
  Hypothesis PC : poison_cells m.
  Hypothesis LC : leafc st m.
  Hypothesis WF : RTWF st.
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + POP_STACK <= bv_unsigned sp.
  Hypothesis AC32 : ro_cells asegs m 0xa6c38 [C8 (Z_to_bv 64 S)].
  Hypothesis AC40 : ro_cells asegs m 0xa6c40 [C4 (Z_to_bv 64 4294967295)].
  Hypothesis AC56 : ro_cells asegs m 0xa6c50 [C1 (Z_to_bv 8 0)].
  Hypothesis RIa : rw_cells asegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)].
  Hypothesis RI24 : rw_cells asegs m (Rc + 24) [C8 (Z_to_bv 64 fam)].
  Hypothesis RIb : rw_cells asegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js].
  Hypothesis TST : rw_cells asegs m (st_t st + 2872) [C8 tj1; C8 tj2].
  Hypothesis SA : rw_cells asegs m (stt + 24) [C8 sa].
  Hypothesis Hstt : stt = st_t st + 2768.
  Hypothesis VFA : stk asegs m (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam).
  Hypothesis HRc : KHIGHMEM_BEG <= Rc /\ Rc + 128 <= alloc_ceiling /\ (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) /\ (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st)
                   /\ RB + 2^32 <= Rc.
  Hypothesis HS : KHIGHMEM_BEG <= S /\ S + 2^37 + 4096 <= alloc_ceiling /\ S mod 65536 = 0.
  Hypothesis HRBd : (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) /\ (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st).
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hq : 0 <= q <= 8 /\ csize c * q <= 262144.
  Hypothesis Ham : 0 <= alloc <= mapped /\ mapped mod 262144 = 0 /\ mapped <= KFREEARRAY_OFF /\ mapped <= alloc + csize c + 262144.
  Hypothesis Hnf : 0 <= nf <= 8 /\ 4 * nf <= fam.
  Hypothesis Hfam : 0 <= fam /\ fam mod 262144 = 0 /\ fam <= 2^29.
  Hypothesis LZS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true.
  Hypothesis HVIS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true -> in_winb G x = true -> m x <> None.
  Hypothesis SITEU : mmap_fixed_site mo U 262144.
  Hypothesis SITEF : forall mo1, fam + 262144 <= 2^29 -> (mo1 = mo \/ mo1 = mm_commit (wz U) (wz 262144) mo) -> mmap_fixed_site mo1 Ufa 262144.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz stt) (wz c) (wz Rc) (wz q) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_POPULATE) fc None m (seg_rom asegs).
  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs).
  (* [comment removed for export] *)
  Let XST (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) :=
    MS (mkR (wz 0x370a0) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz 0) (wz (KFREEARRAY_OFF + 1)) (wz c) (wz (mapped + 262144)) (wz q) x15 x16 x17
             (wz RB) (wz 262144) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (wz 0x373b4) fc None m1 (seg_rom asegs).

  Lemma RB_facts : KHIGHMEM_BEG <= RB /\ RB + 2^32 <= alloc_ceiling /\ RB mod 65536 = 0.
  Proof.
    subst RB. (nelimp HS 3%nat; intros S1 S2 S3). unfold KHIGHMEM_BEG, AIMG_HI in *. split; [(cut_on [Hstt HRc HS HRBd Hc Ham Hfam S1 S3] nia)|]. split; [nia|].
    rewrite Z.add_mod, S3 by lia. replace (2^32) with (65536 * 65536) by reflexivity. rewrite Z.mul_assoc, Z_mod_mult. reflexivity.
  Qed.

  Lemma populate_spec : forall (um fm : bool) (spin : bool) (P : machine_state -> Model -> lghost -> Prop),
    let mapped' := mapped + (if um then 262144 else 0) in
    let Nv := (mapped' - alloc) / csize c in
    let n := nf + Nv in
    let nm := (4 * n + 262143) / 262144 * 262144 in
    let fam' := if fm then nm else fam in
    let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo in
    let G1 := if um then (SH U, SH U + 32768) :: G else G in
    let R1 := R - (if um then LUMP else 0) in
    um = (mapped <? total) -> fm = (fam <? 4 * n) ->
    (if um then LUMP else 0) + (if fm then LUMP else 0) <= R ->
    (* [comment removed for export] *)
    (exhb = true -> um = true -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) ->
       LSCPS asegs P (RET 0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') mo (mkG G R)) ->
    (* [comment removed for export] *)
    (exhb = false -> um = true -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 (m1 : word -> option byte),
       mem_inv asegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -64) ->
       rw_cells asegs m1 (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
       rw_cells asegs m1 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] -> rw_cells asegs m1 (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
       rw_cells asegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells asegs m1 (st_t st + 2872) [C8 tj1; C8 tj2] -> rw_cells asegs m1 (stt + 24) [C8 sa] ->
       LSCPS asegs P (XST x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 m1) mo (mkG G R)) ->
    (* [comment removed for export] *)
    True ->
    True ->
    (* [comment removed for export] *)
    ((um = true -> mapped + 262144 <= KFREEARRAY_OFF) ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte) (tj1' tj2' sa' : word),
       mem_inv asegs m' -> munch (pop_W lo (bv_unsigned sp) Rc (st_t st) stt U D Nv Ufa um fm) m m' -> wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + Nv))] ->
       rw_cells asegs m' (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
       rw_cells asegs m' (Rc + 32) [C8 (Z_to_bv 64 (alloc + Nv * csize c)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells asegs m' (st_t st + 2872) [C8 tj1'; C8 tj2'] -> rw_cells asegs m' (stt + 24) [C8 sa'] ->
       stk asegs m' (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam') ->
       u32arr asegs m' D (fill_vals alloc (csize c) (Z.to_nat Nv)) ->
       (if um then stk asegs m' U (U + 262144) /\ rw_cells asegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       (if fm then rw_cells asegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       LSCPS asegs P (RET 1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m')
             (if fm then mm_commit (wz Ufa) (wz 262144) mo1 else mo1)
             (mkG (if fm then (SH Ufa, SH Ufa + 32768) :: G1 else G1) (R1 - (if fm then LUMP else 0)))) ->
    LSCPS asegs P ENTRY mo (mkG G R).
  Proof.
    intros um fm spin P. cbv zeta. intros EUM EFM HR KX1 KX _ _ K1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [CEIL LO2]. pose proof CEIL as CEILn. idtac. unfold POP_STACK in LO2.
    (nelimp HRc 5%nat; intros RC1 RC2 RC3 RC4 RC5). (nelimp RB_facts 3%nat; intros RB1 RB2 RB3). destruct HRBd as [RB4 RB5]. (nelimp HS 3%nat; intros HS1 HS2 HS3). unfold KHIGHMEM_BEG, AIMG_HI in RB1, RC1, HS1. olin_all.
    destruct Hq as [Hq1 Hq2]. (nelimp Ham 4%nat; intros A1 A2 A3 A4). destruct Hnf as [N1 N2]. (nelimp Hfam 3%nat; intros F1 F2 F3).
    pose proof RC2 as RC2n. idtac. pose proof RB2 as RB2n. idtac. pose proof HS2 as HS2n. idtac.
    pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max c ltac:(lia)) as CL.
    assert (CS32 : 32 <= csize c). { destruct (Z_le_gt_dec c 16); [rewrite csize_small by lia; lia|]. cases_17_30 c; vm_compute; discriminate. }
    pose proof (t_range st WF) as TR. sepM. olin TR. pose proof (ctx_range st WF) as CR. sepM. olin CR. unfold KHIGHMEM_BEG, AIMG_HI in TR, CR. sepM. sepM. olin_all.
    assert (E64 : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (unfold wz; apply unsigned_lit; (lia_on RSP LO2 CEILn RB1 HS1 CP)).
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply pop_A; [exact MI| exact ST| exact CEIL| lia| exact AC32| exact RIb| exact RC1| exact RC2| exact Hc| lia| lia| exact A3| exact HS1| exact HS2]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 18%nat; intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 m1 -> MU1 WM1 MI1 ST1 FR1 RIb1).
    fold total. fold RB.
    pose proof RIa as RIa1. eapply (rw_cells_transport asegs _ m m1) in RIa1; [| exact MU1| exact WM1| cbn; (lia_on HRc HRBd CEILn RC5 RB1 HS1 RC2n CP TR CR)].
    pose proof RI24 as RI241. eapply (rw_cells_transport asegs _ m m1) in RI241; [| exact MU1| exact WM1| cbn; (lia_on HRc HRBd CEILn RC5 RB1 HS1 RC2n CP TR CR)].
    pose proof TST as TST1. eapply (rw_cells_transport asegs _ m m1) in TST1; [| exact MU1| exact WM1| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on HRc HRBd Hc CEILn RC3 RC4 RC5 RB1 RB4 RB5 HS1 RC2n HS2n CP TR CR)].
    pose proof SA as SA1. eapply (rw_cells_transport asegs _ m m1) in SA1; [| exact MU1| exact WM1| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on Hstt HRc HRBd Hc CEILn RC3 RC4 RC5 RB1 RB4 RB5 HS1 RC2n HS2n CP TR CR)].
    pose proof AC40 as AC401. eapply (ro_cells_transport asegs _ m m1) in AC401; [| exact MU1| cbn; (lia_on CEILn RB1 HS1 CP)].
    pose proof AC56 as AC561. eapply (ro_cells_transport asegs _ m m1) in AC561; [| exact MU1| cbn; (lia_on CEILn RB1 HS1 CP)].
    pose proof VFA as VFA1. eapply (stk_transport_disjoint asegs _ m m1) in VFA1; [| exact MU1| exact WM1| cbn; unfold KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HS HRBd CEILn RC5 RB1 F3 RC2n CP TR CR)].
    assert (HC1 : mmap_consts m1) by (eapply mmap_consts_high; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact HC]).
    assert (IC1 : icpt_cells m1) by (eapply icpt_cells_high'; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact IC]).
    assert (PC1 : poison_cells m1) by (eapply poison_cells_high'; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact PC]).
    pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
    assert (LC1 : leafc st m1).
    { eapply (leafc_munch st _ _ _ MU1 WM1); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
      destruct Hin as [E|[]]; injection E; intros; subst.
      destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HS CEIL RB1 HRc HRBd Hc RC3 RC4 RC5 RB4 RB5 RC2n HS2n CP TR CR CT). }
    replace (wz A_RAR_MAP) with (wz RTW_p_map.A_RAR_MAP) in * by reflexivity.
    assert (NVB : forall mp, alloc <= mp <= alloc + csize c + 524288 -> 0 <= (mp - alloc) / csize c <= 16385).
    { intros mp Hmp. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
      assert (32 * 16384 <= csize c * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). (lia_on HRc HRBd RC5 RB1 HS1 A1 CP Hmp H). }
    assert (FAM0 : forall k, 0 <= k <= 16393 -> fam < 4 * k -> fam = 0).
    { intros k Hk LTF. clear -Hk LTF F1 F2. Z.div_mod_to_equations. lia. }
    assert (SHFA : forall x, SH (RB + 3758096384 + 0) <= x < SH (RB + 3758096384 + 0) + 32768 ->
                   (SH RB <= x < SH (RB + 2^32)) /\ x < 17594333495296).
    { intros x Hx. unfold SH, SHADOW_OFFSET in Hx |- *. clear -Hx RB1 RB2n RB3. Z.div_mod_to_equations. lia. }
    assert (SHM : SH (RB + mapped) + 32768 = SH (RB + mapped + 262144)).
    { unfold SH, SHADOW_OFFSET. clear -RB3 A2. Z.div_mod_to_equations. lia. }
    assert (SHK : forall a, 0 <= a -> a + 262144 <= 2^47 -> SH a + 32768 <= 17594333495296).
    { intros a Ha1 Ha2. unfold SH, SHADOW_OFFSET. clear -Ha1 Ha2. Z.div_mod_to_equations. lia. }
    assert (SHle : forall a b, a <= b -> SH a <= SH b) by (intros a b Hab; unfold SH; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
    destruct um.
    - (* [comment removed for export] *)
      assert (LT : mapped < total) by (symmetry in EUM; apply Z.ltb_lt in EUM; exact EUM).
      rewrite <- EUM. cbv iota. cbv iota in EFM, HR, KX1, KX, K1. assert (Hfm0 : 0 <= (if fm then LUMP else 0)) by (destruct fm; unfold LUMP; lia).
      destruct (Z.eq_dec mapped KFREEARRAY_OFF) as [EXH|NEXH].
      + (* [comment removed for export] *)
        destruct exhb; subst exh; cbv iota in RIb1.
        * eapply lscps_evt_then.
          { eapply (pop_exh1 sp gp tp) with (lo := lo);
              [exact MI1| exact ST1| exact CEIL| lia| exact FR1| exact AC401| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact EXH| exact RB1| exact RB2]. }
          cbv beta. intros ms2 nelH_; (nelim nelH_ 9%nat; intros y11 y12 y13 m2 -> MU2 WM2 MI2 ST2).
          apply (KX1 eq_refl eq_refl EXH); [exact MI2| eapply munch_trans; [exact MU1| exact MU2]| eapply wmono_trans; [exact WM1| exact WM2]| exact ST2].
        * eapply lscps_evt_then.
          { eapply (pop_X (wz (bv_unsigned sp + -64)) gp tp); [exact MI1| exact AC401| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact EXH]. }
          cbv beta. intros ms2 ->.
          apply (KX eq_refl eq_refl EXH); [exact MI1| exact MU1| exact WM1| exact ST1| exact FR1| exact RIa1| exact RI241| exact RIb1| exact TST1| exact SA1].
      + (* [comment removed for export] *)
        assert (NEX : mapped + 262144 <= KFREEARRAY_OFF) by (unfold KFREEARRAY_OFF in *; clear -A2 A3 NEXH A1; Z.div_mod_to_equations; lia).
        assert (U1 : KHIGHMEM_BEG <= U /\ U + 262144 <= RB + KFREEARRAY_OFF /\ U mod 32768 = 0).
        { subst U. split; [lia|]. split; [lia|]. clear -RB3 A2. Z.div_mod_to_equations. lia. }
        (nelim U1 3%nat; intros U1 U2 U3). unfold KHIGHMEM_BEG, AIMG_HI in U1. olin_all. unfold KFREEARRAY_OFF in U2.
        assert (SHFB : forall x, SH (RB + 3758096384 + 0) <= x -> SH (RB + mapped + 262144) <= x).
        { intros x Hx. unfold SH, SHADOW_OFFSET in Hx |- *. unfold KFREEARRAY_OFF in NEX. clear -Hx NEX. Z.div_mod_to_equations. lia. }
        eapply lscps_evt_then.
        { eapply (pop_B_map (wz 0x370a0) (wz (bv_unsigned sp + -64)) gp tp) with (S := S);
            [exact MI1| exact AC401| exact AC561| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact NEX| exact RB1| exact RB2]. }
        cbv beta. intros ms2 (y15 & ->). fold U.
        eapply (map_tol_spec (wz 0x3720c) (wz (bv_unsigned sp + -64))) with (lo := lo) (spin := spin);
          [exact HC1| exact MI1| rewrite E64; exact ST1| rewrite E64; split; [exact CEIL| unfold MAPTOL_STACK; lia]
          | (lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3)| clear -U3; Z.div_mod_to_equations; lia| unfold AIMG_HI; lia| lia| exact SITEU| unfold LUMP in *; (lia_on HRc HRBd Ham HR RC5 RB1 HS1 A1 CP Hfm0 U1)| |].
        * (* [comment removed for export] *) exact I.
        * (* [comment removed for export] *)
          intros y5 y6 y7 y11 y12 y13 y14 y15' y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 ZN. rewrite E64 in MU2, ST2.
          cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 225804)) with (Z_to_bv 64 225804 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          assert (SHU : SH U mod 4096 = 0 /\ 2147450880 <= SH U /\ SH U + 32768 <= 17594333495296 /\ SH (U + 262144) = SH U + 32768).
          { unfold SH, SHADOW_OFFSET. clear - U1 U2 U3 RB2n. Z.div_mod_to_equations. lia. }
          (nelim SHU 4%nat; intros SH1 SH2 SH3 SH4).
          assert (SHU' : SH (RB + mapped) mod 4096 = 0 /\ 2147450880 <= SH (RB + mapped) /\ SH (RB + mapped) + 32768 <= 17594333495296) by exact (conj SH1 (conj SH2 SH3)). (nelim SHU' 3%nat; intros SH1' SH2' SH3').
          eapply (lscps_open asegs _ _ _ G (R - 262144) (SH U) (SH U + 32768)).
          { unfold win_ok. cbn [fst snd]. clear - SH1 SH2 SH3. Z.div_mod_to_equations. lia. }
          { replace (4096 * ((SH U + 32768 - SH U) / 4096)) with 32768 by (replace (SH U + 32768 - SH U) with 32768 by lia; reflexivity). unfold LUMP in *. (lia_on HRc HRBd Ham HR RC5 RB1 HS1 A1 CP Hfm0 U1 SH2 SH2'). }
          intros mv' Emv ZFN FRZ. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS msw] in Emv |- *.
          replace (4096 * ((SH U + 32768 - SH U) / 4096)) with 32768 by (replace (SH U + 32768 - SH U) with 32768 by lia; reflexivity).
          assert (VNN : forall x : word, SH U <= bv_unsigned x < SH U + 32768 -> mv' x <> None).
          { intros x Hx.
            assert (HxR : SH RB <= bv_unsigned x < SH (RB + 2^32)) by (unfold SH, SHADOW_OFFSET in *; clear -Hx U1 U2 RB1 A1; subst U RB; Z.div_mod_to_equations; lia).
            pose proof (LZS x HxR) as Hz. destruct (in_winb G x) eqn:EW.
            - assert (V0 : m x <> None) by (apply (HVIS x HxR Hz EW)).
              assert (V1 : m1 x <> None) by (rewrite (MU1 x); [exact V0|]; cbn; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH3 SH2' Hx)).
              assert (V2 : m2 x <> None) by (rewrite (MU2 x); [exact V1|]; cbn; (lia_on HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 CP U1 SH2 SH3 SH2' Hx)).
              rewrite Emv, (open_mem_mono _ _ _ _ _ V2). exact V2.
            - rewrite (FRZ x Hx); [discriminate| | exact EW]. rewrite (lzf_commit_out mo U 262144 HOK); [exact Hz| unfold RT_artF.CEIL, KHIGHMEM_BEG, AIMG_HI; (lia_on HRc HRBd Ham RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH2')|].
              unfold in_range. apply andb_false_iff. left. apply Z.leb_gt. (lia_on HRc HRBd Hc Ham RC5 RB1 HS1 A1 CP U1 SH2 SH3 SH2' Hx). }
          assert (STSH : stk asegs mv' (SH U) (SH U + 32768)) by (apply stk_of_some; [lia| lia| exact VNN]).
          (nelim (stk_carve asegs mv' (SH U) (SH U + 32768) (Z.to_nat (262144 / 8)) STSH ltac:((lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3 SH2 SH2'))) 3%nat; intros _ shj SHJ).
          replace (SH U + 32768 - Z.of_nat (Z.to_nat (262144 / 8))) with (SH U) in SHJ by (lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3 SH2 SH2').
          (* [comment removed for export] *)
          pose proof (rw_cells_open asegs _ (SH U) (SH U + 32768) m2 _ _ ZFN ZN) as ZNv. rewrite <- Emv in ZNv.
          pose proof (stk_open asegs _ (SH U) (SH U + 32768) m2 _ _ ZFN ST2) as STv. rewrite <- Emv in STv.
          pose proof (mem_inv_open asegs _ (SH U) (SH U + 32768) m2 ZFN MI2) as MIv. rewrite <- Emv in MIv.
          assert (MUv : munch [(lo, bv_unsigned sp); (U, U + 262144); (SH U, SH U + 32768)] m mv').
          { rewrite Emv. apply munch_open_r; [| cbn; intros; lia].
            eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; subfp. }
          assert (WMv : wmono asegs m mv'). { rewrite Emv. apply wmono_open. eapply wmono_trans; [exact WM1| exact WM2]. }
          assert (HWv : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (U, U + 262144); (SH U, SH U + 32768)]).
          { repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH2'). }
          pose proof (icpt_cells_high' _ _ _ MUv HWv IC) as ICv. pose proof (poison_cells_high' _ _ _ MUv HWv PC) as PCv.
          pose proof (mmap_consts_high _ _ _ MUv HWv HC) as HCv.
          assert (LCv : leafc st mv').
          { eapply (leafc_munch st _ _ _ MUv WMv); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
            destruct Hin as [E|[E|[E|[]]]]; injection E; intros; subst;
            destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on CEIL RB1 SH2 HRBd Ham CR U2 OLx0 SH3). }
          assert (MU2v : munch [(lo, bv_unsigned sp + -64); (U, U + 262144); (SH U, SH U + 32768)] m1 mv').
          { rewrite Emv. apply munch_open_r; [eapply munch_weaken; [| exact MU2]; subfp| cbn; intros; lia]. }
          assert (WM2v : wmono asegs m1 mv') by (rewrite Emv; apply wmono_open; exact WM2).
          pose proof FR1 as FRv. eapply (rw_cells_transport asegs _ m1 mv') in FRv; [| exact MU2v| exact WM2v| cbn; (lia_on HRc HRBd Ham LO2 CEILn RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RIa as RIav. eapply (rw_cells_transport asegs _ m mv') in RIav; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RI24 as RI24v. eapply (rw_cells_transport asegs _ m mv') in RI24v; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RIb as RIbv. eapply (rw_cells_transport asegs _ m mv') in RIbv; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof TST as TSTv. eapply (rw_cells_transport asegs _ m mv') in TSTv; [| exact MUv| exact WMv| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on HRBd Ham CEILn TR OLx U2 SH2 SH3)].
          pose proof SA as SAv. eapply (rw_cells_transport asegs _ m mv') in SAv; [| exact MUv| exact WMv| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on Hstt HRBd Ham CEILn TR OLx U2 SH2 SH3)].
          pose proof AC56 as AC56v. eapply (ro_cells_transport asegs _ m mv') in AC56v; [| exact MUv| cbn; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH2')].
          pose proof VFA as VFAv. eapply (stk_transport_disjoint asegs _ m mv') in VFAv; [| exact MUv| exact WMv| cbn; unfold KFREEARRAY_OFF in *; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 F3 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          clear ZN ST2 MI2 VNN STSH.
          lazymatch goal with |- LSCPS _ _ (msw (MS ?RR ?FF ?p ?cc ?v ?mm ?ro) ?mv) _ _ => change (msw (MS RR FF p cc v mm ro) mv) with (MS RR FF p cc v mv ro) end.
          subst exh.
          eapply lscps_evt_then.
          { eapply (pop_D PS sp gp tp) with (st := st) (lo := lo) (msz := 262144) (stt := stt);
              [exact ICv| exact PCv| exact LCv| exact WF| exact TP| exact MIv| exact STv| exact CEIL| lia| exact RIbv| exact RC1| exact RC2| exact RC3| exact RC4| exact RC5
              | exact TSTv| exact SAv| exact Hstt| exact RB1| exact RB2| exact RB3| exact RB4| exact RB5| (lia_on HRc HRBd Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2')| clear -A2; Z.div_mod_to_equations; lia| reflexivity| exact NEX| exact SHJ]. }
          cbv beta. intros ms3 nelH_; (nelim nelH_ 27%nat; intros w1 w5 w6 w7 w11 w12 w14 w15 w16 w17 w28 w29 w30 w31 m3 tj1' tj2' sa' -> MU3 WM3 MI3 ST3 RIb3 SHP3 TST3 SA3).
          cbv beta delta [wz] in *|-. change (262144 / 8) with 32768 in *.
          pose proof FRv as FR3. eapply (rw_cells_transport asegs _ mv' m3) in FR3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc LO2 CEILn TR SH3')].
          pose proof RIav as RIa3. eapply (rw_cells_transport asegs _ mv' m3) in RIa3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 SH2 SH2' SH3')].
          pose proof RI24v as RI243. eapply (rw_cells_transport asegs _ mv' m3) in RI243; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 SH2 SH2' SH3')].
          pose proof AC56v as AC563. eapply (ro_cells_transport asegs _ mv' m3) in AC563; [| exact MU3| cbn; (lia_on Hstt Ham CEILn RC1 RC5 RB1 HS1 A1 CP OLx OLx2 U1 SH2 SH2')].
          pose proof VFAv as VFA3. eapply (stk_transport_disjoint asegs _ mv' m3) in VFA3; [| exact MU3| exact WM3| cbn; unfold KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; (lia_on Hstt HRc HS HRBd Ham CEILn RC5 RB1 F3 RC2n CP U1 SH2 SH2' SH3')].
          pose proof ZNv as STU3. apply (stk_of_rw_cellsZ _ _ _ 262144) in STU3; [| cbn; (lia_on HRc HRBd Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2')]. eapply (stk_transport_disjoint asegs _ mv' m3) in STU3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 RC2n CP U1 U2 SH2 SH2' SH3')].
          assert (MUt : munch (prf_W lo (bv_unsigned sp) Rc (st_t st) stt U true) m m3).
          { unfold prf_W. cbn [app]. eapply munch_trans; [eapply munch_weaken; [| exact MUv]| eapply munch_weaken; [| exact MU3]]; subfp. }
          assert (WMt : wmono asegs m m3) by (eapply wmono_trans; [exact WMv| exact WM3]).
          pose proof (t_range st WF) as [TRo _]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa _ TRi). unfold AIMG_LO, AIMG_HI in TRi. clear TRo.
          assert (HWt : Forall outI (prf_W lo (bv_unsigned sp) Rc (st_t st) stt U true)).   (* [comment removed for export] *)
          { unfold prf_W, outI. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; (lia_on HS Ham CEILn RB1 CP U1 SH2 SH2' HRc RC1 RC5 A1 OLx2 Hstt). }
          assert (LC3 : leafc st m3).
          { eapply (leafc_munch st _ _ _ MUt WMt); [| exact LC]. intros lo' hi' a b Hin Hab. unfold prf_W in Hin. cbn in Hin, Hab.
            sepM. sepM. destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros; subst;
            destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on CEIL RB1 SH2 HRc HRBd Ham CR CT OLx2 U2 OLx0 SH3). }
          eapply (pop_P1 PS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 (mm_commit (Z_to_bv 64 U) (Z_to_bv 64 262144) mo) ((SH U, SH U + 32768) :: G) (R - 262144 - 32768) st Rc RB (csize c) alloc (mapped + 262144) nf fam lo tj1' tj2' mtx sem jr je js) with (spin := spin);
            [exact (mmap_consts_out _ _ _ MUt HWt HC)| exact (icpt_cells_out _ _ _ MUt HWt IC)| exact (poison_cells_out _ _ _ MUt HWt PC)| exact LC3| exact WF| exact TP| exact MI3| exact ST3
            | split; [exact CEIL| unfold POP_STACK; lia]| exact FR3| exact RIa3| exact RI243| exact RIb3| exact AC563| exact TST3| exact VFA3
            | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| lia| unfold KFREEARRAY_OFF in *; lia| lia| lia| | | | | |].
          -- (* [comment removed for export] *) intros LTF x Hx. unfold KFREEARRAY_OFF in Hx. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB.
             assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). pose proof (SHFB _ (proj1 Hx)) as HxU.
             unfold wz. rewrite (lzf_commit_out mo U 262144 HOK); [apply LZS; exact HxR| unfold RT_artF.CEIL, KHIGHMEM_BEG, AIMG_HI; (lia_on HRc HRBd Ham RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH2')|].
             unfold in_range. apply andb_false_iff. left. apply Z.leb_gt. (lia_on HRc HRBd Hc Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2' HxK).
          -- (* [comment removed for export] *) intros LTF x Hx Hz EW. unfold KFREEARRAY_OFF in Hx. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB.
             assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). pose proof (SHFB _ (proj1 Hx)) as HxU.
             assert (EW' : in_winb G x = true).
             { unfold in_winb in EW |- *. cbn [existsb] in EW. apply orb_true_iff in EW. destruct EW as [EW|EW]; [| exact EW].
               exfalso. unfold in_range in EW. apply andb_true_iff in EW. destruct EW as [EW1 EW2]. apply Z.leb_le in EW1. apply Z.ltb_lt in EW2.
               cbn [fst snd] in EW1, EW2. subst U. lia. }
             assert (V0 : m x <> None) by (apply (HVIS x HxR (LZS x HxR) EW')).
             rewrite (MUt x); [exact V0|]. unfold prf_W. cbn. subst U. (lia_on Hstt HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 CP OLx U1 SH2 SH4 SH2' HxK HxU).
          -- (* [comment removed for export] *) intros LTF. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB. assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). apply SITEF; [lia| right; reflexivity].
          -- (* [comment removed for export] *) intros LTF. assert (EF : fm = true) by (rewrite EFM; apply Z.ltb_lt; exact LTF). rewrite EF in HR. cbv iota in HR. unfold LUMP in *. lia.
          -- (* [comment removed for export] *) exact I.
          -- (* [comment removed for export] *) intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 tj1'' tj2'' MI4 MU4 WM4 ST4 RIa4 RI244 RIb4 TST4 VFA4 FILL4 SHF4.
             rewrite <- !EFM in *. replace (R - 262144 - 32768) with (R - LUMP) by (unfold LUMP; lia).
             assert (NB : 0 <= (mapped + 262144 - alloc) / csize c <= 16385) by (apply NVB; lia).
             assert (SK : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296) by (apply SHK; (lia_on Ham RC1 RB1 HS1 F1 CP U1 SH2 SH2' HRc HRBd RC5 F3 RC2n TR CR)).
             assert (SLE : SH (RB + mapped + 262144) <= SH (RB + 3758096384 + fam)) by (apply SHle; unfold KFREEARRAY_OFF in NEX; (lia_on HRc HRBd Ham RC5 RB1 HS1 F1 CP NEX U1 SH2 SH2')).
             assert (SHMU : SH U + 32768 = SH (RB + mapped + 262144)) by exact SHM.
             unfold p1_W in MU4. unfold pop_W, prf_W, KFREEARRAY_OFF. destruct fm; cbn [app] in MU4 |- *.
             all: apply (K1 (fun _ => NEX)) with (tj1' := tj1'') (tj2' := tj2'') (sa' := sa');
               [exact MI4| | eapply wmono_trans; [exact WMt| exact WM4]| exact ST4| exact RIa4| exact RI244| exact RIb4| exact TST4| | exact VFA4| exact FILL4| | exact SHF4].
             all: try (eapply munch_trans; [eapply munch_weaken; [| exact MUt]| eapply munch_weaken; [| exact MU4]]; unfold prf_W; cbn [app]; subfp).
             all: try (eapply (rw_cells_transport asegs _ m3 m4); [exact SA3| exact MU4| exact WM4| cbn; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *; (cut_on [Hstt HRc HRBd EFM CEILn N1 F1 F3 TR OLx SHM SH2' NB SK SLE] (repeat match goal with |- context [?a / csize c] => let Q := fresh "Qd" in set (Q := a / csize c) in *; clearbody Q end; (lia_on Hstt HRc HRBd EFM CEILn N1 F1 TR OLx SHM SH2' NB SK SLE)))]).
             all: split.
             all: try (eapply (stk_transport_disjoint asegs _ m3 m4); [exact STU3| exact MU4| exact WM4| cbn; unfold KFREEARRAY_OFF in *; (lia_on HRc HRBd Ham CEILn RB1 N1 F1 NEX SK)]).
             all: eapply (rw_cells_transport asegs _ m3 m4); [exact SHP3| exact MU4| exact WM4| cbn [disjoint_from cells_size Cells.csize app]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold KFREEARRAY_OFF in *; (lia_on HRc CEILn RB1 N1 F1 OLx SH2 SK SLE SHMU)].
    - (* [comment removed for export] *)
      assert (GE : total <= mapped) by (symmetry in EUM; apply Z.ltb_ge in EUM; exact EUM).
      rewrite <- EUM. cbv iota. cbv iota in EFM, HR, KX1, KX, K1.
      try replace (mapped + 0) with mapped in EFM by lia. try replace (mapped + 0) with mapped in K1 by lia.
      try replace (R - 0) with R in K1 by lia. try replace (0 + (if fm then LUMP else 0)) with (if fm then LUMP else 0) in HR by lia.
      try replace (mapped + 0) with mapped by lia.
      subst exh.
      eapply (pop_P1 PS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 mo G R st Rc RB (csize c) alloc mapped nf fam lo tj1 tj2 mtx sem jr je js) with (spin := spin);
        [exact HC1| exact IC1| exact PC1| exact LC1| exact WF| exact TP| exact MI1| exact ST1
        | split; [exact CEIL| unfold POP_STACK; lia]| exact FR1| exact RIa1| exact RI241| exact RIb1| exact AC561| exact TST1| exact VFA1
        | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| lia| unfold KFREEARRAY_OFF in *; lia| lia| lia| | | | | |].
      + (* [comment removed for export] *) intros LTF x Hx. unfold KFREEARRAY_OFF in Hx. pose proof (NVB mapped ltac:(lia)) as NB.
        assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). apply LZS. exact HxR.
      + (* [comment removed for export] *) intros LTF x Hx Hz EW. unfold KFREEARRAY_OFF in Hx. pose proof (NVB mapped ltac:(lia)) as NB.
        assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK).
        rewrite (MU1 x); [exact (HVIS x HxR Hz EW)|]. cbn. lia.
      + (* [comment removed for export] *) intros LTF. pose proof (NVB mapped ltac:(lia)) as NB. assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). apply SITEF; [lia| left; reflexivity].
      + (* [comment removed for export] *) intros LTF. assert (EF : fm = true) by (rewrite EFM; apply Z.ltb_lt; exact LTF). rewrite EF in HR. cbv iota in HR. unfold LUMP in *. lia.
      + (* [comment removed for export] *) exact I.
      + (* [comment removed for export] *) intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 tj1'' tj2'' MI4 MU4 WM4 ST4 RIa4 RI244 RIb4 TST4 VFA4 FILL4 SHF4.
        rewrite <- !EFM in *. rewrite ?Z.sub_0_r.
        assert (NB : 0 <= (mapped - alloc) / csize c <= 16385) by (apply NVB; lia).
        assert (SK : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296) by (apply SHK; (lia_on Ham RC1 RB1 HS1 F1 CP HRc HRBd RC5 F3 RC2n TR CR)).
        unfold p1_W in MU4. unfold pop_W, prf_W, KFREEARRAY_OFF. destruct fm; cbn [app] in MU4 |- *.
        all: apply (K1 ltac:(discriminate)) with (tj1' := tj1'') (tj2' := tj2'') (sa' := sa);
          [exact MI4| | eapply wmono_trans; [exact WM1| exact WM4]| exact ST4| exact RIa4| exact RI244| exact RIb4| exact TST4| | exact VFA4| exact FILL4| exact I| exact SHF4].
        all: try (eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU4]]; subfp).
        all: sepM. all: (pose proof (t_range st WF) as TRq; olin TRq).   (* [comment removed for export] *)
        all: (pose proof (rt_SH_mono 0 (RB + 3758096384 + fam) ltac:((lia_on Ham RC1 RB1 HS1 F1 CP))) as SKlo; change (SH 0) with 2147450880 in SKlo).   (* [comment removed for export] *)
        all: eapply (rw_cells_transport asegs _ m1 m4); [exact SA1| exact MU4| exact WM4| cbn; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *; (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 F3 NB SK TRq SKlo] (repeat match goal with |- context [?a / csize c] => let Q := fresh "Qd" in set (Q := a / csize c) in *; clearbody Q end; (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 NB SK TRq SKlo F3] (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 NB SK TRq SKlo F3] blia))))].
  Qed.
End POPW.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].
End RTW_p_pop2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_pop1.
Import RTW_p_pop2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_gfa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_refillw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_zone RTW_p_abs.
Import RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_pop RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_cost RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs.
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

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma refill_cells : forall st m cls, RTREP st m -> RTWF st -> 1 <= cls <= 30 -> cch st cls = [] ->
  let r := rg st cls in
  exists (jr je js : list byte) (tj1 tj2 sa : word),
    ro_cells asegs m 0xa6c38 [C8 (Z_to_bv 64 (st_spacebeg st))]
    /\ ro_cells asegs m 0xa6c40 [C4 (Z_to_bv 64 4294967295)]
    /\ ro_cells asegs m 0xa6c48 [C8 (Z_to_bv 64 (ris st))]
    /\ ro_cells asegs m 0xa6c50 [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 (num_freed st cls))]
    /\ rw_cells asegs m (rinfo st cls + 24) [C8 (Z_to_bv 64 (r_mapped_fa r))]
    /\ rw_cells asegs m (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r)); C8 (Z_to_bv 64 0);
                                            CB 4 jr; C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]
    /\ rw_cells asegs m (st_t st + 2872) [C8 tj1; C8 tj2]
    /\ rw_cells asegs m (st_t st + 2768 + 24) [C8 sa]
    /\ vis m (fabeg st cls) (fabeg st cls + r_mapped_fa r)
    /\ (forall i, 0 <= i < num_freed st cls -> rw_cells asegs m (fabeg st cls + 4 * i) [W4 (nthz (r_fa r) i 0)])
    /\ rw_cells asegs m (pcaddr st cls) [C4 (wz 0); C4 (Z_to_bv 64 (pc_max_count st cls)); C8 (wz (pc_class_size st cls))].
Proof.
  intros st m cls HR WF Hc HC0. cbv zeta.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelimp (proj1 (rr_alloc st m HR)) 4%nat; intros j1 j2 j3 AL).
  (nelim (proj2 (rr_rinfo st m HR) cls Hcls) 4%nat; intros jr je js RC).
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR. olin_all.
  pose proof (proj1 (rr_thread st m HR)) as VT.
  destruct (vis_c8 m _ _ (st_t st + 2872) VT ltac:(lia) ltac:(lia)) as [tj1 T1].
  destruct (vis_c8 m _ _ (st_t st + 2880) VT ltac:(lia) ltac:(lia)) as [tj2 T2].
  destruct (vis_c8 m _ _ (st_t st + 2768 + 24) VT ltac:(lia) ltac:(lia)) as [sa SA].
  (nelim (rr_regions st m HR cls Hcls) 6%nat; intros V1 V2 V3 V4 EN TL).
  destruct (rr_cache st m HR cls Hcls) as [PC _]. rewrite HC0 in PC. change (zlen (@nil Z)) with 0 in PC.
  exists jr, je, js, tj1, tj2, sa.
  unfold A_ALLOC in AL.
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6c18 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1] [W8 (st_spacebeg st)]
             [W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6c18 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st)] [W4 (2^32 - 1)]
             [CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6c18 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2] [W8 (st_spacebeg st + KSPACESIZE)]
             [W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6c18 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE)] [W1 0]
             [CB 7 j3]). exact AL. }
  unfold rinfo_cells in RC.
  split. { apply (rw_cells_take m _ _ [W8 (r_mapped_fa (rg st cls)); W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_mid m _ [W8 0; W8 0; W8 (num_freed st cls)] [W8 (r_mapped_fa (rg st cls))] [W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_drop m _ [W8 0; W8 0; W8 (num_freed st cls); W8 (r_mapped_fa (rg st cls))]). exact RC. }
  split. { apply (proj2 (rw_cells_app m _ [C8 tj1] [C8 tj2])). split; [exact T1|]. replace (st_t st + 2872 + Z.of_nat (cells_size [C8 tj1])) with (st_t st + 2880) by (cbn; lia). exact T2. }
  split; [exact SA|]. split; [exact V3|]. split; [exact EN|]. exact PC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WPRE (lo sp P : Z) : list (Z * Z) := [(lo, sp); (P + 80, P + 2560)].

Lemma refill_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (cls lo : Z),
  RTREP st m -> RTWF st -> 1 <= cls <= 30 -> cch st cls = [] ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  let P := acache st in let pc := pcaddr st cls in
  evt asegs (fun ms1 => exists (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (j : list byte) (m1 : word -> option byte),
      ms1 = refill_call sp gp tp x5 x6 x7 pc (nrefill cls) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc (P + 2560) cls m1
      /\ munch (WPRE lo (bv_unsigned sp) P) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) (refill_frame j s1 s0 ra)
      /\ (forall c, 0 <= c < KNUMCLASSES -> rw_cells asegs m1 (pcaddr st c) [W4 (zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)])
      /\ (forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells asegs m1 (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz pc) (wz A_ALLOC) (wz cls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AREFILL) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF Hc HC0 MI ST CEIL LO. cbv zeta.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR. olin_all. pose proof CEIL as CEILn. idtac.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct (rr_cache st m HR cls Hcls) as [PC _]. rewrite HC0 in PC. change (zlen (@nil Z)) with 0 in PC.
  assert (PCB : (4096 <= pcaddr st cls /\ (pcaddr st cls + 80 <= AIMG_LO \/ AIMG_HI <= pcaddr st cls)) /\ pcaddr st cls + 80 <= alloc_ceiling /\ pcaddr st cls = acache st + 80 * cls /\ acache st = st_t st + 208)
    by (unfold pcaddr, acache, T_ACACHE, KHIGHMEM_BEG, AIMG_LO, AIMG_HI; idtac; lia).
  (nelim PCB 4%nat; intros PB1 PB2 PB3 PB4).
  pose proof (cmaxcount_range cls ltac:(lia)) as [CMR _].
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (refill_pro ra sp gp tp) with (lo := lo) (mc := pc_max_count st cls); [exact MI| exact ST| exact CEIL| exact LO| exact PC| exact PB1| exact PB2|].
    unfold pc_max_count. destruct (st_cache_inited st && negb (cls =? 0)); lia. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros j m1 -> MU1 WM1 MI1 ST1 FR1 PC1).
  unfold pc_max_count. destruct (st_cache_inited st) eqn:INI.
  - (* [comment removed for export] *)
    cbn [andb negb]. rewrite (proj2 (Z.eqb_neq cls 0)) by lia. cbn [negb]. rewrite (proj2 (Z.eqb_neq (cmaxcount cls) 0)) by lia.
    eapply evt_cut. { eapply (refill_B ra sp gp tp) with (P := acache st); [exact MI1| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc]. }
    cbv beta. intros ms2 ->. apply evt_done. nexists 12%nat. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU1]. unfold WPRE, sub_fp. cbn. intros x Hx. tauto. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|]. split.
    + intros c Hc'. destruct (rr_cache st m HR c Hc') as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
      replace (if negb (c =? 0) then cmaxcount c else 0) with (if c =? 0 then 0 else cmaxcount c) in H by (destruct (c =? 0); reflexivity).
      replace (if negb (c =? 0) then csize c else 0) with (if c =? 0 then 0 else csize c) in H by (destruct (c =? 0); reflexivity).
      eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn. unfold pcaddr, acache, T_ACACHE. unfold KNUMCLASSES in Hc'. lia.
    + intros c i Hc' Hi. destruct (rr_cache st m HR c Hc') as [_ H]. specialize (H i Hi).
      pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c).
      eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn. unfold pcaddr, acache, T_ACACHE. unfold KNUMCLASSES in Hc'. lia.
  - (* [comment removed for export] *)
    cbn [andb]. cbn [Z.eqb].
    assert (CELLS : forall c, 1 <= c <= 31 -> rw_cells asegs m1 (acache st + 80 * c) [C4 (wz (zlen (cch st c))); CB 4 (le4 (wz 0)); CB 8 (le8 (wz 0))]).
    { intros c Hc'. destruct (rr_cache st m HR c ltac:(unfold KNUMCLASSES; lia)) as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
      eapply rw_cells_transport in H; [| exact MU1| exact WM1| cbn; unfold pcaddr, acache, T_ACACHE; lia].
      change (pcaddr st c) with (acache st + 80 * c) in H.
      eapply rw_cells_recast_p; [exact H| cbn; repeat split; reflexivity| reflexivity]. }
    eapply evt_cut.
    { eapply (refill_init ra sp gp tp) with (P := acache st) (cnt := fun c => wz (zlen (cch st c))) (j2 := fun _ => le4 (wz 0)) (j3 := fun _ => le8 (wz 0));
        [exact MI1| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc| exact CELLS]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 11%nat; intros x13 x15 x28 x29 x30 m2 -> MU2 WM2 MI2 CELLS2).
    assert (MU12 : munch (WPRE lo (bv_unsigned sp) (acache st)) m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold WPRE, sub_fp; cbn; intros x Hx; tauto. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
    eapply evt_cut. { eapply (refill_B ra sp gp tp) with (P := acache st); [exact MI2| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc]. }
    cbv beta. intros ms3 ->. apply evt_done. nexists 12%nat. split; [reflexivity|].
    split; [exact MU12|]. split; [exact WM12|]. split; [exact MI2|].
    split. { eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. unfold acache, T_ACACHE. lia. }
    split. { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. unfold acache, T_ACACHE. lia. }
    split.
    + intros c Hc'. destruct (Z.eq_dec c 0) as [->|NZ].
      * cbn [Z.eqb]. destruct (rr_cache st m HR 0 Hc') as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
        eapply rw_cells_transport; [exact H| exact MU12| exact WM12|]. unfold WPRE. cbn. unfold pcaddr, acache, T_ACACHE. lia.
      * rewrite (proj2 (Z.eqb_neq c 0)) by lia. unfold KNUMCLASSES in Hc'. exact (CELLS2 c ltac:(lia)).
    + intros c i Hc' Hi. exfalso. rewrite (wb_uninit st (wf_base_ok st WF) INI c) in Hi. change (zlen (@nil Z)) with 0 in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fa_entry_small : forall st c i, RTWF st -> 1 <= c <= 30 -> 0 <= i < num_freed st c -> 0 <= nthz (r_fa (rg st c)) i 0 < 2^28.
Proof.
  intros st c i WF Hc Hi. assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (wf_class_ok st WF c HcK) as WC.
  set (k := nthz (r_fa (rg st c)) i 0).
  assert (IN : In k (r_fa (rg st c))).
  { unfold k, nthz. destruct (Z.ltb_spec0 i 0); [lia|]. apply nth_In. unfold num_freed, zlen in Hi. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c WC). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. left. exact IN. }
  (nelim CV 3%nat; intros j Hj Ek). pose proof (chunk_cptr_eq c j ltac:(lia)) as E16. rewrite <- Ek in E16.
  pose proof (wc_alloc_carved st c WC) as AC. pose proof (wc_alloc_mapped st c WC) as AM. pose proof (wc_mapped_max st c WC) as MM.
  pose proof (csize_pos c ltac:(lia)) as CP. unfold ncarved in Hj. unfold KFREEARRAY_OFF in MM.
  assert (j * csize c <= r_allocated (rg st c) - csize c).
  { rewrite AC. unfold ncarved. pose proof (Z.mul_div_le (r_allocated (rg st c)) (csize c) ltac:(lia)).
    assert (j * csize c + csize c <= r_allocated (rg st c) / csize c * csize c) by nia. nia. }
  nia.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr asegs m A [].
Proof.
  intros m A H1 H2. split.
  - split; [exact H1|]. split; [cbn [u32s length Z.of_nat flat_map]; rewrite Z.add_0_r; exact H2|]. intros i Hi. cbn in Hi. exfalso. clear -Hi. lia.
  - split; [exact H1|]. split; [cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; exact H2|]. intros i Hi. exfalso. clear -Hi. cbn in Hi. lia.
Qed.

Lemma nthz_map_seq : forall (f : nat -> Z) k i d, 0 <= i < Z.of_nat k -> nthz (map f (seq 0 k)) i d = f (Z.to_nat i).
Proof.
  intros f k i d Hi. unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|]. apply map_seq_nth. lia.
Qed.

(* [comment removed for export] *)
Lemma fill_vals_nth : forall alloc SZ (N t : nat), (t < N)%nat ->
  nth_error (fill_vals alloc SZ N) t = Some (Z_to_bv 64 ((alloc + Z.of_nat (N - 1 - t) * SZ) / 16)).
Proof.
  intros alloc SZ N. induction N as [|N IH]; intros t Ht; [lia|].
  rewrite fill_vals_S. destruct t as [|t].
  - cbn [nth_error]. replace (S N - 1 - 0)%nat with N by lia. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. replace (S N - 1 - S t)%nat with (N - 1 - t)%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma chunk_cptr_small : forall c j, 1 <= c <= 30 -> 0 <= j -> j * csize c + csize c <= 3758096384 -> 0 <= chunk_cptr c j < 2^28.
Proof.
  intros c j Hc Hj Hb. pose proof (chunk_cptr_eq c j ltac:(lia)) as E. pose proof (csize_pos c ltac:(lia)). nia.
Qed.

Ltac dj := cbn; repeat match goal with |- _ /\ _ => split end; try exact I; first [left; lia | right; lia | lia].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition WREST (lo sp pc t Rc U usz FA nf : Z) : list (Z * Z) :=
  [(lo, sp); (pc, pc + 80); (t + 2768, t + 2896); (Rc, Rc + 128); (U, U + usz); (SH U, SH U + 32768);
   (FA + 4 * nf, FA + 536870912); (SH FA, SH FA + 67108864)].
(* [comment removed for export] *)
Definition WTOT (lo sp P pc t Rc U usz FA nf : Z) : list (Z * Z) := WPRE lo sp P ++ WREST lo sp pc t Rc U usz FA nf.

Definition hideP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| lia] end ].

(* [comment removed for export] *)
Definition pch_at (st : rtstate) (cls : Z) (m' : word -> option byte) (k : Z) : Prop :=
  forall c, 0 <= c < KNUMCLASSES ->
    rw_cells asegs m' (pcaddr st c) [W4 (if c =? cls then k else zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Definition pco_at (st : rtstate) (m' : word -> option byte) : Prop :=
  forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells asegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPC.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hc : 1 <= cls <= 30.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma tail_blockfree : forall lo hi, rbeg st cls + r_mapped (rg st cls) <= lo -> hi <= rbeg st cls + KREGIONSIZE -> blockfree st lo hi.
Proof.
  intros lo hi H1 H2. (nelimp (cls_facts st WF cls Hc) 8%nat; intros C1 C2 C3 C4 C5 C6 C7 _).
  apply (prim_nonuser_blockfree st WF); [lia| lia|].
  intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE]; [right; exact H1|].
  (nelim (region_range st WF c Hc') 6%nat; intros _ R2 _ _ R5 _).
  rewrite !(rbeg_val st) in *. unfold KFREEARRAY_OFF, KREGIONSIZE, KNUMCLASSES in *.
  destruct (Z_lt_le_dec c cls); [right| left]; nia.
Qed.

Lemma pz_not_client : forall lo hi a, pz_ok st cls (lo, hi) -> (CEIL <= lo -> hi <= SP) -> lo <= a < hi ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros lo hi a PZ HS Ha. (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
  pose proof (t_range st WF) as [T1 T2].
  unfold pz_ok in PZ. cbn [fst snd] in PZ. destruct PZ as [Z1|[Z2|[Z3|[Z4|[Z5|Z6]]]]].
  - eapply (tpage_not_client st WF SP); try exact HSP. unfold T_ACACHE, T_UNWINDING in *. lia.
  - eapply (below_sp_not_client st WF SP); try exact HSP. specialize (HS (proj1 (conj Z2 I))). lia.
  - eapply (hm_not_client st WF SP) with (lo := ris st) (hi := ris st + 4096); try exact HSP;
      [apply (ris_blockfree st WF)| apply (prim_framefree st WF); pose proof (ris_range st WF); lia
      | pose proof (ris_range st WF); blia| pose proof (ris_range st WF); unfold CEIL; lia| unfold KNUMCLASSES in *; lia].
  - eapply (hm_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| unfold KFREEARRAY_OFF, KREGIONSIZE in *; lia].
  - eapply (hm_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia
      | rewrite C13 in Z5; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia].
  - eapply (hmsh_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| lia].
Qed.

Lemma cli_pres_pz : forall W m m', munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as [A1 A2]. cbn [fst snd] in A2. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. exact (pz_not_client lo hi a A1 A2 Hin HC).
Qed.

(* [comment removed for export] *)
Lemma outside_intro' : forall W a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. intros W a H. induction W as [|[l' h'] W IH]; [exact I|]. cbn. split; [exact (H (l', h') ltac:(left; reflexivity))| apply IH; intros iv Hiv; apply H; right; exact Hiv]. Qed.
Lemma rt_frame_pz : forall W m m' lo FP, munch W m m' ->
  (forall a iv, In iv W -> fst iv <= a < snd iv -> (lo <= a < SP) \/ in_ivs FP a) ->
  rt_frame FP lo SP m m'.
Proof.
  intros W m m' lo FP MU HW a Ha Hs Hn. apply MU. rewrite wa_unsigned by lia. apply outside_intro'.
  intros iv Hiv Hin. destruct (HW a iv Hiv Hin) as [X|X]; [exact (Hs X)| exact (Hn X)].
Qed.
End FPC.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rinfo_join3 : forall m Rc (a b c d : cell) rest,
  rw_cells asegs m Rc [a; b; c] -> rw_cells asegs m (Rc + 24) [d] -> rw_cells asegs m (Rc + 32) rest ->
  cells_size [a; b; c] = 24%nat -> cells_size [d] = 8%nat ->
  rw_cells asegs m Rc ([a; b; c] ++ [d] ++ rest).
Proof.
  intros m Rc a b c d rest H1 H2 H3 E1 E2. apply rw_cells_app. split; [exact H1|]. rewrite E1. change (Z.of_nat 24) with 24.
  apply rw_cells_app. split; [exact H2|]. rewrite E2. change (Z.of_nat 8) with 8. replace (Rc + 24 + 8) with (Rc + 32) by lia. exact H3.
Qed.

Lemma nth_error_wl : forall (fa : list Z) k, (k < length fa)%nat -> nth_error (wl fa) k = Some (wz (nth k fa 0)).
Proof.
  intros fa k Hk. unfold wl. rewrite nth_error_map. rewrite (nth_error_nth' fa 0 Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma GWIN_addwin : forall st m mo G R R' lo hi,
  GWIN st m mo (mkG G R) -> (forall x : word, lo <= bv_unsigned x < hi -> m x <> None) -> GWIN st m mo (mkG ((lo, hi) :: G) R').
Proof.
  intros st m mo G R R' lo hi HG VIS. apply (GWIN_open st m mo G R lo hi R' HG). intros x Hx _ _. exact (VIS x Hx).   (* [comment removed for export] *)
Qed.
Lemma GWIN_R : forall st m mo G R R', GWIN st m mo (mkG G R) -> GWIN st m mo (mkG G R').
Proof. intros st m mo G R R' HG x Hw Hz Hr. exact (HG x Hw Hz Hr). Qed.

Lemma vis_bytes : forall m lo hi, stk asegs m lo hi -> AIMG_HI <= lo -> forall x : word, lo <= bv_unsigned x < hi -> m x <> None.
Proof.
  intros m lo hi ST Hlo x Hx. pose proof (stk_some m lo hi (bv_unsigned x) ST Hx Hlo) as H. unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma zsum_ge_In : forall (f : Z -> Z) l x, (forall y, In y l -> 0 <= f y) -> In x l -> List.NoDup l -> f x <= zsum (map f l).
Proof.
  intros f l x Hf Hx ND. induction l as [|y l IH]; [destruct Hx|]. cbn [map]. rewrite zsum_cons. inversion ND; subst.
  destruct Hx as [->|Hx].
  - pose proof (zsum_nonneg (map f l) ltac:(apply Forall_map; apply Forall_forall; intros z Hz; apply Hf; right; exact Hz)). lia.
  - specialize (IH ltac:(intros z Hz; apply Hf; right; exact Hz) Hx ltac:(assumption)). pose proof (Hf y ltac:(left; reflexivity)). lia.
Qed.
Lemma prov_cls_le : forall st cls, RTWF st -> 1 <= cls <= 30 -> provU st cls + provF st cls <= rt_prov st.
Proof.
  intros st cls WF Hc. (nelimp (rt_prov_parts_nonneg st WF) 8%nat; intros P1 P2 P3 P4 P5 P6 P7 P8).
  pose proof (prov_l24_nonneg st) as P9. pose proof (prov_emb_nonneg st) as [P10 _].
  assert (provU st cls + provF st cls <= prov_classes st).
  { unfold prov_classes. apply (zsum_ge_In (fun c => provU st c + provF st c) classes cls).
    - intros y _. unfold provU, provF. lia.
    - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
    - apply classes_nodup. }
  unfold rt_prov. lia.
Qed.
Lemma lumpU_ok : forall st cls, RTWF st -> 1 <= cls <= 30 -> cch st cls = [] -> num_freed st cls < nrefill cls ->
  r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls * (nrefill cls - num_freed st cls) -> LUMPU <= provU st cls.
Proof.
  intros st cls WF Hc HC0 LT UM. (nelimp (slack_ok' cls Hc) 3%nat; intros SL1 SL2 SL3). pose proof (csize_pos cls ltac:(lia)) as CP.
  pose proof (wc_num_freed st cls (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia))) as NF. pose proof (zlen_nonneg (r_fa (rg st cls))) as NF0. unfold num_freed in *.
  unfold provU, delta, navail, avail_cptrs. rewrite HC0, app_nil_r.
  replace (r_mapped (rg st cls) - r_allocated (rg st cls) <? nrefill cls * csize cls) with true.
  2:{ symmetry. apply Z.ltb_lt. assert (csize cls * (nrefill cls - zlen (r_fa (rg st cls))) <= csize cls * nrefill cls) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  unfold Nmax, FAPROV. pose proof (Z.div_pos (2^18) (csize cls) ltac:(lia) ltac:(lia)).
  assert (2 * csize cls * zlen (r_fa (rg st cls)) <= 2 * csize cls * (nrefill cls - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold LUMPU in *. lia.
Qed.
Lemma lumpF_ok : forall st cls, RTWF st -> 1 <= cls <= 30 -> r_mapped_fa (rg st cls) = 0 -> LUMPF <= provF st cls.
Proof.
  intros st cls WF Hc F0. unfold provF, fa_cap. rewrite F0. cbn [Z.div].
  pose proof (wc_alloc_nonneg st cls (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia))) as A0. pose proof (csize_pos cls ltac:(lia)).
  assert (0 <= ncarved st cls) by (unfold ncarved; apply Z.div_pos; lia). unfold FAPROV, LUMPF, LUMPU. lia.
Qed.

(* [comment removed for export] *)
Lemma WTOT_facts : forall st cls lo SP usz, RTWF st -> 1 <= cls <= 30 -> CEIL <= lo -> lo <= SP -> 0 <= usz <= 262144 -> r_mapped (rg st cls) + usz <= KFREEARRAY_OFF ->
  let U := rbeg st cls + r_mapped (rg st cls) in
  Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls))
  /\ (forall st', rbeg st' cls = rbeg st cls -> rinfo st' cls = rinfo st cls -> st_t st' = st_t st ->
      forall a iv, In iv (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)) -> fst iv <= a < snd iv ->
      (lo <= a < SP) \/ in_ivs (primary_fp_fine st cls ++ fp_emb st') a).
Proof.
  intros st cls lo SP usz WF Hc HCE HLS HU1 HU2. cbv zeta.
  (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
  pose proof (t_range st WF) as [T1 T2].
  assert (SHU : SH (rbeg st cls + r_mapped (rg st cls)) + 32768 <= SH (rbeg st cls + KREGIONSIZE) /\ SH (rbeg st cls + r_mapped (rg st cls)) <= SH (fabeg st cls)
                /\ SH (fabeg st cls) + 67108864 <= SH (rbeg st cls + KREGIONSIZE) /\ SH (rbeg st cls) + KREGIONSIZE / 8 = SH (rbeg st cls + KREGIONSIZE)
                /\ SH (rbeg st cls + KREGIONSIZE) <= KHIGHMEM_BEG).
  { rewrite C13. unfold SH, SHADOW_OFFSET, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. (nelimp (ris_range st WF) 3%nat; intros Z1 Z2 _). unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *.
    clear -C1 C3 C6 C7 C11 C12 Z2. Z.div_mod_to_equations. lia. }
  (nelim SHU 5%nat; intros S1 S2 S3 S4 S5).
  unfold WTOT, WPRE, WREST. unfold pcaddr, acache, T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  split.
  - apply Forall_forall. intros iv Hiv. unfold pz_ok. unfold T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL, KHIGHMEM_BEG, AIMG_HI.
    cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd]; split; try (intros HH; lia).
    + right; left; lia.
    + left; lia.
    + right; left; lia.
    + left; lia.
    + left; lia.
    + right; right; left; lia.
    + right; right; right; left; lia.
    + do 5 right; lia.
    + do 4 right; left; lia.
    + do 5 right; lia.
  - intros st' E1 E2 E3 a iv Hiv Hr. unfold primary_fp_fine, fp_class_fine, fp_tpage.
    cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Hr.
    + left. exact Hr.
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + left. exact Hr.
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + right. exists (rinfo st cls), (rinfo st cls + 128). split; [apply in_or_app; left; do 2 right; left; reflexivity| lia].
    + right. exists (rbeg st cls + r_mapped (rg st cls)), (rbeg st cls + 4294967296). split; [apply in_or_app; left; left; reflexivity| lia].
    + right. exists (SH (rbeg st cls + r_mapped (rg st cls))), (SH (rbeg st cls) + 4294967296 / 8). split; [apply in_or_app; left; right; left; reflexivity| lia].
    + right. exists (rbeg st cls + r_mapped (rg st cls)), (rbeg st cls + 4294967296). split; [apply in_or_app; left; left; reflexivity| rewrite C13 in Hr; lia].
    + right. exists (SH (rbeg st cls + r_mapped (rg st cls))), (SH (rbeg st cls) + 4294967296 / 8). split; [apply in_or_app; left; right; left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINF.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls : Z) (um : bool) (m m' : word -> option byte) (mo : Model) (G : list (Z * Z)) (R SP lo : Z) (jr je js : list byte).
Let st' := mkRT a1 a2 a3 (updz a4 cls (r_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um)) true a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Let r := rg st cls.
Let nf := num_freed st cls.
Let mapped := r_mapped r.
Let U := rbeg st cls + mapped.
Let usz := Z.min 262144 (3758096384 - mapped).
Let mapped' := mapped + (if um then 262144 else 0).
Let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo.
Let G1 := if um then (SH U, SH U + 32768) :: G else G.
Let R1 := R - (if um then LUMP else 0).
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).
Hypothesis HOK : LOK asegs mo.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HUM : um = true -> nf < nrefill cls /\ mapped < r_allocated r + (nrefill cls - nf) * csize cls /\ mapped + 262144 <= KFREEARRAY_OFF.
Hypothesis MI' : mem_inv asegs m'.
Hypothesis MU : munch (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis ST' : stk asegs m' lo SP.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis RIa : rw_cells asegs m' (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)].
Hypothesis RI24 : rw_cells asegs m' (rinfo st cls + 24) [C8 (Z_to_bv 64 (r_mapped_fa r))].
Hypothesis RIb : rw_cells asegs m' (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr;
                                                     C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js].
Hypothesis VUH : if um then stk asegs m' U (U + 262144) /\ rw_cells asegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis PCH : pch_at st cls m' 0.
Hypothesis PCO : pco_at st m'.
Hypothesis HRu : (if um then LUMP else 0) <= R.

Lemma Hcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma WX : wf_pd st. Proof. intros c Hc'. exact (RTWF_pd st c WF Hc'). Qed.
Lemma usz_ok : 0 <= usz <= 262144 /\ mapped + usz <= KFREEARRAY_OFF /\ (um = true -> usz = 262144).
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros _ _ _ _ _ C6 C7 _). pose proof HUM as HU. unfold usz, KFREEARRAY_OFF in *. fold r mapped in C6, C7.
  split; [lia|]. split; [lia|]. intros E. (nelim (HU E) 3%nat; intros _ _ X). lia.
Qed.
Lemma WT : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)).
Proof. (nelimp usz_ok 3%nat; intros U1 U2 _). exact (proj1 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2)). Qed.
Lemma WTz : Forall (pz_ok st cls) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)).
Proof. eapply Forall_impl; [| exact WT]. intros iv [H _]. exact H. Qed.

Theorem RTREP_finf : RTREP st' m'.
Proof.
  pose proof VUH as VU0. pose proof PCH as PCH0.
  eapply (RTREP_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); try exact WX; try exact WTz; try exact PCO; try eassumption.
  - (* [comment removed for export] *) exists jr, je, js. unfold rinfo_cells.
    rewrite (num_freed_all a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) by (first [exact WX| eassumption]).
    rewrite (rg_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) by (first [exact WX| eassumption]).
    cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_f]. change (rinfo st' cls) with (rinfo st cls).
    apply (rinfo_join3 m' (rinfo st cls)); [exact RIa| exact RI24| exact RIb| reflexivity| reflexivity].
  - (* [comment removed for export] *) intros E. rewrite E in VU0. destruct VU0 as [V1 V2]. split; [exact V1|]. apply CB_to_zcells_zrep; [lia| exact V2].
  - (* [comment removed for export] *) intros c Hc'. pose proof (PCH0 c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE]; [fold st; rewrite HC0; exact X| exact X].
Qed.
Theorem RTWF_finf : RTWF st'.
Proof. eapply (RTWF_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); try exact WX; eassumption. Qed.
Lemma U_facts : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ (um = true -> U + 262144 <= rbeg st cls + KFREEARRAY_OFF) /\ 2147450880 <= SH U /\ SH U + 32768 <= KHIGHMEM_BEG.
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros C1 C2 C3 C4 C5 C6 C7 _). pose proof HUM as HU. fold r mapped in C6, C7.
  unfold U, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KREGIONSIZE, CEIL, SH, SHADOW_OFFSET in *. (nelimp (ris_range st WF) 3%nat; intros _ Z2 _).
  split; [lia|]. split; [lia|]. split; [intros E; (nelim (HU E) 3%nat; intros _ _ X); lia|]. clear -C1 C3 C6 C7 Z2. Z.div_mod_to_equations. lia.
Qed.
Theorem RTMODEL_finf : RTMODEL st' mo1.
Proof.
  apply (RTMODEL_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  (nelimp U_facts 3%nat; intros U1 U2 _). unfold mo1. destruct um; [| exact HM]. apply (RTMODEL_commit mo U 262144 HOK ltac:(lia) st HM).
Qed.
Theorem GWIN_finf : GWIN st' m' mo1 (mkG G1 R1).
Proof.
  apply (GWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  (nelimp U_facts 5%nat; intros U1 U2 _ U4 U5). pose proof VUH as VU0. pose proof (GWIN_mem st m m' mo (mkG G R) HG HOK WM) as G0.
  unfold mo1, G1, R1. destruct um.
  - destruct VU0 as [V1 V2]. apply (GWIN_commit mo U 262144 HOK ltac:(lia) st m').
    apply (GWIN_addwin st m' mo G R). { exact G0. }
    pose proof (stk_of_rw_cells asegs m' _ _ V2) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
    apply (vis_bytes m' (SH U) (SH U + 32768) SV). unfold AIMG_HI. lia.
  - rewrite Z.sub_0_r. exact G0.
Qed.
Theorem FRONTR_finf : FRONTR mo1 R1.
Proof. unfold mo1, R1. destruct um; [apply FRONTR_commit; apply (FRONTR_le mo R); [exact HFR| unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact HFR]. Qed.
Theorem SWIN_finf : SWIN st' (mkG G1 R1).
Proof.
  apply (SWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  apply (SWIN_mono st (mkG G R)); [exact HSW|]. unfold G1. intros w Hw. cbn [g_win] in *. destruct um; [right; exact Hw| exact Hw].
Qed.
Theorem RTS_finf : RTS st' m' mo1 (mkG G1 R1).
Proof. exact (RTS_intro _ _ _ _ RTREP_finf RTWF_finf RTMODEL_finf GWIN_finf FRONTR_finf SWIN_finf). Qed.
Theorem gmono_finf : gmono (mkG G R) (mkG G1 R1).
Proof. unfold G1. intros w Hw. cbn [g_win] in *. destruct um; [right; exact Hw| exact Hw]. Qed.
Theorem budget_finf : budget_ok st (mkG G R) st' (mkG G1 R1) 0.
Proof.
  unfold budget_ok, R1. cbn [g_res].
  pose proof (rt_prov_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) as P0.
  assert (P : rt_prov st' + (if um then LUMPU else 0) <= rt_prov st) by (apply P0; first [exact WX| assumption]). clear P0.
  unfold LUMP, LUMPU in *. destruct um; lia.
Qed.
Theorem cli_pres_finf : cli_pres st SP m m'.
Proof. exact (cli_pres_pz st WF cls Hc SP (ltac:(lia)) _ m m' MU WM WT). Qed.
Theorem rt_frame_finf : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m'.
Proof.
  (nelimp usz_ok 3%nat; intros U1 U2 _).
  apply (rt_frame_pz SP _ m m' lo _ MU). exact (proj2 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2) st' eq_refl eq_refl eq_refl).
Qed.
Theorem rt_frame_finf' : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  eapply rt_frame_weaken; [| exact rt_frame_finf]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  (nelimp (cls_facts st WF cls Hc) 7%nat; intros _ _ _ _ _ C6 _). (nelim Ha 4%nat; intros l h Hin Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
Theorem rel_finf : refill_rel st st' cls 0.
Proof.
  split; [| split; [reflexivity| split; [reflexivity| split]]].
  - unfold same_but_primary. repeat match goal with |- _ /\ _ => split end; try reflexivity; [apply dtls_same_of_eq; reflexivity| apply loose0_ext_of_eq; reflexivity].
  - intros c Hc' NE. split; [| reflexivity]. apply (rg_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); first [exact NE| exact WX| assumption].
  - right. split; [reflexivity|]. exact HC0.
Qed.
End FINF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINS.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls Nv nm : Z) (um fm pop : bool) (m m' : word -> option byte) (mo : Model) (G : list (Z * Z)) (R SP lo : Z) (jr je js : list byte) (fa : list Z).
Let n := nrefill cls.
Let r := rg st cls.
Let S := csize cls.
Let nf := num_freed st cls.
Let alloc := r_allocated r.
Let mapped := r_mapped r.
Let fam := r_mapped_fa r.
Let mapped' := mapped + (if um then 262144 else 0).
Let fam' := if fm then nm else fam.
Let base := nf + Nv - n.
Let L := r_fa r ++ newc cls (ncarved st cls) Nv.
Let FA := fabeg st cls.
Let U := rbeg st cls + mapped.
Let Ufa := FA + fam.
Let D := FA + 4 * nf.
Let usz := Z.min 262144 (3758096384 - mapped).
Let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo.
Let G1 := if um then (SH U, SH U + 32768) :: G else G.
Let R1 := R - (if um then LUMP else 0).
Let mo2 := if fm then mm_commit (wz Ufa) (wz 262144) mo1 else mo1.
Let G2 := if fm then (SH Ufa, SH Ufa + 32768) :: G1 else G1.
Let R2 := R1 - (if fm then LUMP else 0).
Let st' := mkRT a1 a2 a3 (updz a4 cls (r_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop)) true
                (updz a6 cls (skipn (Z.to_nat base) L)) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).
Hypothesis HOK : LOK asegs mo.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HNv : 0 <= Nv /\ n <= nf + Nv.
Hypothesis HPOP : pop = true ->
  nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
  /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
  /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144.
Hypothesis HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false.
Hypothesis NVB : Nv <= 16385.
Hypothesis FAM0 : fm = true -> fam = 0 /\ nm = 262144.
Hypothesis MI' : mem_inv asegs m'.
Hypothesis MU : munch (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis ST' : stk asegs m' lo SP.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis RIa : rw_cells asegs m' (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 base)].
Hypothesis RI24 : rw_cells asegs m' (rinfo st cls + 24) [C8 (Z_to_bv 64 fam')].
Hypothesis RIb : rw_cells asegs m' (rinfo st cls + 32) [C8 (Z_to_bv 64 (alloc + Nv * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr;
                                                     C1 (Z_to_bv 8 (if pop then 0 else if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js].
Hypothesis VFA' : stk asegs m' FA (FA + fam').
Hypothesis FILL : u32arr asegs m' D (fill_vals alloc S (Z.to_nat Nv)).
Hypothesis VUH : if um then stk asegs m' U (U + 262144) /\ rw_cells asegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis VFH : if fm then rw_cells asegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis Hfa : length fa = Z.to_nat n /\ (forall i, 0 <= i < n -> nthz fa i 0 = nthz L (base + i) 0).
Hypothesis CHU : u32arr asegs m' (pcaddr st cls + 16) (wl fa).
Hypothesis PCH : pch_at st cls m' n.
Hypothesis PCO : pco_at st m'.
Hypothesis HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R.

Lemma SHcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma SWX : wf_pd st. Proof. intros c Hc'. exact (RTWF_pd st c WF Hc'). Qed.
Lemma SHn : n = nrefill cls. Proof. reflexivity. Qed.
Lemma NR : 1 <= n <= 8. Proof. exact (proj2 (nrefill_eq cls ltac:(lia))). Qed.
Lemma s_usz_ok : 0 <= usz <= 262144 /\ mapped + usz <= KFREEARRAY_OFF /\ (um = true -> usz = 262144).
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros _ _ _ _ _ C6 C7 _). pose proof HPOP as HP. pose proof HHAVE as HH. unfold usz, KFREEARRAY_OFF in *. fold r mapped in C6, C7.
  split; [lia|]. split; [lia|]. intros E. destruct pop; [(nelim (HP eq_refl) 5%nat; intros _ _ _ X _); pose proof (X E); lia| (nelim (HH eq_refl) 3%nat; intros _ X _); congruence].
Qed.
Lemma SWT : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf).
Proof. (nelimp s_usz_ok 3%nat; intros U1 U2 _). exact (proj1 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2)). Qed.
Lemma SWTz : Forall (pz_ok st cls) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf).
Proof. eapply Forall_impl; [| exact SWT]. intros iv [H _]. exact H. Qed.
Lemma SU_facts : KHIGHMEM_BEG <= U /\ (um = true -> U + 262144 <= rbeg st cls + KFREEARRAY_OFF) /\ 2147450880 <= SH U /\ SH U + 32768 <= KHIGHMEM_BEG
                 /\ KHIGHMEM_BEG <= FA /\ FA + 262144 <= CEIL /\ 2147450880 <= SH FA /\ SH FA + 32768 <= KHIGHMEM_BEG /\ rbeg st cls + KFREEARRAY_OFF = FA /\ FA + 262144 <= CEIL.
Proof.
  (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14). (nelimp s_usz_ok 3%nat; intros _ _ U3). fold r mapped in C6, C7. fold FA in C13.
  unfold U, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL, SH, SHADOW_OFFSET in *. (nelimp (ris_range st WF) 3%nat; intros _ Z2 _).
  split; [lia|]. split; [intros E; pose proof (U3 E); unfold usz in *; lia|]. clear -C1 C3 C6 C7 C13 Z2. Z.div_mod_to_equations. lia.
Qed.
Lemma zlen_cache' : zlen (cch st' cls) = n.
Proof.
  assert (E : cch st' cls = skipn (Z.to_nat base) L) by (apply (RTW_p_abs.cch_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact SWX| exact SHn| assumption]).
  rewrite E. unfold zlen. rewrite length_skipn.
  assert (LL : Z.of_nat (length L) = nf + Nv).
  { unfold L. rewrite length_app, Nat2Z.inj_add. pose proof (newc_length cls (ncarved st cls) Nv (proj1 HNv)) as NL. unfold zlen in NL. rewrite NL. reflexivity. }
  pose proof HNv as [H0 H1]. pose proof NR as NR'. unfold base in *.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  rewrite Nat2Z.inj_sub by lia. rewrite LL. rewrite Z2Nat.id by lia. lia.
Qed.

Theorem RTREP_fins : RTREP st' m'.
Proof.
  pose proof SHcls as HK. pose proof NR as NR0. pose proof VUH as VU0. pose proof VFH as VF0. pose proof PCH as PCH0. pose proof Hfa as [FL FN]. pose proof FAM0 as F0. pose proof HHAVE as HH. pose proof HPOP as HP.
  (nelimp SU_facts 10%nat; intros U1 U2 U3 U4 U5 U6 U7 U8 U9 U10). pose proof zlen_cache' as ZC.
  pose proof (wc_alloc_carved st cls (wf_class_ok st WF cls HK)) as EAL. fold r alloc in EAL. change (csize cls) with S in EAL.
  pose proof (csize_pos cls ltac:(lia)) as CP. change (csize cls) with S in CP.
  eapply (RTREP_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); try exact SWX; try exact SHn; try exact SWTz; try eassumption.
  - (* [comment removed for export] *) exists jr, je, js. unfold rinfo_cells.
    rewrite (num_freed_same' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact SWX| exact SHn| eassumption]).
    rewrite (RTW_p_abs.rg_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact SWX| exact SHn| eassumption]).
    cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_new]. change (rinfo st' cls) with (rinfo st cls).
    pose proof RIb as RIb0. destruct pop; cbv iota in RIb0; cbv iota;
      (apply (rinfo_join3 m' (rinfo st cls)); [exact RIa| exact RI24| exact RIb0| reflexivity| reflexivity]).
  - (* [comment removed for export] *) intros E. rewrite E in VU0. destruct VU0 as [V1 V2]. split; [exact V1|]. apply CB_to_zcells_zrep; [lia| exact V2].
  - (* [comment removed for export] *) split; [exact VFA'|]. change (if fm then nm else r_mapped_fa (rg st cls)) with fam'. unfold fam'. destruct fm.
    + destruct (F0 eq_refl) as [FZ ->]. change (262144 / 8) with 32768.
      pose proof (stk_of_rw_cells asegs m' _ _ VF0) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
      unfold Ufa in SV. rewrite FZ, Z.add_0_r in SV. exact SV.
    + (nelim (rr_regions st m HR cls HK) 5%nat; intros _ _ _ V4 _). eapply (stk_wmono_noseg m m'); [exact V4| exact WM| match goal with |- _ <= ?x => change x with (SH FA) end; unfold AIMG_HI; clear -U7; lia].
  - (* [comment removed for export] *) intros t Ht.
    match goal with |- rw_cells _ _ ?a _ => replace a with (D + 4 * t) by (unfold D, FA, nf, st; lia) end.
    assert (NC0 : 0 <= ncarved st cls) by (pose proof (wc_alloc_nonneg st cls (wf_class_ok st WF cls HK)) as A0; fold r alloc in A0; clear -A0 EAL CP; nia).
    match goal with |- rw_cells _ _ _ [W4 ?v] => replace v with ((alloc + Z.of_nat (Z.to_nat Nv - 1 - Z.to_nat t) * S) / 16) end.
    2:{ unfold chunk_cptr. change (csize cls) with S. change (ncarved _ cls) with (ncarved st cls). rewrite EAL.
        f_equal. rewrite <- Z.mul_add_distr_r. f_equal. clear -Ht NC0 HNv. lia. }
    eapply (cells_of_u32arr _ _ _ t); [exact FILL| apply fill_vals_nth; clear -Ht HNv; lia| clear -Ht; lia].
  - (* [comment removed for export] *) intros c Hc'. pose proof (PCH0 c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE].
    { match goal with |- rw_cells _ _ _ (W4 ?z :: _) => replace z with n by (first [exact ZC| symmetry; exact ZC]) end. exact X. }
    rewrite (RTW_p_abs.cch_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact NE| exact SWX| exact SHn| eassumption]). exact X.
  - (* [comment removed for export] *) intros i Hi.
    match goal with |- rw_cells _ _ _ [W4 ?v] => replace v with (nthz fa i 0) by (first [apply FN; exact Hi| symmetry; apply FN; exact Hi]) end.
    change (pcaddr _ cls) with (pcaddr st cls).
    eapply (cells_of_u32arr _ _ _ i); [exact CHU| | clear -Hi; lia]. rewrite nth_error_wl by (rewrite FL; clear -Hi NR0; lia).
    unfold nthz. destruct (Z.ltb_spec0 i 0); [lia| reflexivity].
  - (* [comment removed for export] *) intros c i Hc' NE Hi. exact (PCO c i Hc' Hi).
Qed.
Theorem RTWF_fins : RTWF st'.
Proof. eapply (RTWF_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); try exact SWX; try exact SHn; eassumption. Qed.
Lemma LOK1 : LOK asegs mo1. Proof. unfold mo1. destruct um; [apply mm_commit_LOK; exact HOK| exact HOK]. Qed.
Theorem RTMODEL_fins : RTMODEL st' mo2.
Proof.
  apply (RTMODEL_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). (nelimp SU_facts 7%nat; intros U1 U2 U3 U4 U5 U6 _). pose proof FAM0 as F0. pose proof LOK1 as LK1.
  assert (M1 : RTMODEL st mo1).
  { unfold mo1. destruct um; [| exact HM].
    assert (UC : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ 0 < 262144).
    { (nelimp (cls_facts st WF cls Hc) 6%nat; intros _ _ C3 C4 C5 _). specialize (U2 eq_refl). unfold CEIL, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI in *. clear -U1 U2 C3 C4 C5. lia. }
    exact (RTMODEL_commit mo U 262144 HOK UC st HM). }
  unfold mo2. destruct fm; [| exact M1]. destruct (F0 eq_refl) as [FZ _]. unfold Ufa. rewrite FZ, Z.add_0_r.
  apply (RTMODEL_commit mo1 FA 262144 LK1 ltac:(clear -U5 U6; lia) st M1).
Qed.
Theorem GWIN_fins : GWIN st' m' mo2 (mkG G2 R2).
Proof.
  apply (GWIN_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). (nelimp SU_facts 9%nat; intros U1 U2 U3 U4 U5 U6 U7 U8 _). pose proof VUH as VU0. pose proof VFH as VF0. pose proof FAM0 as F0. pose proof LOK1 as LK1.
  pose proof (GWIN_mem st m m' mo (mkG G R) HG HOK WM) as G0.
  assert (GW1 : GWIN st m' mo1 (mkG G1 R1)).
  { unfold mo1, G1, R1. destruct um.
    - destruct VU0 as [V1 V2].
      assert (UC : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ 0 < 262144).
      { (nelimp (cls_facts st WF cls Hc) 6%nat; intros _ _ C3 C4 C5 _). specialize (U2 eq_refl). unfold CEIL, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI in *. clear -U1 U2 C3 C4 C5. lia. }
      apply (GWIN_commit mo U 262144 HOK UC st m').
      apply (GWIN_addwin st m' mo G R). { exact G0. }
      pose proof (stk_of_rw_cells asegs m' _ _ V2) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
      apply (vis_bytes m' (SH U) (SH U + 32768) SV). unfold AIMG_HI, KHIGHMEM_BEG in *. lia.
    - rewrite Z.sub_0_r. exact G0. }
  unfold mo2, G2, R2. destruct fm.
  - destruct (F0 eq_refl) as [FZ _]. apply (GWIN_commit mo1 Ufa 262144 LK1 ltac:(unfold Ufa; rewrite FZ, Z.add_0_r; clear -U5 U6; lia) st m').
    apply (GWIN_addwin st m' mo1 G1 R1). { exact GW1. }
    pose proof (stk_of_rw_cells asegs m' _ _ VF0) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
    apply (vis_bytes m' (SH Ufa) (SH Ufa + 32768) SV). unfold Ufa. rewrite FZ, Z.add_0_r. unfold AIMG_HI, KHIGHMEM_BEG in *. lia.
  - rewrite Z.sub_0_r. exact GW1.
Qed.
Theorem FRONTR_fins : FRONTR mo2 R2.
Proof.
  unfold mo2, R2, mo1, R1. assert (F1 : FRONTR (if um then mm_commit (wz U) (wz 262144) mo else mo) (R - (if um then LUMP else 0))).
  { generalize HRR. destruct um; intros HRR'; [apply FRONTR_commit; apply (FRONTR_le mo R); [exact HFR| revert HRR'; destruct fm; intros HRR'; unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact HFR]. }
  generalize HRR. destruct fm; intros HRR'; [apply FRONTR_commit; eapply FRONTR_le; [exact F1| revert HRR'; destruct um; intros HRR'; unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact F1].
Qed.
Theorem gmono_fins : gmono (mkG G R) (mkG G2 R2).
Proof. unfold G2, G1. intros w Hw. cbn [g_win] in *. destruct fm; destruct um; cbn; tauto. Qed.
Theorem SWIN_fins : SWIN st' (mkG G2 R2).
Proof. apply (SWIN_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). apply (SWIN_mono st (mkG G R)); [exact HSW| exact gmono_fins]. Qed.
Theorem RTS_fins : RTS st' m' mo2 (mkG G2 R2).
Proof. exact (RTS_intro _ _ _ _ RTREP_fins RTWF_fins RTMODEL_fins GWIN_fins FRONTR_fins SWIN_fins). Qed.
Theorem budget_fins : budget_ok st (mkG G R) st' (mkG G2 R2) 0.
Proof.
  unfold budget_ok, R2, R1. cbn [g_res].
  pose proof (rt_prov_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) as P0.
  assert (P : rt_prov st' + (if um then LUMPU else 0) + (if fm then LUMPF else 0) <= rt_prov st) by (apply P0; first [exact SWX| exact SHn| assumption]). clear P0.
  unfold LUMP, LUMPU, LUMPF, LUMPU in *. destruct um; destruct fm; lia.
Qed.
Theorem cli_pres_fins : cli_pres st SP m m'.
Proof. exact (cli_pres_pz st WF cls Hc SP (ltac:(lia)) _ m m' MU WM SWT). Qed.
Theorem rt_frame_fins : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m'.
Proof.
  (nelimp s_usz_ok 3%nat; intros U1 U2 _).
  apply (rt_frame_pz SP _ m m' lo _ MU). exact (proj2 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2) st' eq_refl eq_refl eq_refl).
Qed.
Theorem rt_frame_fins' : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  eapply rt_frame_weaken; [| exact rt_frame_fins]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  (nelimp (cls_facts st WF cls Hc) 7%nat; intros _ _ _ _ _ C6 _). (nelim Ha 4%nat; intros l h Hin Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
Theorem rel_fins : refill_rel st st' cls 1.
Proof.
  split; [| split; [reflexivity| split; [reflexivity| split]]].
  - unfold same_but_primary. repeat match goal with |- _ /\ _ => split end; try reflexivity; [apply dtls_same_of_eq; reflexivity| apply loose0_ext_of_eq; reflexivity].
  - intros c Hc' NE. split.
    + apply (RTW_p_abs.rg_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact NE| exact SWX| exact SHn| assumption].
    + apply (RTW_p_abs.cch_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact NE| exact SWX| exact SHn| assumption].
  - left. split; [reflexivity|]. exact zlen_cache'.
Qed.
End FINS.



End CeilWrap.
(* [comment removed for export] *)
Ltac dj := cbn; repeat match goal with |- _ /\ _ => split end; try exact I; first [left; lia | right; lia | lia].
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| lia] end ].
