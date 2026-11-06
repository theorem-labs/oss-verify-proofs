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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_p_absf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.
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
Hypothesis WM : wmono bsegs m m'.
Hypothesis HW : Forall (pz_ok st cls) W.
Let rb := rbeg st cls.
Let fb := fabeg st cls.
Let alloc := r_allocated r.
Let mapped := r_mapped r.
Let mapped' := r_mapped r + (if um then 262144 else 0).
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells bsegs m' (rinfo st cls) (rinfo_cells st' cls jr je js).
(* [comment removed for export] *)
Hypothesis VU : um = true -> vis m' (rb + mapped) (rb + mapped + 262144) /\ rw_cells bsegs m' (SH (rb + mapped)) (zcells (zrep SV_HEAP_LEFT_RZ 32768)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m' (pcaddr st c) [W4 (zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Hypothesis PCO : forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

Lemma RF : KHIGHMEM_BEG <= rb /\ rb mod 8 = 0 /\ alloc mod 8 = 0 /\ mapped mod 8 = 0 /\ 0 <= alloc <= mapped /\ mapped <= KFREEARRAY_OFF /\ rb + KREGIONSIZE <= CEIL.
Proof.
  pose proof (region_facts st WF cls Hcls) as X. cbn zeta in X. destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold rb, alloc, mapped, r. unfold CEIL. repeat split; try lia; assumption.
Qed.

Lemma tail_shadow_f : rw_cells bsegs m' (SH (rb + alloc)) (zcells (zrep SV_HEAP_LEFT_RZ ((mapped' - alloc) / 8))).
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
      destruct (stk_split bsegs m (ris st) (rinfo st cls) (ris st + 4096) VR ltac:(rewrite RL; lia)) as [VA VB].
      destruct (stk_split bsegs m (rinfo st cls) (rinfo st cls + 128) (ris st + 4096) VB ltac:(rewrite RL; lia)) as [_ VC].
      apply (stk_merge bsegs m' _ (rinfo st cls)); [| | rewrite RL; lia].
      - eapply stk_transport_disjoint; [exact VA| exact MU| exact WM|].
        pose proof (cls_facts st WF cls Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
        apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia.
      - apply (stk_merge bsegs m' _ (rinfo st cls + 128)); [| | rewrite RL; lia].
        + pose proof (stk_of_rw_cells bsegs m' _ _ RC0) as SR. rewrite E128 in SR. exact SR.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Module RTW_cd_abs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_refillw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma ck_eqb_eq' : forall u v, ck_eqb u v = true <-> u = v.
Proof.
  intros [a b] [c d]. unfold ck_eqb. cbn [fst snd]. rewrite andb_true_iff, !Z.eqb_eq. split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.
Lemma apend_filter_remove_same : forall (l : list (Z * Z)) c k, In (c, k) l ->
  Permutation (map snd (List.filter (fun ck => fst ck =? c) l)) (k :: map snd (List.filter (fun ck => fst ck =? c) (remove_first ck_eqb (c, k) l))).
Proof.
  induction l as [|[c' k'] l IH]; intros c k HIN; [destruct HIN|].
  cbn [remove_first]. destruct (ck_eqb (c, k) (c', k')) eqn:E.
  - apply ck_eqb_eq' in E. injection E as E1 E2. subst c' k'. cbn [List.filter map fst snd]. rewrite Z.eqb_refl. cbn [map snd]. apply Permutation_refl.
  - assert (HIN' : In (c, k) l).
    { destruct HIN as [H|H]; [| exact H]. exfalso. symmetry in H. apply (proj2 (ck_eqb_eq' _ _)) in H. rewrite H in E. discriminate. }
    cbn [List.filter map fst snd]. destruct (c' =? c); cbn [map snd]; [| exact (IH c k HIN')].
    apply (Permutation_trans (perm_skip k' (IH c k HIN'))). apply perm_swap.
Qed.
Lemma apend_filter_remove_other : forall (l : list (Z * Z)) c k c', c' <> c ->
  List.filter (fun ck => fst ck =? c') (remove_first ck_eqb (c, k) l) = List.filter (fun ck => fst ck =? c') l.
Proof.
  induction l as [|[c1 k1] l IH]; intros c k c' NE; [reflexivity|].
  cbn [remove_first]. destruct (ck_eqb (c, k) (c1, k1)) eqn:E.
  - apply ck_eqb_eq' in E. injection E as E1 E2. subst c1 k1. cbn [List.filter fst]. destruct (Z.eqb_spec c c'); [lia| reflexivity].
  - cbn [List.filter fst]. destruct (c1 =? c'); [f_equal|]; apply IH; exact NE.
Qed.
Lemma remove_first_sub : forall (l : list (Z * Z)) x y, In y (remove_first ck_eqb x l) -> In y l.
Proof.
  induction l as [|z l IH]; intros x y H; [destruct H|]. cbn [remove_first] in H.
  destruct (ck_eqb x z); [right; exact H|]. destruct H as [->|H]; [left; reflexivity| right; exact (IH x y H)].
Qed.
Lemma remove_first_length : forall (l : list (Z * Z)) x, In x l -> length l = S (length (remove_first ck_eqb x l)).
Proof.
  induction l as [|z l IH]; intros x H; [destruct H|]. cbn [remove_first].
  destruct (ck_eqb x z) eqn:E; [reflexivity|]. destruct H as [->|H]; [rewrite (proj2 (ck_eqb_eq' x x) eq_refl) in E; discriminate|].
  cbn [length]. rewrite (IH x H). reflexivity.
Qed.

Lemma nthz_In : forall (l : list Z) i d, 0 <= i < zlen l -> In (nthz l i d) l.
Proof. intros l i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. apply nth_In. lia. Qed.

Lemma cd_zsum_map_le : forall (f g : Z -> Z) l d x, (forall y, In y l -> y <> x -> f y = g y) -> f x + d <= g x ->
  List.NoDup l -> In x l -> zsum (map f l) + d <= zsum (map g l).
Proof.
  intros f g l d x Hfg Hx ND IN. induction l as [|y l IH]; [destruct IN|].
  inversion ND as [|y' l' Hni ND']; subst. cbn [map]. rewrite !zsum_cons.
  destruct (Z.eq_dec y x) as [->|NE].
  - rewrite (zsum_map_ext f g l); [lia|]. intros z Hz. apply Hfg; [right; exact Hz|]. intros ->. exact (Hni Hz).
  - rewrite (Hfg y ltac:(left; reflexivity) NE). destruct IN as [E|IN]; [exfalso; exact (NE E)|].
    specialize (IH ltac:(intros w Hw Hne; apply Hfg; [right; exact Hw| exact Hne]) ND' IN). lia.
Qed.

(* [comment removed for export] *)
Section CDT.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls k : Z) (dr fm : bool).
Let r := rg st cls.
Let C := cch st cls.
Let cnt := zlen C.
Let n := nrefill cls.
Let nf := num_freed st cls.
Let fam := r_mapped_fa r.
Definition cd_base : Z := if dr then cnt - n else cnt.
Let base := cd_base.
Let drained := skipn (Z.to_nat base) C.
Let nm := fam + 262144.
Definition cd_rnew : region_st :=
  mkRegion (r_allocated r) (r_mapped r) (if fm then nm else fam) (r_exhausted r) (r_fa r ++ drained).
Let cache' := firstn (Z.to_nat base) C ++ [k].
Let st' := mkRT a1 a2 a3 (updz a4 cls cd_rnew) true (updz a6 cls cache') a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
                (remove_first ck_eqb (cls, k) b1) b2 b3 b4 b5.

Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HIN : In (cls, k) b1.
Hypothesis HDR : dr = true -> cnt = cmaxcount cls /\ fm = (fam <? 4 * (nf + n)).
Hypothesis HND : dr = false -> cnt <> cmaxcount cls /\ fm = false.

Lemma Hcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma WC : wf_class st cls. Proof. exact (wf_class_ok st WF cls Hcls). Qed.
Lemma Er : r = rg st cls. Proof. reflexivity. Qed.
Lemma Enf : nf = zlen (r_fa r). Proof. reflexivity. Qed.
Lemma len_regions : length a4 = 32%nat. Proof. exact (wb_len_regions st (wf_base_ok st WF)). Qed.
Lemma len_cache : length a6 = 32%nat. Proof. exact (wb_len_cache st (wf_base_ok st WF)). Qed.
Lemma nrange : 1 <= n <= 8 /\ cmaxcount cls = 2 * n.
Proof. pose proof (cmaxcount_range cls ltac:(lia)) as [A B]. unfold n. rewrite B. unfold nrefill. lia. Qed.
Lemma cnt_range : 0 <= cnt <= cmaxcount cls.
Proof. split; [apply zlen_nonneg| exact (wc_cache_max st cls WC)]. Qed.
Lemma base_range : 0 <= base <= cnt /\ base + 1 <= cmaxcount cls /\ (dr = true -> base = cnt - n) /\ (dr = false -> base = cnt).
Proof.
  pose proof nrange as [N1 N2]. pose proof cnt_range as [C1 C2]. unfold base, cd_base.
  destruct dr; [destruct (HDR eq_refl) as [E _]| destruct (HND eq_refl) as [E _]]; repeat split; try lia; intros; try discriminate; reflexivity.
Qed.
Lemma C_split : C = firstn (Z.to_nat base) C ++ drained.
Proof. unfold drained. symmetry. apply firstn_skipn. Qed.
Lemma drained_len : zlen drained = cnt - base.
Proof. unfold drained, zlen. rewrite length_skipn. pose proof base_range as (B & _). unfold cnt, zlen in *. lia. Qed.
Lemma firstn_len : zlen (firstn (Z.to_nat base) C) = base.
Proof. unfold zlen. rewrite length_firstn. pose proof base_range as (B & _). unfold cnt, zlen in *. lia. Qed.

(* [comment removed for export] *)
Lemma rg_same : rg st' cls = cd_rnew.
Proof. unfold rg. cbn [st_regions st']. apply nthz_updz_same. unfold zlen. rewrite len_regions. unfold KNUMCLASSES in *. lia. Qed.
Lemma rg_other : forall c, c <> cls -> rg st' c = rg st c.
Proof. intros c H. unfold rg. cbn [st_regions st st']. apply nthz_updz_other. lia. Qed.
Lemma cch_same : cch st' cls = cache'.
Proof. unfold cch. cbn [st_cache st']. apply nthz_updz_same. unfold zlen. rewrite len_cache. unfold KNUMCLASSES in *. lia. Qed.
Lemma cch_other : forall c, c <> cls -> cch st' c = cch st c.
Proof. intros c H. unfold cch. cbn [st_cache st st']. apply nthz_updz_other. lia. Qed.
Lemma rbeg_same : forall c, rbeg st' c = rbeg st c. Proof. reflexivity. Qed.
Lemma fabeg_same : forall c, fabeg st' c = fabeg st c. Proof. reflexivity. Qed.
Lemma rinfo_same : forall c, rinfo st' c = rinfo st c. Proof. reflexivity. Qed.
Lemma cptr_addr_same : forall c j, cptr_addr st' c j = cptr_addr st c j. Proof. reflexivity. Qed.
Lemma pcaddr_same : forall c, pcaddr st' c = pcaddr st c. Proof. reflexivity. Qed.
Lemma all_blocks_same : all_blocks st' = all_blocks st. Proof. reflexivity. Qed.
Lemma live_same : forall c, live_cptrs st' c = live_cptrs st c. Proof. reflexivity. Qed.
Lemma quar_same : forall c, quar_cptrs st' c = quar_cptrs st c. Proof. reflexivity. Qed.
Lemma qpend_same : forall c, qpend_cptrs st' c = qpend_cptrs st c. Proof. reflexivity. Qed.
Lemma batch_same : forall c, batch_cptrs st' c = batch_cptrs st c. Proof. reflexivity. Qed.
Lemma apend_perm : Permutation (apend_cptrs st cls) (k :: apend_cptrs st' cls).
Proof. unfold apend_cptrs. cbn [st_apend st st']. apply apend_filter_remove_same. exact HIN. Qed.
Lemma apend_other : forall c, c <> cls -> apend_cptrs st' c = apend_cptrs st c.
Proof. intros c H. unfold apend_cptrs. cbn [st_apend st st']. rewrite apend_filter_remove_other by exact H. reflexivity. Qed.
Lemma apend_sub : forall c j, In j (apend_cptrs st' c) -> In j (apend_cptrs st c).
Proof.
  intros c j H. destruct (Z.eq_dec c cls) as [->|NE]; [| rewrite apend_other in H by exact NE; exact H].
  eapply Permutation_in; [apply Permutation_sym; exact apend_perm| right; exact H].
Qed.
Lemma ncarved_same : forall c, ncarved st' c = ncarved st c.
Proof. intros c. unfold ncarved. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite rg_same; reflexivity| rewrite rg_other by exact NE; reflexivity]. Qed.
Lemma carved_same : forall c j, carved_cptr st' c j <-> carved_cptr st c j.
Proof. intros c j. unfold carved_cptr. rewrite ncarved_same. reflexivity. Qed.
Lemma num_freed_same' : num_freed st' cls = nf + (cnt - base).
Proof. unfold num_freed. rewrite rg_same. cbn [r_fa cd_rnew]. rewrite zlen_app, drained_len, <- Enf. reflexivity. Qed.
Lemma num_freed_other : forall c, c <> cls -> num_freed st' c = num_freed st c.
Proof. intros c H. unfold num_freed. rewrite rg_other by exact H. reflexivity. Qed.
Lemma avail_same' : avail_cptrs st' cls = (r_fa r ++ drained) ++ (firstn (Z.to_nat base) C ++ [k]).
Proof. unfold avail_cptrs. rewrite rg_same, cch_same. reflexivity. Qed.
Lemma avail_other : forall c, c <> cls -> avail_cptrs st' c = avail_cptrs st c.
Proof. intros c H. unfold avail_cptrs. rewrite rg_other, cch_other by exact H. reflexivity. Qed.
Lemma avail_perm : Permutation (avail_cptrs st' cls) (k :: avail_cptrs st cls).
Proof.
  rewrite avail_same'. unfold avail_cptrs. fold r C.
  assert (E : r_fa r ++ C = r_fa r ++ firstn (Z.to_nat base) C ++ drained) by (rewrite <- C_split; reflexivity). rewrite E.
  apply Permutation_sym. rewrite <- app_assoc.
  apply (Permutation_trans (perm_skip k (Permutation_app_head (r_fa r) (Permutation_app_comm (firstn (Z.to_nat base) C) drained)))).
  rewrite <- ?app_assoc.
  replace (r_fa r ++ drained ++ firstn (Z.to_nat base) C ++ [k]) with ((r_fa r ++ drained ++ firstn (Z.to_nat base) C) ++ [k]) by (rewrite <- ?app_assoc; reflexivity).
  apply Permutation_cons_append.
Qed.
Lemma perm_move : forall (A1 A1' M P P' : list Z) x, Permutation A1' (x :: A1) -> Permutation P (x :: P') ->
  Permutation (A1' ++ M ++ P') (A1 ++ M ++ P).
Proof.
  intros A1 A1' M P P' x H1 H2.
  apply (Permutation_trans (Permutation_app H1 (Permutation_refl (M ++ P')))). cbn [app].
  apply Permutation_sym. apply (Permutation_trans (Permutation_app_head A1 (Permutation_app_head M H2))).
  rewrite (app_assoc A1 M (x :: P')), (app_assoc A1 M P'). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma used_perm : Permutation (used_cptrs st' cls) (used_cptrs st cls).
Proof.
  unfold used_cptrs. rewrite live_same, quar_same, qpend_same, batch_same.
  replace (live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls ++ apend_cptrs st' cls)
    with ((live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls) ++ apend_cptrs st' cls) by (rewrite <- ?app_assoc; reflexivity).
  replace (live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls ++ apend_cptrs st cls)
    with ((live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls) ++ apend_cptrs st cls) by (rewrite <- ?app_assoc; reflexivity).
  apply (perm_move _ _ _ _ _ k); [exact avail_perm| exact apend_perm].
Qed.
Lemma used_other : forall c, c <> cls -> used_cptrs st' c = used_cptrs st c.
Proof. intros c H. unfold used_cptrs. rewrite avail_other, apend_other by exact H. reflexivity. Qed.
Lemma navail_same' : navail st' cls = navail st cls + 1.
Proof. unfold navail, zlen. rewrite (Permutation_length avail_perm). cbn [length]. lia. Qed.
Lemma navail_other : forall c, c <> cls -> navail st' c = navail st c.
Proof. intros c H. unfold navail. rewrite avail_other by exact H. reflexivity. Qed.
Lemma nexh_same : nexh st' = nexh st.
Proof.
  unfold nexh. cbn [st_regions st st']. rewrite count_exh_updz by (unfold zlen; rewrite len_regions; unfold KNUMCLASSES in *; lia).
  cbn [r_exhausted cd_rnew]. replace (nthz a4 cls region0) with r by reflexivity. lia.
Qed.
Lemma k_avail : In k (avail_cptrs st' cls).
Proof. rewrite avail_same'. apply in_or_app. right. apply in_or_app. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nf_cnt_le : nf + cnt <= ncarved st cls /\ 4 * ncarved st cls < 2^29.
Proof.
  pose proof (wc_used_all st cls WC) as UA. pose proof (wc_alloc_carved st cls WC) as AC. pose proof (wc_alloc_mapped st cls WC) as AM.
  pose proof (wc_mapped_max st cls WC) as MM. pose proof (csize_pos cls ltac:(lia)) as SP.
  assert (L : nf + cnt <= zlen (used_cptrs st cls)).
  { unfold used_cptrs, avail_cptrs. rewrite !zlen_app. fold r C. rewrite <- Enf. fold cnt.
    pose proof (zlen_nonneg (live_cptrs st cls)). pose proof (zlen_nonneg (quar_cptrs st cls)). pose proof (zlen_nonneg (qpend_cptrs st cls)).
    pose proof (zlen_nonneg (batch_cptrs st cls)). pose proof (zlen_nonneg (apend_cptrs st cls)). lia. }
  rewrite UA in L. split; [exact L|].
  assert (0 <= ncarved st cls) by (unfold ncarved; apply Z.div_pos; [exact (wc_alloc_nonneg st cls WC)| lia]).
  unfold KFREEARRAY_OFF in MM. rewrite <- Er in *. nia.
Qed.

Lemma RTWF_new : RTWF st'.
Proof.
  pose proof (wf_base_ok st WF) as WB. pose proof nrange as [NR1 NR2]. pose proof base_range as (B1 & B2 & B3 & B4). pose proof cnt_range as [CR1 CR2].
  pose proof (wc_num_freed st cls WC) as NF. pose proof (wc_fa_nonneg st cls WC) as F0. pose proof (wc_fa_align st cls WC) as FA. pose proof (wc_fa_max st cls WC) as FM.
  unfold num_freed in NF. rewrite <- Er, <- Enf in NF. rewrite <- Er in F0, FA, FM. fold fam in NF, F0, FA, FM.
  pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0. pose proof nf_cnt_le as [NC1 NC2].
  constructor.
  - destruct WB; constructor; try assumption.
    + cbn [st_regions st']. rewrite updz_length. assumption.
    + cbn [st_cache st']. rewrite updz_length. assumption.
    + split; [rewrite rg_other by lia; apply (proj1 wb_class0)| rewrite cch_other by lia; apply (proj2 wb_class0)].
    + intros Hu. exfalso. cbn in Hu. discriminate.
    + change (emb_sz st') with (emb_sz st). rewrite nexh_same. exact wb_emb_sz.
  - intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE].
    + destruct WC; constructor; rewrite ?rg_same, ?ncarved_same, ?cch_same, ?num_freed_same'; cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa cd_rnew]; rewrite <- ?Er; try assumption.
      * destruct fm; [unfold nm; lia| exact F0].
      * destruct fm; [| exact FA]. unfold nm. rewrite Z.add_mod, FA by lia. reflexivity.
      * destruct fm; [| exact FM]. unfold nm, KFREEARRAY_SIZE.
        destruct dr; [| destruct (HND eq_refl) as [_ E]; discriminate]. destruct (HDR eq_refl) as [E1 E2]. symmetry in E2. apply Z.ltb_lt in E2.
        change (2^18) with 262144 in FA. assert (fam < 536870912) by (clear -E2 NC1 NC2 NF0 NR1 NR2 E1; lia). clear -FA H. Z.div_mod_to_equations. lia.
      * (* [comment removed for export] *) destruct dr.
        -- destruct (HDR eq_refl) as [E1 E2]. rewrite (B3 eq_refl). replace (nf + (cnt - (cnt - n))) with (nf + n) by lia.
           destruct fm; [unfold nm; lia|]. symmetry in E2. apply Z.ltb_ge in E2. exact E2.
        -- destruct (HND eq_refl) as [_ ->]. rewrite (B4 eq_refl). lia.
      * unfold zlen. unfold cache'. rewrite length_app, length_firstn. cbn [length]. unfold cnt, zlen in *. lia.
      * intros j Hj. apply carved_same. apply wc_used_carved. eapply Permutation_in; [exact used_perm| exact Hj].
      * eapply Permutation_NoDup; [apply Permutation_sym; exact used_perm| exact wc_used_nodup].
      * unfold zlen in *. rewrite (Permutation_length used_perm). exact wc_used_all.
    + destruct (wf_class_ok st WF c Hc'); constructor; rewrite ?rg_other, ?ncarved_same, ?cch_other, ?used_other, ?num_freed_other by exact NE; try assumption.
      intros j Hj. apply carved_same. apply wc_used_carved. exact Hj.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    + intros b Hb. destruct (wq_batch b Hb) as [Cb (j & CK & E)]. split; [exact Cb| exists j; split; [apply carved_same; exact CK| exact E]].
    + cbn [st_apend st']. split; [| exact (proj2 wq_inflight)]. pose proof (proj1 wq_inflight) as L. cbn [st_apend] in L. unfold zlen in *.
      change (st_apend st) with b1 in L. rewrite (remove_first_length b1 (cls, k) HIN) in L. lia.
    + cbn [st_apend st']. intros ck Hck. apply wq_apend. cbn [st_apend]. exact (remove_first_sub _ _ _ Hck).
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma provU_le : provU st' cls <= provU st cls.
Proof.
  unfold provU, delta. rewrite rg_same, navail_same'. cbn [r_allocated r_mapped cd_rnew]. rewrite <- Er.
  pose proof (csize_pos cls ltac:(lia)). pose proof (zlen_nonneg (avail_cptrs st cls)) as A0. unfold navail. lia.
Qed.
Lemma provF_le : provF st' cls + (if fm then LUMPF else 0) <= provF st cls.
Proof.
  unfold provF, fa_cap. rewrite rg_same, ncarved_same. cbn [r_mapped_fa cd_rnew]. rewrite <- Er. fold fam.
  pose proof nf_cnt_le as [NC1 NC2]. pose proof nrange as [NR1 NR2]. pose proof base_range as (B1 & B2 & B3 & B4).
  pose proof (wc_fa_align st cls WC) as FA. rewrite <- Er in FA. fold fam in FA. change (2^18) with 262144 in FA.
  pose proof (wc_fa_nonneg st cls WC) as F0. rewrite <- Er in F0. fold fam in F0.
  destruct fm; [| lia].
  destruct dr; [| destruct (HND eq_refl) as [_ E]; discriminate]. destruct (HDR eq_refl) as [E1 E2]. symmetry in E2. apply Z.ltb_lt in E2.
  assert (LT : fam / 4 < ncarved st cls) by (assert (fam < 4 * (nf + cnt)) by (clear -E2 E1 NR1 NR2; lia); clear -H NC1 F0; Z.div_mod_to_equations; lia).
  unfold nm, LUMPF, LUMPU, FAPROV. replace ((fam + 262144) / 4) with (fam / 4 + 65536) by (clear -FA F0; Z.div_mod_to_equations; lia).
  clear -LT. lia.
Qed.
Lemma provU_other : forall c, c <> cls -> provU st' c = provU st c.
Proof. intros c H. unfold provU, delta. rewrite rg_other, navail_other by exact H. reflexivity. Qed.
Lemma provF_other : forall c, c <> cls -> provF st' c = provF st c.
Proof. intros c H. unfold provF, fa_cap. rewrite rg_other, ncarved_same by exact H. reflexivity. Qed.
Lemma prov_classes_new : prov_classes st' + (if fm then LUMPF else 0) <= prov_classes st.
Proof.
  unfold prov_classes.
  apply (cd_zsum_map_le (fun c => provU st' c + provF st' c) (fun c => provU st c + provF st c) classes _ cls).
  - intros y Hy Hne. rewrite provU_other, provF_other by exact Hne. reflexivity.
  - pose proof provU_le. pose proof provF_le. lia.
  - apply classes_nodup.
  - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
Qed.
Lemma rt_prov_new : rt_prov st' + (if fm then LUMPF else 0) <= rt_prov st.
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
  unfold rt_prov. rewrite E2, E3, E4, E5, E6, E7, E8, E9, E10. pose proof prov_classes_new. lia.
Qed.

(* [comment removed for export] *)
Lemma cd_rel : cdealloc_rel st st' cls k.
Proof.
  split; [| split; [reflexivity| split; [reflexivity| split; [| exact k_avail]]]].
  - unfold same_but_primary. repeat (split; [reflexivity|]).
    repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; try reflexivity.
    + apply dtls_same_of_eq. reflexivity.
    + apply loose0_ext_of_eq. reflexivity.
  - intros c Hc' NE. split; [apply rg_other; exact NE| apply cch_other; exact NE].
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_new : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_new : forall m mo g, GWIN st m mo g -> GWIN st' m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_new : forall g, SWIN st g -> SWIN st' g.
Proof. intros g H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variables (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis HR : RTREP st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis HW : Forall (pz_ok st cls) W.
Let fb := fabeg st cls.
Let fam' := if fm then nm else fam.
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells bsegs m' (rinfo st cls) (rinfo_cells st' cls jr je js).
(* [comment removed for export] *)
Hypothesis VF : vis m' fb (fb + fam') /\ vis m' (SH fb) (SH fb + fam' / 8).
(* [comment removed for export] *)
Hypothesis FILL : forall t, 0 <= t < cnt - base -> rw_cells bsegs m' (fb + 4 * (nf + t)) [W4 (nthz drained t 0)].
(* [comment removed for export] *)
Hypothesis PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m' (pcaddr st c) [W4 (zlen (cch st' c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Hypothesis PCE : forall i, 0 <= i <= base -> rw_cells bsegs m' (pcaddr st cls + 16 + 4 * i) [W4 (nthz cache' i 0)].
Hypothesis PCO : forall c i, 0 <= c < KNUMCLASSES -> c <> cls -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

Lemma RTREP_new : RTREP st' m'.
Proof.
  pose proof nrange as [NR1 NR2]. pose proof base_range as (B1 & B2 & B3 & B4). pose proof cnt_range as [CR1 CR2].
  destruct (pz_others st WF cls Hc W HW m m' MU WM HR) as (Y1 & Y2 & Y3 & Y5 & Y6 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16).
  pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0.
  constructor.
  - exact Y1.
  - exact Y2.
  - exact Y3.
  - (* [comment removed for export] *) split.
    { pose proof (proj1 (rr_rinfo st m HR)) as VR. pose proof (ris_range st WF) as (Z1 & Z2 & Z3 & Z4). change (ris st') with (ris st).
      destruct RINFO as (jr0 & je0 & js0 & RC0). pose proof (rw_cells_bound bsegs m' _ _ RC0) as RB0.
      assert (E128 : Z.of_nat (cells_size (rinfo_cells st' cls jr0 je0 js0)) = 128).
      { destruct RC0 as [[Wf _] _]. cbn in Wf. unfold rinfo_cells. cbn [cells_size Cells.csize].
        destruct Wf as (_ & _ & _ & _ & _ & _ & _ & _ & L1 & _ & L2 & L3 & _). lia. }
      assert (RL : rinfo st cls = ris st + 128 * cls) by reflexivity.
      destruct (stk_split bsegs m (ris st) (rinfo st cls) (ris st + 4096) VR ltac:(rewrite RL; lia)) as [VA VB].
      destruct (stk_split bsegs m (rinfo st cls) (rinfo st cls + 128) (ris st + 4096) VB ltac:(rewrite RL; lia)) as [_ VC].
      apply (stk_merge bsegs m' _ (rinfo st cls)); [| | rewrite RL; lia].
      - eapply stk_transport_disjoint; [exact VA| exact MU| exact WM|].
        pose proof (cls_facts st WF cls Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
        apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia.
      - apply (stk_merge bsegs m' _ (rinfo st cls + 128)); [| | rewrite RL; lia].
        + pose proof (stk_of_rw_cells bsegs m' _ _ RC0) as SR. rewrite E128 in SR. exact SR.
        + eapply stk_transport_disjoint; [exact VC| exact MU| exact WM|].
          pose proof (cls_facts st WF cls Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
          apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, KNUMCLASSES in *; lia. }
    intros c Hc'. change (rinfo st' c) with (rinfo st c). destruct (Z.eq_dec c cls) as [->|NE]; [exact RINFO|].
    destruct (proj2 (rr_rinfo st m HR) c Hc') as (jr & je & js & RC). exists jr, je, js.
    replace (rinfo_cells st' c jr je js) with (rinfo_cells st c jr je js) by (unfold rinfo_cells; rewrite rg_other by exact NE; unfold num_freed; rewrite rg_other by exact NE; reflexivity).
    exact (pz_rinfo_other st WF cls Hc W HW m m' c jr je js MU WM Hc' NE RC).
  - (* [comment removed for export] *) intros c Hc'. change (rbeg st' c) with (rbeg st c). change (fabeg st' c) with (fabeg st c).
    destruct (Z.eq_dec c cls) as [->|NE].
    2:{ unfold num_freed. rewrite rg_other by exact NE. exact (Y5 c Hc'). }
    rewrite rg_same. unfold num_freed. rewrite rg_same. cbn [r_allocated r_mapped r_mapped_fa r_fa cd_rnew]. fold fb fam'.
    destruct (Y5 cls Hcls) as (V1 & V2 & V3 & V4 & EN & TL). fold r fb in V1, V2, V3, V4, EN, TL |- *.
    change (num_freed st cls) with nf in EN.
    split; [exact V1|]. split; [exact V2|]. split; [exact (proj1 VF)|]. split; [exact (proj2 VF)|]. split; [| exact TL].
    intros i Hi. rewrite zlen_app, drained_len, <- Enf in Hi.
    destruct (Z_lt_le_dec i nf) as [LT|GE].
    + rewrite nthz_app_l by (rewrite <- Enf; lia). apply EN. lia.
    + rewrite nthz_app_r, <- Enf by (rewrite <- ?Enf; lia). replace i with (nf + (i - nf)) at 1 by lia. apply FILL. lia.
  - (* [comment removed for export] *) intros c j Hc' Hj. change (cptr_addr st' c j) with (cptr_addr st c j).
    apply (Y6 c j Hc'). apply in_app_iff in Hj. apply in_or_app. destruct Hj as [Hj|Hj]; [| right; exact (apend_sub c j Hj)].
    destruct (Z.eq_dec c cls) as [->|NE]; [| left; rewrite <- (avail_other c NE); exact Hj].
    eapply Permutation_in in Hj; [| exact avail_perm]. destruct Hj as [<-|Hj]; [| left; exact Hj].
    right. unfold apend_cptrs. apply in_map_iff. exists (cls, k). split; [reflexivity|]. apply filter_In. split; [exact HIN| cbn [fst]; apply Z.eqb_refl].
  - (* [comment removed for export] *) intros c Hc'. change (pcaddr st' c) with (pcaddr st c).
    assert (PM : pc_max_count st' c = (if c =? 0 then 0 else cmaxcount c)) by (unfold pc_max_count; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    assert (PS' : pc_class_size st' c = (if c =? 0 then 0 else csize c)) by (unfold pc_class_size; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    rewrite PM, PS'. split; [exact (PCH c Hc')|].
    destruct (Z.eq_dec c cls) as [->|NE].
    + rewrite cch_same. intros i Hi. apply PCE. unfold cache' in Hi. rewrite zlen_app, firstn_len in Hi. change (zlen [k]) with 1 in Hi. lia.
    + rewrite cch_other by exact NE. intros i Hi. exact (PCO c i Hc' NE Hi).
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
End CDT.


End CeilWrap.
End RTW_cd_abs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kit RT_fp RT_artF RT_front RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_map RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_gfa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_refillw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_zone RTW_p_abs.
Import RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_primary_iface RTW_cd_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_cd_leaves.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_cd_rta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_cd_dd.
Import RTW_cd_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac3 RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_libo.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Definition hideP (P : Prop) : Prop := P.
(* [comment removed for export] *)
Ltac prune :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H
  | H : forall _ : Z, _ |- _ => clear H | H : forall _ : word, _ |- _ => clear H | H : forall _ : nat, _ |- _ => clear H | H : forall _ : bool, _ |- _ => clear H
  | H : forall _ : (word -> option byte), _ |- _ => clear H | H : RTREP _ _ |- _ => clear H | H : RTMODEL _ _ |- _ => clear H | H : GWIN _ _ _ _ |- _ => clear H
  | H : FRONTR _ _ |- _ => clear H | H : SWIN _ _ |- _ => clear H | H : leafc _ _ |- _ => clear H | H : mmap_consts _ |- _ => clear H
  | H : icpt_cells _ |- _ => clear H | H : poison_cells _ |- _ => clear H | H : LOK _ _ |- _ => clear H | H : BINV _ _ |- _ => clear H
  | H : no_wx _ |- _ => clear H | H : In _ _ |- _ => clear H | H : wf_class _ _ |- _ => clear H | H : carved_cptr _ _ _ |- _ => clear H
  | H : hideP _ |- _ => clear H | H : _ = wz _ |- _ => clear H | H : gmono _ _ |- _ => clear H
  end.
Ltac plia := prune; lia.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| plia] end ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma split3_bytes : forall (js : list byte), firstn 8 js ++ firstn 8 (skipn 8 js) ++ firstn 8 (skipn 16 js) ++ skipn 24 js = js.
Proof.
  intros js. transitivity (firstn 8 js ++ skipn 8 js); [| apply firstn_skipn]. f_equal.
  transitivity (firstn 8 (skipn 8 js) ++ skipn 8 (skipn 8 js)); [| apply firstn_skipn]. f_equal.
  rewrite !skipn_skipn. cbn [Nat.add].
  transitivity (firstn 8 (skipn 16 js) ++ skipn 8 (skipn 16 js)); [| apply firstn_skipn]. f_equal.
  rewrite !skipn_skipn. reflexivity.
Qed.
Lemma rinfo_split3 : forall m Rc (alloc z1 mapped z2 : word) jr exh je js,
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; CB 56 js] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je;
                              C8 (le_bytes_to_word (firstn 8 js)); C8 (le_bytes_to_word (firstn 8 (skipn 8 js))); C8 (le_bytes_to_word (firstn 8 (skipn 16 js))); CB 32 (skipn 24 js)].
Proof.
  intros m Rc alloc z1 mapped z2 jr exh je js H.
  pose proof H as [[W _] _]. cbn in W.
  assert (LJ : length js = 56%nat) by tauto.
  eapply rw_cells_recast_p; [exact H| cbn; rewrite ?length_firstn, ?length_skipn; intuition lia|].
  cbn [cells_bytes cbytes]. rewrite !p_le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite <- (split3_bytes js) at 5. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma rinfo_join3 : forall m Rc (alloc z1 mapped z2 w1 w2 w3 : word) jr exh je js3,
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 w1; C8 w2; C8 w3; CB 32 js3] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; CB 56 (le8 w1 ++ le8 w2 ++ le8 w3 ++ js3)].
Proof.
  intros m Rc alloc z1 mapped z2 w1 w2 w3 jr exh je js3 H.
  pose proof H as [[W _] _]. cbn in W.
  eapply rw_cells_recast_p; [exact H| cbn; rewrite ?length_app, ?length_le8; intuition lia|].
  cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rinfo_line : forall m Rc (a b c d : cell) rest,
  rw_cells bsegs m Rc [a; b; c] -> rw_cells bsegs m (Rc + 24) [d] -> rw_cells bsegs m (Rc + 32) rest ->
  cells_size [a; b; c] = 24%nat -> cells_size [d] = 8%nat ->
  rw_cells bsegs m Rc ([a; b; c] ++ [d] ++ rest).
Proof.
  intros m Rc a b c d rest H1 H2 H3 S1 S2.
  apply (proj2 (rw_cells_app m _ _ _)). split; [exact H1|]. rewrite S1. apply (proj2 (rw_cells_app m _ _ _)). split; [exact H2|]. rewrite S2.
  replace (Rc + Z.of_nat 24 + Z.of_nat 8) with (Rc + 32) by lia. exact H3.
Qed.

Lemma vis_bytes : forall m lo hi, stk bsegs m lo hi -> AIMG_HI <= lo -> forall x : word, lo <= bv_unsigned x < hi -> m x <> None.
Proof.
  intros m lo hi ST Hlo x Hx. pose proof (stk_some m lo hi (bv_unsigned x) ST Hx Hlo) as H. unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma zsum_ge_In' : forall (f : Z -> Z) l x, (forall y, In y l -> 0 <= f y) -> In x l -> List.NoDup l -> f x <= zsum (map f l).
Proof.
  intros f l x Hf Hx ND. induction l as [|y l IH]; [destruct Hx|]. cbn [map]. rewrite zsum_cons. inversion ND; subst.
  destruct Hx as [->|Hx].
  - pose proof (zsum_nonneg (map f l) ltac:(apply Forall_map; apply Forall_forall; intros z Hz; apply Hf; right; exact Hz)). lia.
  - specialize (IH ltac:(intros z Hz; apply Hf; right; exact Hz) Hx ltac:(assumption)). pose proof (Hf y ltac:(left; reflexivity)). lia.
Qed.
Lemma prov_cls_le' : forall st cls, RTWF st -> 1 <= cls <= 30 -> provU st cls + provF st cls <= rt_prov st.
Proof.
  intros st cls WF Hc. (nelimp (rt_prov_parts_nonneg st WF) 8%nat; intros P1 P2 P3 P4 P5 P6 P7 P8).
  pose proof (prov_l24_nonneg st) as P9. pose proof (prov_emb_nonneg st) as [P10 _].
  assert (provU st cls + provF st cls <= prov_classes st).
  { unfold prov_classes. apply (zsum_ge_In' (fun c => provU st c + provF st c) classes cls).
    - intros y _. unfold provU, provF. lia.
    - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
    - apply classes_nodup. }
  unfold rt_prov. lia.
Qed.

(* [comment removed for export] *)
Lemma carved_cptr_small : forall st c k, RTWF st -> 1 <= c <= 30 -> carved_cptr st c k -> 0 <= k < 2^28.
Proof.
  intros st c k WF Hc nelH_; (nelim nelH_ 3%nat; intros j Hj ->). pose proof (wf_class_ok st WF c ltac:(unfold KNUMCLASSES; lia)) as WC.
  pose proof (wc_alloc_carved st c WC) as AC. pose proof (wc_alloc_mapped st c WC) as AM. pose proof (wc_mapped_max st c WC) as MM.
  pose proof (csize_pos c ltac:(lia)) as SP. pose proof (chunk_cptr_eq c j ltac:(lia)) as CE.
  unfold KFREEARRAY_OFF in MM.
  assert (j * csize c + csize c <= ncarved st c * csize c) by nia.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPC.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hc : 1 <= cls <= 30.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma cd_tail_blockfree : forall lo hi, rbeg st cls + r_mapped (rg st cls) <= lo -> hi <= rbeg st cls + KREGIONSIZE -> blockfree st lo hi.
Proof.
  intros lo hi H1 H2. (nelimp (cls_facts st WF cls Hc) 8%nat; intros C1 C2 C3 C4 C5 C6 C7 _).
  apply (prim_nonuser_blockfree st WF); [lia| lia|].
  intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE]; [right; exact H1|].
  (nelim (region_range st WF c Hc') 6%nat; intros _ R2 _ _ R5 _).
  rewrite !(rbeg_val st) in *. unfold KFREEARRAY_OFF, KREGIONSIZE, KNUMCLASSES in *.
  destruct (Z_lt_le_dec c cls); [right| left]; nia.
Qed.

Lemma cd_pz_not_client : forall lo hi a, pz_ok st cls (lo, hi) -> (CEIL <= lo -> hi <= SP) -> lo <= a < hi ->
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
      [apply cd_tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| unfold KFREEARRAY_OFF, KREGIONSIZE in *; lia].
  - eapply (hm_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply cd_tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia
      | rewrite C13 in Z5; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia].
  - eapply (hmsh_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| lia].
Qed.

Lemma cd_cli_pres : forall W m m', munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as [A1 A2]. cbn [fst snd] in A2. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. exact (cd_pz_not_client lo hi a A1 A2 Hin HC).
Qed.

Lemma cd_outside_intro : forall W a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. intros W a H. induction W as [|[l' h'] W IH]; [exact I|]. cbn. split; [exact (H (l', h') ltac:(left; reflexivity))| apply IH; intros iv Hiv; apply H; right; exact Hiv]. Qed.
Lemma cd_rt_frame : forall W m m' lo FP, munch W m m' ->
  (forall a iv, In iv W -> fst iv <= a < snd iv -> (lo <= a < SP) \/ in_ivs FP a) ->
  rt_frame FP lo SP m m'.
Proof.
  intros W m m' lo FP MU HW a Ha Hs Hn. apply MU. rewrite wa_unsigned by lia. apply cd_outside_intro.
  intros iv Hiv Hin. destruct (HW a iv Hiv Hin) as [X|X]; [exact (Hs X)| exact (Hn X)].
Qed.
End FPC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cd_cells : forall st m cls, RTREP st m -> RTWF st -> 1 <= cls <= 30 ->
  let r := rg st cls in
  exists (jr je js : list byte) (tj1 tj2 sa : word),
    ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 (st_spacebeg st))]
    /\ ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)]
    /\ ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 (ris st))]
    /\ ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 (num_freed st cls))]
    /\ rw_cells bsegs m (rinfo st cls + 24) [C8 (Z_to_bv 64 (r_mapped_fa r))]
    /\ rw_cells bsegs m (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r)); C8 (Z_to_bv 64 0);
                                            CB 4 jr; C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]
    /\ rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2]
    /\ rw_cells bsegs m (st_t st + 2784) [C8 sa]
    /\ vis m (fabeg st cls) (fabeg st cls + r_mapped_fa r)
    /\ vis m (SH (fabeg st cls)) (SH (fabeg st cls) + r_mapped_fa r / 8)
    /\ (forall i, 0 <= i < num_freed st cls -> rw_cells bsegs m (fabeg st cls + 4 * i) [W4 (nthz (r_fa r) i 0)])
    /\ (forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m (pcaddr st c) [C4 (Z_to_bv 64 (zlen (cch st c))); C4 (Z_to_bv 64 (pc_max_count st c)); C8 (Z_to_bv 64 (pc_class_size st c))])
    /\ (forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)])
    /\ vis m (st_t st) (st_t st + 4096)
    /\ ro_cells bsegs m GOT_SEALED [C8 (Z_to_bv 64 1)] /\ ro_cells bsegs m GOT_DYING [C8 (Z_to_bv 64 A_DYING)] /\ ro_cells bsegs m A_DYING [C4 (Z_to_bv 64 0)].
Proof.
  intros st m cls HR WF Hc. cbv zeta.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelimp (proj1 (rr_alloc st m HR)) 4%nat; intros j1 j2 j3 AL).
  (nelim (proj2 (rr_rinfo st m HR) cls Hcls) 4%nat; intros jr je js RC).
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (proj1 (rr_thread st m HR)) as VT.
  destruct (vis_c8 m _ _ (st_t st + 2872) VT ltac:(lia) ltac:(lia)) as [tj1 T1].
  destruct (vis_c8 m _ _ (st_t st + 2880) VT ltac:(lia) ltac:(lia)) as [tj2 T2].
  destruct (vis_c8 m _ _ (st_t st + 2784) VT ltac:(lia) ltac:(lia)) as [sa SA].
  (nelim (rr_regions st m HR cls Hcls) 6%nat; intros V1 V2 V3 V4 EN TL).
  pose proof (rr_consts st m HR) as HC. (nelim HC 17%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K16 _).
  pose proof (rr_link st m HR) as HL.
  exists jr, je, js, tj1, tj2, sa.
  unfold A_ALLOC in AL.
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1] [W8 (st_spacebeg st)]
             [W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st)] [W4 (2^32 - 1)]
             [CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2] [W8 (st_spacebeg st + KSPACESIZE)]
             [W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE)] [W1 0]
             [CB 7 j3]). exact AL. }
  unfold rinfo_cells in RC.
  split. { apply (rw_cells_take m _ _ [W8 (r_mapped_fa (rg st cls)); W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_mid m _ [W8 0; W8 0; W8 (num_freed st cls)] [W8 (r_mapped_fa (rg st cls))] [W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_drop m _ [W8 0; W8 0; W8 (num_freed st cls); W8 (r_mapped_fa (rg st cls))]). exact RC. }
  split. { apply (proj2 (rw_cells_app m _ [C8 tj1] [C8 tj2])). split; [exact T1|]. replace (st_t st + 2872 + Z.of_nat (cells_size [C8 tj1])) with (st_t st + 2880) by (cbn; lia). exact T2. }
  split; [exact SA|]. split; [exact V3|]. split; [exact V4|]. split; [exact EN|].
  split. { intros c Hc'. destruct (rr_cache st m HR c Hc') as [PC _]. exact PC. }
  split. { intros c i Hc' Hi. destruct (rr_cache st m HR c Hc') as [_ PE]. exact (PE i Hi). }
  split; [exact VT|].
  split; [apply (R_link_at m GOT_SEALED 1 HL); vm_compute; reflexivity|].
  split; [apply (R_link_at m GOT_DYING A_DYING HL); vm_compute; reflexivity|].
  exact K16.
Qed.

(* [comment removed for export] *)
Lemma vis_c4 : forall m lo hi a, stk bsegs m lo hi -> lo <= a -> a + 4 <= hi -> exists v : word, rw_cells bsegs m a [C4 v].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (stk_split bsegs m lo a hi ST ltac:(lia)) as [_ S2]. destruct (stk_split bsegs m a (a + 4) hi S2 ltac:(lia)) as [S3 _].
  (nelim (stk_carve bsegs m a (a + 4) 4 S3 ltac:(lia)) 3%nat; intros _ junk JK). replace (a + 4 - Z.of_nat 4) with a in JK by lia.
  pose proof JK as [[W _] _]. cbn in W.
  exists (le_bytes_to_word junk). eapply rw_cells_recast_p; [exact JK| cbn; tauto| cbn [cells_bytes cbytes]; rewrite p_le4_of_bytes by tauto; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma nf_cnt_bound : forall st cls, RTWF st -> 1 <= cls <= 30 ->
  num_freed st cls + zlen (cch st cls) <= ncarved st cls /\ 4 * ncarved st cls < 2^29.
Proof.
  intros st cls WF Hc. pose proof (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia)) as WC.
  pose proof (wc_used_all st cls WC) as UA. pose proof (wc_alloc_carved st cls WC) as AC. pose proof (wc_alloc_mapped st cls WC) as AM.
  pose proof (wc_mapped_max st cls WC) as MM. pose proof (csize_pos cls ltac:(lia)) as SP.
  assert (L : num_freed st cls + zlen (cch st cls) <= zlen (used_cptrs st cls)).
  { unfold used_cptrs, avail_cptrs, num_freed. rewrite !zlen_app.
    pose proof (zlen_nonneg (live_cptrs st cls)). pose proof (zlen_nonneg (quar_cptrs st cls)). pose proof (zlen_nonneg (qpend_cptrs st cls)).
    pose proof (zlen_nonneg (batch_cptrs st cls)). pose proof (zlen_nonneg (apend_cptrs st cls)). lia. }
  rewrite UA in L. split; [exact L|].
  assert (0 <= ncarved st cls) by (unfold ncarved; apply Z.div_pos; [exact (wc_alloc_nonneg st cls WC)| lia]).
  unfold KFREEARRAY_OFF in MM. nia.
Qed.

(* [comment removed for export] *)
Lemma cache_entry_small : forall st cls i, RTWF st -> 1 <= cls <= 30 -> 0 <= i < zlen (cch st cls) -> 0 <= nthz (cch st cls) i 0 < 2^28.
Proof.
  intros st cls i WF Hc Hi. pose proof (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia)) as WC.
  apply (carved_cptr_small st cls _ WF Hc). apply (wc_used_carved st cls WC). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right.
  apply nthz_In. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cd_fam' (fm : bool) (fam : Z) : Z := if fm then fam + 262144 else fam.

Definition cd_wpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (cls k lo : Z) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
  : machine_state -> Model -> lghost -> Prop :=
  fun ms mo' g' => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (dr fm : bool) (W : list (Z * Z)) (jr je js : list byte),
    let C := cch st cls in let cnt := zlen C in let n := nrefill cls in let nf := num_freed st cls in
    let r := rg st cls in let fam := r_mapped_fa r in let base := (if dr then cnt - n else cnt) in
    let FA := fabeg st cls in let U := FA + fam in let fam' := cd_fam' fm fam in
    ms = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch W m m' /\ wmono bsegs m m'
    /\ Forall (pz_ok st cls) W
    /\ (forall a iv, In iv W -> fst iv <= a < snd iv -> (lo <= a < bv_unsigned sp) \/ in_ivs (primary_fp st cls) a)
    /\ Forall (fun iv : Z * Z => CEIL <= fst iv -> snd iv <= bv_unsigned sp) W
    /\ (dr = true -> cnt = cmaxcount cls /\ fm = (fam <? 4 * (nf + n)))
    /\ (dr = false -> cnt <> cmaxcount cls /\ fm = false)
    /\ rw_cells bsegs m' (rinfo st cls) [W8 0; W8 0; W8 (nf + (cnt - base)); W8 fam'; W8 (r_allocated r); W8 0; W8 (r_mapped r); W8 0;
                                         CB 4 jr; W1 (if r_exhausted r then 1 else 0); CB 3 je; CB 56 js]
    /\ vis m' FA (FA + fam') /\ vis m' (SH FA) (SH FA + fam' / 8)
    /\ (forall t, 0 <= t < cnt - base -> rw_cells bsegs m' (FA + 4 * (nf + t)) [W4 (nthz (skipn (Z.to_nat base) C) t 0)])
    /\ (forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m' (pcaddr st c)
           [W4 (if c =? cls then base + 1 else zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)])
    /\ (forall i, 0 <= i <= base -> rw_cells bsegs m' (pcaddr st cls + 16 + 4 * i) [W4 (nthz (firstn (Z.to_nat base) C ++ [k]) i 0)])
    /\ (forall c i, 0 <= c < KNUMCLASSES -> c <> cls -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)])
    /\ RTMODEL st mo' /\ GWIN st m' mo' g' /\ FRONTR mo' (g_res g') /\ SWIN st g' /\ gmono (mkG G R) g'
    /\ g_res g' = R - (if fm then LUMPF else 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wl_of_nthz : forall (l : list Z) nn, length l = nn -> map (fun j : nat => wz (nthz l (Z.of_nat j) 0)) (seq 0 nn) = wl l.
Proof.
  induction l as [|a l IH]; intros nn HL; cbn [length] in HL; subst nn; [reflexivity|].
  rewrite <- cons_seq. cbn [map]. rewrite <- seq_shift, map_map.
  change (wl (a :: l)) with (wz a :: wl l). f_equal.
  rewrite <- (IH (length l) eq_refl). apply map_ext. intros j. f_equal.
  unfold nthz. destruct (Z.ltb_spec0 (Z.of_nat (S j)) 0); [lia|]. destruct (Z.ltb_spec0 (Z.of_nat j) 0); [lia|].
  replace (Z.to_nat (Z.of_nat (S j))) with (S (Z.to_nat (Z.of_nat j))) by lia. reflexivity.
Qed.
Lemma nth_error_wl : forall (zs : list Z) t, (t < length zs)%nat -> nth_error (wl zs) t = Some (wz (nth t zs 0)).
Proof.
  intros zs t Ht. unfold wl. rewrite nth_error_map. rewrite (nth_error_nth' zs 0 Ht). reflexivity.
Qed.

Section CDM.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (cls k lo : Z).
  Let S := st_spacebeg st.
  Let t := st_t st.
  Let P := acache st.
  Let pc := pcaddr st cls.
  Let Rc := rinfo st cls.
  Let RB := rbeg st cls.
  Let FA := fabeg st cls.
  Let r := rg st cls.
  Let fam := r_mapped_fa r.
  Let nf := num_freed st cls.
  Let n := nrefill cls.
  Let C := cch st cls.
  Let cnt := zlen C.
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Hypothesis HG : GWIN st m mo (mkG G R).
  Hypothesis HFR : FRONTR mo R.
  Hypothesis HSW : SWIN st (mkG G R).
  Hypothesis HIN : In (cls, k) (st_apend st).
  Hypothesis Hc : 1 <= cls <= 30.
  Hypothesis TP : tp = wz ATP.
  Hypothesis HPROV : rt_prov st <= R.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + ACDEALLOC_STACK <= bv_unsigned sp.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz A_ALLOC) (wz cls) (wz (cptr_addr st cls k)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ACDEALLOC) fc None m (seg_rom bsegs).
  Let WPOST := cd_wpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls k lo m mo G R.

  Local Ltac ulia := rewrite ?unsigned_lit by plia; plia.
  Local Ltac xrw H MU WM := eapply (rw_cells_transport bsegs _ _ _) in H; [| exact MU| exact WM| cbn; plia].
  Local Ltac xrwk K H MU WM := eapply (rw_cells_transport bsegs _ _ _) in H; [| exact MU| exact WM| cbn; (K; lia)].  (* [comment removed for export] *)
  Local Ltac xro H MU := eapply (ro_cells_transport bsegs _ _ _) in H; [| exact MU| cbn; plia].
  Local Ltac xrok K H MU := eapply (ro_cells_transport bsegs _ _ _) in H; [| exact MU| cbn; (K; lia)].  (* [comment removed for export] *)
  Local Ltac xst H MU WM := eapply (stk_transport_disjoint bsegs _ _ _) in H; [| exact MU| exact WM| cbn; plia].
  (* [comment removed for export] *)

  Local Ltac stkx H := lazymatch goal with |- stk _ _ _ ?hi => lazymatch type of H with stk _ _ _ ?hi' => replace hi with hi' by ulia end end; exact H.
  Local Ltac rwx H := lazymatch goal with |- rw_cells _ _ ?a _ => lazymatch type of H with rw_cells _ _ ?a' _ => replace a with a' by ulia end end; exact H.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cd_tail : forall (fm : bool) (m4 : word -> option byte) (moq : Model) (Gq : list (Z * Z)) (Rq : Z)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (j2 j3 : list byte) (tj1 tj2 : word),
    let fam' := cd_fam' fm fam in
    st_cache_inited st = true -> cnt = cmaxcount cls ->
    mem_inv bsegs m4 ->
    munch [(lo, bv_unsigned sp); (pc, pc + 4); (Rc, Rc + 32); (FA + fam, FA + fam'); (SH FA + fam / 8, SH FA + fam' / 8); (t + 2872, t + 2888)] m m4 ->
    wmono bsegs m m4 -> stk bsegs m4 lo (bv_unsigned sp + -240) ->
    rw_cells bsegs m4 (bv_unsigned sp + -48) (cd_frame s4 s3 s2 s1 s0 ra) ->
    rw_cells bsegs m4 (bv_unsigned sp + -112) (drain_frame j2 (wz 0x3472c)) ->
    rw_cells bsegs m4 (bv_unsigned sp + -240) (rta_frame j3 (wz (Rc + 8)) s11 s10 s9 s8 s7 s6 s5 (wz (S + cls * 2^32 + 16 * k)) (wz cls) (wz A_ALLOC) (wz P) (wz pc) (wz 0x34974)) ->
    rw_cells bsegs m4 Rc [C8 (wz MTX_LOCKED); C8 (wz 0); C8 (Z_to_bv 64 nf)] ->
    rw_cells bsegs m4 (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
    rw_cells bsegs m4 pc [C4 (Z_to_bv 64 (cnt - n)); C4 (Z_to_bv 64 (cmaxcount cls)); C8 (Z_to_bv 64 (csize cls))] ->
    rw_cells bsegs m4 (t + 2872) [C8 tj1; C8 tj2] ->
    stk bsegs m4 (FA + fam) (FA + fam') ->
    (fm = true -> rw_cells bsegs m4 (SH FA + fam / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))]) ->
    (fm = true -> fam < 4 * (nf + n)) -> (fm = false -> 4 * (nf + n) <= fam) ->
    RTMODEL st moq -> GWIN st m4 moq (mkG Gq Rq) -> FRONTR moq Rq -> SWIN st (mkG Gq Rq) -> gmono (mkG G R) (mkG Gq Rq) ->
    Rq = R - (if fm then LUMPF else 0) -> LOK bsegs moq ->
    LSCPS bsegs WPOST
      (MS (mkR (wz 0x34c18) (wz (bv_unsigned sp + -112 + -128)) gp tp y5 y6 y7 (wz Rc) (wz nf) (wz 1) y11 y12 y13 y14 y15 y16 y17
               (wz cls) (wz (bv_unsigned sp + -112 + 8)) (wz A_ALLOC) (wz n) (wz (pc + 16 + 4 * (cnt - n))) (wz (nf + n)) (wz MTX_BIT61) (wz FA) (wz LOCK_MASK) (wz MTX_LOCKED) y28 y29 y30 y31)
          F (wz 0x34c18) fc None m4 (seg_rom bsegs)) moq (mkG Gq Rq).
  Proof.
    intros fm m4 moq Gq Rq y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 j2 j3 tj1' tj2'. cbv zeta.
    intros EI FULL MI4 MU4 WM4 ST4 FR1 FR2 FR3 MTX4 RI4 PCC4 TST4 VU4 SHU4 HLT HGE HM4 HG4 HFR4 HSW4 GM4 ER4 HOK4.
    assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; plia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [HCE LO2]. pose proof HCE as HCEn. idtac. unfold ACDEALLOC_STACK in LO2.
    pose proof (t_range st WF) as [TRo TRc]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa TRb TRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TRb, TRi. assert (TR : 4096 <= t /\ t + 4096 <= alloc_ceiling) by (split; assumption).
    pose proof (ctx_range st WF) as [CRo CRc]. (nelimp (oclr_lin _ _ CRo ltac:(lia)) 3%nat; intros CRa CRb CRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in CRb, CRi. assert (CR : 4096 <= st_ctx st /\ st_ctx st + 160 <= alloc_ceiling) by (split; assumption).
    (nelimp (cls_facts st WF cls Hc) 14%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14).
    assert (G1 : 17594333495296 <= RB) by exact Q1. assert (G2 : st_pbase st <= RB) by exact Q2. assert (G3 : RB + 4294967296 <= ris st) by exact Q3.
    assert (G4 : ris st + 4096 <= st_pbase st + 137439023104) by exact Q4. assert (G5 : st_pbase st + 137439023104 <= alloc_ceiling) by exact Q5.
    assert (G6 : 0 <= r_allocated r <= r_mapped r) by exact Q6. assert (G7 : r_mapped r <= 3758096384) by exact Q7.
    assert (G8 : 0 <= nf) by exact Q8. assert (G9 : 4 * nf <= fam) by exact Q9. assert (G10 : fam <= 536870912) by exact Q10.
    assert (G11 : hideP (RB mod 8 = 0)) by exact Q11. assert (G12 : hideP (r_mapped r mod 8 = 0)) by exact Q12.
    assert (EFA : FA = RB + 3758096384) by exact Q13. assert (ERC : Rc = ris st + 128 * cls) by exact Q14.
    clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14.
    (nelimp (S_range st WF) 3%nat; intros SR1' SR2' SR3'). assert (SR1 : st_pbase st <= S) by exact SR1'. assert (SR2 : S + 137438953472 + 4096 <= st_pbase st + 137439023104) by exact SR2'.
    assert (SR3 : hideP (S mod 4096 = 0)) by exact SR3'. clear SR1' SR2' SR3'.
    assert (SAL : hideP (S mod 65536 = 0)) by exact (wb_S_align st (wf_base_ok st WF)).
    (nelimp (P_range st WF) 3%nat; intros PR1' PR2' PR3'). assert (PR1 : 17594333495296 <= st_pbase st) by exact PR1'. assert (PR2 : st_pbase st + 137439023104 <= alloc_ceiling) by exact PR2'.
    clear PR1' PR2' PR3'.
    assert (ERB : RB = S + cls * 4294967296) by (unfold RB; rewrite (rbeg_val st); reflexivity).
    assert (ERIS : ris st = S + 137438953472) by reflexivity.
    pose proof (wf_class_ok st WF cls Hcls) as WC.
    assert (FAL : hideP (fam mod 262144 = 0)) by exact (wc_fa_align st cls WC). assert (FA0 : 0 <= fam) by exact (wc_fa_nonneg st cls WC).
    pose proof (cmaxcount_range cls ltac:(plia)) as [CMR CME']. assert (CME : cmaxcount cls = 2 * n) by exact CME'. clear CME'.
    pose proof (wc_cache_max st cls WC) as CMX'. assert (CMX : cnt <= cmaxcount cls) by exact CMX'. clear CMX'. pose proof (zlen_nonneg C) as CNT0'. assert (CNT0 : 0 <= cnt) by exact CNT0'. clear CNT0'.
    pose proof (nf_cnt_bound st cls WF Hc) as [NC1' NC2]. assert (NC1 : nf + cnt <= ncarved st cls) by exact NC1'. clear NC1'.
    pose proof (csize_pos cls ltac:(plia)) as CP. pose proof (csize_le64k' cls Hc) as CL.
    assert (PCB : pc = P + 80 * cls /\ P = t + 208) by (split; reflexivity). destruct PCB as [EPC EP].
    assert (TAL : hideP (t mod 4096 = 0)) by (pose proof (wb_t_loose st (wf_base_ok st WF)) as TL; (nelim (loose0_range st WF t 4096 TL) 4%nat; intros _ _ _ X); exact X).
    assert (TDJ : hideP (t + 4096 <= st_pbase st \/ st_pbase st + 137439023104 <= t)) by
      (pose proof (loose_vs_prim st WF t 4096 (wb_t_loose st (wf_base_ok st WF))) as H0; assert (H : st_pbase st + 137439023104 <= t \/ t + 4096 <= st_pbase st) by exact H0; unfold hideP; clear -H; plia).
    assert (CDJ : hideP (st_ctx st + 160 <= st_pbase st \/ st_pbase st + 137439023104 <= st_ctx st)) by
      ((nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros b kk Hin B1 B2); pose proof (loose_vs_prim st WF b kk Hin) as H0; assert (H : st_pbase st + 137439023104 <= b \/ b + kk <= st_pbase st) by exact H0; unfold hideP; clear -H B1 B2; plia).
    assert (HK : carved_cptr st cls k) by
      (apply (wc_used_carved st cls WC); unfold used_cptrs; rewrite !in_app_iff; do 5 right; unfold apend_cptrs; apply in_map_iff; exists (cls, k); split; [reflexivity|];
       apply filter_In; split; [exact HIN| cbn [fst]; apply Z.eqb_refl]).
    pose proof (carved_cptr_small st cls k WF Hc HK) as KR.
    assert (EPK : cptr_addr st cls k = S + cls * 2^32 + 16 * k) by (unfold cptr_addr; fold RB; rewrite ERB; plia).
    (nelim (cd_cells st m cls HR WF Hc) 24%nat; intros jr je js tj1 tj2 sa AC32' AC40' AC48' AC56' MTX' RI24' RIb' TST' SA' VFA' VSF' EN' PCH' PCE' VT' GS' GD' DY').
    assert (AC32 : ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)]) by exact AC32'. assert (AC40 : ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)]) by exact AC40'.
    assert (AC48 : ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 (ris st))]) by exact AC48'. assert (AC56 : ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)]) by exact AC56'.
    assert (MTX : rw_cells bsegs m Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)]) by exact MTX'. assert (RI24 : rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)]) by exact RI24'.
    assert (RIb : rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r)); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]) by exact RIb'.
    assert (TST : rw_cells bsegs m (t + 2872) [C8 tj1; C8 tj2]) by exact TST'. assert (SA : rw_cells bsegs m (P + 2576) [C8 sa]) by (replace (P + 2576) with (st_t st + 2784) by (rewrite EP; unfold t; plia); exact SA').
    assert (VFA : stk bsegs m FA (FA + fam)) by exact VFA'. assert (VSF : stk bsegs m (SH FA) (SH FA + fam / 8)) by exact VSF'.
    assert (EN : forall i, 0 <= i < nf -> rw_cells bsegs m (FA + 4 * i) [W4 (nthz (r_fa r) i 0)]) by exact EN'.
    assert (PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m (P + 80 * c) [C4 (Z_to_bv 64 (zlen (cch st c))); C4 (Z_to_bv 64 (pc_max_count st c)); C8 (Z_to_bv 64 (pc_class_size st c))]) by exact PCH'.
    assert (PCE : forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m (P + 80 * c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)]) by exact PCE'.
    assert (VT : stk bsegs m t (t + 4096)) by exact VT'.
    assert (GS : ro_cells bsegs m GOT_SEALED [C8 (Z_to_bv 64 1)]) by exact GS'. assert (GD : ro_cells bsegs m GOT_DYING [C8 (Z_to_bv 64 A_DYING)]) by exact GD'. assert (DY : ro_cells bsegs m A_DYING [C4 (Z_to_bv 64 0)]) by exact DY'.
    clear AC32' AC40' AC48' AC56' MTX' RI24' RIb' TST' SA' VFA' VSF' EN' PCH' PCE' VT' GS' GD' DY'.
    pose proof (leafc_of_RTREP st m HR) as LC. pose proof (mmap_cells st m HR) as HC.
    pose proof (artcells_icpt m (rtrep_artcells st m HR)) as IC. pose proof (artcells_poison m (rtrep_artcells st m HR)) as PCz.
    assert (E48 : bv_unsigned (wz (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (unfold wz; apply unsigned_lit; plia).
    assert (E112 : bv_unsigned (wz (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (unfold wz; rewrite unsigned_lit by plia; plia). assert (E112' : bv_unsigned (wz (bv_unsigned sp + -48 + -64)) = bv_unsigned sp + -112) by (unfold wz; rewrite unsigned_lit by plia; plia).
    assert (E240 : bv_unsigned (wz (bv_unsigned sp + -112 + -128)) = bv_unsigned sp + -240) by (unfold wz; rewrite unsigned_lit by plia; plia).
    assert (SHFA : hideP (SH (FA + fam) = SH FA + fam / 8 /\ SH FA = SH RB + 469762048 /\ (FA + fam) mod 32768 = 0 /\ 2147450880 <= SH RB /\ SH (RB + 4294967296) = SH RB + 536870912 /\ SH RB + 536870912 <= 17594333495296)) by
      (unfold hideP in G11, FAL, SAL |- *; unfold SH, SHADOW_OFFSET; rewrite EFA;
       assert (RB32 : RB mod 32768 = 0) by (rewrite ERB; clear -SAL Hc; Z.div_mod_to_equations; plia);
       assert (RBH : RB + 4294967296 + 4096 <= alloc_ceiling) by (clear -G3 G4 G5; plia);
       clear -RB32 RBH FAL FA0 G1 G10; Z.div_mod_to_equations; plia).


    pose proof (nrefill_eq cls ltac:(plia)) as [_ NR']. assert (NR : 1 <= n <= 8) by exact NR'. clear NR'.
    unfold hideP in SHFA. (nelim SHFA 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6). unfold hideP in TDJ.
    set (base := cnt - n) in *. assert (EB : base = cnt - n) by reflexivity.
    assert (BR : 0 <= base /\ base + n = cnt /\ base <= 15) by plia.
    set (CH := pc + 16 + 4 * base) in *. assert (ECH : CH = pc + 16 + 4 * base) by reflexivity.
    assert (FM' : (fm = true -> cd_fam' fm fam = fam + 262144) /\ (fm = false -> cd_fam' fm fam = fam)) by (split; intros ->; reflexivity).
    assert (FMR : fam <= cd_fam' fm fam <= 536870912 /\ 4 * (nf + n) <= cd_fam' fm fam /\ cd_fam' fm fam mod 8 = 0).
    { unfold hideP in FAL. destruct fm; cbn [cd_fam']; [pose proof (HLT eq_refl) as HX| pose proof (HGE eq_refl) as HX]; (split; [| split]); try plia;
        clear -HX FAL G9 G8 G10 NR NC1 NC2 CNT0 BR FA0 FULL; Z.div_mod_to_equations; nia. }
    set (fam' := cd_fam' fm fam) in *.
    (* [comment removed for export] *)
    xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) AC32 MU4. xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) AC40 MU4. xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) AC48 MU4.
    unfold GOT_SEALED in GS. unfold GOT_DYING in GD. unfold A_DYING in DY at 1. xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) GS MU4. xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) GD MU4. xrok ltac:(cut_to HCEn TRb TRi G1 G2 G3 EFA ERC SR2 PR1 ERB ERIS FA0 EPC EP SH2 SH3 SH4) DY MU4.
    xrwk ltac:(cut_to HCEn TRb TR G2 G3 EFA ERC SR2 ERB ERIS FA0 EPC EP TDJ SH2 SH4 SH6 FMR) SA MU4 WM4. xrwk ltac:(cut_to HCEn G1 G2 G3 EFA ERC SR2 PR2 ERB ERIS EPC EP TDJ SH2 SH6 FMR) RIb MU4 WM4.
    pose proof VT as VT4. eapply (stk_wmono_oclr _ _ _ _) in VT4; [| exact WM4| exact TRo| pose proof ceil_lt64; plia].
    pose proof VFA as VFA4. eapply stk_wmono_noseg in VFA4; [| exact WM4| unfold AIMG_HI; plia].
    pose proof VSF as VSF4. eapply stk_wmono_noseg in VSF4; [| exact WM4| unfold AIMG_HI; plia].
    assert (VF4 : stk bsegs m4 FA (FA + fam')) by (eapply stk_merge; [exact VFA4| exact VU4| plia]).
    assert (VS4 : stk bsegs m4 (SH FA) (SH FA + fam' / 8)).
    { destruct fm.
      - pose proof (SHU4 eq_refl) as X. apply (stk_of_rw_cellsZ _ _ _ 32768) in X; [| cbn; plia]. rewrite (proj1 FM') in * by reflexivity.
        eapply stk_merge; [exact VSF4| | unfold hideP in FAL; clear -FAL FA0; Z.div_mod_to_equations; plia].
        replace (SH FA + (fam + 262144) / 8) with (SH FA + fam / 8 + 32768) by (unfold hideP in FAL; clear -FAL FA0; Z.div_mod_to_equations; plia). exact X.
      - rewrite (proj2 FM') in * by reflexivity. exact VSF4. }
    assert (HC4 : mmap_consts m4) by (eapply (mmap_consts_out _ m); [exact MU4| unfold outI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI; (cut_on [HCEn TRi G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 EPC EP SH3 ERC SR1 SH2 SH4] plia)| exact HC]).
    (* [comment removed for export] *)
    assert (PCE4 : forall i, 0 <= i < cnt -> rw_cells bsegs m4 (P + 80 * cls + 16 + 4 * i) [W4 (nthz C i 0)]).
    { intros i Hi. pose proof (PCE cls i Hcls Hi) as X. xrwk ltac:(cut_to FULL HCEn TRb TR G2 G3 EFA ERC SR2 ERB ERIS FA0 CMR EPC EP TDJ SH2 SH4 SH6 FMR Hi) X MU4 WM4. exact X. }
    pose proof (u32arr_of_cells (Z.to_nat n) m4 (P + 80 * cls + 16) base (fun i => nthz C i 0) ltac:(plia) ltac:(plia) ltac:(plia)
                  ltac:(intros i Hi; apply PCE4; plia)) as SRC. cbv beta in SRC.
    replace (map (fun j : nat => wz (nthz C (base + Z.of_nat j) 0)) (seq 0 (Z.to_nat n))) with (wl (skipn (Z.to_nat base) C)) in SRC.
    2:{ rewrite <- (wl_of_nthz (skipn (Z.to_nat base) C) (Z.to_nat n)) by (rewrite length_skipn; unfold cnt, zlen in BR; plia).
        apply map_ext. intros j. f_equal. rewrite nthz_skipn by plia. f_equal. plia. }
    replace (P + 80 * cls + 16 + 4 * base) with CH in SRC by plia.
    (* [comment removed for export] *)
    destruct (stk_split bsegs m4 FA (FA + 4 * nf) (FA + fam') VF4 ltac:(plia)) as [VL VR0].
    destruct (stk_split bsegs m4 (FA + 4 * nf) (FA + 4 * nf + 4 * n) (FA + fam') VR0 ltac:(plia)) as [VM VR].
    (nelim (stk_carve bsegs m4 (FA + 4 * nf) (FA + 4 * nf + 4 * n) (Z.to_nat (4 * n)) VM ltac:(plia)) 3%nat; intros _ junk JK).
    replace (FA + 4 * nf + 4 * n - Z.of_nat (Z.to_nat (4 * n))) with (FA + 4 * nf) in JK by plia.
    destruct (p_u32arr_of_u8arr bsegs m4 (FA + 4 * nf) junk (Z.to_nat n) (u8arr_of_rw_cells bsegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
    { pose proof JK as [[WFj _] _]. cbn in WFj. plia. }
    pose proof (rinfo_split3 _ _ _ _ _ _ _ _ _ _ RIb) as RIb4. clear RIb.
    assert (ZS : length (skipn (Z.to_nat base) C) = Z.to_nat n) by (rewrite length_skipn; unfold cnt, zlen in BR; plia).
    assert (ZSM : Forall (fun z => 0 <= z < 2^31) (skipn (Z.to_nat base) C)).
    { apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-). rewrite nth_skipn.
      unfold cnt, zlen in BR. rewrite length_skipn in Hi. unfold C in Hi |- *.
      pose proof (cache_entry_small st cls (Z.of_nat (Z.to_nat base + i)) WF Hc ltac:(unfold zlen; plia)) as X.
      unfold nthz in X. destruct (Z.ltb_spec0 (Z.of_nat (Z.to_nat base + i)) 0); [plia|]. rewrite Nat2Z.id in X. plia. }
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply (rta_B (wz (bv_unsigned sp + -112 + -128)) gp tp) with (Rc := Rc) (mm := bv_unsigned sp + -112 + 8) (c := cls) (CH := CH) (FA := FA) (n := n) (nf := nf)
        (zs := skipn (Z.to_nat base) C) (dpre := dpre);
        [exact MI4| exact MTX4| exact RIb4| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| unfold AIMG_HI; plia| plia| unfold AIMG_LO, AIMG_HI; (cut_on [FULL TRi TR G2 G3 SR2 ERB ERIS CMR CME EPC EP] plia)| idtac; plia
        | (cut_on [FULL G2 G3 ERC SR2 ERB ERIS CMR CME EPC EP TDJ] plia)| (cut_on [FULL G2 G3 EFA SR2 ERB ERIS CMR CME EPC EP TDJ] plia)| exact NR| exact G8| plia| plia| exact ZS| exact ZSM| exact LD| exact SRC| exact DST]. }
    cbv beta. intros ms5 nelH_; (nelim nelH_ 17%nat; intros z5 z6 z7 z14 z15 z16 z17 m5 s80' -> MU5 WM5 MI5 MTX5 RIb5 SRC5 DST5).
    pose proof ST4 as ST5. xst ST5 MU5 WM5.
    (* [comment removed for export] *)
    assert (HC5 : mmap_consts m5) by (eapply (mmap_consts_out _ m4); [exact MU5| unfold outI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI; plia| exact HC4]).
    pose proof AC40 as AC40_5. xro AC40_5 MU5. pose proof AC48 as AC48_5. xro AC48_5 MU5.
    pose proof (rw_cells_drop m5 _ [C8 (wz MTX_LOCKED); C8 (wz 0)] [C8 (Z_to_bv 64 (nf + n))] MTX5) as R16. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R16.
    lazymatch type of RIb5 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] =>
      pose proof (rw_cells_mid m5 _ [c1; c2; c3; c4; c5; c6; c7; c8] [c9; c10] [c11] RIb5) as R80 end.
    lazymatch type of R80 with rw_cells _ _ ?a _ => replace a with (Rc + 80) in R80 by (cbn; plia) end.
    eapply lscps_evt_then.
    { replace (wz 0x34f5c) with (wz A_MRTO) by reflexivity.
      eapply (mrto (wz 0x34c68) (wz (bv_unsigned sp + -112 + -128)) gp tp) with (lo := lo) (RIS := ris st) (Rc := Rc) (c := cls);
        [exact MI5| rewrite E240; exact ST5| exact HCE| rewrite E240; plia| exact HC5| exact AC40_5| exact AC48_5
        | exact R16 | exact R80
        | exact ERC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| exact Hc]. }
    cbv beta. unfold leaf_post. rewrite E240.
    intros ms6 nelH_; (nelim nelH_ 22%nat; intros w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m6 -> MU6 WM6 MI6 ST6 _).
    replace (ret_pc (wz 0x34c68)) with (wz 0x34c68) by (unfold wz; symmetry; apply ret_pc_even; [plia| reflexivity]).
    pose proof FR3 as FR3_6. xrw FR3_6 MU5 WM5. xrw FR3_6 MU6 WM6.
    pose proof MTX5 as MTX6. xrw MTX6 MU6 WM6.
    (* [comment removed for export] *)
    replace (wz (bv_unsigned sp + -112 + -128)) with (wz (bv_unsigned (wz (bv_unsigned sp + -112)) + -128)) by (rewrite E112; reflexivity).
    eapply lscps_evt_then.
    { eapply (rta_unlock _ (wz (bv_unsigned sp + -112)) gp tp) with (lo := lo) (Rc := Rc);
        [exact MI6| stkx ST6| exact HCE| ulia| rwx FR3_6| exact MTX6| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia
        | rewrite ERC, ERIS; unfold hideP in SR3; clear -SR3 Hc; Z.div_mod_to_equations; plia]. }
    cbv beta. rewrite E112. intros ms7 nelH_; (nelim nelH_ 22%nat; intros v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 m7 -> MU7 WM7 MI7 ST7 MTX7).
    replace (ret_pc (wz 0x34974)) with (wz 0x34974) by (unfold wz; symmetry; apply ret_pc_even; [plia| reflexivity]).
    (* [comment removed for export] *)
    pose proof FR2 as FR2_7. xrw FR2_7 MU5 WM5. xrw FR2_7 MU6 WM6. xrw FR2_7 MU7 WM7.
    replace (wz (bv_unsigned sp + -112)) with (wz (bv_unsigned (wz (bv_unsigned sp + -48)) + -64)) by (rewrite E48; f_equal; plia).
    eapply lscps_evt_then.
    { eapply (drain_post (wz (bv_unsigned sp + -48)) gp tp) with (lo := lo);
        [exact MI7| stkx ST7| exact HCE| ulia| rwx FR2_7]. }
    cbv beta. rewrite E48. intros ms8 nelH_; (nelim nelH_ 21%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m8 -> MU8 WM8 MI8 ST8).
    replace (ret_pc (wz 0x3472c)) with (wz 0x3472c) by (unfold wz; symmetry; apply ret_pc_even; [plia| reflexivity]).
    (* [comment removed for export] *)
    pose proof PCC4 as PCC8. xrwk ltac:(cut_to TRb G1 G2 G3 G8 EFA ERC SR1 SR2 PR1 ERB ERIS FA0 EPC EP TDJ NR SH3 FMR) PCC8 MU5 WM5. xrw PCC8 MU6 WM6. xrwk ltac:(cut_to HCEn TRb TR G1 G2 G3 EFA ERC SR1 SR2 PR2 ERB ERIS FA0 EPC EP TDJ NR SH3) PCC8 MU7 WM7. xrw PCC8 MU8 WM8.
    eapply lscps_evt_then.
    { eapply (cd_after_drain (wz 0x3472c)) with (cnt := cnt - n); [exact MI8| exact PCC8| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 EPC EP NR SH3] plia)| idtac; plia| plia]. }
    cbv beta. intros ms9 ->.
    pose proof VT4 as VT8. eapply (stk_wmono_oclr _ _ _ _) in VT8; [| eapply wmono_trans; [exact WM5| eapply wmono_trans; [exact WM6| eapply wmono_trans; [exact WM7| exact WM8]]]| exact TRo| pose proof ceil_lt64; plia].
    destruct (vis_c4 m8 t (t + 4096) (pc + 4 * (cnt - n) + 16) VT8 ltac:(plia) ltac:(plia)) as [slot SLOT].
    pose proof FR1 as FR1_8. xrw FR1_8 MU5 WM5. xrw FR1_8 MU6 WM6. xrw FR1_8 MU7 WM7. xrw FR1_8 MU8 WM8.
    pose proof AC32 as AC32_8. xro AC32_8 MU5. xro AC32_8 MU6. xro AC32_8 MU7. xro AC32_8 MU8.
    pose proof SA as SA8. xrwk ltac:(cut_to TRb G1 G2 G3 G8 EFA ERC SR1 SR2 PR1 ERB ERIS FA0 EP TDJ NR SH3 FMR) SA8 MU5 WM5. xrw SA8 MU6 WM6. xrwk ltac:(cut_to HCEn TRb TR G1 G2 G3 EFA ERC SR1 SR2 PR2 ERB ERIS FA0 EP TDJ NR SH3) SA8 MU7 WM7. xrw SA8 MU8 WM8.
    eapply lscps_evt_then.
    { eapply (cd_push _ sp gp tp) with (lo := lo) (S := S) (P := P) (pc := pc) (c := cls) (k := k) (cnt := cnt - n);
        [exact MI8| exact ST8| exact HCE| plia| exact FR1_8| exact AC32_8| exact PCC8| exact SLOT| exact SA8
        | exact EPC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR EP] plia)| idtac; plia| unfold hideP in TAL; clear -TAL EP; Z.div_mod_to_equations; plia| exact Hc
        | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| exact KR| plia| plia]. }
    cbv beta. intros ms10 nelH_; (nelim nelH_ 25%nat; intros q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m9 sa' -> MU9 WM9 MI9 ST9 PCC9 SLOT9 SA9).
    (* [comment removed for export] *)
    set (W := [(lo, bv_unsigned sp); (pc, pc + 4); (pc + 4 * (cnt - n) + 16, pc + 4 * (cnt - n) + 20); (t + 2768, t + 2896); (Rc, Rc + 128);
               (FA + 4 * nf, FA + KFREEARRAY_SIZE); (SH FA, SH FA + 67108864)]).
    unfold KFREEARRAY_SIZE in W.
    assert (MU09 : munch W m m9).
    { subst W. eapply munch_trans; [eapply munch_weaken; [| exact MU4]; clear -G9 FMR FA0 EP EPC Hc BR; subfp|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU5]; clear -G9 FMR FA0 EP EPC Hc BR NR; subfp|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU6]; clear -LO2; subfp|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU7]; clear -LO2; subfp|].
      eapply munch_trans; [eapply munch_weaken; [| exact MU8]; clear -LO2; subfp|].
      eapply munch_weaken; [| exact MU9]; clear -LO2 EP EPC Hc BR; subfp. }
    assert (WM09 : wmono bsegs m m9).
    { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7|]. eapply wmono_trans; [exact WM8| exact WM9]. }
    assert (WM49 : wmono bsegs m4 m9).
    { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7|]. eapply wmono_trans; [exact WM8| exact WM9]. }
    pose proof (rt_SH_mono (RB + r_mapped r) FA ltac:(plia)) as SHM.
    apply lscps_done. unfold WPOST, cd_wpost. cbv beta.
    exists q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, m9, true, fm, W, jr, je.
    exists (le8 (le_bytes_to_word (firstn 8 js)) ++ le8 s80' ++ le8 (le_bytes_to_word (firstn 8 (skipn 16 js))) ++ skipn 24 js).
    cbv zeta. cbv iota. fold C cnt n nf r. fold fam FA. cbv beta iota.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MU09|]. split; [exact WM09|].
    split.
    { (* [comment removed for export] *) subst W. unfold pz_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; fold t; change (rinfo st cls) with Rc; change (rbeg st cls) with RB; change (fabeg st cls) with FA;
        change (num_freed st cls) with nf; change (rg st cls) with r; unfold T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL; change (2 ^ 32) with 4294967296.
      - right. left. plia.
      - left. plia.
      - left. plia.
      - left. plia.
      - right. right. left. plia.
      - right. right. right. right. left. plia.
      - do 5 right. plia. }
    split.
    { (* [comment removed for export] *) subst W. intros a iv Hiv Ha. unfold primary_fp, fp_class, fp_tpage, in_ivs. cbn [app]. fold t. change (rinfo st cls) with Rc. change (rbeg st cls) with RB. unfold KREGIONSIZE.
      cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Ha.
      - left. exact Ha.
      - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia].
      - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia].
      - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia].
      - right. exists Rc, (Rc + 128). split; [do 2 right; left; reflexivity| plia].
      - right. exists RB, (RB + 4294967296). split; [left; reflexivity| plia].
      - right. exists (SH RB), (SH RB + 4294967296 / 8). split; [right; left; reflexivity| change (4294967296 / 8) with 536870912; plia]. }
    split.
    { subst W. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL; intros; plia. }
    split. { intros _. split; [exact FULL|]. destruct fm; symmetry; [apply Z.ltb_lt; exact (HLT eq_refl)| apply Z.ltb_ge; exact (HGE eq_refl)]. }
    split; [intros X; discriminate X|].
    split.
    { (* [comment removed for export] *)
      pose proof MTX7 as MTX9. xrw MTX9 MU8 WM8. xrwk ltac:(cut_to FULL HCEn TRb TR G1 G2 G3 EFA ERC SR1 SR2 PR1 PR2 ERB ERIS FA0 CMR CME EPC EP TDJ NR SH3) MTX9 MU9 WM9.
      pose proof RI4 as RI9. xrw RI9 MU5 WM5. xrw RI9 MU6 WM6. xrw RI9 MU7 WM7. xrw RI9 MU8 WM8. xrwk ltac:(cut_to FULL HCEn TRb TR G1 G2 G3 EFA ERC SR1 SR2 PR1 PR2 ERB ERIS FA0 CMR CME EPC EP TDJ NR SH3) RI9 MU9 WM9.
      pose proof RIb5 as RIb9. xrw RIb9 MU6 WM6. xrw RIb9 MU7 WM7. xrw RIb9 MU8 WM8. xrwk ltac:(cut_to FULL HCEn TRb TR G1 G2 G3 EFA ERC SR1 SR2 PR1 PR2 ERB ERIS FA0 CMR CME EPC EP TDJ NR SH3) RIb9 MU9 WM9.
      apply rinfo_join3 in RIb9.
      change (rinfo st cls) with Rc. replace (nf + (cnt - (cnt - n))) with (nf + n) by plia.
      exact (rinfo_line m9 Rc _ _ _ _ _ MTX9 RI9 RIb9 eq_refl eq_refl). }
    split; [eapply stk_wmono_noseg; [exact VF4| exact WM49| unfold AIMG_HI; plia]|].
    split; [eapply stk_wmono_noseg; [exact VS4| exact WM49| unfold AIMG_HI; plia]|].
    split.
    { (* [comment removed for export] *) intros i Hi.
      pose proof (cells_of_u32arr m5 (FA + 4 * nf) _ i _ DST5 ltac:(rewrite nth_error_wl by (rewrite ZS; plia); reflexivity) ltac:(plia)) as X.
      xrw X MU6 WM6. xrw X MU7 WM7. xrw X MU8 WM8. xrwk ltac:(cut_to FULL HCEn TRb TR G1 G2 G3 G8 G9 EFA SR1 SR2 PR1 PR2 ERB ERIS FA0 CMR CME EPC EP TDJ NR SH3 FMR Hi) X MU9 WM9.
      replace (FA + 4 * (nf + i)) with (FA + 4 * nf + 4 * i) by plia.
      unfold nthz. destruct (Z.ltb_spec0 i 0); [plia|]. exact X. }
    split.
    { (* [comment removed for export] *) intros c Hc'. change (pcaddr st c) with (P + 80 * c).
      destruct (Z.eqb_spec c cls) as [->|NE].
      - rewrite <- EPC. replace (cls =? 0) with false by (symmetry; apply Z.eqb_neq; plia). replace (cnt - n + 1) with (cnt - n + 1) by plia. exact PCC9.
      - pose proof (PCH c Hc') as X. unfold pc_max_count, pc_class_size in X. rewrite EI in X. cbn [andb] in X.
        unfold KNUMCLASSES in Hc'. xrwk ltac:(cut_to FULL HCEn TRb TR G2 G3 G8 EFA ERC SR2 ERB ERIS CMR CME EPC EP TDJ SH2 SH4 SH6 Hc' NE) X MU09 WM09. destruct (Z.eqb_spec c 0); cbn [negb] in X; exact X. }
    split.
    { (* [comment removed for export] *) intros i Hi. change (pcaddr st cls) with pc.
      destruct (Z_lt_le_dec i (cnt - n)) as [LT|GE].
      - pose proof (PCE cls i Hcls ltac:(change (zlen (cch st cls)) with cnt; plia)) as X. unfold KNUMCLASSES in Hcls. xrwk ltac:(cut_to FULL HCEn TRb TR G2 G3 G8 EFA ERC SR2 ERB ERIS CMR CME EPC EP TDJ SH2 SH4 SH6 Hi LT) X MU09 WM09.
        rewrite nthz_app_l by (unfold zlen; rewrite length_firstn; unfold cnt, zlen in BR; plia). rewrite nthz_firstn by plia.
        rewrite EPC. exact X.
      - replace i with (cnt - n) by plia. rewrite nthz_app_r by (unfold zlen; rewrite length_firstn; unfold cnt, zlen in BR; plia).
        replace (cnt - n - zlen (firstn (Z.to_nat (cnt - n)) C)) with 0 by (unfold zlen; rewrite length_firstn; unfold cnt, zlen in BR; plia).
        cbn [nthz Z.ltb Z.to_nat nth]. replace (pc + 16 + 4 * (cnt - n)) with (pc + 4 * (cnt - n) + 16) by plia. exact SLOT9. }
    split.
    { (* [comment removed for export] *) intros c i Hc' NE Hi. change (pcaddr st c) with (P + 80 * c).
      pose proof (PCE c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16. unfold KNUMCLASSES in Hc'.
      xrwk ltac:(cut_to FULL HCEn TRb TR G2 G3 G8 EFA ERC SR2 ERB ERIS CMR CME EPC EP TDJ SH2 SH4 SH6 Hc' NE Hi CM CM16) X MU09 WM09. exact X. }
    all: match goal with |- ?g => idtac "REMAINING" g end.
    split; [exact HM4|]. split; [eapply GWIN_mem; [exact HG4| exact HOK4| exact WM49]|]. split; [exact HFR4|]. split; [exact HSW4|]. split; [exact GM4|].
    cbn [g_res]. exact ER4.
  Qed.
  (* [comment removed for export] *)
  Lemma cd_walk : LSCPS bsegs WPOST ENTRY mo (mkG G R).
  Proof.
    assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; plia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [HCE LO2]. pose proof HCE as HCEn. idtac. unfold ACDEALLOC_STACK in LO2.
    pose proof (t_range st WF) as [TRo TRc]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa TRb TRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TRb, TRi. assert (TR : 4096 <= t /\ t + 4096 <= alloc_ceiling) by (split; assumption).
    pose proof (ctx_range st WF) as [CRo CRc]. (nelimp (oclr_lin _ _ CRo ltac:(lia)) 3%nat; intros CRa CRb CRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in CRb, CRi. assert (CR : 4096 <= st_ctx st /\ st_ctx st + 160 <= alloc_ceiling) by (split; assumption).
    (nelimp (cls_facts st WF cls Hc) 14%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14).
    assert (G1 : 17594333495296 <= RB) by exact Q1. assert (G2 : st_pbase st <= RB) by exact Q2. assert (G3 : RB + 4294967296 <= ris st) by exact Q3.
    assert (G4 : ris st + 4096 <= st_pbase st + 137439023104) by exact Q4. assert (G5 : st_pbase st + 137439023104 <= alloc_ceiling) by exact Q5.
    assert (G6 : 0 <= r_allocated r <= r_mapped r) by exact Q6. assert (G7 : r_mapped r <= 3758096384) by exact Q7.
    assert (G8 : 0 <= nf) by exact Q8. assert (G9 : 4 * nf <= fam) by exact Q9. assert (G10 : fam <= 536870912) by exact Q10.
    assert (G11 : hideP (RB mod 8 = 0)) by exact Q11. assert (G12 : hideP (r_mapped r mod 8 = 0)) by exact Q12.
    assert (EFA : FA = RB + 3758096384) by exact Q13. assert (ERC : Rc = ris st + 128 * cls) by exact Q14.
    clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14.
    (nelimp (S_range st WF) 3%nat; intros SR1' SR2' SR3'). assert (SR1 : st_pbase st <= S) by exact SR1'. assert (SR2 : S + 137438953472 + 4096 <= st_pbase st + 137439023104) by exact SR2'.
    assert (SR3 : hideP (S mod 4096 = 0)) by exact SR3'. clear SR1' SR2' SR3'.
    assert (SAL : hideP (S mod 65536 = 0)) by exact (wb_S_align st (wf_base_ok st WF)).
    (nelimp (P_range st WF) 3%nat; intros PR1' PR2' PR3'). assert (PR1 : 17594333495296 <= st_pbase st) by exact PR1'. assert (PR2 : st_pbase st + 137439023104 <= alloc_ceiling) by exact PR2'.
    clear PR1' PR2' PR3'.
    assert (ERB : RB = S + cls * 4294967296) by (unfold RB; rewrite (rbeg_val st); reflexivity).
    assert (ERIS : ris st = S + 137438953472) by reflexivity.
    pose proof (wf_class_ok st WF cls Hcls) as WC.
    assert (FAL : hideP (fam mod 262144 = 0)) by exact (wc_fa_align st cls WC). assert (FA0 : 0 <= fam) by exact (wc_fa_nonneg st cls WC).
    pose proof (cmaxcount_range cls ltac:(plia)) as [CMR CME']. assert (CME : cmaxcount cls = 2 * n) by exact CME'. clear CME'.
    pose proof (wc_cache_max st cls WC) as CMX'. assert (CMX : cnt <= cmaxcount cls) by exact CMX'. clear CMX'. pose proof (zlen_nonneg C) as CNT0'. assert (CNT0 : 0 <= cnt) by exact CNT0'. clear CNT0'.
    pose proof (nf_cnt_bound st cls WF Hc) as [NC1' NC2]. assert (NC1 : nf + cnt <= ncarved st cls) by exact NC1'. clear NC1'.
    pose proof (csize_pos cls ltac:(plia)) as CP. pose proof (csize_le64k' cls Hc) as CL.
    assert (PCB : pc = P + 80 * cls /\ P = t + 208) by (split; reflexivity). destruct PCB as [EPC EP].
    assert (TAL : hideP (t mod 4096 = 0)) by (pose proof (wb_t_loose st (wf_base_ok st WF)) as TL; (nelim (loose0_range st WF t 4096 TL) 4%nat; intros _ _ _ X); exact X).
    assert (TDJ : hideP (t + 4096 <= st_pbase st \/ st_pbase st + 137439023104 <= t)) by
      (pose proof (loose_vs_prim st WF t 4096 (wb_t_loose st (wf_base_ok st WF))) as H0; assert (H : st_pbase st + 137439023104 <= t \/ t + 4096 <= st_pbase st) by exact H0; unfold hideP; clear -H; plia).
    assert (CDJ : hideP (st_ctx st + 160 <= st_pbase st \/ st_pbase st + 137439023104 <= st_ctx st)) by
      ((nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros b kk Hin B1 B2); pose proof (loose_vs_prim st WF b kk Hin) as H0; assert (H : st_pbase st + 137439023104 <= b \/ b + kk <= st_pbase st) by exact H0; unfold hideP; clear -H B1 B2; plia).
    assert (HK : carved_cptr st cls k) by
      (apply (wc_used_carved st cls WC); unfold used_cptrs; rewrite !in_app_iff; do 5 right; unfold apend_cptrs; apply in_map_iff; exists (cls, k); split; [reflexivity|];
       apply filter_In; split; [exact HIN| cbn [fst]; apply Z.eqb_refl]).
    pose proof (carved_cptr_small st cls k WF Hc HK) as KR.
    assert (EPK : cptr_addr st cls k = S + cls * 2^32 + 16 * k) by (unfold cptr_addr; fold RB; rewrite ERB; plia).
    (nelim (cd_cells st m cls HR WF Hc) 24%nat; intros jr je js tj1 tj2 sa AC32' AC40' AC48' AC56' MTX' RI24' RIb' TST' SA' VFA' VSF' EN' PCH' PCE' VT' GS' GD' DY').
    assert (AC32 : ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)]) by exact AC32'. assert (AC40 : ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)]) by exact AC40'.
    assert (AC48 : ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 (ris st))]) by exact AC48'. assert (AC56 : ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)]) by exact AC56'.
    assert (MTX : rw_cells bsegs m Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)]) by exact MTX'. assert (RI24 : rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)]) by exact RI24'.
    assert (RIb : rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r)); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]) by exact RIb'.
    assert (TST : rw_cells bsegs m (t + 2872) [C8 tj1; C8 tj2]) by exact TST'. assert (SA : rw_cells bsegs m (P + 2576) [C8 sa]) by (replace (P + 2576) with (st_t st + 2784) by (rewrite EP; unfold t; plia); exact SA').
    assert (VFA : stk bsegs m FA (FA + fam)) by exact VFA'. assert (VSF : stk bsegs m (SH FA) (SH FA + fam / 8)) by exact VSF'.
    assert (EN : forall i, 0 <= i < nf -> rw_cells bsegs m (FA + 4 * i) [W4 (nthz (r_fa r) i 0)]) by exact EN'.
    assert (PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m (P + 80 * c) [C4 (Z_to_bv 64 (zlen (cch st c))); C4 (Z_to_bv 64 (pc_max_count st c)); C8 (Z_to_bv 64 (pc_class_size st c))]) by exact PCH'.
    assert (PCE : forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m (P + 80 * c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)]) by exact PCE'.
    assert (VT : stk bsegs m t (t + 4096)) by exact VT'.
    assert (GS : ro_cells bsegs m GOT_SEALED [C8 (Z_to_bv 64 1)]) by exact GS'. assert (GD : ro_cells bsegs m GOT_DYING [C8 (Z_to_bv 64 A_DYING)]) by exact GD'. assert (DY : ro_cells bsegs m A_DYING [C4 (Z_to_bv 64 0)]) by exact DY'.
    clear AC32' AC40' AC48' AC56' MTX' RI24' RIb' TST' SA' VFA' VSF' EN' PCH' PCE' VT' GS' GD' DY'.
    pose proof (leafc_of_RTREP st m HR) as LC. pose proof (mmap_cells st m HR) as HC.
    pose proof (artcells_icpt m (rtrep_artcells st m HR)) as IC. pose proof (artcells_poison m (rtrep_artcells st m HR)) as PCz.
    assert (E48 : bv_unsigned (wz (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (unfold wz; apply unsigned_lit; plia).
    assert (E112 : bv_unsigned (wz (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (unfold wz; rewrite unsigned_lit by plia; plia). assert (E112' : bv_unsigned (wz (bv_unsigned sp + -48 + -64)) = bv_unsigned sp + -112) by (unfold wz; rewrite unsigned_lit by plia; plia).
    assert (E240 : bv_unsigned (wz (bv_unsigned sp + -112 + -128)) = bv_unsigned sp + -240) by (unfold wz; rewrite unsigned_lit by plia; plia).
    assert (SHFA : hideP (SH (FA + fam) = SH FA + fam / 8 /\ SH FA = SH RB + 469762048 /\ (FA + fam) mod 32768 = 0 /\ 2147450880 <= SH RB /\ SH (RB + 4294967296) = SH RB + 536870912 /\ SH RB + 536870912 <= 17594333495296)) by
      (unfold hideP in G11, FAL, SAL |- *; unfold SH, SHADOW_OFFSET; rewrite EFA;
       assert (RB32 : RB mod 32768 = 0) by (rewrite ERB; clear -SAL Hc; Z.div_mod_to_equations; plia);
       assert (RBH : RB + 4294967296 + 4096 <= alloc_ceiling) by (clear -G3 G4 G5; plia);
       clear -RB32 RBH FAL FA0 G1 G10; Z.div_mod_to_equations; plia).


    pose proof (nrefill_eq cls ltac:(plia)) as [_ NR']. assert (NR : 1 <= n <= 8) by exact NR'. clear NR'.
    unfold hideP in SHFA. (nelim SHFA 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6). unfold hideP in TDJ. unfold hideP in CDJ.
    pose proof (rt_SH_mono (RB + r_mapped r) FA ltac:(plia)) as SHM.
    pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT0. assert (CT : st_ctx st + 160 <= t \/ t + 4096 <= st_ctx st) by exact CT0. clear CT0.
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { subst ENTRY. eapply (cd_pro ra sp gp tp) with (lo := lo); [exact MI| exact ST| exact HCE| plia| exact Hc| plia| plia| rewrite EPK; plia]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 7%nat; intros m1 -> MU1 WM1 MI1 ST1 FR1). rewrite <- EPC, EPK.
    pose proof AC32 as AC32_1. xro AC32_1 MU1. pose proof SA as SA1. xrw SA1 MU1 WM1.
    pose proof VT as VT1. xst VT1 MU1 WM1.
    assert (PCH1 : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m1 (P + 80 * c) [C4 (Z_to_bv 64 (zlen (cch st c))); C4 (Z_to_bv 64 (pc_max_count st c)); C8 (Z_to_bv 64 (pc_class_size st c))]).
    { intros c Hc'. pose proof (PCH c Hc') as X. unfold KNUMCLASSES in Hc'. xrw X MU1 WM1. exact X. }
    (* [comment removed for export] *)
    assert (FIN : forall (mP m' : word -> option byte) (WP : list (Z * Z)) (q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (sa' : word),
      cnt <> cmaxcount cls ->
      munch WP m mP -> wmono bsegs m mP ->
      (WP = [(lo, bv_unsigned sp)] \/ (WP = [(lo, bv_unsigned sp); (P + 80, P + 2560)] /\ st_cache_inited st = false)) ->
      munch [(lo, bv_unsigned sp); (pc, pc + 4); (pc + 4 * cnt + 16, pc + 4 * cnt + 20); (P + 2576, P + 2584)] mP m' -> wmono bsegs mP m' ->
      mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) ->
      rw_cells bsegs m' pc [C4 (Z_to_bv 64 (cnt + 1)); C4 (Z_to_bv 64 (cmaxcount cls)); C8 (Z_to_bv 64 (csize cls))] ->
      rw_cells bsegs m' (pc + 4 * cnt + 16) [C4 (Z_to_bv 64 k)] ->
      (forall c, 0 <= c < KNUMCLASSES -> c <> cls -> rw_cells bsegs mP (P + 80 * c) [C4 (Z_to_bv 64 (zlen (cch st c))); C4 (Z_to_bv 64 (if c =? 0 then 0 else cmaxcount c)); C8 (Z_to_bv 64 (if c =? 0 then 0 else csize c))]) ->
      WPOST (MS (mkR ra sp gp tp q5 q6 q7 s0 s1 q10 q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31) F (ret_pc ra) fc None m' (seg_rom bsegs)) mo (mkG G R)).
    { intros mP m' WP q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 sa' ROOM MUP WMP HWP MU' WM' MI' ST' PCC' SLOT' PCHP.
      set (W := [(lo, bv_unsigned sp); (P + 80, P + 2560); (pc + 4 * cnt + 16, pc + 4 * cnt + 20); (t + 2768, t + 2896)]).
      assert (MUW : munch W m m').
      { subst W. eapply munch_trans; [eapply munch_weaken; [| exact MUP]| eapply munch_weaken; [| exact MU']]; [destruct HWP as [->|[-> _]]|]; clear -EP EPC Hc CMX CMR; subfp. }
      assert (WMW : wmono bsegs m m') by (eapply wmono_trans; [exact WMP| exact WM']).
      unfold WPOST, cd_wpost. cbv beta.
      exists q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, m', false, false, W, jr, je, js.
      cbv zeta. cbv iota. fold C cnt n nf r. fold fam FA. cbv beta iota delta [cd_fam'].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MUW|]. split; [exact WMW|].
      split.
      { subst W. unfold pz_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; fold t; change (rinfo st cls) with Rc; change (rbeg st cls) with RB; change (fabeg st cls) with FA;
          change (num_freed st cls) with nf; change (rg st cls) with r; unfold T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL; change (2 ^ 32) with 4294967296.
        - right. left. plia.
        - left. plia.
        - left. plia.
        - left. plia. }
      split.
      { subst W. intros a iv Hiv Ha. unfold primary_fp, fp_class, fp_tpage, in_ivs. cbn [app]. fold t. change (rinfo st cls) with Rc. change (rbeg st cls) with RB. unfold KREGIONSIZE.
        cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha.
        - left. exact Ha.
        - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia].
        - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia].
        - right. exists t, (t + 4096). split; [do 3 right; left; reflexivity| plia]. }
      split.
      { subst W. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL; intros; plia. }
      split; [intros X; discriminate X|].
      split; [intros _; split; [exact ROOM| reflexivity]|].
      split.
      { pose proof MTX as MTX'. xrwk ltac:(cut_to HCEn G2 G3 ERC SR2 PR2 ERB ERIS CMR CMX CNT0 EPC EP TDJ) MTX' MUW WMW. pose proof RI24 as RI'. xrwk ltac:(cut_to HCEn G2 G3 ERC SR2 PR2 ERB ERIS CMR CMX CNT0 EPC EP TDJ) RI' MUW WMW. pose proof RIb as RIb'. xrwk ltac:(cut_to HCEn G2 G3 ERC SR2 PR2 ERB ERIS CMR CMX CNT0 EPC EP TDJ) RIb' MUW WMW.
        change (rinfo st cls) with Rc. replace (nf + (cnt - cnt)) with nf by plia.
        exact (rinfo_line m' Rc _ _ _ _ _ MTX' RI' RIb' eq_refl eq_refl). }
      split; [eapply stk_wmono_noseg; [exact VFA| exact WMW| unfold AIMG_HI; plia]|].
      split; [eapply stk_wmono_noseg; [exact VSF| exact WMW| unfold AIMG_HI; plia]|].
      split; [intros i Hi; exfalso; plia|].
      split.
      { intros c Hc'. change (pcaddr st c) with (P + 80 * c).
        destruct (Z.eqb_spec c cls) as [->|NE].
        - rewrite <- EPC. replace (cls =? 0) with false by (symmetry; apply Z.eqb_neq; plia). exact PCC'.
        - pose proof (PCHP c Hc' NE) as X. unfold KNUMCLASSES in Hc'. xrwk ltac:(cut_to HCEn TR CMR CMX CNT0 EPC EP ROOM Hc' NE) X MU' WM'. exact X. }
      split.
      { intros i Hi. change (pcaddr st cls) with pc.
        destruct (Z_lt_le_dec i cnt) as [LT|GE].
        - pose proof (PCE cls i Hcls ltac:(change (zlen (cch st cls)) with cnt; plia)) as X. unfold KNUMCLASSES in Hcls.
          destruct HWP as [->|[-> EI0]]; [| exfalso; pose proof (wb_uninit st (wf_base_ok st WF) EI0 cls) as E0; unfold cnt, C in LT; rewrite E0 in LT; change (@zlen Z []) with 0 in LT; plia].
          xrw X MUP WMP. xrw X MU' WM'.
          rewrite nthz_app_l by (unfold zlen; rewrite length_firstn; unfold cnt, zlen in CMX, LT |- *; plia). rewrite nthz_firstn by plia.
          rewrite EPC. exact X.
        - replace i with cnt by plia. rewrite nthz_app_r by (unfold zlen; rewrite length_firstn; unfold cnt, zlen; plia).
          replace (cnt - zlen (firstn (Z.to_nat cnt) C)) with 0 by (unfold zlen; rewrite length_firstn; unfold cnt, zlen; plia).
          cbn [nthz Z.ltb Z.to_nat nth]. replace (pc + 16 + 4 * cnt) with (pc + 4 * cnt + 16) by plia. exact SLOT'. }
      split.
      { intros c i Hc' NE Hi. change (pcaddr st c) with (P + 80 * c).
        pose proof (PCE c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16. unfold KNUMCLASSES in Hc'.
        destruct HWP as [->|[-> EI0]].
        - xrw X MUP WMP. xrwk ltac:(cut_to HCEn TR CMR CMX CNT0 EPC EP Hc' NE Hi CM CM16) X MU' WM'. exact X.
        - exfalso. pose proof (wb_uninit st (wf_base_ok st WF) EI0 c) as E0. rewrite E0 in Hi. change (@zlen Z []) with 0 in Hi. plia. }
      split; [exact HM|]. split; [eapply GWIN_mem; [exact HG| exact HOK| exact WMW]|]. split; [exact HFR|]. split; [exact HSW|].
      split; [intros w Hw; exact Hw|]. cbn [g_res]. plia. }
    destruct (st_cache_inited st) eqn:EI.
    - (* [comment removed for export] *)
      assert (PCC1 : rw_cells bsegs m1 pc [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (cmaxcount cls)); C8 (Z_to_bv 64 (csize cls))]).
      { pose proof (PCH1 cls Hcls) as X. unfold pc_max_count, pc_class_size in X. rewrite EI in X. replace (cls =? 0) with false in X by (symmetry; apply Z.eqb_neq; plia). cbn [andb negb] in X.
        rewrite <- EPC in X. exact X. }
      destruct (Z.eq_dec cnt (cmaxcount cls)) as [FULL|ROOM].
      + (* [comment removed for export] *)
        assert (EN2 : cmaxcount cls / 2 = n) by (rewrite CME, Z.mul_comm; apply Z.div_mul; plia).
        eapply lscps_evt_then.
        { eapply (cd_chk_full ra) with (mc := cmaxcount cls) (csz := csize cls); [exact MI1| rewrite <- FULL at 1; exact PCC1| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR G2 G3 SR2 ERB ERIS EPC EP] plia)| idtac; plia| plia]. }
        cbv beta. intros ms2 ->.
        eapply lscps_evt_then. { eapply cd_call_drain. exact MI1. } cbv beta. intros ms2 ->.
        (* [comment removed for export] *)
        eapply lscps_evt_then.
        { eapply (drain_pre (wz 0x3472c) (wz (bv_unsigned sp + -48)) gp tp) with (lo := lo) (P := P) (c := cls) (cnt := cmaxcount cls) (mc := cmaxcount cls) (csz := csize cls);
            [exact MI1| stkx ST1| exact HCE| ulia| rewrite <- FULL at 1; exact PCC1| exact EPC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR EP] plia)| idtac; plia| exact Hc| plia| plia| rewrite EN2; plia]. }
        cbv beta. rewrite E48, EN2. replace (cmaxcount cls - n) with (cnt - n) by plia. replace (bv_unsigned sp + -48 + -64) with (bv_unsigned sp + -112) by plia.
        intros ms3 nelH_; (nelim nelH_ 9%nat; intros j2 m2 -> MU2 WM2 MI2 ST2 FR2 PCC2).
        (* [comment removed for export] *)
        pose proof MTX as MTX2. xrw MTX2 MU1 WM1. xrwk ltac:(cut_to HCEn G2 G3 ERC SR2 PR2 ERB ERIS EPC EP TDJ) MTX2 MU2 WM2.
        pose proof AC32_1 as AC32_2. xrok ltac:(cut_to HCEn TRi CRb CRi G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 CMR EPC EP TDJ CDJ SH3 CT) AC32_2 MU2. pose proof AC48 as AC48_2. xro AC48_2 MU1. xrok ltac:(cut_to HCEn TRi CRb CRi G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 CMR EPC EP TDJ CDJ SH3 CT) AC48_2 MU2.
        eapply lscps_evt_then.
        { eapply (rta_A (wz 0x34974) (wz (bv_unsigned sp + -112)) gp tp) with (lo := lo) (S := S) (RIS := ris st) (Rc := Rc) (RB := RB) (c := cls) (n := n) (nf := nf) (sem := wz 0);
            [exact MI2| stkx ST2| exact HCE| ulia| exact AC32_2| exact AC48_2| exact MTX2| exact ERC| exact ERB| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia
            | rewrite ERIS; unfold hideP in SR3; clear -SR3; Z.div_mod_to_equations; plia| exact Hc| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| plia| exact NR| ulia| plia| plia]. }
        cbv beta. unfold rta_A_post. rewrite E112. intros ms4 nelH_; (nelim nelH_ 16%nat; intros x5 x6 x7 x28 x29 x30 x31 j3 m3 -> MU3 WM3 MI3 ST3 FR3 MTX3).
        (* [comment removed for export] *)
        assert (MU03 : munch [(lo, bv_unsigned sp); (pc, pc + 4); (Rc, Rc + 8)] m m3).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]]; clear -LO2; subfp. }
        assert (WM03 : wmono bsegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
        assert (HI3 : Forall outI [(lo, bv_unsigned sp); (pc, pc + 4); (Rc, Rc + 8)]) by (unfold outI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI; (cut_on [HCEn CMR TRi CRb CRi G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 EPC EP TDJ CDJ SH3 CT ERC SR1] plia)).
        pose proof (icpt_cells_out _ _ _ MU03 HI3 IC) as IC3. pose proof (poison_cells_out _ _ _ MU03 HI3 PCz) as PC3. pose proof (mmap_consts_out _ _ _ MU03 HI3 HC) as HC3.
        assert (LC3 : leafc st m3).
        { eapply (leafc_munch st _ _ _ MU03 WM03); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
          destruct Hin as [E|[E|[E|[]]]]; injection E; intros; subst;
          destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; (cut_on [HCE CR G1 TRi G2 G3 SR2 ERB ERIS EPC EP CDJ CT ERC] plia). }
        pose proof RI24 as RI24_3. xrwk ltac:(cut_to HCEn G2 G3 ERC SR2 PR2 ERB ERIS EPC EP TDJ) RI24_3 MU03 WM03. pose proof AC56 as AC56_3. xrok ltac:(cut_to HCEn TRi G1 G2 G3 ERC SR2 ERB ERIS EPC EP) AC56_3 MU03. pose proof TST as TST3. xrwk ltac:(cut_to HCEn TR G2 G3 ERC SR2 ERB ERIS EPC EP TDJ) TST3 MU03 WM03.
        pose proof FR1 as FR1_3. xrw FR1_3 MU2 WM2. xrw FR1_3 MU3 WM3. pose proof FR2 as FR2_3. xrw FR2_3 MU3 WM3.
        pose proof PCC2 as PCC3. xrwk ltac:(cut_to HCEn TRb TR CRb CR G1 G2 G3 EFA ERC SR1 SR2 PR1 PR2 ERB ERIS FA0 CMR EPC EP TDJ CDJ SH3 CT) PCC3 MU3 WM3.
        pose proof GS as GS3. unfold GOT_SEALED in GS3. xrok ltac:(cut_to HCEn TRi G1 G2 G3 ERC SR2 ERB ERIS EPC EP) GS3 MU03. pose proof GD as GD3. unfold GOT_DYING in GD3. xrok ltac:(cut_to HCEn TRi G1 G2 G3 ERC SR2 ERB ERIS EPC EP) GD3 MU03. pose proof DY as DY3. unfold A_DYING in DY3 at 1. xrok ltac:(cut_to HCEn TRi G1 G2 G3 ERC SR2 ERB ERIS EPC EP) DY3 MU03.
        assert (SZ : fam < 4 * (nf + n) -> (4 * (nf + n) + 262143) / 262144 * 262144 = fam + 262144).
        { intros LT. unfold hideP in FAL. clear -LT FAL G9 NR FA0. Z.div_mod_to_equations. nia. }
        assert (LR : fam < 4 * (nf + n) -> LUMPF <= R).   (* [comment removed for export] *)
        { intros LT. pose proof (prov_cls_le' st cls WF Hc) as PL.
          assert (PF : LUMPF <= provF st cls).
          { unfold provF, fa_cap. change (rg st cls) with r. fold fam.
            assert (LT4 : fam / 4 < ncarved st cls) by (assert (fam < 4 * (nf + cnt)) by (clear -LT FULL CME NR; plia); clear -H NC1 FA0; Z.div_mod_to_equations; plia).
            unfold FAPROV. clear -LT4. plia. }
          assert (PU : 0 <= provU st cls) by (unfold provU; plia). plia. }
        assert (SHRNG : forall x : word, SH (RB + KFREEARRAY_OFF + fam) <= bv_unsigned x < SH (RB + KFREEARRAY_OFF + fam) + ((4 * (nf + n) + 262143) / 262144 * 262144 - fam) / 8 ->
                         KHIGHSHADOW_BEG <= bv_unsigned x < KHIGHMEM_BEG).
        { intros x Hx. unfold KFREEARRAY_OFF, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI in *. rewrite <- EFA in Hx. rewrite SH1 in Hx.
          destruct (Z_lt_le_dec fam (4 * (nf + n))) as [LT|GE].
          - rewrite (SZ LT) in Hx. replace ((fam + 262144 - fam) / 8) with 32768 in Hx by (clear; Z.div_mod_to_equations; plia).
            assert (FB : fam + 262144 <= 536870912) by (unfold hideP in FAL; clear -LT NC1 NC2 FULL CME NR FAL G8 CNT0; Z.div_mod_to_equations; plia).
            unfold SH, SHADOW_OFFSET in *. clear -Hx SH2 SH4 SH6 FA0 FB G1. Z.div_mod_to_equations. plia.
          - exfalso. assert (LE : (4 * (nf + n) + 262143) / 262144 * 262144 - fam <= 0) by (unfold hideP in FAL; clear -GE FAL G9 G8 NR FA0; Z.div_mod_to_equations; nia).
            clear -Hx LE. Z.div_mod_to_equations. plia. }
        eapply (efa_spec poison_shadow_ok) with (st := st) (fam := fam) (lo := lo) (tj1 := tj1) (tj2 := tj2) (spin := true) (n := nf + n) (G := G) (R := R);
          [exact HC3| exact IC3| exact PC3| exact LC3| exact WF| exact TP| exact MI3| stkx ST3| split; [exact HCE| unfold EFA_STACK; ulia]
          | exact RI24_3| exact AC56_3| exact TST3
          | change (st_t st) with t; unfold KHIGHMEM_BEG, AIMG_HI; idtac; repeat split; (cut_on [G1 ERC ERIS Hc G2 SR2 PR2 G3 TDJ CDJ] plia)
          | change (st_t st) with t; unfold KHIGHMEM_BEG, AIMG_HI; idtac; repeat split; try (cut_to G1 SR2 PR2 Hc G2 ERB TDJ CDJ; plia); rewrite ERB; unfold hideP in SAL; clear -SAL Hc; Z.div_mod_to_equations; plia
          | plia
          | unfold hideP in FAL; repeat split; plia
          | exact HOK
          | | | | | | | ].
        * (* [comment removed for export] *) intros LT. rewrite (SZ LT). replace (fam + 262144 - fam) with 262144 by plia. unfold KFREEARRAY_OFF.
          apply (prim_fixed_site mo (RB + 3758096384 + fam) 262144 HOK ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL; plia) st HM); unfold PRIM_RES_SIZE, CEIL; try plia;
            rewrite ERB; unfold hideP in FAL, SR3; clear -FAL SR3 Hc; Z.div_mod_to_equations; plia.
        * (* [comment removed for export] *) intros x Hx. (nelimp HM 8%nat; intros _ _ _ _ _ _ LZ _). apply LZ. right. revert x Hx. exact SHRNG.
        * (* [comment removed for export] *) intros x Hx L Wx. apply (GWIN_mem _ _ _ _ _ HG HOK WM03 x (or_introl Wx) L). right. left. exact (SHRNG x Hx).
        * (* [comment removed for export] *) intros LT. rewrite (SZ LT). replace (fam + 262144 - fam) with 262144 by plia. change (262144 + 262144 / 8) with LUMPF.
          pose proof (prov_cls_le' st cls WF Hc) as PL.
          assert (PF : LUMPF <= provF st cls).
          { unfold provF, fa_cap. change (rg st cls) with r. fold fam.
            assert (LT4 : fam / 4 < ncarved st cls) by (assert (fam < 4 * (nf + cnt)) by (clear -LT FULL CME NR; plia); clear -H NC1 FA0; Z.div_mod_to_equations; plia).
            unfold FAPROV. clear -LT4. plia. }
          assert (PU : 0 <= provU st cls) by (unfold provU; plia). plia.
        * (* [comment removed for export] *)
          intros GE y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m4 MI4 MU4 WM4 ST4 RI4. cbv beta delta [wz].
          replace (ret_pc (Z_to_bv 64 0x34c18)) with (wz 0x34c18) by (unfold wz; symmetry; apply ret_pc_even; [plia| reflexivity]).
          rewrite E240 in MU4, ST4.
          pose proof FR1_3 as FR1_4. xrw FR1_4 MU4 WM4. pose proof FR2_3 as FR2_4. xrw FR2_4 MU4 WM4. pose proof FR3 as FR3_4. xrw FR3_4 MU4 WM4.
          pose proof MTX3 as MTX4. xrw MTX4 MU4 WM4. pose proof PCC3 as PCC4. xrw PCC4 MU4 WM4. pose proof TST3 as TST4. xrw TST4 MU4 WM4.
          replace (Z_to_bv 64 (RB + KFREEARRAY_OFF)) with (wz FA) by (unfold KFREEARRAY_OFF; rewrite EFA; reflexivity).
          eapply (cd_tail false m4 mo G R) with (j2 := j2) (j3 := j3) (tj1 := tj1) (tj2 := tj2);
            [exact EI| exact FULL| exact MI4
            | cbn [cd_fam']; eapply munch_trans; [eapply munch_weaken; [| exact MU03]| eapply munch_weaken; [| exact MU4]]; clear -LO2 FA0 G9; subfp
            | eapply wmono_trans; [exact WM03| exact WM4]| exact ST4| rwx FR1_4| rwx FR2_4| rwx FR3_4| exact MTX4| cbn [cd_fam']; exact RI4| exact PCC4| exact TST4
            | cbn [cd_fam']; apply stk_empty; plia| intros X; discriminate X| intros X; discriminate X| intros _; exact GE
            | exact HM| eapply GWIN_mem; [exact HG| exact HOK| eapply wmono_trans; [exact WM03| exact WM4]]| exact HFR| exact HSW| intros w Hw; exact Hw| cbn; plia| exact HOK].
        * (* [comment removed for export] *) exact I.
        * (* [comment removed for export] *)
          intros LT y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m4 tj1' tj2' MI4 MU4 WM4 ST4 RI4 VU4 SHU4 TST4. cbv beta delta [wz].
          replace (ret_pc (Z_to_bv 64 0x34c18)) with (wz 0x34c18) by (unfold wz; symmetry; apply ret_pc_even; [plia| reflexivity]).
          rewrite (SZ LT) in MU4, RI4, VU4, SHU4 |- *.
          repeat match goal with H : context [fam + 262144 - fam] |- _ => replace (fam + 262144 - fam) with 262144 in H by plia end.
          replace (fam + 262144 - fam) with 262144 by plia. change (262144 / 8) with 32768 in *.
          unfold KFREEARRAY_OFF in MU4, VU4, SHU4 |- *. rewrite <- EFA in MU4, VU4, SHU4 |- *. rewrite SH1 in MU4, SHU4 |- *.
          rewrite E240 in MU4, ST4.
          pose proof FR1_3 as FR1_4. xrw FR1_4 MU4 WM4. pose proof FR2_3 as FR2_4. xrw FR2_4 MU4 WM4. pose proof FR3 as FR3_4. xrw FR3_4 MU4 WM4.
          pose proof MTX3 as MTX4. xrwk ltac:(cut_to Hc HCEn G1 G2 G10 EFA ERC SR2 PR2 ERB ERIS TDJ SH2 SH6) MTX4 MU4 WM4. pose proof PCC3 as PCC4. xrwk ltac:(cut_to Hc HCEn TRb TR G2 G3 G8 G9 EFA ERC SR2 ERIS CME NC2 NC1 EPC EP TDJ SH2 SH4 SH6 FULL SZ LT) PCC4 MU4 WM4.
          assert (VW : forall x : word, SH FA + fam / 8 <= bv_unsigned x < SH FA + fam / 8 + 32768 -> m4 x <> None).
          { apply (stk_of_rw_cellsZ _ _ _ 32768) in SHU4 as VSH; [| cbn; plia]. exact (vis_bytes m4 _ _ VSH ltac:(unfold AIMG_HI; plia)). }
          eapply (cd_tail true m4 (mm_commit (wz (FA + fam)) (wz 262144) mo) ((SH FA + fam / 8, SH FA + fam / 8 + 32768) :: G) (R - 262144 - 32768)) with (j2 := j2) (j3 := j3) (tj1 := tj1') (tj2 := tj2');
            [exact EI| exact FULL| exact MI4
            | cbn [cd_fam']; eapply munch_trans; [eapply munch_weaken; [| exact MU03]| eapply munch_weaken; [| exact MU4]]; clear -LO2 FA0 G9 FAL; unfold hideP in FAL; subfp
            | eapply wmono_trans; [exact WM03| exact WM4]| exact ST4| rwx FR1_4| rwx FR2_4| rwx FR3_4| exact MTX4| cbn [cd_fam']; exact RI4| exact PCC4| exact TST4
            | cbn [cd_fam']; replace (FA + (fam + 262144)) with (FA + fam + 262144) by plia; exact VU4
            | intros _; cbn [cd_fam']; exact SHU4
            | intros _; exact LT| intros X; discriminate X
            | apply (RTMODEL_commit mo (FA + fam) 262144 HOK ltac:(unfold KHIGHMEM_BEG, AIMG_HI, RT_artF.CEIL; plia) st HM)
            | apply (GWIN_commit mo (FA + fam) 262144 HOK ltac:(unfold KHIGHMEM_BEG, AIMG_HI, RT_artF.CEIL; plia) st m4);
              eapply (GWIN_open st m4 mo G R); [eapply GWIN_mem; [exact HG| exact HOK| eapply wmono_trans; [exact WM03| exact WM4]]| intros x Hx _ _; exact (VW x Hx)]
            | apply FRONTR_commit; eapply FRONTR_le; [exact HFR| pose proof (LR LT) as LRq; unfold LUMPF, LUMPU in LRq; plia| plia]
            | eapply SWIN_mono; [exact HSW| intros w Hw; cbn; right; exact Hw]
            | intros w Hw; cbn; right; exact Hw
            | unfold LUMPF, LUMPU; plia
            | apply mm_commit_LOK; exact HOK].
      + (* [comment removed for export] *)
        eapply lscps_evt_then.
        { eapply (cd_chk_room ra) with (cnt := cnt) (mc := cmaxcount cls); [exact MI1| exact PCC1| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR CRb CRi G1 G2 G3 EFA SR2 PR1 ERB ERIS FA0 CMX EPC EP TDJ CDJ SH3 CT ROOM] plia)| idtac; plia| plia| plia| exact ROOM]. }
        cbv beta. intros ms2 ->.
        destruct (vis_c4 m1 t (t + 4096) (pc + 4 * cnt + 16) VT1 ltac:(plia) ltac:(plia)) as [slot SLOT].
        eapply lscps_evt_then.
        { eapply (cd_push _ sp gp tp) with (lo := lo) (S := S) (P := P) (pc := pc) (c := cls) (k := k) (cnt := cnt);
            [exact MI1| exact ST1| exact HCE| plia| exact FR1| exact AC32_1| exact PCC1| exact SLOT| exact SA1
            | exact EPC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR CRb CRi G1 EFA PR1 FA0 CMX EP TDJ CDJ SH3 CT ROOM] plia)| idtac; plia| unfold hideP in TAL; clear -TAL EP; Z.div_mod_to_equations; plia| exact Hc
            | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| exact KR| (cut_on [TRb TRi CRb CRi G1 EFA PR1 FA0 CMR CMX CNT0 TDJ CDJ SH3 CT ROOM] plia)| plia]. }
        cbv beta. intros ms3 nelH_; (nelim nelH_ 25%nat; intros q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3 sa' -> MU3 WM3 MI3 ST3 PCC3 SLOT3 SA3).
        apply lscps_done. eapply (FIN m1 m3 [(lo, bv_unsigned sp)]) with (sa' := sa'); [exact ROOM| exact MU1| exact WM1| left; reflexivity| exact MU3| exact WM3| exact MI3| exact ST3| exact PCC3| exact SLOT3|].
        intros c Hc' NE. pose proof (PCH1 c Hc') as X. unfold pc_max_count, pc_class_size in X. rewrite EI in X. cbn [andb] in X. destruct (Z.eqb_spec c 0); cbn [negb] in X; exact X.
    - (* [comment removed for export] *)
      pose proof (wb_uninit st (wf_base_ok st WF) EI) as CE.
      assert (CNT : cnt = 0) by (unfold cnt, C; rewrite (CE cls); reflexivity).
      assert (PCH0 : forall c', 1 <= c' <= 31 -> rw_cells bsegs m1 (P + 80 * c') [C4 (wz 0); C4 (wz 0); C8 (wz 0)]).
      { intros c' Hc'. pose proof (PCH1 c' ltac:(unfold KNUMCLASSES; plia)) as X. rewrite (CE c') in X. change (@zlen Z []) with 0 in X. unfold pc_max_count, pc_class_size in X. rewrite EI in X. cbn [andb] in X. exact X. }
      eapply lscps_evt_then.
      { eapply (cd_init ra) with (P := P) (pc := pc) (c := cls); [exact MI1| exact EPC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR CRb CRi G1 EFA PR1 FA0 EP TDJ CDJ SH3 CT] plia)| idtac; plia| exact Hc| exact PCH0]. }
      cbv beta. intros ms2 nelH_; (nelim nelH_ 15%nat; intros x5 x6 x7 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 CELLS2).
      pose proof (CELLS2 cls ltac:(plia)) as PCC2. rewrite <- EPC in PCC2.
      pose proof ST1 as ST2. xst ST2 MU2 WM2. pose proof FR1 as FR2. xrw FR2 MU2 WM2. pose proof AC32_1 as AC32_2. xrok ltac:(cut_to TRi CRb CRi G1 EFA PR1 FA0 EP TDJ CDJ SH3 CT) AC32_2 MU2. pose proof SA1 as SA2. xrw SA2 MU2 WM2.
      pose proof VT1 as VT2. eapply (stk_wmono_oclr _ _ _ _) in VT2; [| exact WM2| exact TRo| pose proof ceil_lt64; plia].
      destruct (vis_c4 m2 t (t + 4096) (pc + 4 * 0 + 16) VT2 ltac:(plia) ltac:(plia)) as [slot SLOT].
      eapply lscps_evt_then.
      { eapply (cd_push _ sp gp tp) with (lo := lo) (S := S) (P := P) (pc := pc) (c := cls) (k := k) (cnt := 0);
          [exact MI2| exact ST2| exact HCE| plia| exact FR2| exact AC32_2| unfold wz in PCC2 |- *; exact PCC2| exact SLOT| exact SA2
          | exact EPC| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; (cut_on [TRi TR EP] plia)| idtac; plia| unfold hideP in TAL; clear -TAL EP; Z.div_mod_to_equations; plia| exact Hc
          | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; plia| idtac; plia| exact KR| plia| plia]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 25%nat; intros q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3 sa' -> MU3 WM3 MI3 ST3 PCC3 SLOT3 SA3).
      apply lscps_done. rewrite CNT in FIN.
      eapply (FIN m2 m3 [(lo, bv_unsigned sp); (P + 80, P + 2560)]) with (sa' := sa');
        [plia| eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; clear; subfp| eapply wmono_trans; [exact WM1| exact WM2]| right; split; reflexivity
        | exact MU3| exact WM3| exact MI3| exact ST3| exact PCC3| exact SLOT3|].
      intros c Hc' NE. rewrite (CE c). destruct (Z.eqb_spec c 0) as [->|NZ].
      + pose proof (PCH1 0 Hc') as X. rewrite (CE 0) in X. change (@zlen Z []) with 0 in X |- *. unfold pc_max_count, pc_class_size in X. rewrite EI in X. cbn [andb negb Z.eqb] in X. xrw X MU2 WM2. exact X.
      + pose proof (CELLS2 c ltac:(unfold KNUMCLASSES in Hc'; plia)) as X. change (@zlen Z []) with 0. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; plia). unfold wz in X |- *. exact X.
  Qed.
End CDM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINAL.
  Variables (r1 r2 r3 : Z) (r4 : list region_st) (r5 : bool) (r6 : list (list Z)) (r7 r8 : Z) (r9 : list (Z * Z))
            (r10 r11 : list qbatch) (r12 : depot_st) (r13 r14 : list (list Z)) (r15 : Z) (r16 : list Z) (r17 : list fframe)
            (r18 r19 : Z) (r20 : tls_st) (r21 : list (Z * Z)) (r22 : bool) (r23 : list (Z * Z))
            (q1 q2 q3 : list (Z * Z)) (q4 : list qbatch) (q5 : list (qbatch * Z)).
  Let st := mkRT r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5.
  Lemma cd_final : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (cls k lo : Z),
    RTS st m mo g -> In (cls, k) q1 -> 1 <= cls <= 30 -> tp = wz ATP -> rt_prov st <= g_res g ->
    stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACDEALLOC_STACK -> mem_inv bsegs m ->
    LSCPS bsegs (cdealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls k lo m g)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (acache st)) (wz A_ALLOC) (wz cls) (wz (cptr_addr st cls k)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz ACDEALLOC) fc None m (seg_rom bsegs)) mo g.
  Proof.
    intros until lo. intros (HR & WF & HM & HG & HFR & HSW) HIN Hc TP HPROV ST HCE LO MI. destruct g as [G R]. cbn [g_res] in HPROV, HFR.
    eapply lscps_mono.
    { eapply cd_walk; try eassumption. split; [exact HCE| lia]. }
    cbv beta. intros ms' mo' g' POST. unfold cd_wpost in POST.
    (nelim POST 23%nat; intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' dr fm W jr je js POST). cbv zeta in POST.
    (nelim POST 23%nat; intros -> MI' ST' MU' WM' PZ FRM CE HDR HND RINFO VF1 VF2 FILL PCH PCE PCO HM' HG' HFR' HSW' GM ER).
    Local Ltac dis := try (lazymatch goal with
      | |- RTWF _ => eassumption | |- 1 <= _ <= 30 => eassumption | |- In _ _ => eassumption
      | |- _ = true -> _ => eassumption | |- _ = false -> _ => eassumption
      | |- RTREP _ _ => eassumption | |- munch _ _ _ => eassumption | |- wmono _ _ _ => eassumption | |- Forall _ _ => eassumption end).
    unshelve epose proof (RTWF_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm _ _ _ _ _) as WF'; dis.
    pose proof (cmaxcount_range cls ltac:(lia)) as [CMA CMB]. pose proof (zlen_nonneg (cch st cls)) as Z0.
    pose proof (wc_cache_max st cls (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia))) as CM.
    assert (BR : 0 <= cd_base r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls dr <= zlen (cch st cls)).
    { unfold cd_base. fold st. destruct dr; [destruct (HDR eq_refl) as [E _]| destruct (HND eq_refl) as [E _]]; unfold nrefill; lia. }
    unfold cdealloc_post, rt_post_std. nexists 15%nat. exists m'. eexists.
    split; [reflexivity|]. split; [exact MI'|].
    split. { unshelve eapply (cd_rel r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm); dis. }
    split.
    { apply RTS_intro.
      - unshelve eapply (RTREP_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm _ _ _ _ _ m m' W); dis.
        + exists jr, je, js. unfold rinfo_cells. erewrite (rg_same r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm) by dis. unfold num_freed at 1. erewrite (rg_same r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm) by dis.
          unfold cd_rnew. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa]. rewrite zlen_app. fold st.
          unfold num_freed, cd_fam' in RINFO.
          replace (zlen (skipn (Z.to_nat (cd_base r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls dr)) (cch st cls))) with (zlen (cch st cls) - cd_base r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls dr) by (unfold zlen in *; rewrite length_skipn; lia).
          unfold cd_base. fold st. exact RINFO.
        + unfold cd_fam' in VF1, VF2. split; [exact VF1| exact VF2].
        + unfold cd_base. fold st. exact FILL.
        + intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE].
          * erewrite (cch_same r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm) by dis. rewrite zlen_app. fold st. pose proof (PCH cls Hc') as X. rewrite Z.eqb_refl in X.
            replace (zlen (firstn (Z.to_nat (cd_base r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls dr)) (cch st cls)) + zlen [k]) with (cd_base r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls dr + 1) by (unfold zlen in *; rewrite length_firstn; cbn [length]; lia).
            unfold cd_base. fold st. exact X.
          * erewrite (cch_other r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm c NE) by dis. pose proof (PCH c Hc') as X. replace (c =? cls) with false in X by (symmetry; apply Z.eqb_neq; exact NE). exact X.
        + unfold cd_base. fold st. exact PCE.
        + exact PCO.
      - exact WF'.
      - unshelve eapply (RTMODEL_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm); dis. exact HM'.
      - unshelve eapply (GWIN_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm); dis. exact HG'.
      - exact HFR'.
      - unshelve eapply (SWIN_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm); dis. exact HSW'. }
    split; [exact ST'|].
    split.
    { eapply (cd_cli_pres st WF cls Hc (bv_unsigned sp) ltac:(unfold CEIL; idtac; unfold ACDEALLOC_STACK in LO; lia) W m m' MU' WM').
      apply Forall_forall. intros iv Hiv. split; [exact (proj1 (Forall_forall _ _) PZ iv Hiv)| exact (proj1 (Forall_forall _ _) CE iv Hiv)]. }
    split; [exact (cd_rt_frame (bv_unsigned sp) W m m' lo (primary_fp st cls) MU' FRM)|].
    split; [exact GM|].
    unfold budget_ok. change (g_res (mkG G R)) with R. rewrite ER. first [pose proof (rt_prov_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm WF Hc HDR HND) as PV | pose proof (rt_prov_new r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 q1 q2 q3 q4 q5 cls k dr fm WF Hc HIN HDR HND) as PV].
    fold st in PV |- *. destruct fm; cbv iota in PV |- *; unfold LUMPF, LUMPU in *; lia.
  Qed.
End FINAL.

Theorem cache_dealloc_proof : cache_dealloc_specC.
Proof.
  unfold cache_dealloc_specC. intros until lo. intros RTS0 HIN Hc -> -> -> -> TP HPROV ST HCE LO MI.
  destruct st. eapply cd_final; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac prune :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H
  | H : forall _ : Z, _ |- _ => clear H | H : forall _ : word, _ |- _ => clear H | H : forall _ : nat, _ |- _ => clear H | H : forall _ : bool, _ |- _ => clear H
  | H : forall _ : (word -> option byte), _ |- _ => clear H | H : RTREP _ _ |- _ => clear H | H : RTMODEL _ _ |- _ => clear H | H : GWIN _ _ _ _ |- _ => clear H
  | H : FRONTR _ _ |- _ => clear H | H : SWIN _ _ |- _ => clear H | H : leafc _ _ |- _ => clear H | H : mmap_consts _ |- _ => clear H
  | H : icpt_cells _ |- _ => clear H | H : poison_cells _ |- _ => clear H | H : LOK _ _ |- _ => clear H | H : BINV _ _ |- _ => clear H
  | H : no_wx _ |- _ => clear H | H : In _ _ |- _ => clear H | H : wf_class _ _ |- _ => clear H | H : carved_cptr _ _ _ |- _ => clear H
  | H : hideP _ |- _ => clear H | H : _ = wz _ |- _ => clear H | H : gmono _ _ |- _ => clear H
  end.
Ltac plia := prune; lia.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| plia] end ].
