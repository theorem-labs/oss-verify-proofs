(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_zone RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_refillA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA.RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface RTW_p_refillA RT_grant RT_sec RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_embz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_embz.RT_emb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_embz RT_wokapp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3 RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_ci (st : rtstate) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 true a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 end.
Definition st_exh (st : rtstate) (cls : Z) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 (updz a4 cls (rg_set_exh (nthz a4 cls region0))) a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 end.
Definition st_emb (st : rtstate) (d sz : Z) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    if tl_emb_d a20 =? 0
    then mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 (mkTLS (tl_dtls_block a20) (tl_dtls_w a20) d sz) (a21 ++ [(d, EMB_CAP)]) a22 a23 b1 b2 b3 b4 b5
    else mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 (mkTLS (tl_dtls_block a20) (tl_dtls_w a20) (tl_emb_d a20) sz) a21 a22 a23 b1 b2 b3 b4 b5 end.
(* [comment removed for export] *)
Definition st_fx (st : rtstate) (cls d sz : Z) : rtstate := st_emb (st_exh (st_ci st) cls) d sz.

Lemma updz_nat_id : forall {A} (l : list A) k d, updz_nat l k (nth k l d) = l.
Proof. induction l as [|y l IH]; intros [|k] d; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma updz_nthz_id : forall {A} (l : list A) i d, updz l i (nthz l i d) = l.
Proof. intros A l i d. unfold updz, nthz. destruct (i <? 0); [reflexivity|]. apply updz_nat_id. Qed.

(* [comment removed for export] *)
Lemma r_f_false : forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls,
  updz a4 cls (r_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) = a4.
Proof.
  intros. unfold r_f. cbn [rg st_regions]. rewrite Z.add_0_r.
  replace (mkRegion _ _ _ _ _) with (nthz a4 cls region0); [apply updz_nthz_id|]. unfold rg. cbn [st_regions]. destruct (nthz a4 cls region0); reflexivity.
Qed.

Section CHAIN.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].

Lemma RTWF_ci : RTWF (st_ci st).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci.
  pose proof (RTWF_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma RTMODEL_ci : forall mo, RTMODEL st mo -> RTMODEL (st_ci st) mo.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros mo HM.
  pose proof (RTMODEL_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HM| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma GWIN_ci : forall m mo g, GWIN st m mo g -> GWIN (st_ci st) m mo g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros m mo g HG.
  pose proof (GWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HG| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma SWIN_ci : forall g, SWIN st g -> SWIN (st_ci st) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros g HS.
  pose proof (SWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HS| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma rt_prov_ci : rt_prov (st_ci st) <= rt_prov st.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci.
  pose proof (rt_prov_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. cbn [Z.add] in X. rewrite Z.add_0_r in X.
  apply X; first [exact WF| exact Hc| exact HC0| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
End CHAIN.

(* [comment removed for export] *)
Lemma RTWF_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 ->
  r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls -> RTWF (st_exh st cls).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HX. exact (RTWF_exh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF cls Hc HX). Qed.
Lemma rt_prov_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 ->
  r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls -> rt_prov (st_exh st cls) = rt_prov st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HX. exact (rt_prov_exh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF cls Hc). Qed.
Lemma RTMODEL_exh_g : forall st cls mo, RTWF st -> 1 <= cls <= 31 -> RTMODEL st mo -> RTMODEL (st_exh st cls) mo.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls mo WF Hc HM. eapply RTMODEL_exh; eassumption. Qed.
Lemma GWIN_exh_g : forall st cls m mo g, RTWF st -> 1 <= cls <= 31 -> GWIN st m mo g -> GWIN (st_exh st cls) m mo g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls m mo g WF Hc HG. eapply GWIN_exh; eassumption. Qed.
Lemma SWIN_exh_g : forall st cls g, RTWF st -> 1 <= cls <= 31 -> SWIN st g -> SWIN (st_exh st cls) g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls g WF Hc HS. eapply SWIN_exh; eassumption. Qed.
Lemma nexh_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 -> nexh st <= nexh (st_exh st cls) <= nexh st + 1.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc. eapply nexh_exh_ge; eassumption. Qed.

(* [comment removed for export] *)
Section EMBG.
Variables (st : rtstate) (d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hsz : 0 <= sz <= EMB_MSG * nexh st.
(* [comment removed for export] *)
Hypothesis HN : emb_d st = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).

Lemma RTWF_emb_g : RTWF (st_emb st d sz).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb.
  destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply RTWF_embN; eassumption.
  - eapply RTWF_embA; eassumption.
Qed.
Lemma rt_prov_emb_g : rt_prov (st_emb st d sz) = rt_prov st - (if emb_d st =? 0 then EMB_CAP else 0).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply rt_prov_embN; eassumption.
  - rewrite Z.sub_0_r. eapply rt_prov_embA; eassumption.
Qed.
Lemma RTMODEL_emb_g : forall mo, RTMODEL st mo ->
  RTMODEL (st_emb st d sz) (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  intros mo HM. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply RTMODEL_embN; try eassumption. pose proof (ablk_lin _ _ N2). lia.
  - exact HM.
Qed.
Lemma GWIN_emb_g : forall m mo g, GWIN st m mo g ->
  GWIN (st_emb st d sz) m (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  intros m mo g HG. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - intros x Hw Hz Hr. rewrite mm_add_map_lzf in Hz. exact (HG x Hw Hz Hr).
  - exact HG.
Qed.
Lemma SWIN_emb_g : forall g, SWIN st g -> SWIN (st_emb st d sz) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb.
  intros g HS. destruct (tl_emb_d a20 =? 0); exact HS.
Qed.
End EMBG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FXP.
Variables (st : rtstate) (cls d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.

Lemma fx_rg : forall c, rg (st_fx st cls d sz) c = if c =? cls then rg_set_exh (rg st cls) else rg st c.
Proof.
  intros c. pose proof (wb_len_regions st (wf_base_ok st WF)) as L.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5].
  unfold st_fx, st_emb, st_exh, st_ci. cbn [st_regions] in L. destruct (tl_emb_d a20 =? 0); unfold rg; cbn [st_regions];
    (destruct (Z.eqb_spec c cls) as [->|NE]; [apply nthz_updz_same; unfold zlen; rewrite L; lia| rewrite nthz_updz_other by lia; reflexivity]).
Qed.
Lemma fx_proj : forall c,
  r_allocated (rg (st_fx st cls d sz) c) = r_allocated (rg st c) /\ r_mapped (rg (st_fx st cls d sz) c) = r_mapped (rg st c)
  /\ r_mapped_fa (rg (st_fx st cls d sz) c) = r_mapped_fa (rg st c) /\ r_fa (rg (st_fx st cls d sz) c) = r_fa (rg st c).
Proof. intros c. rewrite fx_rg. destruct (Z.eqb_spec c cls) as [->|NE]; [cbn; repeat split; reflexivity| repeat split; reflexivity]. Qed.
Lemma fx_exhausted : forall c, r_exhausted (rg (st_fx st cls d sz) c) = if c =? cls then true else r_exhausted (rg st c).
Proof. intros c. rewrite fx_rg. destruct (c =? cls); reflexivity. Qed.
Lemma fx_num_freed : forall c, num_freed (st_fx st cls d sz) c = num_freed st c.
Proof. intros c. unfold num_freed. rewrite (proj2 (proj2 (proj2 (fx_proj c)))). reflexivity. Qed.
Lemma fx_cch : forall c, cch (st_fx st cls d sz) c = cch st c.
Proof. intros c. destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_avail : forall c, avail_cptrs (st_fx st cls d sz) c = avail_cptrs st c.
Proof. intros c. unfold avail_cptrs. rewrite (proj2 (proj2 (proj2 (fx_proj c)))), fx_cch. reflexivity. Qed.
End FXP.

(* [comment removed for export] *)
Local Ltac fxconv := intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz m H;
  unfold st_fx, st_emb, st_exh, st_ci; destruct (tl_emb_d a20 =? 0); exact H.
Lemma R_alloc_fx : forall st cls d sz m, R_alloc st m -> R_alloc (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_thread_fx : forall st cls d sz m, R_thread st m -> R_thread (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_live_fx : forall st cls d sz m, R_live st m -> R_live (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_quar_fx : forall st cls d sz m, R_quar st m -> R_quar (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_batches_fx : forall st cls d sz m, R_batches st m -> R_batches (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_ptrarr_fx : forall st cls d sz m, R_ptrarr st m -> R_ptrarr (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_depot_fx : forall st cls d sz m, R_depot st m -> R_depot (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_fs_fx : forall st cls d sz m, R_fs st m -> R_fs (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma fx_ia_inited : forall st cls d sz, st_ia_inited (st_fx st cls d sz) = st_ia_inited st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_cache_inited : forall st cls d sz, st_cache_inited (st_fx st cls d sz) = true.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_geom : forall st cls d sz, st_pbase (st_fx st cls d sz) = st_pbase st /\ st_t (st_fx st cls d sz) = st_t st /\ st_apend (st_fx st cls d sz) = st_apend st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); repeat split; reflexivity. Qed.

Lemma fx_addr : forall st cls d sz,
  ris (st_fx st cls d sz) = ris st /\ (forall c, rinfo (st_fx st cls d sz) c = rinfo st c) /\ (forall c, rbeg (st_fx st cls d sz) c = rbeg st c)
  /\ (forall c, fabeg (st_fx st cls d sz) c = fabeg st c) /\ (forall c, pcaddr (st_fx st cls d sz) c = pcaddr st c)
  /\ (forall c k, cptr_addr (st_fx st cls d sz) c k = cptr_addr st c k) /\ (forall c, apend_cptrs (st_fx st cls d sz) c = apend_cptrs st c).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); repeat split; reflexivity. Qed.

Section XREP.
Variables (st : rtstate) (cls d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Variables (W1 W2 : list (Z * Z)) (elo ehi : Z) (m m' : word -> option byte).
Hypothesis HW1 : Forall (pz_ok st cls) W1.
Hypothesis HBA : ablk elo ehi.
Hypothesis Hz : forall a n, (a + n <= A_EMB \/ A_EMB + 56 <= a) -> a + n <= CEIL -> (a + n <= elo \/ ehi <= a) -> disjoint_from W2 a n.
Hypothesis HBLK : (forall r, In r (rt_ranges st) -> ehi <= fst r \/ snd r <= elo)
               \/ (emb_d st <> 0 /\ elo = emb_d st /\ ehi = emb_d st + EMB_CAP).
Hypothesis HR : RTREP st m.
Hypothesis MU : munch (W1 ++ W2) m m'.
Hypothesis WM : wmono asegs m m'.
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells asegs m' (rinfo st cls) (rinfo_cells (st_fx st cls d sz) cls jr je js).
Hypothesis PCH : pch_at st cls m' 0.
Hypothesis PCO : pco_at st m'.
Hypothesis EMB : R_emb (st_fx st cls d sz) m'.

Let W := W1 ++ W2.
Local Ltac tapp T := first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].

Local Ltac pzz L := first [ exact (L st WF cls Hc W1 HW1) | exact (L st cls W1 HW1) | eapply L; eassumption ].
Local Ltac ezz L := first [ exact (L st WF W2 elo ehi HBA Hz HBLK) | exact (L st WF W2 elo ehi HBA Hz) | exact (L W2 elo ehi HBA Hz) | eapply L; eassumption ].

Lemma T_consts_rest : R_consts_rest st m -> WOK_consts_rest W -> R_consts_rest st m'.
Proof.
  intros H K. unfold R_consts_rest, WOK_consts_rest in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  Local Ltac trx MU WM H K := first [ eapply (roT _ _ _ MU _ _ H); exact K | eapply (rwT _ _ _ MU WM _ _ H); exact K
                           | eapply (roTn _ _ _ MU _ _ _ H); [| exact K]; cbn; lia | eapply (rwTn _ _ _ MU WM _ _ _ H); [| exact K]; cbn; lia ].
  split; [trx MU WM H1 K1|]. split; [trx MU WM H2 K2|]. split; [trx MU WM H3 K3|]. split; [trx MU WM H4 K4|]. split; [trx MU WM H5 K5|]. split; [trx MU WM H6 K6|].
  split; [trx MU WM H7 K7|]. split; [trx MU WM H8 K8|]. split; [trx MU WM H9 K9|]. split; [trx MU WM H10 K10|]. split; [trx MU WM H11 K11|]. split; [trx MU WM H12 K12|].
  split; [trx MU WM H13 K13|]. split; [trx MU WM H14 K14|]. split; [exists oom; trx MU WM H15 K15|]. split; [trx MU WM H16 K16|]. split; [trx MU WM H17 K17|].
  split; [trx MU WM H18 K18|]. split; [trx MU WM H19 K19|]. split; [trx MU WM H20 K20|]. split; [trx MU WM H21 K21|]. split; [trx MU WM H22 K22|]. split; [trx MU WM H23 K23|]. split; [trx MU WM H24 K24|].
  split; [trx MU WM H25 K25|]. split; [trx MU WM H26 K26|]. trx MU WM H27 K27.
Qed.

Theorem RTREP_fx : RTREP (st_fx st cls d sz) m'.
Proof.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (* [comment removed for export] *)
  assert (Y1 : R_link m').
  { tapp T_link; [exact (rr_link st m HR)| apply WOK_link_app; [pzz PZ_link| ezz EZ_link]]. }
  assert (Y3 : R_alloc st m').
  { tapp T_alloc; [exact (rr_alloc st m HR)| apply WOK_alloc_app; [pzz PZ_alloc| ezz EZ_alloc]]. }
  assert (Y5 : R_regions st m').
  { tapp T_regions; [exact (rr_regions st m HR)| apply WOK_regions_app; [pzz PZ_regions| ezz EZ_regions]]. }
  assert (Y6 : R_avail st m').
  { tapp T_avail; [exact (rr_avail st m HR)| apply WOK_avail_app; [pzz PZ_avail| ezz EZ_avail]]. }
  assert (Y8 : R_thread st m').
  { tapp T_thread; [exact (rr_thread st m HR)| apply WOK_thread_app; [pzz PZ_thread| ezz EZ_thread]]. }
  assert (Y9 : R_live st m').
  { tapp T_live; [exact (rr_live st m HR)| apply WOK_live_app; [pzz PZ_live| ezz EZ_live]]. }
  assert (Y10 : R_quar st m').
  { tapp T_quar; [exact (rr_quar st m HR)| apply WOK_quar_app; [pzz PZ_quar| ezz EZ_quar]]. }
  assert (Y11 : R_batches st m').
  { tapp T_batches; [exact (rr_batches st m HR)| apply WOK_batches_app; [pzz PZ_batches| ezz EZ_batches]]. }
  assert (Y12 : R_ptrarr st m').
  { tapp T_ptrarr; [exact (rr_ptrarr st m HR)| apply WOK_ptrarr_app; [pzz PZ_ptrarr| ezz EZ_ptrarr]]. }
  assert (Y13 : R_depot st m').
  { tapp T_depot; [exact (rr_depot st m HR)| apply WOK_depot_app; [pzz PZ_depot| ezz EZ_depot]]. }
  assert (Y14 : R_fs st m').
  { tapp T_fs; [exact (rr_fs st m HR)| apply WOK_fs_app; [pzz PZ_fs| ezz EZ_fs]]. }
  assert (Y15 : R_ia m').
  { tapp T_ia; [exact (rr_ia st m HR)| apply WOK_ia_app; [pzz PZ_ia| ezz EZ_ia]]. }
  assert (Y16 : R_lowshadow m').
  { tapp T_lowshadow; [exact (rr_lowshadow st m HR)| apply WOK_lowshadow_app; [pzz PZ_lowshadow| ezz EZ_lowshadow]]. }
  assert (Y2 : R_consts_rest st m').
  { apply T_consts_rest; [exact (proj1 (R_consts_split st m (rr_consts st m HR)))|].
    apply WOK_consts_rest_app; [apply WOK_consts_rest_of; pzz PZ_consts| ezz EZ_consts_rest]. }
  pose proof (fx_proj st cls d sz WF Hc) as PJ. pose proof (fx_num_freed st cls d sz WF Hc) as NF. pose proof (fx_avail st cls d sz WF Hc) as AV.
  assert (CC : forall c, cch (st_fx st cls d sz) c = cch st c) by (intros c0; apply fx_cch; assumption). pose proof (fx_rg st cls d sz WF Hc) as RG. pose proof (fx_geom st cls d sz) as (GP & GT & GA).
  pose proof (fx_addr st cls d sz) as (AR & AI & AB & AF & AP & ACP & AAP).
  constructor.
  - exact Y1.
  - apply R_consts_join; [apply (R_consts_rest_indep st); [apply fx_ia_inited| exact Y2]| exact EMB].
  - apply R_alloc_fx. exact Y3.
  - (* [comment removed for export] *) destruct (rr_rinfo st m HR) as [VR HLn]. pose proof (ris_range st WF) as (Z1 & Z2 & Z3 & Z4).
    split.
    { rewrite AR. eapply stk_wmono_noseg; [exact VR| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]. }
    intros c Hc'. rewrite AI.
    destruct (Z.eq_dec c cls) as [->|NE]; [exact RINFO|].
    destruct (HLn c Hc') as (jr & je & js & RC). exists jr, je, js.
    replace (rinfo_cells (st_fx st cls d sz) c jr je js) with (rinfo_cells st c jr je js).
    2:{ unfold rinfo_cells. rewrite NF. destruct (PJ c) as (P1 & P2 & P3 & P4). rewrite P1, P2, P3. rewrite (fx_exhausted st cls d sz WF Hc c).
        replace (c =? cls) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. }
    eapply (rw_cells_transport asegs _ m m'); [exact RC| exact MU| exact WM|].
    assert (E128 : Z.of_nat (cells_size (rinfo_cells st c jr je js)) = 128).
    { destruct RC as [[Wf _] _]. cbn in Wf. unfold rinfo_cells. cbn [cells_size Cells.csize]. destruct Wf as (_ & _ & _ & _ & _ & _ & _ & _ & L1 & _ & L2 & L3 & _). lia. }
    rewrite E128. apply dj_app; [pzz PZ_rinfo_other; assumption| exact (EZ_rinfo st WF W2 elo ehi HBA Hz HBLK c Hc')].
  - (* [comment removed for export] *) intros c Hc'. pose proof (Y5 c Hc') as R5. cbn zeta in *. destruct (PJ c) as (P1 & P2 & P3 & P4).
    rewrite AB, AF, P1, P2, P3, P4, NF. exact R5.
  - (* [comment removed for export] *) intros c k Hc' Hk. rewrite AV, AAP in Hk. rewrite ACP. exact (Y6 c k Hc' Hk).
  - (* [comment removed for export] *) intros c Hc'. rewrite AP.
    assert (PM : pc_max_count (st_fx st cls d sz) c = (if c =? 0 then 0 else cmaxcount c)) by (unfold pc_max_count; rewrite fx_cache_inited; destruct (c =? 0); reflexivity).
    assert (PS' : pc_class_size (st_fx st cls d sz) c = (if c =? 0 then 0 else csize c)) by (unfold pc_class_size; rewrite fx_cache_inited; destruct (c =? 0); reflexivity).
    rewrite PM, PS', CC. split.
    + pose proof (PCH c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE]; [rewrite HC0; exact X| exact X].
    + intros i Hi. exact (PCO c i Hc' Hi).
  - apply R_thread_fx. exact Y8.
  - apply R_live_fx. exact Y9.
  - apply R_quar_fx. exact Y10.
  - apply R_batches_fx. exact Y11.
  - apply R_ptrarr_fx. exact Y12.
  - apply R_depot_fx. exact Y13.
  - apply R_fs_fx. exact Y14.
  - exact Y15.
  - exact Y16.
Qed.
End XREP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ci_same : forall st, rt_ranges (st_ci st) = rt_ranges st /\ (forall c, rg (st_ci st) c = rg st c) /\ nexh (st_ci st) = nexh st
  /\ emb_d (st_ci st) = emb_d st /\ emb_sz (st_ci st) = emb_sz st /\ (forall c, cch (st_ci st) c = cch st c).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. repeat split; reflexivity. Qed.
Lemma exh_same : forall st cls, rt_ranges (st_exh st cls) = rt_ranges st /\ emb_d (st_exh st cls) = emb_d st /\ emb_sz (st_exh st cls) = emb_sz st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls. repeat split; reflexivity. Qed.
Lemma nexh_exh_flip : forall st cls, RTWF st -> 1 <= cls <= 31 -> r_exhausted (rg st cls) = false -> nexh (st_exh st cls) = nexh st + 1.
Proof.
  intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HE.
  pose proof (nexh_exh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 WF cls Hc) as X.
  cbv zeta in X. rewrite HE in X. exact X.
Qed.
Lemma fx_emb : forall st cls d sz, (emb_d st <> 0 -> d = emb_d st) -> emb_d (st_fx st cls d sz) = d /\ emb_sz (st_fx st cls d sz) = sz.
Proof.
  intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz H.
  unfold st_fx, st_emb, st_exh, st_ci, emb_d, emb_sz in *. cbn [st_tls] in *. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE]; cbn [st_tls tl_emb_d tl_emb_sz]; [split; reflexivity| split; [symmetry; exact (H NE)| reflexivity]].
Qed.

Section FINX.
Variables (st : rtstate) (cls d sz : Z) (mo mo' : Model) (G : list (Z * Z)) (R R' : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HX : r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls.
Hypothesis HEX : r_exhausted (rg st cls) = false.
Hypothesis HSZ : emb_sz st <= sz <= emb_sz st + EMB_MSG.
Hypothesis HM : RTMODEL st mo.
Hypothesis HOK : LOK asegs mo.
Hypothesis HFR : FRONTR mo R.
Hypothesis HRV : rt_prov st <= R.
Hypothesis STEP : (emb_d st <> 0 /\ d = emb_d st /\ mo' = mo /\ R' = R)
   \/ (emb_d st = 0 /\ d <> 0 /\ mmap_grant mo (wz d) EMB_CAP /\ mo' = mm_add_map (wz d) (wz EMB_CAP) mo /\ R' = R - EMB_CAP).

Let st2 := st_exh (st_ci st) cls.

Hypothesis HD64 : 0 <= d < 2^64.

(* [comment removed for export] *)
Lemma fx_new : emb_d st = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).
Proof.
  intros Z0. destruct STEP as [(NZ & _)|(_ & NZ & GR & _)]; [exfalso; exact (NZ Z0)|].
  pose proof (grant_ablk st mo (wz d) EMB_CAP HOK HM ltac:(unfold EMB_CAP; lia) GR) as BK.
  pose proof (grant_fresh st mo (wz d) EMB_CAP HOK HM WF ltac:(unfold EMB_CAP; lia) GR) as FR.
  destruct GR as (GA & _ & GC & _). unfold wz, page_size in *. rewrite unsigned_lit in * by lia.
  split; [exact GA|]. split; [exact BK|]. split; [unfold CEIL; exact GC| exact FR].
Qed.
Lemma fx_mo : mo' = (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo) /\ R' = R - (if emb_d st =? 0 then EMB_CAP else 0).
Proof.
  destruct STEP as [(NZ & _ & -> & ->)|(Z0 & _ & _ & -> & ->)].
  - replace (emb_d st =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). split; [reflexivity| lia].
  - rewrite Z0. cbn [Z.eqb]. split; reflexivity.
Qed.

Lemma RTWF_st2 : RTWF st2.
Proof.
  destruct (ci_same st) as (_ & RGc & _). apply RTWF_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia| rewrite !RGc; exact HX].
Qed.
Lemma st2_emb : emb_d st2 = emb_d st /\ emb_sz st2 = emb_sz st /\ rt_ranges st2 = rt_ranges st /\ nexh st2 = nexh st + 1.
Proof.
  destruct (ci_same st) as (C1 & C2 & C3 & C4 & C5 & _). destruct (exh_same (st_ci st) cls) as (E1 & E2 & E3). unfold st2.
  rewrite E2, E3, E1, C4, C5, C1. repeat split.
  rewrite (nexh_exh_flip (st_ci st) cls (RTWF_ci st WF cls Hc HC0) ltac:(lia)); [rewrite C3; reflexivity| rewrite C2; exact HEX].
Qed.
Lemma fx_sz : 0 <= sz <= EMB_MSG * nexh st2.
Proof. destruct st2_emb as (_ & _ & _ & NX). rewrite NX. pose proof (wb_emb_sz st (wf_base_ok st WF)) as SZ. unfold EMB_MSG in *. lia. Qed.
Lemma fx_hn : emb_d st2 = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st2) -> d + EMB_CAP <= fst r \/ snd r <= d).
Proof. destruct st2_emb as (E1 & _ & E3 & _). rewrite E1, E3. exact fx_new. Qed.

Theorem RTWF_fx : RTWF (st_fx st cls d sz).
Proof. exact (RTWF_emb_g st2 d sz RTWF_st2 fx_sz fx_hn). Qed.
Theorem RTMODEL_fx : RTMODEL (st_fx st cls d sz) mo'.
Proof.
  rewrite (proj1 fx_mo). destruct st2_emb as (E1 & _). rewrite <- E1.
  apply (RTMODEL_emb_g st2 d sz RTWF_st2 fx_sz fx_hn). apply RTMODEL_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia| eapply RTMODEL_ci; eassumption].
Qed.
Theorem GWIN_fx : forall m m', GWIN st m mo (mkG G R) -> wmono asegs m m' -> GWIN (st_fx st cls d sz) m' mo' (mkG G R').
Proof.
  intros m m' HG WM. rewrite (proj1 fx_mo). destruct st2_emb as (E1 & _). rewrite <- E1.
  eapply GWIN_emb_g; first [exact RTWF_st2| exact fx_sz| exact fx_hn| idtac].
  apply GWIN_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia|]. eapply GWIN_ci; try eassumption.
  apply (GWIN_R st m' mo G R R'). exact (GWIN_mem st m m' mo (mkG G R) HG HOK WM).
Qed.
Theorem SWIN_fx : SWIN st (mkG G R) -> SWIN (st_fx st cls d sz) (mkG G R').
Proof.
  intros HS. eapply SWIN_emb_g; first [exact RTWF_st2| exact fx_sz| exact fx_hn| idtac]. apply SWIN_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia|]. eapply SWIN_ci; try eassumption.
Qed.
Theorem rt_prov_fx : rt_prov (st_fx st cls d sz) + (if emb_d st =? 0 then EMB_CAP else 0) <= rt_prov st.
Proof.
  pose proof (rt_prov_emb_g st2 d sz RTWF_st2 fx_sz fx_hn) as P1. destruct st2_emb as (E1 & _). rewrite E1 in P1. unfold st_fx. fold st2. rewrite P1.
  destruct (ci_same st) as (_ & RGc & _).
  pose proof (rt_prov_exh_g (st_ci st) cls (RTWF_ci st WF cls Hc HC0) ltac:(lia) ltac:(rewrite !RGc; exact HX)) as P2. fold st2 in P2. rewrite P2.
  assert (P3 : rt_prov (st_ci st) <= rt_prov st) by (eapply rt_prov_ci; eassumption). lia.
Qed.
Theorem FRONTR_fx : FRONTR mo' R'.
Proof.
  destruct STEP as [(NZ & _ & -> & ->)|(Z0 & _ & _ & -> & ->)]; [exact HFR|].
  apply FRONTR_grant; [exact HFR| unfold FR_MINGRANT, EMB_CAP; lia| unfold EMB_CAP; lia|].
  pose proof (prov_emb_nonneg st) as PE. pose proof (rt_prov_parts_nonneg st WF) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof (prov_l24_nonneg st) as Q9.
  assert (PV : prov_emb st <= rt_prov st) by (unfold rt_prov; lia).
  unfold prov_emb in PV. rewrite Z0 in PV. cbn [Z.eqb] in PV. lia.
Qed.
Theorem budget_fx : budget_ok st (mkG G R) (st_fx st cls d sz) (mkG G R') 0.
Proof. unfold budget_ok. cbn [g_res]. rewrite (proj2 fx_mo). pose proof rt_prov_fx. lia. Qed.
Theorem gmono_fx : gmono (mkG G R) (mkG G R').
Proof. intros w Hw. exact Hw. Qed.
End FINX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rel_fx : forall st cls d sz, RTWF st -> 1 <= cls <= 30 -> cch st cls = [] -> refill_rel st (st_fx st cls d sz) cls 0.
Proof.
  intros st cls d sz WF Hc HC0. pose proof (fx_rg st cls d sz WF Hc) as RG. assert (CC : forall c, cch (st_fx st cls d sz) c = cch st c) by (intros c0; apply fx_cch; assumption).
  split; [| split; [| split; [apply fx_cache_inited| split]]].
  - destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5].
    unfold same_but_primary, st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0);
      (repeat match goal with |- _ /\ _ => split end; try reflexivity; [split; reflexivity|]);
      [exists [(d, EMB_CAP)]; reflexivity| exists []; cbn [st_loose0]; rewrite app_nil_r; reflexivity].
  - apply (fx_geom st cls d sz).
  - intros c Hc' NE. split; [rewrite RG; replace (c =? cls) with false by (symmetry; apply Z.eqb_neq; exact NE); reflexivity| apply CC].
  - right. split; [reflexivity|]. rewrite CC. exact HC0.
Qed.

Lemma fresh_blockfree : forall st lo hi, RTWF st -> (forall r, In r (rt_ranges st) -> hi <= fst r \/ snd r <= lo) -> blockfree st lo hi.
Proof.
  intros st lo hi WF FR A n Hin. pose proof (block_geom st WF A n Hin) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs).
  destruct (bprim n) eqn:EB.
  - destruct (Gp eq_refl) as (P1 & P2 & P3 & P4 & P5 & P6).
    destruct (FR (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia.
  - destruct (Gs eq_refl) as (S1 & S2 & S3 & S4).
    destruct (FR (b_lo A n, b_lo A n + smapsize n) ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1])) as [D|D];
      cbn [fst snd] in D; lia.
Qed.
Lemma fresh_framefree : forall st lo hi, RTWF st -> (forall r, In r (rt_ranges st) -> hi <= fst r \/ snd r <= lo) -> framefree st lo hi.
Proof.
  intros st lo hi WF FR. unfold framefree.
  destruct (FR (st_fs st, st_fs st + FS_TOTAL) ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists (st_fs st, FS_TOTAL); split; [reflexivity| exact (wb_fs_loose st (wf_base_ok st WF))])) as [D|D];
    cbn [fst snd] in D; [left| right]; exact D.
Qed.

Section FRAMEX.
Variables (st st' : rtstate) (cls d : Z) (SP lo : Z) (W1 : list (Z * Z)) (m m' : word -> option byte).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HSP : CEIL <= SP.
Hypothesis HW1c : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) W1.
Hypothesis HW1f : forall a iv, In iv W1 -> fst iv <= a < snd iv -> (lo <= a < SP) \/ in_ivs (primary_fp_fine st cls ++ fp_emb st') a.
Hypothesis HD : d <> 0 /\ emb_d st' = d.
Hypothesis HBK : (emb_d st <> 0 /\ d = emb_d st)
              \/ (ablk d (d + EMB_CAP) /\ forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).
Let W2 : list (Z * Z) := [(A_EMB, A_EMB + 56); (d, d + EMB_CAP)].
Hypothesis MU : munch (W1 ++ W2) m m'.
Hypothesis WM : wmono asegs m m'.

Lemma blk_not_client : forall a, d <= a < d + EMB_CAP -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha. destruct HBK as [(NZ & E)|(BK & FR)].
  - pose proof (emb_block_range st WF NZ) as (BK & B2 & B3). pose proof (wb_emb_loose st (wf_base_ok st WF) NZ) as LS. rewrite <- E in *.
    eapply (hm_not_client st WF SP HSP d (d + EMB_CAP) a); [exact (loose_blockfree st WF d EMB_CAP LS)| | exact (oclr_of_ablk _ _ BK)| unfold CEIL; exact B2| exact Ha].
    apply (loose_framefree st WF d EMB_CAP LS). intros EQ. injection EQ as E1 E2. unfold EMB_CAP, FS_TOTAL in E2. lia.
  - eapply (hm_not_client st WF SP HSP d (d + EMB_CAP) a); [exact (fresh_blockfree st _ _ WF FR)| exact (fresh_framefree st _ _ WF FR)| exact (oclr_of_ablk _ _ BK)
      | unfold CEIL; exact (ablk_top _ _ BK)| exact Ha].
Qed.

Theorem cli_pres_fx : cli_pres st SP m m'.
Proof.
  unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. apply outside_intro'. intros iv Hiv Hin. apply in_app_or in Hiv. destruct Hiv as [H1|H2].
  - rewrite Forall_forall in HW1c. destruct (HW1c iv H1) as [A1 A2]. destruct iv as [l h]. cbn [fst snd] in *.
    exact (pz_not_client st WF cls Hc SP HSP l h a A1 A2 Hin HC).
  - destruct H2 as [E|[E|[]]]; subst iv; cbn [fst snd] in Hin.
    + revert HC. apply (wstatic_not_client st SP a WF HSP). unfold A_EMB in Hin. lia.
    + exact (blk_not_client a Hin HC).
Qed.

Theorem rt_frame_fx : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  assert (FINE : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m').
  { apply (rt_frame_pz SP _ m m' lo _ MU). intros a iv Hiv Hin. apply in_app_or in Hiv. destruct Hiv as [H1|H2]; [exact (HW1f a iv H1 Hin)|].
    right. apply in_ivs_app. right. destruct HD as [NZ ED]. unfold fp_emb. rewrite ED. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
    destruct H2 as [E|[E|[]]]; subst iv; cbn [fst snd] in Hin; [exists A_EMB, (A_EMB + 56)| exists d, (d + EMB_CAP)]; (split; [cbn; tauto| exact Hin]). }
  eapply rt_frame_weaken; [| exact FINE]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  pose proof (cls_facts st WF cls Hc) as (_ & _ & _ & _ & _ & C6 & _). destruct Ha as (l & h & Hin & Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
End FRAMEX.

End CeilWrap.
