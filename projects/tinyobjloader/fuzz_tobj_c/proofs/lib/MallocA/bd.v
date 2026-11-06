(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.

(* [comment removed for export] *)
Module SegQ3D_inv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "length"; "nat"; "nil"; "option"; "None"; "S"; "Some"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "class_state"; "aa_geom"; "mkQB"; "aa_cls"; "aa_sec"; "class_fresh"; "cs_empty"; "qb_items"; "ageom"; "qb_addr"; "sec_chunk"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "sec_foot"; "set_q"; "push_cache"; "QRD"; "batch_mem"; "item_mem"; "qpost"; "same_but_qcs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "present"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "sub"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "CURB"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv.D"; "JRD"; "JRI"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineBatchCount"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineBatchSize"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "RMEM2"; "JRX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "qitems"; "@Stdlib.Lists.List"; "incl"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CURB (m : bview) (a n0 : Z) (ndone : nat) (its : list (Z * Z)) : Prop := ltac2:(tb__ "0|5|
S1dS32Vm;S33S35Va;Z10M0A2U8M1Vn0;A3A2S1dS1cS0Vn0;S35S37Vndone;A1M2S37S5S4S0S0A2M3Vits;A2A1A2A3S1dS36Vn0;S4aA2S1dS34Vm;S35Va;Z18A2M4S35Va;S4dA2A3S6G3S1cS8G3A1S54G3Vits;R2A3SbG3R1A2A3S1dS32Vm;S33S35G4S39Z8S35G2S37R3A1A2A2A2G1S3aScS0S0R2A3G0A2A3A2S2dVm;R2A2A2F_;Fit;Fj;A2A2A2A2").

Lemma CURB_of_batch_mem : ltac2:(tb__ "0|2|
S31SdS2cR2R1A2S36S37S5S4S0S0A2M0S18R2A1A2A1S4aA2S42R4S1aR3A1S37S5G0S18R3A1M1A2A1U0G1A5F_;F_;Fb;Fm;").
Proof.
  intros m b (H1 & H2 & H3 & H4 & H5) HL. split; [exact H2|]. split; [cbn; lia|]. split; [exact HL|]. split; [exact H4|].
  intros j it Hj. cbn [Z.of_nat]. rewrite Z.add_0_l. exact (H5 j it Hj).
Qed.
Lemma CURB_next : ltac2:(tb__ "0|1|
S31S0S0S6S4S0S0A2M0S2G0A1S42R6R5R4R3S3G0R2R1A3A5S42R7R6R5SaR4A1R2A5F_;Fits;Fit;Fnd;Fn0;Fa;Fm;").
Proof.
  intros m a n0 nd it its (H1 & H2 & H2' & H3 & H4). split; [exact H1|]. split; [cbn [length] in H2; lia|]. split; [exact H2'|]. split; [exact H3|].
  intros j it' Hj. specialize (H4 (S j) it' Hj). replace (Z.of_nat (S nd) + Z.of_nat j) with (Z.of_nat nd + Z.of_nat (S j)) by lia. exact H4.
Qed.

Section D.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Definition JRD (A : AA) (tmp rest : list qbatch) : jpredA := ltac2:(tb__ "0|0|
S23S2S3cQ40A1A1S2S3fA1S3eS1dVK;VA;R4R3R2R1A5S1dS4fS30S21S22R4A1A2S12VA;A1Vtmp;Vrest;A4S44VA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Definition JRI (A : AA) (a n0 : Z) (ndone : nat) (its : list (Z * Z)) (tmp rest : list qbatch) : jpredA := ltac2:(tb__ "0|1|
S23S2S3cQ40A1A1S2S3fA1S3eS1dVK;VA;R4R3R2R1A5S1dS42S30S21S22R4A1A2M0Va;Vn0;Vndone;Vits;A5S1dS4fG0S12VA;A1Vtmp;Vrest;A4S44VA0;Vrho0;R4A3A2A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma FRM_stable : ltac2:(tb__ "0|1|
S23S23S26S45R2R1A3S44VA0;Vrho0;R3A3M0G0F_;F_;Frho';Frho;").
Proof.
  intros rho rho' Hag ((F1 & F1') & F2 & F3 & F4).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [|rewrite Erm; auto]. split; [intros i Hi; rewrite (F1 i Hi); apply (proj1 Hag); exact Hi | intros l; rewrite (F1' l); apply (proj1 (proj2 Hag))].
Qed.
Lemma JRD_stable : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S41S21S45S46R3R2R1A3A3Frest;Ftmp;FA;").
Proof.
  intros A tmp rest rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A); eauto|]. split; [rewrite Erm; exact HR | exact (FRM_stable rho rho' Hag HF)].
Qed.
Lemma JRI_stable : ltac2:(tb__ "0|1|
SeS0S0S6S2S4S0S0A2A1S2SdA1M0G0S41S21S45S47R7R6R5R4R3R2R1A7A3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Proof.
  intros A a n0 nd its tmp rest rho rho' tp tr md md' Hag Hme (HK & HC & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A); eauto|]. split; [rewrite Erm; exact HC|]. split; [rewrite Erm; exact HR | exact (FRM_stable rho rho' Hag HF)].
Qed.
Lemma JRD_okf : ltac2:(tb__ "0|1|
S49OF_;SeS2SdA1M0G0SeS40S21R5VK;R1A1A3FA';S40S21R5S46R4R3R2A3A3F_;Frest;Ftmp;FA;Fok;").
Proof. intros ok A tmp rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A rho tp tr ms md msv' HK). Qed.
Lemma JRI_okf : ltac2:(tb__ "0|1|
S49OF_;SeS0S0S6S2S4S0S0A2A1S2SdA1M0G0SeS40S21R9VK;R1A1A3FA';S40S21R9S47R8R7R6R5R4R3R2A7A3F_;Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;Fok;").
Proof. intros ok A a n0 nd its tmp rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A rho tp tr ms md msv' HK). Qed.

Lemma K_FRM_absorb2 : ltac2:(tb__ "0|7|
SeS0S27R2R1A2S27VA0;R2A2F_;Fz;S23S23S2S3cQ40M0A1M1A1S2S3fA1S3eS0OF_;S0S1fR2R1A1M2S1eG2A1A2Fz;S1S1cG1S25R7R1A2S25R8R1A2A3Fi;S1S1cS2S3cQ8A1M3A1S24R8R1A2S24R9R1A2A3Fl;S0R5R1A1S1dS1eS1dS36S4cR2A2S38R2S4bA2A2A1S1fS27RdR2A2S1dS2bVA0;R2A2S1cS8G3A1M4S30S21S22RaA1R2A3S30S21S22RbA1R2A3M5A3A2A2A2F_;Fz;S0S1eR6R1A1A1S1cG4G5S30S21S22RcA1R2A3A3F_;Fz;G1S1eR7S3dG0R1A2A1A1S1cG4S22RcR2A2S22RdR2A2A3F_;Fa;S0R8R1A1S1eS1cG4S30S21S22RdA1R2A3S9G3A1A3A1F_;Fz;VK;RfRdRbRaR9A5S44VA0;Vrho0;ReA3M6S1dVK;R11ReRdRcRbA5G6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FP;Fmd;Ftr;Ftp;Frho3;Frho;F_;FA1;").
Proof.
  intros A1 HQW rho rho3 tp tr md P PD Hrw Hrl HP FR FRrm PPR HK ((F1 & F1') & F2 & F3 & F4). split.
  - apply (kq_view segsA K HL A1 rho rho3 tp tr md Hrw Hrl); [| | exact HK].
    + intros z NQ. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [_ [HQ|[_ HE]]]; [exfalso; exact (NQ HQ) | exact HE].
    + intros z _ Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
  - split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
    + intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. destruct (HP _ Hp) as [_ [HQ|[HQ _]]]; [left; left; exact (HQW _ HQ) | exact HQ].
    + intros z NQ. rewrite <- (F3 z NQ). destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [_ [HQ|[_ HE]]]; [exfalso; apply NQ; left; exact (HQW _ HQ) | exact HE].
    + intros a HB Hdef. pose proof (F4 a HB Hdef) as X. destruct (PD (bv_unsigned a)) as [Hp|Np]; [|rewrite (FRrm a Np); exact X].
      exfalso. exact (proj1 (HP _ Hp) HB).
Qed.
Lemma JRX_JRD : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S23S2S3cQ40A1A1S2S3fA1S3eS20S50VK;VA0;Vrho0;R7R6R5R4R3R2R1AaS46R7R6R5R4R3R2R1A7A2Fmd;Ftr;Ftp;Frho;Frest;Ftmp;FA1;").
Proof. intros. unfold JRX, JRD. tauto. Qed.
End D.

Definition QP (A0 A : AA) : Prop := ltac2:(tb__ "0|3|
S1dS2fVA0;VA;A2S1dS1cS6S5S11S14VA;A1M0A2S5S11S14VA0;A1M1A2A3S0S16VA0;R1A2S1cS11S48S11S3bR2A1M2G0S17A4S48S11G2G1S17A4A3F_;Fc;A2A2").
Lemma QP_refl_q : ltac2:(tb__ "0|1|
SeS2SdA1M0G0S43R3S29R3R2R1A3A2Fg;Ft;FA;").
Proof. intros A t g. split; [destruct A; reflexivity|]. split; [reflexivity | intros c _; reflexivity]. Qed.
Lemma QP_push : ltac2:(tb__ "0|1|
SeSeS2SdA1M0G0S0S0S43R6R5A2S36Z0R3A2S1eS16R8R4A2A1S43R9S2aS29R8R7R6A3R5R4A3A2F_;F_;F_;Fx;Fc;Fg;Ft;FA;FA0;").
Proof.
  intros A0 A t g c x (E & EL & EF) Hc NF. split; [|split].
  - unfold same_but_qcs in *. rewrite E. reflexivity.
  - unfold push_cache, set_cls. cbn [aa_cls set_q]. rewrite length_list_upd. exact EL.
  - intros c' Hf. unfold push_cache, set_cls. cbn [aa_cls set_q]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [En|Nn].
    + exfalso. apply NF. unfold class_fresh in *. rewrite En. exact Hf.
    + rewrite nth_list_upd_other by exact Nn. exact (EF c' Hf).
Qed.
Lemma QP_qpost : ltac2:(tb__ "0|0|
SeSeS43R2R1A2S1cS2SdA1S10R2A1S7SdA1A3S36S55SfR3A1A1S4eA2S2eR5R4A2F_;F_;F_;FA;FA0;").
Proof.
  intros A0 A (E & EL & EF) HT HS. split; [exact E|]. split; [exact HT|]. split; [exact EL|]. split; [|exact HS].
  intros c Hf. unfold class_fresh in *. rewrite (EF c Hf). exact Hf.
Qed.

Lemma QW_push_item : ltac2:(tb__ "0|3|
SeS0S4S0S0A2M0S2G0A1S0S0S2SdA1M1S0S0S0S1cG1S10RaA1S7SdA1M2A3S1cG1SfRbA1S3SdS13RaS3G0R9R8A3R7A3R5A3A3S27S2aS29RcG2S3SdS13RbR9R7A3R6A3A3R5R4A3R3A2S27RdR4A2F_;F_;F_;Fz;Fx;Fc;Fg2;Fs';Fs;Fi2;Fit;Fa;FA;").
Proof.
  intros A a it i2 s s' g2 c x z HT HG [H|H]; [left | right; exact H].
  unfold qzone, qall in *. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app] in H. rewrite HT, HG. cbn [app].
  apply Exists_cons in H as [H|H]; [apply Exists_cons_hd | apply Exists_cons_tl; exact H].
  cbn [qb_addr qb_items] in *. destruct H as [H|H]; [left; exact H | right]. apply Exists_cons_tl. exact H.
Qed.
Lemma QW_push_batch : ltac2:(tb__ "0|2|
SeSdS2SdA1M0S0S0S1cG0S10R5A1S7SdA1M1A3S1cG0SfR6A1S3SdR5R4A3A3S27S2aS29R7G1R5A3Z18R4A3R3A2S27R8R4A2F_;F_;F_;Fz;Fx;Fg2;Fb;FA;").
Proof.
  intros A b g2 x z HT HG [H|H]; [left | right; exact H].
  unfold qzone, qall in *. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app] in H. rewrite HT, HG. cbn [app]. apply Exists_cons_tl. exact H.
Qed.

Lemma sec_foot_mono : ltac2:(tb__ "0|0|
SeSeS0S1cS19S12R2A1S12R3A1A3S53S1bS15R3A1S15R4A1A3S53S4S0S0A2S52S51R4A1A1S52S51R5A1A1A3S28R5R4A2S28R7R5A2F_;F_;F_;F_;Fz;FA';FA;").
Proof.
  intros A A' z EG IS IQ [H|[H|[H|H]]].
  - left. exact H.
  - right; left. rewrite <- EG. exact H.
  - right; right; left. apply Exists_exists in H as (ch & Hch & Hz). apply Exists_exists. exists ch. split; [exact (IS _ Hch) | exact Hz].
  - right; right; right. apply Exists_exists in H as (ch & Hch & (it & Hit & HP & Eit) & Hz). apply Exists_exists. exists ch. split; [exact (IS _ Hch)|].
    split; [exists it; split; [exact (IQ _ Hit) | split; assumption] | exact Hz].
Qed.
Lemma SF_push_item : ltac2:(tb__ "0|3|
SeS0S4S0S0A2M0S2G0A1S0S0S2SdA1M1S0S0S0S1cG1S10RaA1S7SdA1M2A3S1cG1SfRbA1S3SdS13RaS3G0R9R8A3R7A3R5A3A3S28S2aS29RcG2S3SdS13RbR9R7A3R6A3A3R5R4A3R3A2S28RdR4A2F_;F_;F_;Fz;Fx;Fc;Fg2;Fs';Fs;Fi2;Fit;Fa;FA;").
Proof.
  intros A a it i2 s s' g2 c x z HT HG. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |].
  unfold qall. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app]. rewrite HT, HG. cbn [app]. unfold qitems. cbn [flat_map qb_items].
  intros y Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app; [left; right; exact Hy | right; exact Hy].
Qed.
Lemma SF_push_batch : ltac2:(tb__ "0|2|
SeSdS2SdA1M0S0S0S1cG0S10R5A1S7SdA1M1A3S1cG0SfR6A1S3SdR5R4A3A3S28S2aS29R7G1R5A3Z18R4A3R3A2S28R8R4A2F_;F_;F_;Fz;Fx;Fg2;Fb;FA;").
Proof.
  intros A b g2 x z HT HG. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |].
  unfold qall. cbn [aa_q_thread aa_q_global push_cache set_cls set_q app]. rewrite HT, HG. cbn [app]. unfold qitems. cbn [flat_map].
  intros y Hy. apply in_or_app. right. exact Hy.
Qed.
End SegQ3D_inv.

(* [comment removed for export] *)
Module CertCallocSU.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SVar"; "SLit"; "sprop"; "SPBranch"; "SPNot"; "sv"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "nat"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "rstS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SecLog2 CertCallocST.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_g4 : list sprop := ltac2:(tb__ "0|1|
SaS5S7S6S1S2S0S3S10A1S2S0S3Vnx;A1M0S4Z1000A1A3A3S2S0S2S0G0S4Z1800A1A3S3PcA1A3A3A1S9S5A1A3").
End NX.

Definition DPENT : Z := 0x7e850.
Definition DPRET : Z := 0x3c58c.
Definition U4p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S11VE;S9ScSbS8A2A1S13Vnx;A1A3").
Definition runT5 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
SfS14Ufa0SaSeS12S9SeA1A3VT;SdA5").
End CertCallocSU.

