(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstFreeImgreply.v (commit eb934de95d13, blob 640d11e5a864) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 7 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); DImg_A's zone fields are AFgn.IZONE / AFgi.DZONE (A/ADIfaceA.v:54), the same text as reply's DGgi ones, so the unfold after the field's cbn names them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB13 DGgi AGImgA AFgn AFgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFfl AFfy AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstFreePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition cloc (ly : alayout) (a : Z) : Prop :=
(TFIB_IMG_LO <= a < TFIB_IAL_LO \/ TFIB_IAL_HI <= a < TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= a < TFIB_IMG_END \/
 SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8) \/
(ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 256) \/ (ly_D ly <= a < ly_D ly + 4096).
Lemma const_loc : forall B ly, TfibSyms B -> ly_tsd ly = TFIB_TSD ->
Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> cloc ly (aeval B ly (c_at c) + i)) (as_const B ly).
Proof.
intros B ly TS HTSD. rewrite (ts_const _ TS). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (AFfy.Tfib_const_loc ly) c Hc) as K. unfold AFfy.const_loc_ok in K.
unfold cloc. destruct (c_at c); try discriminate K; cbn [aeval]; rewrite ?HTSD, ?(ts_inst _ TS), ?(ts_tp _ TS);
unfold AFfy.low_ok in K; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *;
first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; lia ].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

Lemma owned_big_preset : forall a, 0xaa710 <= a < 0x5cd510 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha. rewrite (ts_owned _ TS). apply Exists_exists. exists (0xaa710, 0x5cd510 - 0xaa710).
split; [unfold Tfib_owned_static; do 3 right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma FP_IZONE_ROM_preset : FP_IZONE_ROM B.
Proof.
intros a Ha. cbn [dg_izone DImg_A] in Ha. unfold AFgn.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha.
rewrite (ts_inst _ TS), (ts_depot _ TS), (ts_store _ TS). split; [apply AB13.tfib_rom_all; lia|].
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, d_map1. lia.
Qed.

Lemma FP_DSTAT_preset : FP_DSTAT B.
Proof.
intros a Ha. rewrite (ts_depot _ TS), (ts_store _ TS) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
apply owned_big_preset. lia.
Qed.

Lemma lg_inst_img : forall ly, LGUARD B ly ->
  fst (ly_img ly) <= as_inst B /\ as_inst B + 3632 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly ((LO & TSD & SI) & IC & SY).
pose proof (proj1 (Forall_forall _ _) (aso_cover _ SY) (as_inst B, 3632) ltac:(cbn; tauto)) as X.
apply Exists_exists in X as (r & Hr & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2]. lia.
Qed.

Lemma FP_DZONE_FP_preset : FP_DZONE_FP B.
Proof.
intros ly a G. pose proof (lg_inst_img ly G) as [I1 I2]. destruct G as ((LO & TSD & SI) & IC & SY).
split.
- intros F. cbn [dg_dzone DImg_A]. unfold AFgi.DZONE. unfold CLdepot.depot_footprint in F.
  rewrite (ts_depot _ TS), (ts_store _ TS) in F. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in F.
  destruct F as [F|[F|[F|F]]]; [left; lia | right; left; exact F | right; right; exact F | left; lia].
- intros D Hin. cbn [dg_dzone DImg_A] in D. unfold AFgi.DZONE in D.
  destruct D as [D|[D|D]].
  + rewrite (ts_inst _ TS) in Hin. unfold TFIB_INST in Hin. lia.
  + pose proof (AFfl.pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
  + pose proof (AFfl.pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
Qed.

Lemma FP_CONST_preset : FP_CONST B.
Proof.
intros ly c j G Hc Hj. destruct G as ((LO & TSD & SI) & IC & SY).
assert (HT : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd _ TS)).
pose proof (proj1 (Forall_forall _ _) (const_loc B ly TS HT) c Hc j Hj) as K.
unfold cloc in K. set (a := aeval B ly (c_at c) + j) in *.
assert (IC' : img_cover ly) by exact IC. destruct IC' as [IC1 IC2].
pose proof (AFfl.pairwise_nth zdisjoint _ 2 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DT.
pose proof (AFfl.pairwise_nth zdisjoint _ 6 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DC.
pose proof (AFfl.pairwise_nth zdisjoint _ 7 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DD.
pose proof (AFfl.pairwise_nth zdisjoint _ 2 6 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DTC.
pose proof (AFfl.pairwise_nth zdisjoint _ 2 7 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DTD.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as APT.
unfold zdisjoint, in_app in *. cbn [fst snd] in DT, DC, DD, DTC, DTD, APT.
assert (E1 : TFIB_IMG_LO / 8 = 8192) by reflexivity. assert (E2 : TFIB_IMG_END / 8 = 0xc0000) by reflexivity.
rewrite E1, E2 in K.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *.
split.
- intros Hz. cbn [dg_izone DImg_A] in Hz. unfold AFgn.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz.
  destruct K as [[K|[K|[K|K]]]|[K|[K|K]]]; unfold kThreadObjSize in *; lia.
- intros Hw. unfold DGgiC.WINT in Hw.
  destruct K as [[K|[K|[K|K]]]|[K|[K|K]]];
    unfold kThreadObjSize, t_qc, t_unwinding, t_stats, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
End c.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Lemma FP_IZONE_ROM_TfibB : FP_IZONE_ROM AD2l.TfibB. Proof. exact (FP_IZONE_ROM_preset _ AD2l.TfibB_syms). Qed.
Lemma FP_DSTAT_TfibB : FP_DSTAT AD2l.TfibB. Proof. exact (FP_DSTAT_preset _ AD2l.TfibB_syms). Qed.
Lemma FP_DZONE_FP_TfibB : FP_DZONE_FP AD2l.TfibB. Proof. exact (FP_DZONE_FP_preset _ AD2l.TfibB_syms). Qed.
Lemma FP_CONST_TfibB : FP_CONST AD2l.TfibB. Proof. exact (FP_CONST_preset _ AD2l.TfibB_syms). Qed.
End t.

Print Assumptions FP_IZONE_ROM_TfibB.
Print Assumptions FP_DSTAT_TfibB.
Print Assumptions FP_DZONE_FP_TfibB.
Print Assumptions FP_CONST_TfibB.
