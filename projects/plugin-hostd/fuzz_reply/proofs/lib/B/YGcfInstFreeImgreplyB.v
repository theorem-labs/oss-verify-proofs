(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane's AFREE_CF at image B, the image rows of a Theorem Labs lane's ReplyDeallocPartsRh: rdr_FP_IZONE_ROM /
   rdr_FP_DSTAT / rdr_FP_DZONE_FP / rdr_FP_CONST): the four image premises of the generic cf layer's Deallocate post
   (lib/B/YGcfInstFreePost section 0) DISCHARGED at plugin-hostd / fuzz_reply's asan-ubsan image B: the image classes are
   reply B's (lib/B AGif2reply.AImg_reply, DGif0reply.DImg_reply) and the symbol table is any B with reply B's symbol facts
   (YF0m.TfibSyms B).  The B twin of lib/A/YGcfInstFreeImgreply.v (a working branch 48710ff6f0c), itself relocated
   from cgif_file's YGcfInstFreeImgcgif.v (lane F2a, a working branch): same proofs, B's module twins (YB13, YF0m, YF0x,
   YFfl, YFfy, YD2l) and B's numerals; cgif's DGif1.cloc / const_loc (reply has no DGif1.v) restated here over reply B's
   YFfy.Tfib_const_loc.  rule 24: no function proved (kind: image facts of a fixed binary).

   Every numeral is reply B's (pinned asan-ubsan ELF sha256 10ffb5f9202a), read from B's own tables AND cross-checked with
   the frozen alreloc a5c53bb2bed4 --dry run A -> B of the A file (OBJECT twin by symbol for each; per-numeral report in the
   commit message):
   - TFIB_INST 0xa2fd8 (asan::instance, 3632 bytes), TFIB_DEPOT 0x188518 (theDepot), TFIB_STORE 0x178508 (stackStore),
     TFIB_IAL_LO 0xa7840 (internal_alloc_placeholder), TFIB_IAL_HI 0x128870 (placeholder + 0x81030), TFIB_IAL_FLAG 0x1360c8
     (internal_allocator_initialized) (YF0m.v:16-19);
   - the one owned static range that holds the depot, the store and the internal allocator's zone and flag is
     Tfib_owned_static's 5th row (0xa5e90, 0x5c8c90 - 0xa5e90) (YF0m.v:822); the depot's static data ends at
     0x188518 + d_map1 + 8 * 32768 = 0x5c8528 <= 0x5c8c90 (hand decision: derived, not a symbol);
   - DGgi.DZONE's static part is [0x178508, 0x5c8c90) (DGgi.v:515-516); DGgi.IZONE is [IAL_LO, IAL_HI) + [IAL_FLAG, +4)
     (DGgi.v:517);
   - the image window [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x5fc000) (YF0x.v:25,37), so TFIB_IMG_END / 8 = 0xbf800 (hand
     decision: an image-derived count, not an address); YB13.tfib_rom_all covers it.
   One closed lemma per premise; CfImg / CfParams stay generic (no premise reads them). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YB13 DGgi AGif0reply CLdepot YFfl YFfy YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstFreePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Where reply B's constant cells are (YFfy.Tfib_const_loc): the low image outside the internal allocator's zone, the
   image's shadow, the thread object's first 80 bytes, the context page, the D page.  cgif's DGif1.cloc / const_loc
   (DGif1.v:874-886), whose text this is; reply has no DGif1.v. *)
Definition cloc (ly : alayout) (a : Z) : Prop :=
(TFIB_IMG_LO <= a < TFIB_IAL_LO \/ TFIB_IAL_HI <= a < TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= a < TFIB_IMG_END \/
 SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8) \/
(ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 256) \/ (ly_D ly <= a < ly_D ly + 4096).
Lemma const_loc : forall B ly, TfibSyms B -> ly_tsd ly = TFIB_TSD ->
Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> cloc ly (aeval B ly (c_at c) + i)) (as_const B ly).
Proof.
intros B ly TS HTSD. rewrite (ts_const _ TS). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YFfy.Tfib_const_loc ly) c Hc) as K. unfold YFfy.const_loc_ok in K.
unfold cloc. destruct (c_at c); try discriminate K; cbn [aeval]; rewrite ?HTSD, ?(ts_inst _ TS), ?(ts_tp _ TS);
unfold YFfy.low_ok in K; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *;
first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; lia ].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* The one owned static range of reply B's table that holds the depot, the store and the internal allocator's zone
   and flag (Tfib_owned_static's 5th row). *)
Lemma owned_big_reply : forall a, 0xa5e90 <= a < 0x5c8c90 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha. rewrite (ts_owned _ TS). apply Exists_exists. exists (0xa5e90, 0x5c8c90 - 0xa5e90).
split; [unfold Tfib_owned_static; do 4 right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma FP_IZONE_ROM_reply : FP_IZONE_ROM B.
Proof.
intros a Ha. cbn [dg_izone DImg_reply] in Ha. unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha.
rewrite (ts_inst _ TS), (ts_depot _ TS), (ts_store _ TS). split; [apply YB13.tfib_rom_all; lia|].
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, d_map1. lia.
Qed.

Lemma FP_DSTAT_reply : FP_DSTAT B.
Proof.
intros a Ha. rewrite (ts_depot _ TS), (ts_store _ TS) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
apply owned_big_reply. lia.
Qed.

(* Under LGUARD: the instance object inside the image window, and an owned extent apart from that window. *)
Lemma lg_inst_img : forall ly, LGUARD B ly ->
  fst (ly_img ly) <= as_inst B /\ as_inst B + 3632 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly ((LO & TSD & SI) & IC & SY).
pose proof (proj1 (Forall_forall _ _) (aso_cover _ SY) (as_inst B, 3632) ltac:(cbn; tauto)) as X.
apply Exists_exists in X as (r & Hr & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2]. lia.
Qed.

Lemma FP_DZONE_FP_reply : FP_DZONE_FP B.
Proof.
intros ly a G. pose proof (lg_inst_img ly G) as [I1 I2]. destruct G as ((LO & TSD & SI) & IC & SY).
split.
- intros F. cbn [dg_dzone DImg_reply]. unfold DGgi.DZONE. unfold CLdepot.depot_footprint in F.
  rewrite (ts_depot _ TS), (ts_store _ TS) in F. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in F.
  destruct F as [F|[F|[F|F]]]; [left; lia | right; left; exact F | right; right; exact F | left; lia].
- intros D Hin. cbn [dg_dzone DImg_reply] in D. unfold DGgi.DZONE in D.
  destruct D as [D|[D|D]].
  + rewrite (ts_inst _ TS) in Hin. unfold TFIB_INST in Hin. lia.
  + pose proof (YFfl.pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
  + pose proof (YFfl.pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
Qed.

Lemma FP_CONST_reply : FP_CONST B.
Proof.
intros ly c j G Hc Hj. destruct G as ((LO & TSD & SI) & IC & SY).
assert (HT : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd _ TS)).
pose proof (proj1 (Forall_forall _ _) (const_loc B ly TS HT) c Hc j Hj) as K.
unfold cloc in K. set (a := aeval B ly (c_at c) + j) in *.
assert (IC' : img_cover ly) by exact IC. destruct IC' as [IC1 IC2].
pose proof (YFfl.pairwise_nth zdisjoint _ 2 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DT.
pose proof (YFfl.pairwise_nth zdisjoint _ 6 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DC.
pose proof (YFfl.pairwise_nth zdisjoint _ 7 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DD.
pose proof (YFfl.pairwise_nth zdisjoint _ 2 6 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DTC.
pose proof (YFfl.pairwise_nth zdisjoint _ 2 7 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DTD.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as APT.
unfold zdisjoint, in_app in *. cbn [fst snd] in DT, DC, DD, DTC, DTD, APT.
assert (E1 : TFIB_IMG_LO / 8 = 8192) by reflexivity. assert (E2 : TFIB_IMG_END / 8 = 0xbf800) by reflexivity.
rewrite E1, E2 in K.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *.
split.
- intros Hz. cbn [dg_izone DImg_reply] in Hz. unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz.
  destruct K as [[K|[K|[K|K]]]|[K|[K|K]]]; unfold kThreadObjSize in *; lia.
- intros Hw. unfold DGgiC.WINT in Hw.
  destruct K as [[K|[K|[K|K]]]|[K|[K|K]]];
    unfold kThreadObjSize, t_qc, t_unwinding, t_stats, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
End c.

(* The four record fields of ReplyDeallocPartsRh (rdr_FP_IZONE_ROM .. rdr_FP_CONST) at reply B's symbol table YD2l.TfibB. *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Lemma FP_IZONE_ROM_TfibB : FP_IZONE_ROM YD2l.TfibB. Proof. exact (FP_IZONE_ROM_reply _ YD2l.TfibB_syms). Qed.
Lemma FP_DSTAT_TfibB : FP_DSTAT YD2l.TfibB. Proof. exact (FP_DSTAT_reply _ YD2l.TfibB_syms). Qed.
Lemma FP_DZONE_FP_TfibB : FP_DZONE_FP YD2l.TfibB. Proof. exact (FP_DZONE_FP_reply _ YD2l.TfibB_syms). Qed.
Lemma FP_CONST_TfibB : FP_CONST YD2l.TfibB. Proof. exact (FP_CONST_reply _ YD2l.TfibB_syms). Qed.
End t.

Print Assumptions FP_IZONE_ROM_TfibB.
Print Assumptions FP_DSTAT_TfibB.
Print Assumptions FP_DZONE_FP_TfibB.
Print Assumptions FP_CONST_TfibB.
