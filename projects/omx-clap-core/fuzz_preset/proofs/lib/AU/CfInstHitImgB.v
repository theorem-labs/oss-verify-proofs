(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset (a Theorem Labs lane, row MISS-top at field round 3 part 3c): two image hypotheses of
   a Theorem Labs lane's cf hit / miss instances (YGcfInstHit.v / YGcfInstMiss.v / YGcfInstMissW.v, Section b) at B' (#102 pin
   fuzz_preset.asan-ubsan d663f82d7f48, twin c90d4fa54d43; AImg_cgif / AGImg_cgif, TfibSyms of lib/Reusable/YF0m.v),
   the oom_const row, and the depot hash fact of the unit's B' symbol record.  The B' twin of lib/A/CfInstHitImgA.v
   (this lane's own file, no cgif source), ported between images by the internal file port_img_b.py: the same
   statements and scripts, the B' modules (lib/Reusable YB1v / YB1q / YF0l / YF0m / YF0x / YD2l, lib/AU AGif2cgif /
   AGif0cgif / AGix) and B''s values.
   rule 24: no function proved (image arithmetic over this unit's generated facts).
   - [HCW_B]: the constant cells miss the thread cells the hit walk writes (ImgBaseAG.WINT), through AGif0cgif.CZONE
     (lib/AU/AGif0cgif.v:65-67; AGix.const_cells_zone), as at B'.
   - [INST_CELLS_B]: YGcfInstHit.INST_CELLS_t at B': the eight instance cells are constant cells of lib/Reusable/YF0m.v's
     table at B''s instance 0xa8098: Tfib_const_abs's z8 at 0xa8eb8 / 0xa8ec0 / 0xa80d8 / 0xa80f0 (TFIB_INST + 0xe20 /
     0xe28 / 64 / 88; the same stored values as at B') and z1 / z2 at 0xa8341 / 0xa8342 (+ 681 / + 682), found by value.
   - [oom_const_B]: the oom byte 0x12d960 lies in the 4th owned static extent [0xaaf50, 0x5cdd50) (YF0m.v:1789); the
     absolute and shadow cells miss it by the closed check.
   - [dhash_TfibB_B]: the depot hash of the B' record lib/Reusable/YD2l.v's TfibB is tfib_dhash (its field, YD2l.v:31). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGix.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstHit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstMiss.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Two distinct static extents of a layout are disjoint (layout_ok's lo_disj); a Theorem Labs lane's YGcfInstHitcgif.v:43-56. *)
Lemma pairwise_nth_B {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

Lemma static_disj_B : forall ly, layout_ok ly -> forall i j x y, nth_error (static_extents ly) i = Some x ->
  nth_error (static_extents ly) j = Some y -> (i < j)%nat -> zdisjoint x y.
Proof. intros ly LO i j x y Hi Hj Lt. exact (pairwise_nth_B zdisjoint _ i j x y (lo_disj _ LO) Hi Hj Lt). Qed.

(* Three zero bytes from a one-byte and a two-byte zero cell. *)
Lemma val_mem_zero3_B : forall m a, val_mem tfibsegs m a 1 0 -> val_mem tfibsegs m (a + 1) 2 0 -> val_mem tfibsegs m a 3 0.
Proof.
intros m a V1 V2 k Hk. unfold val_mem in V1, V2.
destruct k as [|[|[|k]]].
- exact (V1 0%nat ltac:(lia)).
- pose proof (V2 0%nat ltac:(lia)) as X. replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. exact X.
- pose proof (V2 1%nat ltac:(lia)) as X. replace (a + Z.of_nat 2) with (a + 1 + Z.of_nat 1) by lia. exact X.
- lia.
Qed.

(* B' copy of YGcfInstMisscgif.v:49-55 (YFi5.v:342-348's check): every absolute and shadow constant cell lies wholly
   below or wholly above the OOM byte TFIB_OOM = 0x12d960 (lib/Reusable/YF0m.v:18). *)
Definition oom_abs_ok_B (cc : acell) : bool :=
match c_at cc with
| ANum a => (a + Z.max 1 (Z.of_nat (c_w cc)) <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a)
| _ => false
end.
Lemma oom_abs_cells_B : forallb oom_abs_ok_B (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* HCW at B' (YGcfInstMissW.v Section b; the script of YGcfInstHitcgif.HCW_cgif with this unit's names). *)
Theorem HCW_B : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof.
intros ly c j cl LY IMG HT Hc Hj Hcl Hw.
change (YF0x.img_cover ly) in IMG.
assert (HT' : ly_tsd ly = TFIB_TSD) by (rewrite HT; exact (ts_tsd B TS)).
pose proof (AGix.const_cells_zone B ly TS LY IMG HT' c j Hc Hj) as CZ.
set (a := aeval B ly (c_at c) + j) in *.
destruct IMG as [I1 I2].
pose proof (static_disj_B ly LY 2 9 _ _ eq_refl eq_refl ltac:(lia)) as DTI.
pose proof (static_disj_B ly LY 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DTC.
pose proof (static_disj_B ly LY 2 7 _ _ eq_refl eq_refl ltac:(lia)) as DTD.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as AT.
unfold zdisjoint in DTI, DTC, DTD. cbn [fst snd] in DTI, DTC, DTD, AT.
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold AGif0cgif.CZONE in CZ.
unfold in_app, TFIB_TSD, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, kThreadObjSize, t_cache, t_stats, t_unwinding,
  kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

(* INST_CELLS_t at B' (YGcfInstHit.v:171-180): each instance cell is a constant cell of lib/Reusable/YF0m.v's table. *)
Theorem INST_CELLS_B : YGcfInstHit.INST_CELLS_t B.
Proof.
intros ly H mem LY HT CST.
assert (VM : forall e w e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' E. apply (YF0x.cell_holds_val_mem B ly H mem e w e').
  apply (proj1 (Forall_forall _ _) CST). rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E). }
assert (EI : as_inst B = TFIB_INST) by exact (ts_inst B TS).
change im_segs with tfibsegs. rewrite EI.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- pose proof (VM (AInst o_space) 8%nat (ASp 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (ANum 0xa8eb8) 8%nat (ANum 0x10000000000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa8ec0) 8%nat (ANum 0x108000010) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa80d8) 8%nat (ANum 0x1000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (AInst o_sec_chunks) 8%nat (AQ 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (AInst 80) 8%nat (AQ 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (ANum 0xa80f0) 8%nat (ANum 0x800000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa8341) 1%nat (ANum 0) ltac:(vm_compute; reflexivity)) as V1.
  pose proof (VM (ANum 0xa8342) 2%nat (ANum 0) ltac:(vm_compute; reflexivity)) as V2.
  cbn [aeval] in V1, V2. exact (val_mem_zero3_B _ 0xa8341 V1 V2).
Qed.

(* oom_const_t at B' (cgif/cgif_file_fuzzer lib/YGcfInstMiss.v (file sha256 7be6d43a1f59; donor not released) :312-314, over ly_img_ok; the script of
   a Theorem Labs lane's YGcfInstMisscgif.oom_const_cgif with this unit's names): the OOM byte lies in the owned static entry
   (0xaaf50, 0x5cdd50 - 0xaaf50) (lib/Reusable/YF0m.v:1789), which ly_img_ok puts inside ly_img; the thread, context and D
   extents are apart from ly_img (lo_disj); the symbol cells' absolute addresses are not 0x12d960; the absolute and
   shadow cells miss it by the closed check. *)
Theorem oom_const_B : YGcfInstMiss.oom_const_t B.
Proof.
intros ly c k (LY & HTSD & SUB) Hin Hk _.
assert (OI : fst (ly_img ly) <= TFIB_OOM < fst (ly_img ly) + snd (ly_img ly)).
{ rewrite (ts_owned B TS) in SUB. apply Forall_app in SUB as [SUB _].
  pose proof (proj1 (Forall_forall _ _) SUB (0xaaf50, 0x5cdd50 - 0xaaf50) ltac:(unfold Tfib_owned_static; cbn; tauto))
    as [S1 S2].
  cbn [fst snd] in S1, S2. unfold TFIB_OOM. lia. }
assert (DT : zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly)) by exact (static_disj_B ly LY 2 9 _ _ eq_refl eq_refl ltac:(lia)).
assert (DC : zdisjoint (ly_C ly, 256) (ly_img ly)) by exact (static_disj_B ly LY 6 9 _ _ eq_refl eq_refl ltac:(lia)).
assert (DD : zdisjoint (ly_D ly, 4096) (ly_img ly)) by exact (static_disj_B ly LY 7 9 _ _ eq_refl eq_refl ltac:(lia)).
unfold zdisjoint in DT, DC, DD. cbn [fst snd] in DT, DC, DD.
rewrite (ts_oom B TS).
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (ts_tsd B TS) as ETS.
  unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin];
      [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk;
       rewrite ?ETP, ?EIN, ?HTSD, ?ETS;
       unfold TFIB_OOM, TFIB_TP, TFIB_INST, TFIB_TSD, kThreadObjSize, o_space, o_rinfo, o_sec_chunks in *; lia |]
  | _ = c => subst c; cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk;
      rewrite ?ETP, ?EIN, ?HTSD, ?ETS;
      unfold TFIB_OOM, TFIB_TP, TFIB_INST, TFIB_TSD, kThreadObjSize, o_space, o_rinfo, o_sec_chunks in *; lia
  | False => destruct Hin
  end.
- pose proof (proj1 (forallb_forall _ _) oom_abs_cells_B c Hin) as Hc. unfold oom_abs_ok_B in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
  apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.

End b.

(* The depot hash of the unit's symbol record (lib/Reusable/YD2l.v:31). *)
Lemma dhash_TfibB_B : forall t, as_dhash YD2l.TfibB t = tfib_dhash t.
Proof. reflexivity. Qed.

End a.
