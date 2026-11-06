(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: fuzz_preset (a Theorem Labs lane memnorm102): two image hypotheses of a Theorem Labs lane's cf hit / miss
   instances (cgif/cgif_file_fuzzer lib/YGcfInstHit.v (file sha256 3a63e7a692ce; donor not released) / cgif/cgif_file_fuzzer lib/YGcfInstMiss.v (file sha256 19108561272e; donor not released) / cgif/cgif_file_fuzzer lib/YGcfInstMissW.v (file sha256 8b390d808abb; donor not released), Section b) at A'
   (#102 pin fuzz_preset.asan 1be0f53d96cb; AImg_A / AGImg_A, TfibSyms), and the depot hash fact of the unit's own
   symbol record.  The A' twin of a Theorem Labs lane's YGcfInstHitcgif.v for HCW (its script, :91-113), plus INST_CELLS, which has
   no cgif discharge.
   rule 24: no function proved (image arithmetic over this unit's generated facts).
   - [HCW_A]: the constant cells miss the thread cells the hit walk writes (ImgBaseAG.WINT): the constant cells lie in
     AGImgA.CZONE (AGix.const_cells_zone), and CZONE misses WINT, which lies inside the thread object [T, T + 4096):
     the image window and TFIB_TSD's cell are apart from the thread object (lo_disj + img_cover), the shadow window is
     apart from it (lo_app), the thread object's first 80 bytes are below every WINT cell, and the context map and
     the D page are apart from it (lo_disj).
   - [INST_CELLS_A]: YGcfInstHit.INST_CELLS_t at A': the eight instance cells the walks read are constant cells of
     this unit's table A/AF0m.v (Tfib_const_sym's (AInst o_space) (ASp 0), (AInst o_sec_chunks) (AQ 0), (AInst 80)
     (AQ 0); Tfib_const_abs's z8 at TFIB_INST + 0xe20 / 0xe28 / 64 / 88, and z1 / z2 at + 681 / + 682, which together
     are the three zero bytes at o_sec_mutex + 1), found by value (cell_lookup, vm_compute), read by AF0x's
     cell_holds_val_mem.
   - [dhash_TfibB_A]: the depot hash of preset's symbol record A/AD2l.v's TfibB is tfib_dhash (its field,
     A/AD2l.v:33).  The depot contract (A/AFem.v:1523 tfib_depot_ok) takes `forall t, as_dhash B t = tfib_dhash t`;
     TfibSyms does not constrain as_dhash (only two hash values, ts_hash), so the fact is a premise on B like TfibSyms
     itself, and it holds at the unit's record B := TfibB (TfibSyms TfibB is A/AD2l.v:73 TfibB_syms). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGix AD2l.
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
Lemma pairwise_nth_A {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

Lemma static_disj_A : forall ly, layout_ok ly -> forall i j x y, nth_error (static_extents ly) i = Some x ->
  nth_error (static_extents ly) j = Some y -> (i < j)%nat -> zdisjoint x y.
Proof. intros ly LO i j x y Hi Hj Lt. exact (pairwise_nth_A zdisjoint _ i j x y (lo_disj _ LO) Hi Hj Lt). Qed.

(* Three zero bytes from a one-byte and a two-byte zero cell. *)
Lemma val_mem_zero3_A : forall m a, val_mem tfibsegs m a 1 0 -> val_mem tfibsegs m (a + 1) 2 0 -> val_mem tfibsegs m a 3 0.
Proof.
intros m a V1 V2 k Hk. unfold val_mem in V1, V2.
destruct k as [|[|[|k]]].
- exact (V1 0%nat ltac:(lia)).
- pose proof (V2 0%nat ltac:(lia)) as X. replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. exact X.
- pose proof (V2 1%nat ltac:(lia)) as X. replace (a + Z.of_nat 2) with (a + 1 + Z.of_nat 1) by lia. exact X.
- lia.
Qed.

(* A' copy of YGcfInstMisscgif.v:49-55 (YFi5.v:342-348's check): every absolute and shadow constant cell lies wholly
   below or wholly above the OOM byte TFIB_OOM = 0x12d120 (A/AF0m.v:17). *)
Definition oom_abs_ok_A (cc : acell) : bool :=
match c_at cc with
| ANum a => (a + Z.max 1 (Z.of_nat (c_w cc)) <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a)
| _ => false
end.
Lemma oom_abs_cells_A : forallb oom_abs_ok_A (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* HCW at A' (YGcfInstMissW.v Section b; the script of YGcfInstHitcgif.HCW_cgif with this unit's names). *)
Theorem HCW_A : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof.
intros ly c j cl LY IMG HT Hc Hj Hcl Hw.
change (AF0x.img_cover ly) in IMG.
assert (HT' : ly_tsd ly = TFIB_TSD) by (rewrite HT; exact (ts_tsd B TS)).
pose proof (AGix.const_cells_zone B ly TS LY IMG HT' c j Hc Hj) as CZ.
set (a := aeval B ly (c_at c) + j) in *.
destruct IMG as [I1 I2].
pose proof (static_disj_A ly LY 2 9 _ _ eq_refl eq_refl ltac:(lia)) as DTI.
pose proof (static_disj_A ly LY 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DTC.
pose proof (static_disj_A ly LY 2 7 _ _ eq_refl eq_refl ltac:(lia)) as DTD.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as AT.
unfold zdisjoint in DTI, DTC, DTD. cbn [fst snd] in DTI, DTC, DTD, AT.
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold AGImgA.CZONE in CZ.
unfold in_app, TFIB_TSD, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, kThreadObjSize, t_cache, t_stats, t_unwinding,
  kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

(* INST_CELLS_t at A' (YGcfInstHit.v:171-180): each instance cell is a constant cell of A/AF0m.v's table. *)
Theorem INST_CELLS_A : YGcfInstHit.INST_CELLS_t B.
Proof.
intros ly H mem LY HT CST.
assert (VM : forall e w e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' E. apply (AF0x.cell_holds_val_mem B ly H mem e w e').
  apply (proj1 (Forall_forall _ _) CST). rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E). }
assert (EI : as_inst B = TFIB_INST) by exact (ts_inst B TS).
change im_segs with tfibsegs. rewrite EI.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- pose proof (VM (AInst o_space) 8%nat (ASp 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (ANum 0xa8678) 8%nat (ANum 0x10000000000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa8680) 8%nat (ANum 0x108000010) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa7898) 8%nat (ANum 0x1000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (AInst o_sec_chunks) 8%nat (AQ 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (AInst 80) 8%nat (AQ 0) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. rewrite EI, Z.add_0_r in V. exact V.
- pose proof (VM (ANum 0xa78b0) 8%nat (ANum 0x800000) ltac:(vm_compute; reflexivity)) as V.
  cbn [aeval] in V. exact V.
- pose proof (VM (ANum 0xa7b01) 1%nat (ANum 0) ltac:(vm_compute; reflexivity)) as V1.
  pose proof (VM (ANum 0xa7b02) 2%nat (ANum 0) ltac:(vm_compute; reflexivity)) as V2.
  cbn [aeval] in V1, V2. exact (val_mem_zero3_A _ 0xa7b01 V1 V2).
Qed.

(* oom_const_t at A' (cgif/cgif_file_fuzzer lib/YGcfInstMiss.v (file sha256 7be6d43a1f59; donor not released) :312-314, over ly_img_ok; the script of
   a Theorem Labs lane's YGcfInstMisscgif.oom_const_cgif with this unit's names): the OOM byte lies in the owned static entry
   (0xaa710, 0x5cd510 - 0xaa710) (A/AF0m.v:1784), which ly_img_ok puts inside ly_img; the thread, context and D
   extents are apart from ly_img (lo_disj); the symbol cells' absolute addresses are not 0x12d120; the absolute and
   shadow cells miss it by the closed check. *)
Theorem oom_const_A : YGcfInstMiss.oom_const_t B.
Proof.
intros ly c k (LY & HTSD & SUB) Hin Hk _.
assert (OI : fst (ly_img ly) <= TFIB_OOM < fst (ly_img ly) + snd (ly_img ly)).
{ rewrite (ts_owned B TS) in SUB. apply Forall_app in SUB as [SUB _].
  pose proof (proj1 (Forall_forall _ _) SUB (0xaa710, 0x5cd510 - 0xaa710) ltac:(unfold Tfib_owned_static; cbn; tauto))
    as [S1 S2].
  cbn [fst snd] in S1, S2. unfold TFIB_OOM. lia. }
assert (DT : zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly)) by exact (static_disj_A ly LY 2 9 _ _ eq_refl eq_refl ltac:(lia)).
assert (DC : zdisjoint (ly_C ly, 256) (ly_img ly)) by exact (static_disj_A ly LY 6 9 _ _ eq_refl eq_refl ltac:(lia)).
assert (DD : zdisjoint (ly_D ly, 4096) (ly_img ly)) by exact (static_disj_A ly LY 7 9 _ _ eq_refl eq_refl ltac:(lia)).
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
- pose proof (proj1 (forallb_forall _ _) oom_abs_cells_A c Hin) as Hc. unfold oom_abs_ok_A in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval].
  apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.

End b.

(* The depot hash of the unit's symbol record (A/AD2l.v:33). *)
Lemma dhash_TfibB_A : forall t, as_dhash AD2l.TfibB t = tfib_dhash t.
Proof. reflexivity. Qed.

End a.
