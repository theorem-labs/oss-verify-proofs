From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YK00 YB1v YF0m YD1u YD1y YE22 YF0x YD2l YG0q YCbj YP08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma tj_snp_cr_tfib : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) snp_cr.
Proof.
unfold snp_cr. repeat (apply Forall_cons; [cbv beta; cbn [fst snd]; unfold IMG_LO, IMG_TOP; lia|]). apply Forall_nil.
Qed.

Lemma tj_snp_gcgv_tfib : IMG_LO <= FF_got_canary /\ FF_got_canary + 8 <= IMG_TOP /\ IMG_LO <= FF_canary /\ FF_canary + 8 <= IMG_TOP.
Proof. unfold IMG_LO, IMG_TOP, FF_got_canary, FF_canary. lia. Qed.

Lemma tj_snp_img_tfib : IMG_LO <= IMG_LO /\ IMG_TOP <= IMG_TOP.
Proof. lia. Qed.

Lemma snp_img_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
  YP08.img_byte_ok YB1v.tfibsegs a = true -> exists v, aview YB1v.tfibsegs H m a = Some v.
Proof.
intros H m a Hi. unfold YP08.img_byte_ok, img_byte in Hi. unfold aview, mbyte.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity|].
match type of Hi with (match ?x with Some _ => _ | None => _ end = true) => destruct x as [b|]; [|discriminate Hi] end.
eexists; reflexivity.
Qed.

Lemma snp_canary_rdword : forall (H : word -> bool) (m : word -> option byte),
  exists cval, rdword (aview YB1v.tfibsegs H m) FF_canary = Some cval.
Proof.
intros H m.
assert (Hz : YP08.zallb (YP08.img_byte_ok YB1v.tfibsegs) FF_canary 8 = true) by (vm_compute; reflexivity).
assert (B : forall k, 0 <= k < 8 -> exists v, aview YB1v.tfibsegs H m (FF_canary + k) = Some v).
{ intros k Hk. apply snp_img_aview_some. exact (YP08.zallb_sound _ _ _ (FF_canary + k) Hz ltac:(lia)). }
destruct (B 0 ltac:(lia)) as (v0 & E0). destruct (B 1 ltac:(lia)) as (v1 & E1).
destruct (B 2 ltac:(lia)) as (v2 & E2). destruct (B 3 ltac:(lia)) as (v3 & E3).
destruct (B 4 ltac:(lia)) as (v4 & E4). destruct (B 5 ltac:(lia)) as (v5 & E5).
destruct (B 6 ltac:(lia)) as (v6 & E6). destruct (B 7 ltac:(lia)) as (v7 & E7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
#[local] Notation PI := YCbj.PB_tfib.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).

Lemma tj_snp_canary_of_syms : forall B, YF0m.TfibSyms B ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  exists cval, rdword (aview SEGS (w_H W) mem) FF_got_canary = Some FF_canary /\ rdword (aview SEGS (w_H W) mem) FF_canary = Some cval.
Proof.
intros B HB ly S W mem md HAR.
pose proof (YE22.got_canary_of_AR B HB ly S W mem md HAR) as HG.
destruct (snp_canary_rdword (w_H W) mem) as (cval & HC).
exists cval. split; [|exact HC].
apply YF0x.val_mem_rdword; [unfold FF_canary; lia | exact HG].
Qed.

Lemma tj_snp_canary_tfib : forall ly S (W : world SEGS) mem md, AR SEGS YD2l.TfibB ly S W mem md ->
  exists cval, rdword (aview SEGS (w_H W) mem) FF_got_canary = Some FF_canary /\ rdword (aview SEGS (w_H W) mem) FF_canary = Some cval.
Proof. exact (tj_snp_canary_of_syms YD2l.TfibB YD2l.TfibB_syms). Qed.

Lemma snp_cr_unowned : forallb (fun r => forallb (YD1y.ext_avoids (fst r) (fst r + snd r)) YF0m.Tfib_owned_static) snp_cr = true.
Proof. vm_compute. reflexivity. Qed.

Lemma snp_cr_rows : forall a, Exists (in_zr a) snp_cr ->
  exists r, In r snp_cr /\ fst r <= a < fst r + snd r /\ 0x10000 <= fst r /\ fst r + snd r <= 0x22d60.
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha). exists r. split; [exact Hr|]. split; [exact Ha|].
unfold snp_cr in Hr. cbn [In] in Hr.
repeat (destruct Hr as [Hr|Hr]; [subst r; cbn [fst snd]; lia|]). destruct Hr.
Qed.

Lemma snp_consts_of_arodata_tfib : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi YD2l.TfibB (aview SEGS (w_H W) mem) -> consts_view SEGS W mem snp_cr.
Proof.
intros W mem HR a Ha. destruct (snp_cr_rows a Ha) as (r & Hr & Hra & Hlo & Hhi). apply HR.
- left. exact (snp_cr_in_rom a Ha).
- exact (YD1u.owned_off YD2l.TfibB YD2l.TfibB_syms (fst r) (fst r + snd r) a (proj1 (forallb_forall _ _) snp_cr_unowned r Hr) Hra).
- rewrite (YF0m.ts_errno _ YD2l.TfibB_syms). unfold YF0m.TFIB_ERRNO. lia.
Qed.

Lemma snp_consts_refuted_of_syms : forall B, YF0m.TfibSyms B ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  exists mem', AR SEGS B ly S W mem' md /\ ~ consts_view SEGS W mem' snp_cr.
Proof.
intros B HB ly S W mem md HAR.
assert (Hh : w_H W (Z_to_bv 64 0x15288) = false).
{ destruct (w_H W (Z_to_bv 64 0x15288)) eqn:E; [|reflexivity]. exfalso.
  pose proof (w_Hoff W _ E) as Hf. change (@pa_segs _ _ PI) with YB1v.tfibsegs in Hf. vm_compute in Hf. discriminate Hf. }
exists (fun x : word => if Z.eqb (bv_unsigned x) 0x15288 then Some (Z_to_bv 8 0) else mem x). split.
- apply (al_frame _ _ (YG0q.AR_laws_ok SEGS B) ly S W mem md _ md HAR).
  + intros a Ha Ho. unfold aview, mbyte, mrestrict. cbv beta.
    match goal with |- context [Z.eqb ?x 0x15288] => destruct (Z.eqb x 0x15288) eqn:E end; [|reflexivity].
    exfalso. apply Z.eqb_eq in E. rewrite YK00.u64_lit in E by exact Ha. subst a.
    assert (Hi : in_img SEGS 0x15288) by exact (YD1y.in_img_hull 0x15288 ltac:(unfold IMG_TOP; lia)).
    pose proof (proj1 (al_owned_image _ _ (YG0q.AR_laws_ok SEGS B) ly S W mem md 0x15288 HAR Hi) Ho) as Hs.
    exact (YD1u.owned_off B HB 0x15288 0x15289 0x15288 ltac:(vm_compute; reflexivity) ltac:(lia) Hs).
  + intros a Hv. unfold aview, mbyte, mrestrict in *. cbv beta.
    match goal with |- context [Z.eqb ?x 0x15288] => destruct (Z.eqb x 0x15288) eqn:E end; [|exact Hv].
    destruct (w_H W (Z_to_bv 64 a)); [exact Hv|]. cbn. discriminate.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros a _ Hw. cbv beta.
    match goal with |- context [Z.eqb ?x 0x15288] => destruct (Z.eqb x 0x15288) eqn:E end; [|reflexivity].
    exfalso. apply Z.eqb_eq in E. pose proof (w_Hoff W _ Hw) as Hf. rewrite E in Hf.
    change (@pa_segs _ _ PI) with YB1v.tfibsegs in Hf. vm_compute in Hf. discriminate Hf.
- intros HC.
  assert (Hin : Exists (in_zr 0x15288) snp_cr) by (unfold snp_cr; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
  specialize (HC 0x15288 Hin). unfold aview, mbyte, mrestrict in HC. cbv beta in HC. rewrite Hh in HC.
  assert (Eb : Z.eqb (bv_unsigned (Z_to_bv 64 0x15288)) 0x15288 = true) by (vm_compute; reflexivity).
  rewrite Eb in HC. cbv beta iota in HC. change (@pa_segs _ _ PI) with YB1v.tfibsegs in HC. vm_compute in HC. discriminate HC.
Qed.

Lemma tj_snp_consts_vacuous_tfib :
  (forall ly S (W : world SEGS) mem md, AR SEGS YD2l.TfibB ly S W mem md -> consts_view SEGS W mem snp_cr) ->
  forall ly S (W : world SEGS) mem md, ~ AR SEGS YD2l.TfibB ly S W mem md.
Proof.
intros HT ly S W mem md HAR.
destruct (snp_consts_refuted_of_syms YD2l.TfibB YD2l.TfibB_syms ly S W mem md HAR) as (mem' & HAR' & HN).
exact (HN (HT ly S W mem' md HAR')).
Qed.

End d.
