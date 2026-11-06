From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK04 YP09 YI04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AF0m AD2l AD1u AD1y AE22 AF0x AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable DiscoList DiscoPa DiscoBase DiscoImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma tj_snp_cr_disco : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) snp_cr.
Proof.
assert (H : forallb (fun r => (IMG_LO <=? fst r) && (0 <=? snd r) && (fst r + snd r <=? IMG_TOP)) snp_cr = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. eapply forallb_forall in H; [|exact Hr].
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma tj_snp_gcgv_disco : IMG_LO <= AE2k.FF_got_canary /\ AE2k.FF_got_canary + 8 <= IMG_TOP /\
  IMG_LO <= AE2k.FF_canary /\ AE2k.FF_canary + 8 <= IMG_TOP.
Proof. unfold IMG_LO, IMG_TOP, AE2k.FF_got_canary, AE2k.FF_canary. lia. Qed.

Lemma tj_snp_img_disco : IMG_LO <= IMG_LO /\ IMG_TOP <= IMG_TOP.
Proof. split; apply Z.le_refl. Qed.

Lemma snp_img_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
  YP08.img_byte_ok disco_segs a = true -> exists v, aview disco_segs H m a = Some v.
Proof.
intros H m a Hi. unfold YP08.img_byte_ok, img_byte in Hi. unfold aview, mbyte.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity|].
match type of Hi with (match ?x with Some _ => _ | None => _ end = true) => destruct x as [b|]; [|discriminate Hi] end.
eexists; reflexivity.
Qed.

Lemma snp_canary_rdword : forall (H : word -> bool) (m : word -> option byte),
  exists cval, rdword (aview disco_segs H m) AE2k.FF_canary = Some cval.
Proof.
intros H m.
assert (Hz : YP08.zallb (YP08.img_byte_ok disco_segs) AE2k.FF_canary 8 = true) by (vm_compute; reflexivity).
assert (B : forall k, 0 <= k < 8 -> exists v, aview disco_segs H m (AE2k.FF_canary + k) = Some v).
{ intros k Hk. apply snp_img_aview_some. exact (YP08.zallb_sound _ _ _ (AE2k.FF_canary + k) Hz ltac:(lia)). }
destruct (B 0 ltac:(lia)) as (v0 & E0). destruct (B 1 ltac:(lia)) as (v1 & E1).
destruct (B 2 ltac:(lia)) as (v2 & E2). destruct (B 3 ltac:(lia)) as (v3 & E3).
destruct (B 4 ltac:(lia)) as (v4 & E4). destruct (B 5 ltac:(lia)) as (v5 & E5).
destruct (B 6 ltac:(lia)) as (v6 & E6). destruct (B 7 ltac:(lia)) as (v7 & E7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.

Lemma snp_cr_unowned : forallb (fun r => forallb (AD1y.ext_avoids (fst r) (fst r + snd r)) AF0m.Tfib_owned_static) snp_cr = true.
Proof. vm_compute. reflexivity. Qed.

Lemma snp_cr_rows : forall a, Exists (in_zr a) snp_cr ->
  exists r, In r snp_cr /\ fst r <= a < fst r + snd r /\ fst r + snd r <= 0x22b80.
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha). exists r. split; [exact Hr|]. split; [exact Ha|].
assert (H : forallb (fun r => fst r + snd r <=? 0x22b80) snp_cr = true) by (vm_compute; reflexivity).
apply Z.leb_le. exact (proj1 (forallb_forall _ _) H r Hr).
Qed.

Lemma snp_cr_un_disco : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static AD2l.TfibB) /\ ~ (as_errno AD2l.TfibB <= a < as_errno AD2l.TfibB + 4).
Proof.
intros a Ha. destruct (snp_cr_rows a Ha) as (r & Hr & Hra & Hhi). split.
- exact (AD1u.owned_off AD2l.TfibB AD2l.TfibB_syms (fst r) (fst r + snd r) a
    (proj1 (forallb_forall _ _) snp_cr_unowned r Hr) Hra).
- rewrite (AF0m.ts_errno _ AD2l.TfibB_syms). unfold AF0m.TFIB_ERRNO. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
#[local] Notation PI := PB_disco.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation RLO := (@pa_relro_lo _ disco_listing PI).
#[local] Notation RHI := (@pa_relro_hi _ disco_listing PI).

Lemma tj_snp_canary_of_syms : forall B, AF0m.TfibSyms B ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  exists cval, rdword (aview SEGS (w_H W) mem) AE2k.FF_got_canary = Some AE2k.FF_canary /\
    rdword (aview SEGS (w_H W) mem) AE2k.FF_canary = Some cval.
Proof.
intros B HB ly S W mem md HAR.
pose proof (AE22.got_canary_of_AR B HB ly S W mem md HAR) as HG.
destruct (snp_canary_rdword (w_H W) mem) as (cval & HC).
exists cval. split; [|exact HC].
exact (AF0x.val_mem_rdword (w_H W) mem AE2k.FF_got_canary AE2k.FF_canary ltac:(unfold AE2k.FF_canary; lia) HG).
Qed.

Lemma tj_snp_canary_disco : forall ly S (W : world SEGS) mem md, AR SEGS AD2l.TfibB ly S W mem md ->
  exists cval, rdword (aview SEGS (w_H W) mem) AE2k.FF_got_canary = Some AE2k.FF_canary /\
    rdword (aview SEGS (w_H W) mem) AE2k.FF_canary = Some cval.
Proof. exact (tj_snp_canary_of_syms AD2l.TfibB AD2l.TfibB_syms). Qed.

Lemma snp_consts_of_arodata_disco : forall (W : world SEGS) mem,
  arodata_okP SEGS RLO RHI AD2l.TfibB (aview SEGS (w_H W) mem) -> consts_view SEGS W mem snp_cr.
Proof.
intros W mem HR a Ha. destruct (snp_cr_rows a Ha) as (r & Hr & Hra & Hhi). apply HR.
- left. exact (snp_cr_in_rom a Ha).
- exact (AD1u.owned_off AD2l.TfibB AD2l.TfibB_syms (fst r) (fst r + snd r) a
    (proj1 (forallb_forall _ _) snp_cr_unowned r Hr) Hra).
- rewrite (AF0m.ts_errno _ AD2l.TfibB_syms). unfold AF0m.TFIB_ERRNO. lia.
Qed.

End d.
