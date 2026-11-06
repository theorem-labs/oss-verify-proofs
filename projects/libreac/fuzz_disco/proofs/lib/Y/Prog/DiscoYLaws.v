(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/YCed.v (tfibX_lib, tfibX_PALib0, tfibX_PALibF0,
   tfibX_FFL) for libreac/fuzz_disco's asan-ubsan image, with its module paths changed. tl_lib_consts is discharged by one closed
   check over YRo.tfib_ro_ranges (fuzz_disco's lib_const_addr; cgif_file's was two fixed ranges); tl_errno_img finds the segment
   that holds the errno cell by one closed check (cgif_file named segment 3); PALibF has fuzz_disco's ten fields. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK04 YG00 YG0a YG01 YG0f YG0n YG0s YG0q YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YF0m YF0l YCej YD2l YCeh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC4a YCbj YC1f YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma tfibY_lib_consts_chk :
forallb (fun r => forallb (fun o => (fst r + snd r <=? fst o) || (fst o + snd o <=? fst r)) Tfib_owned_static &&
((fst r + snd r <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst r)))%bool
YRo.tfib_ro_ranges = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfibY_errno_seg_chk :
existsb (fun s : Segment => (Z.of_N (seg_base s) <=? TFIB_ERRNO) && (TFIB_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Theorem tfib_TfibLib : TfibLib TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold in_img.
destruct (proj1 (existsb_exists _ _) tfibY_errno_seg_chk) as (sg & Hin & Hb). cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
- intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold lib_const_addr in Ha.
apply Exists_exists in Ha as (r & Hr & Ha1 & Ha2).
pose proof (proj1 (forallb_forall _ _) tfibY_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. split.
+ intros HE. apply Exists_exists in HE as (o & Ho & Ho1 & Ho2).
pose proof (proj1 (forallb_forall _ _) Hb1 o Ho) as Hc. cbn beta in Hc.
apply Bool.orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
+ apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2; lia.
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfibY_LAWS : AR_laws tfibsegs TfibB := AR_laws_ok tfibsegs TfibB.
Definition tfibY_env : api_env tfibsegs TfibB := tl_env TfibB tfib_TfibLib.
Lemma tfib_PALib : PALib (PI := PB_tfib) TfibB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact tfibY_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Lemma tfib_PALibF : PALibF (PI := PB_tfib) TfibB.
Proof.
constructor.
- reflexivity.
- vm_compute. split; intros X; discriminate X.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ discriminate | left; discriminate | right; discriminate ].
Qed.
Lemma tfib_FFL : frame_flag_lawP tfibsegs TfibB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ tfibY_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ tfibY_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End b.
