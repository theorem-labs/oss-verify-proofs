(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v (tfibX_lib_consts_chk, tfibX_lib, tfibX_LAWS, tfibX_env, tfibX_PALib0, tfibX_PALibF0, tfibX_FFL) to libreac/fuzz_disco's A image: the instance is DiscoImg's PB_disco, B is AD2l.TfibB, and the records are the A ones (DiscoPaLib.PALib, DiscoFrame.PALibF, YCbq.frame_flag_lawP, ACeg.TfibLib). tl_lib_consts is checked over fuzz_disco's read-only ranges (ACeg.lib_consts_of_ro), tl_errno_img over fuzz_disco's fourth load segment, and the image cover lemma is PB_disco's pa_img_cover (IMG_LO..IMG_TOP). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP02 YK04 YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AF0l AF0m ACej AD2l ACeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym DiscoSyms DiscoList DiscoPa DiscoRoList DiscoImg DiscoPaLib DiscoFrame.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {rc : YM05.RunCeil}.
Lemma disco_lib_consts_chk :
forallb (fun q => forallb (fun r => (fst q + snd q <=? fst r) || (fst r + snd r <=? fst q)) AF0m.Tfib_owned_static
&& ((fst q + snd q <=? AF0m.TFIB_ERRNO) || (AF0m.TFIB_ERRNO + 4 <=? fst q)))%bool DiscoRoList.disco_ro_ranges = true.
Proof. vm_compute. reflexivity. Qed.
Theorem disco_TfibLib : ACeg.TfibLib AD2l.TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno AD2l.TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno AD2l.TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 3 = Some (0xa2000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
- intros a Ha. refine (lib_consts_of_ro AD2l.TfibB _ a Ha).
apply Forall_forall. intros q Hq x Hx.
pose proof (proj1 (forallb_forall _ _) disco_lib_consts_chk q Hq) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. cbn [as_owned_static as_errno AD2l.TfibB]. split.
+ intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) Hb1 r Hr) as Hc. cbn beta in Hc.
apply Bool.orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
+ apply Bool.orb_prop in Hb2 as [Hc|Hc]; apply Z.leb_le in Hc; lia.
- cbn [as_gp AD2l.TfibB]. unfold TFIB_GP. lia.
Qed.
#[local] Abbreviation B := AD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ disco_listing PB_disco).
Definition disco_LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Definition disco_env : YCbq.api_env SEGS B := ACeg.tl_env B disco_TfibLib.
Lemma disco_PALib : DiscoPaLib.PALib (PI := PB_disco) B.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact disco_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Lemma disco_PALibF : DiscoFrame.PALibF (PI := PB_disco) B.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ discriminate | left; discriminate | right; discriminate ].
Qed.
Lemma disco_FFL : YCbq.frame_flag_lawP SEGS B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ disco_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ disco_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (pa_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End b.
