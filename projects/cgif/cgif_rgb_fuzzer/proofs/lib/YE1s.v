(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YK05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03 YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2f1cc.
Definition img_ro_chunks {imgk : img} : list YQ0b.chunk :=
[ YQ0b.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YQ0b.mkChunk 0x102f0 (CImg ((0x10308 + D_8) - 0x102f0));
YQ0b.mkChunk (0x10310 + D_10) (CImg ((0x10328 + D_10) - (0x10310 + D_10)));
YQ0b.mkChunk (0x10330 + D_18) (CImg ((0x103a0 + D_20) - (0x10330 + D_18)));
YQ0b.mkChunk (0x103b0 + D_20) (CImg ((0x103c0 + D_20) - (0x103b0 + D_20)));
YQ0b.mkChunk (0x103c8 + D_20) (CImg ((0x10430 + D_20) - (0x103c8 + D_20)));
YQ0b.mkChunk (0x10470 + D_20) (CImg ((0x10530 + D_20) - (0x10470 + D_20)));
YQ0b.mkChunk (0x10570 + D_20) (CImg ((0x1cdaf + D_m9) - (0x10570 + D_20)));
YQ0b.mkChunk (0x1cdc4 + D_m9) (CImg ((0x20c3c + D_m8) - (0x1cdc4 + D_m9)));
YQ0b.mkChunk (0x20c40 + D_m8) (CImg (0x20ec0 - (0x20c40 + D_m8)));
YQ0b.mkChunk 0x20ee0 (CImg (0x20f00 - 0x20ee0));
YQ0b.mkChunk 0x20f20 (CImg (0x214a8 - 0x20f20));
YQ0b.mkChunk 0x214ac (CImg (0x2150c - 0x214ac));
YQ0b.mkChunk 0x2150e (CImg (IMG_RO_HI - 0x2150e)) ].
Definition img_ro_region {imgk : img} : YQ0b.region := YQ0b.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 img_ro_chunks.
Definition ro_img {imgk : img} (m : word -> option byte) : Prop := forall E, region_ok tfxsegs E m img_ro_region.
Definition ro_clean (m : word -> option byte) : Prop :=
forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m x = None.
Lemma img_ro_bytes_ok {imgk : img} : forallb (fun c => zallb (img_byte_ok tfxsegs) (YQ0b.c_off c) (Z.to_nat (c_len c))) img_ro_chunks = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma img_ro_chunks_inside {imgk : img} : Forall (fun c => IMG_RO_LO <= YQ0b.c_off c /\ YQ0b.c_off c + c_len c <= IMG_RO_HI /\ exists n, YQ0b.c_val c = CImg n) img_ro_chunks.
Proof. unfold img_ro_chunks, IMG_RO_LO, IMG_RO_HI. repeat (img_apply Forall_cons; [img_try (cbn; split; [img_lia|]; split; [img_lia | eexists; img_refl])|]). img_apply Forall_nil. Qed.




Lemma ro_img_kept {imgk : img} : forall (Hd : word -> bool) (m m' : word -> option byte),
(forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m' x = m x) -> ro_img (mrestrict Hd m) -> ro_img (mrestrict Hd m').
Proof.
intros Hd m m' Heq Hro E. pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; cbn in Ho; img_lia)|].
img_apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [img_try (img_exact Hcb)|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YQ0b.r_base base_val]. rewrite !Z.add_0_l. unfold mbyte, mrestrict.
rewrite (Heq (Z_to_bv 64 (YQ0b.c_off c + i))) by (img_try (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in *; img_lia); img_lia)).
intros Hmb. img_exact Hmb.
Qed.
End d.
