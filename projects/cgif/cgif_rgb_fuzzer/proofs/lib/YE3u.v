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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YK05 YB1u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2f1cc.
Definition img_ro_chunks : list YQ0b.chunk :=
[ YQ0b.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YQ0b.mkChunk 0x102f0 (CImg (0x10310 - 0x102f0));
YQ0b.mkChunk 0x10320 (CImg (0x10338 - 0x10320));
YQ0b.mkChunk 0x10348 (CImg (0x103c0 - 0x10348));
YQ0b.mkChunk 0x103d0 (CImg (0x103e0 - 0x103d0));
YQ0b.mkChunk 0x103e8 (CImg (0x10450 - 0x103e8));
YQ0b.mkChunk 0x10490 (CImg (0x10550 - 0x10490));
YQ0b.mkChunk 0x10590 (CImg (0x1cda6 - 0x10590));
YQ0b.mkChunk 0x1cdbb (CImg (0x20c34 - 0x1cdbb));
YQ0b.mkChunk 0x20c38 (CImg (0x20ec0 - 0x20c38));
YQ0b.mkChunk 0x20ee0 (CImg (0x20f00 - 0x20ee0));
YQ0b.mkChunk 0x20f20 (CImg (0x214a8 - 0x20f20));
YQ0b.mkChunk 0x214ac (CImg (0x2150c - 0x214ac));
YQ0b.mkChunk 0x2150e (CImg (IMG_RO_HI - 0x2150e)) ].
Definition img_ro_region : YQ0b.region := YQ0b.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 img_ro_chunks.
Definition ro_img (m : word -> option byte) : Prop := forall E, region_ok trbsegs E m img_ro_region.
Lemma img_ro_bytes_ok : forallb (fun c => zallb (img_byte_ok trbsegs) (YQ0b.c_off c) (Z.to_nat (c_len c))) img_ro_chunks = true.
Proof. first [ exact (YE1s.img_ro_bytes_ok (imgk := YF00.K_trb)) | solve [ eapply (YE1s.img_ro_bytes_ok (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1s.img_ro_bytes_ok (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Lemma img_ro_chunks_inside : Forall (fun c => IMG_RO_LO <= YQ0b.c_off c /\ YQ0b.c_off c + c_len c <= IMG_RO_HI /\ exists n, YQ0b.c_val c = CImg n) img_ro_chunks.
Proof. first [ exact (YE1s.img_ro_chunks_inside (imgk := YF00.K_trb)) | solve [ eapply (YE1s.img_ro_chunks_inside (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1s.img_ro_chunks_inside (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Lemma ro_img_kept : forall (Hd : word -> bool) (m m' : word -> option byte),
(forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m' x = m x) -> ro_img (mrestrict Hd m) -> ro_img (mrestrict Hd m').
Proof. first [ exact (YE1s.ro_img_kept (imgk := YF00.K_trb)) | solve [ eapply (YE1s.ro_img_kept (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1s.ro_img_kept (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End a.
