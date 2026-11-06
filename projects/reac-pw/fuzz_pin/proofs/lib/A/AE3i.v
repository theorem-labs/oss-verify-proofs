(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_pin image A by ae3i.py 3cf49addef7e from fuzz_pin.asan and lib/A/AF0m.v's Tfib_owned_static (IMG_RO_HI = this image's read-only PT_LOAD end 0x2f31c), template proofs/cgif/cgif_file_fuzzer/lib/A/AE3i.v at c8557374ad2e, module paths changed *)
(* Read from: fuzz_pin.asan (reac-pw/fuzz_pin asan) sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16; unstripped twin sha256 435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2f31c.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x10398 - 0x10330));
YP09.mkChunk 0x103a8 (CImg (0x103b0 - 0x103a8));
YP09.mkChunk 0x103b8 (CImg (0x10420 - 0x103b8));
YP09.mkChunk 0x10460 (CImg (0x10520 - 0x10460));
YP09.mkChunk 0x10560 (CImg (0x1cc9b - 0x10560));
YP09.mkChunk 0x1ccb0 (CImg (0x20af8 - 0x1ccb0));
YP09.mkChunk 0x20afc (CImg (0x20d82 - 0x20afc));
YP09.mkChunk 0x20da0 (CImg (0x20dc6 - 0x20da0));
YP09.mkChunk 0x20de0 (CImg (0x20df7 - 0x20de0));
YP09.mkChunk 0x20e20 (CImg (0x20e26 - 0x20e20));
YP09.mkChunk 0x20e40 (CImg (0x20e56 - 0x20e40));
YP09.mkChunk 0x20e80 (CImg (0x20e87 - 0x20e80));
YP09.mkChunk 0x20ea0 (CImg (0x20ebd - 0x20ea0));
YP09.mkChunk 0x20ee0 (CImg (0x20eec - 0x20ee0));
YP09.mkChunk 0x20f00 (CImg (0x20f1d - 0x20f00));
YP09.mkChunk 0x20f40 (CImg (0x20f46 - 0x20f40));
YP09.mkChunk 0x20f60 (CImg (0x20f77 - 0x20f60));
YP09.mkChunk 0x20fa0 (CImg (0x20fa6 - 0x20fa0));
YP09.mkChunk 0x20fc0 (CImg (0x20fd8 - 0x20fc0));
YP09.mkChunk 0x21000 (CImg (0x21007 - 0x21000));
YP09.mkChunk 0x21020 (CImg (0x21038 - 0x21020));
YP09.mkChunk 0x21060 (CImg (0x21067 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21098 - 0x21080));
YP09.mkChunk 0x210c0 (CImg (0x210c7 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210f7 - 0x210e0));
YP09.mkChunk 0x21120 (CImg (0x21127 - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x21157 - 0x21140));
YP09.mkChunk 0x21180 (CImg (0x21187 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211b8 - 0x211a0));
YP09.mkChunk 0x211e0 (CImg (0x21764 - 0x211e0));
YP09.mkChunk 0x21768 (CImg (0x217c8 - 0x21768));
YP09.mkChunk 0x217ca (CImg (IMG_RO_HI - 0x217ca)) ].
Definition img_ro_region : YP09.region := YP09.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 img_ro_chunks.
Definition ro_img (m : word -> option byte) : Prop := forall E, region_ok tfibsegs E m img_ro_region.
Definition ro_clean (m : word -> option byte) : Prop :=
forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m x = None.
Lemma img_ro_bytes_ok : forallb (fun c => zallb (img_byte_ok tfibsegs) (YP09.c_off c) (Z.to_nat (c_len c))) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_ro_chunks_inside : Forall (fun c => IMG_RO_LO <= YP09.c_off c /\ YP09.c_off c + c_len c <= IMG_RO_HI /\ exists n, YP09.c_val c = CImg n) img_ro_chunks.
Proof. unfold img_ro_chunks, IMG_RO_LO, IMG_RO_HI. repeat (apply Forall_cons; [cbn; split; [lia|]; split; [lia | eexists; reflexivity]|]). apply Forall_nil. Qed.
Lemma region_ok_img_of : forall E m,
(forall a, IMG_RO_LO <= a < IMG_RO_HI -> img_byte_ok tfibsegs a = true -> mbyte tfibsegs m a = img_byte tfibsegs a) ->
region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hm. unfold region_ok, img_ro_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold IMG_RO_LO; lia|]. split; [unfold IMG_RO_HI; lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
pose proof (zallb_sound _ _ _ (YP09.c_off c + i) Hz ltac:(lia)) as Hb.
rewrite !Z.add_0_l. destruct c as [co cv]; cbn [YP09.c_off YP09.c_val] in *. subst cv. cbn [cbyte].
rewrite (Hm (co + i)) by (first [lia | exact Hb]).
unfold img_byte_ok in Hb. destruct (img_byte tfibsegs (co + i)) as [b|]; [|discriminate]. exists b. split; reflexivity.
Qed.
Lemma region_ok_img_clean : forall E m, ro_clean m -> region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hc. apply region_ok_img_of. intros a Ha _. unfold img_byte, mbyte.
rewrite (Hc (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in Ha; lia); exact Ha). reflexivity.
Qed.
Lemma ro_img_of_clean : forall m, ro_clean m -> ro_img m.
Proof. intros m Hc E. apply region_ok_img_clean. exact Hc. Qed.
Lemma ro_clean_mrestrict : forall (Hd : word -> bool) m, ro_clean m -> ro_clean (mrestrict Hd m).
Proof. intros Hd m Hc x Hx. unfold mrestrict. rewrite (Hc x Hx). destruct (Hd x); reflexivity. Qed.
Lemma ro_img_kept : forall (Hd : word -> bool) (m m' : word -> option byte),
(forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m' x = m x) -> ro_img (mrestrict Hd m) -> ro_img (mrestrict Hd m').
Proof.
intros Hd m m' Heq Hro E. pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l. unfold mbyte, mrestrict.
rewrite (Heq (Z_to_bv 64 (YP09.c_off c + i))) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in *; lia); lia).
intros Hmb. exact Hmb.
Qed.
End d.
