(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 1be0f53d96cb9d6c) by the internal file gen_regions.py: [IMG_RO_LO, IMG_RO_HI) is the image's read-only PT_LOAD (p_vaddr .. p_vaddr + p_filesz); img_ro_chunks are the image chunks of the generated A/AD2j.v's read-only rows (the R_A1 rows) inside it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* IMG_RO_LO / IMG_RO_HI: the read-only PT_LOAD (flags R, no W, no X) of fuzz_preset.asan (sha256 1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44), read by pyelftools: p_vaddr 0x10000, p_vaddr + p_filesz 0x30374. *)
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x30374.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x103b0 - 0x10330));
YP09.mkChunk 0x103c0 (CImg (0x103c8 - 0x103c0));
YP09.mkChunk 0x103d0 (CImg (0x10438 - 0x103d0));
YP09.mkChunk 0x10478 (CImg (0x10538 - 0x10478));
YP09.mkChunk 0x10578 (CImg (0x1ce65 - 0x10578));
YP09.mkChunk 0x1ce7a (CImg (0x20cc4 - 0x1ce7a));
YP09.mkChunk 0x20cc8 (CImg (0x20f65 - 0x20cc8));
YP09.mkChunk 0x20f80 (CImg (0x20f86 - 0x20f80));
YP09.mkChunk 0x20fa0 (CImg (0x20fa5 - 0x20fa0));
YP09.mkChunk 0x20fc0 (CImg (0x20ff8 - 0x20fc0));
YP09.mkChunk 0x21020 (CImg (0x21027 - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21043 - 0x21040));
YP09.mkChunk 0x21060 (CImg (0x21065 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21088 - 0x21080));
YP09.mkChunk 0x210a0 (CImg (0x210aa - 0x210a0));
YP09.mkChunk 0x210c0 (CImg (0x210cb - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210e7 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x21106 - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x21127 - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x21147 - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x21166 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x21189 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211a6 - 0x211a0));
YP09.mkChunk 0x211c0 (CImg (0x211c1 - 0x211c0));
YP09.mkChunk 0x211e0 (CImg (0x211e2 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x21202 - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21222 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21242 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21262 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21282 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212a2 - 0x212a0));
YP09.mkChunk 0x212c0 (CImg (0x212c2 - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212f1 - 0x212e0));
YP09.mkChunk 0x21320 (CImg (0x21322 - 0x21320));
YP09.mkChunk 0x21340 (CImg (0x21342 - 0x21340));
YP09.mkChunk 0x21360 (CImg (0x21363 - 0x21360));
YP09.mkChunk 0x21380 (CImg (0x21395 - 0x21380));
YP09.mkChunk 0x213c0 (CImg (0x21421 - 0x213c0));
YP09.mkChunk 0x21440 (CImg (0x21442 - 0x21440));
YP09.mkChunk 0x21460 (CImg (0x21465 - 0x21460));
YP09.mkChunk 0x21480 (CImg (0x21486 - 0x21480));
YP09.mkChunk 0x214a0 (CImg (0x214a5 - 0x214a0));
YP09.mkChunk 0x214c0 (CImg (0x214c2 - 0x214c0));
YP09.mkChunk 0x214e0 (CImg (0x214e2 - 0x214e0));
YP09.mkChunk 0x21500 (CImg (0x21502 - 0x21500));
YP09.mkChunk 0x21520 (CImg (0x21522 - 0x21520));
YP09.mkChunk 0x21540 (CImg (0x21543 - 0x21540));
YP09.mkChunk 0x21560 (CImg (0x21562 - 0x21560));
YP09.mkChunk 0x21580 (CImg (0x21582 - 0x21580));
YP09.mkChunk 0x215a0 (CImg (0x215a2 - 0x215a0));
YP09.mkChunk 0x215c0 (CImg (0x215c2 - 0x215c0));
YP09.mkChunk 0x215e0 (CImg (0x215e4 - 0x215e0));
YP09.mkChunk 0x21600 (CImg (0x21603 - 0x21600));
YP09.mkChunk 0x21620 (CImg (0x21623 - 0x21620));
YP09.mkChunk 0x21640 (CImg (0x21643 - 0x21640));
YP09.mkChunk 0x21660 (CImg (0x21667 - 0x21660));
YP09.mkChunk 0x21680 (CImg (0x21683 - 0x21680));
YP09.mkChunk 0x216a0 (CImg (0x21c24 - 0x216a0));
YP09.mkChunk 0x21c28 (CImg (0x21c88 - 0x21c28));
YP09.mkChunk 0x21c8a (CImg (IMG_RO_HI - 0x21c8a)) ].
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
