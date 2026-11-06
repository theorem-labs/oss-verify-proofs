(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10 [image A's note, kept from grant A's header; its numbers are fuzz_grant.asan's]: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE3i.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the read-only image chunks are those of fuzz_grant's IMG_REGIONS (A/AD2j.v), split around its 13 registered globals' guard bytes; IMG_RO_HI is 0x2f6ac, the same offset (0x20) into the same .eh_frame entry as cgif_file's 0x2f1ac (the FDE of the function at 0x8e854, cgif's at 0x8fc44). Image B: the read-only image chunks are image B's IMG_REGIONS (lib/B/YD2j.v, a working branch 35735e14404), split around its 13 registered globals' guard bytes and around the owned static at 0x10340; IMG_RO_HI is 0x2f854, the same offset (0x20) into the .eh_frame entry of __multf3 (FDE of the function at 0x8f6b8 in fuzz_grant.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2f854.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10330 - 0x10310));
YP09.mkChunk 0x10338 (CImg (0x10340 - 0x10338)); YP09.mkChunk 0x10348 (CImg (0x103a0 - 0x10348));
YP09.mkChunk 0x103b0 (CImg (0x103b8 - 0x103b0));
YP09.mkChunk 0x103c0 (CImg (0x10428 - 0x103c0));
YP09.mkChunk 0x10468 (CImg (0x10528 - 0x10468));
YP09.mkChunk 0x10568 (CImg (0x1ccff - 0x10568));
YP09.mkChunk 0x1cd14 (CImg (0x20c40 - 0x1cd14));
YP09.mkChunk 0x20c44 (CImg (0x20ed2 - 0x20c44));
YP09.mkChunk 0x20f00 (CImg (0x20f22 - 0x20f00));
YP09.mkChunk 0x20f60 (CImg (0x20f82 - 0x20f60));
YP09.mkChunk 0x20fc0 (CImg (0x20ff2 - 0x20fc0));
YP09.mkChunk 0x21020 (CImg (0x21067 - 0x21020));
YP09.mkChunk 0x21080 (CImg (0x2114c - 0x21080));
YP09.mkChunk 0x21180 (CImg (0x211a0 - 0x21180));
YP09.mkChunk 0x211c0 (CImg (0x211e0 - 0x211c0));
YP09.mkChunk 0x21200 (CImg (0x21222 - 0x21200));
YP09.mkChunk 0x21260 (CImg (0x21282 - 0x21260));
YP09.mkChunk 0x212c0 (CImg (0x21320 - 0x212c0));
YP09.mkChunk 0x21340 (CImg (0x21360 - 0x21340));
YP09.mkChunk 0x21380 (CImg (0x21908 - 0x21380));
YP09.mkChunk 0x2190c (CImg (0x2196c - 0x2190c));
YP09.mkChunk 0x2196e (CImg (IMG_RO_HI - 0x2196e)) ].
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
