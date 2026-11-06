(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: extracted from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v at c8557374ad2e, with its module paths changed: lines 1-29, 40-78 and 129 are taken (A_LIM, A_LIM_text, the class PAListing, the class PAImg, pa_fetch_ok, Eimg, Eimg_env, Eimg_low and Eimg_img); lines 30-39 (cgif's PAListing instances PL_asan3_0 and PL_asan3_1 and their trees and tables, on cgif's listings), 79-126 (the class PAImg2 for cgif's two listings, with its instances PI0_of and PI1_of and its lemmas) and 127-128 (asan3_xcalls, cgif's cross-listing call sites) are left out. In the Require of line 12, cgif's second listing YI0y is dropped; YI0w (the symbol type asym) and YI0x (the listing) are knock's own, generated from knock's binary. *)
(* Modified by Theorem Labs, 2026-10: the image top in pa_img_range, pa_img_cover and pa_obj_img changed from cgif's to knock's 0x5f3000 (both knock ASan builds); the image base 0x10000 is unchanged; both bounds are cited from YImgTop (IMG_LO = 0x10000, IMG_TOP = 0x5f3000) instead of written as literals; pa_obj_img's object count changed from cgif's 13 to knock's 9; the PAListing instances of donor lines 30-39 are restored on knock's two listings (knock_asan_tpi, knock_asan_tw, PL_knock_asan on YI0x's knock_asan_listing; knock_asanubsan_tpi, knock_asanubsan_tw, PL_knock_asanubsan on YI0y's knock_asanubsan_listing), with the donor's field proofs, and YI0y, knock's asan-ubsan listing from a Theorem Labs lane, is Required again. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YC4a.v at origin/ossv/recipes 4b6f0df50aa7 (fuzz_knock's released ASan tree); module paths changed to libdiginet/fuzz_codec; image A form: knock's PAListing instances PL_knock_asan / PL_knock_asanubsan with their trees and tables (donor lines 34-43) are removed (codec's instances are in lib/A/APgImg.v and lib/AU/APgImg.v), pa_obj_img's object count is 33 (fuzz_codec.asan's listing objects; was knock's 9), and the image bounds stay YImgTop.IMG_LO / IMG_TOP, which for fuzz_codec are image A's 0x10000 / 0x5fb000. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0d YP0c YI0w YI0x YI0y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* 512 >= largest atom used, A_HI 9 = 289; audit 21:20Z *)
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable asym) := mkPAListing {
pl_tpi : ptree asym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable asym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : asym -> Z;
pa_cert : pi_check asym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= YImgTop.IMG_LO /\ YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
(* 9 objects A_OBJ 0..8 in both knock ASan builds (0 GOT->UAR slot, 1 GOT->shadow slot, 2 .rodata frame-descr, 3 LLVMF pc word, 4/5 GOT __start/__stop_asan_globals, 6 ___asan_globals_registered, 7 shadow-base cell, 8 UAR flag cell), all inside [IMG_LO, IMG_TOP); an internal audit of both builds (nobj 9; 7 and 8 are built by no slot, so the listings YI0x/YI0y name A_OBJ 0..6 only) *)
pa_obj_img : forall i, (i < 33)%nat -> YImgTop.IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= YImgTop.IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a
}.
Section c.
Context {L : ptable asym} {PI : PAImg L}.
Lemma pa_fetch_ok : forall pc w, clookup pa_tbl pc = Some w -> fetch_word pa_segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Proof. intros pc w H. exact (pa_tbl_ok pc w H). Qed.
Definition Eimg (E : env) : env :=
{| ew := fun n => if ((A_TEXT <=? n) && (n <? A_LIM))%nat then Z_to_bv 64 (pa_val n) else ew E n; ed := ed E |}.
Lemma Eimg_env : forall E, img_env pa_val A_LIM (Eimg E).
Proof.
intros E a [H1 H2]. cbn [Eimg ew]. replace ((A_TEXT <=? a) && (a <? A_LIM))%nat%bool with true.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. pose proof (pa_val_range a). change (bv_modulus 64) with (2 ^ 64). lia.
- symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia].
Qed.
Lemma Eimg_low : forall E n, (n < A_TEXT)%nat -> ew (Eimg E) n = ew E n.
Proof. intros E n Hn. cbn [Eimg ew]. replace (A_TEXT <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. Qed.
Lemma Eimg_img : forall E n, (A_TEXT <= n < A_LIM)%nat -> ew (Eimg E) n = Z_to_bv 64 (pa_val n).
Proof.
intros E n [H1 H2]. cbn [Eimg ew]. replace ((A_TEXT <=? n) && (n <? A_LIM))%nat%bool with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia].
Qed.
End c.
End b.
