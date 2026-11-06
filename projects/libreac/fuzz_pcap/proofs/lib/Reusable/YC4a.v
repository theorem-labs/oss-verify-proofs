(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v, with its module paths changed, names YP0a -> PaSym, YP0b -> PaTable, YP0c -> PaShadow, YP0d -> PaRun. *)
(* Modified by Theorem Labs, 2026-10: the cgif_file_fuzzer instances of the classes below (asan3_0_tpi, asan3_0_tw, PL_asan3_0, asan3_1_tpi, asan3_1_tw, PL_asan3_1, asan3_xcalls) and the Require of YI0x/YI0y are removed, and the image bounds cite YImgTop.IMG_LO / YImgTop.IMG_TOP: they state cgif's own program listing. The classes and their lemmas stay; no fuzz_pcap file instantiates them (fuzz_pcap's program walk states its own copy, lib/A/Prog/PcapPa.v). *)
(* Modified by Theorem Labs, 2026-10: the object bound of pa_obj_img / pa2_obj_img / pa2_obj1_img, cgif's 13 program objects, is the class parameter nobj of PAImg and PAImg2: an instance states its listing's object count in its type. *)
(* lib.A Requires here are image-free engine files (PaTable, PaSym, PaRun, PaShadow / RelimCut); the YImgTop bounds hold for both images. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI0w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
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
Class PAImg (L : ptable asym) (nobj : nat) := mkPAImg {
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
pa_obj_img : forall i, (i < nobj)%nat -> YImgTop.IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= YImgTop.IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a
}.
Section c.
Context {L : ptable asym} {nobj : nat} {PI : PAImg L nobj}.
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
Class PAImg2 (L0 L1 : ptable asym) (X : list (asym * Z)) (nobj : nat) := mkPAImg2 {
pa2_segs : list Segment;
pa2_tbl : ctable;
pa2_tbl_ok : table_ok pa2_segs pa2_tbl;
pa2_val0 : nat -> Z;
pa2_val1 : nat -> Z;
pa2_sigma : asym -> Z;
pa2_cert0 : pi_check asym (clookup pa2_tbl) pa2_val0 pa2_sigma L0 = true;
pa2_cert1 : pi_check asym (clookup pa2_tbl) pa2_val1 pa2_sigma L1 = true;
pa2_B0_ok : 0 <= pa2_val0 A_TEXT /\ pa2_val0 A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa2_val0 A_TEXT mod 4 = 0;
pa2_B1_ok : 0 <= pa2_val1 A_TEXT /\ pa2_val1 A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa2_val1 A_TEXT mod 4 = 0;
pa2_val0_range : forall a, 0 <= pa2_val0 a < 2 ^ 64;
pa2_val01 : forall a, a <> A_TEXT -> pa2_val1 a = pa2_val0 a;
pa2_wx : wx_segs_nowrap pa2_segs;
pa2_segs_low : forall a, in_img pa2_segs a -> 0 <= a < kLowMemEnd;
pa2_img_range : forall a, in_img pa2_segs a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP;
pa2_img_cover : forall ly S md, ALedger pa2_segs ly S md -> fst (ly_img ly) <= YImgTop.IMG_LO /\ YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa2_obj_img : forall i, (i < nobj)%nat -> YImgTop.IMG_LO <= pa2_val0 (A_OBJ i) /\ pa2_val0 (A_OBJ i) + 8 <= YImgTop.IMG_TOP;
pa2_relro_lo : Z;
pa2_relro_hi : Z;
pa2_relro_img : forall a, pa2_relro_lo <= a < pa2_relro_hi -> in_img pa2_segs a;
pa2_xcalls : forall s k, In (s, k) X -> pa2_sigma s = pa2_val1 A_TEXT + k
}.
Section d.
Context {L0 L1 : ptable asym} {X : list (asym * Z)} {nobj : nat} {X2 : PAImg2 L0 L1 X nobj}.
Lemma pa2_val1_range : forall a, 0 <= pa2_val1 a < 2 ^ 64.
Proof.
intros a. destruct (Nat.eq_dec a A_TEXT) as [-> | Ha].
- pose proof pa2_B1_ok. lia.
- rewrite (pa2_val01 a Ha). apply pa2_val0_range.
Qed.
Lemma pa2_obj1_img : forall i, (i < nobj)%nat -> YImgTop.IMG_LO <= pa2_val1 (A_OBJ i) /\ pa2_val1 (A_OBJ i) + 8 <= YImgTop.IMG_TOP.
Proof. intros i Hi. rewrite (pa2_val01 (A_OBJ i)) by (unfold A_OBJ, A_TEXT; lia). exact (pa2_obj_img i Hi). Qed.
#[global] Instance PI0_of : PAImg L0 nobj := {|
pa_segs := pa2_segs; pa_tbl := pa2_tbl; pa_tbl_ok := pa2_tbl_ok; pa_val := pa2_val0; pa_sigma := pa2_sigma; pa_cert := pa2_cert0;
pa_B_ok := pa2_B0_ok; pa_val_range := pa2_val0_range; pa_wx := pa2_wx; pa_segs_low := pa2_segs_low; pa_img_range := pa2_img_range;
pa_img_cover := pa2_img_cover; pa_obj_img := pa2_obj_img; pa_relro_lo := pa2_relro_lo; pa_relro_hi := pa2_relro_hi; pa_relro_img := pa2_relro_img |}.
#[global] Instance PI1_of : PAImg L1 nobj := {|
pa_segs := pa2_segs; pa_tbl := pa2_tbl; pa_tbl_ok := pa2_tbl_ok; pa_val := pa2_val1; pa_sigma := pa2_sigma; pa_cert := pa2_cert1;
pa_B_ok := pa2_B1_ok; pa_val_range := pa2_val1_range; pa_wx := pa2_wx; pa_segs_low := pa2_segs_low; pa_img_range := pa2_img_range;
pa_img_cover := pa2_img_cover; pa_obj_img := pa2_obj1_img; pa_relro_lo := pa2_relro_lo; pa_relro_hi := pa2_relro_hi; pa_relro_img := pa2_relro_img |}.
Lemma pa2_sigma_x : forall s k, In (s, k) X -> @pa_sigma L0 nobj PI0_of s = @pa_val L1 nobj PI1_of A_TEXT + k.
Proof. intros s k H. exact (pa2_xcalls s k H). Qed.
Lemma pa2_segs_01 : @pa_segs L0 nobj PI0_of = @pa_segs L1 nobj PI1_of.   Proof. reflexivity. Qed.
Lemma pa2_sigma_01 : @pa_sigma L0 nobj PI0_of = @pa_sigma L1 nobj PI1_of. Proof. reflexivity. Qed.
Lemma pa2_obj_01 : forall i, @pa_val L1 nobj PI1_of (A_OBJ i) = @pa_val L0 nobj PI0_of (A_OBJ i).
Proof. intros i. cbn [pa_val PI0_of PI1_of]. apply pa2_val01. unfold A_OBJ, A_TEXT. lia. Qed.
End d.
(* The cgif_file_fuzzer instances of these classes (asan3_0_tpi, asan3_0_tw, PL_asan3_0, asan3_1_*, PL_asan3_1,
   asan3_xcalls) are removed with the listing files they read: they state cgif's own program. No fuzz_pcap file
   instantiates these classes; fuzz_pcap's program walk states its own copy in lib/A/Prog/PcapPa.v. *)
End b.
