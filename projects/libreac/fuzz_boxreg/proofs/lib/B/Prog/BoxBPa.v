(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_boxreg's ASan+UBSan program walk (as fuzz_identity's lib/B/Prog/IdentBPa.v, ea5560a967b), as lib/A/Prog/BoxPa.v for the ASan build: module paths changed; the listing is fuzz_boxreg.asan-ubsan's one listing over bbsym (cgif's two listings, PAImg2 and the cross-listing calls are left out); the image range is Reusable/YImgTop.v's [IMG_LO, IMG_TOP) and pa_obj_img covers its 14 objects. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI5b YI5c.
(* Guard (a Theorem Labs lane 22:56Z; fuzz_state S0 bffd3c8f802): the PLAIN build's sink instances of YI5b / YI5c are removed as
   hints for the whole B walk layer (every B file Requires BoxBPa); see lib/A/Prog/BoxPa.v. *)
(* global on purpose: keeps the plain sink instances out of every importer of this file (knock-case defect, a Theorem Labs lane's 06:30Z sweep; a Theorem Labs lane 10:42Z) *)
#[global] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable bbsym) := mkPAListing {
pl_tpi : ptree bbsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition boxb_tpi : ptree bbsym := ptree_of_list boxb_listing.
Definition boxb_tw : ctable := Eval vm_compute in (tw_of 0 boxb_listing).
#[global] Instance PL_boxb : PAListing boxb_listing :=
{| pl_tpi := boxb_tpi; pl_tpi_eq := eq_refl; pl_tw := boxb_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base (as fuzz_grant's GrantPa.v
   grant_xcalls): a walk that calls one meets the callee's contract address through pa_xcalls. *)
Definition boxb_xcalls : list (bbsym * Z) :=
[ (BB_check, AF_check);
(BB_read_name, AF_read_name);
(BB_range_free, AF_range_free);
(BB_read_mac, AF_read_mac);
(BB_reac_boxreg_init, AF_reac_boxreg_init);
(BB_reac_boxreg_find, AF_reac_boxreg_find);
(BB_mac_is_zero, AF_mac_is_zero);
(BB_reac_boxreg_declare, AF_reac_boxreg_declare);
(BB_range_taken, AF_range_taken);
(BB_lowest_free_base, AF_lowest_free_base);
(BB_reac_boxreg_add, AF_reac_boxreg_add);
(BB_reac_boxreg_set_name, AF_reac_boxreg_set_name) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable bbsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : bbsym -> Z;
pa_cert : pi_check bbsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 14)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) boxb_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable bbsym} {PI : PAImg L}.
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
Lemma pa_sigma_check : pa_sigma BB_check = pa_val A_TEXT + AF_check.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_read_name : pa_sigma BB_read_name = pa_val A_TEXT + AF_read_name.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_range_free : pa_sigma BB_range_free = pa_val A_TEXT + AF_range_free.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_read_mac : pa_sigma BB_read_mac = pa_val A_TEXT + AF_read_mac.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_boxreg_init : pa_sigma BB_reac_boxreg_init = pa_val A_TEXT + AF_reac_boxreg_init.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_boxreg_find : pa_sigma BB_reac_boxreg_find = pa_val A_TEXT + AF_reac_boxreg_find.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_mac_is_zero : pa_sigma BB_mac_is_zero = pa_val A_TEXT + AF_mac_is_zero.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_boxreg_declare : pa_sigma BB_reac_boxreg_declare = pa_val A_TEXT + AF_reac_boxreg_declare.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_range_taken : pa_sigma BB_range_taken = pa_val A_TEXT + AF_range_taken.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_lowest_free_base : pa_sigma BB_lowest_free_base = pa_val A_TEXT + AF_lowest_free_base.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_boxreg_add : pa_sigma BB_reac_boxreg_add = pa_val A_TEXT + AF_reac_boxreg_add.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_boxreg_set_name : pa_sigma BB_reac_boxreg_set_name = pa_val A_TEXT + AF_reac_boxreg_set_name.
Proof. apply pa_xcalls. cbn [In boxb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
