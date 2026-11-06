(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/UciPPa.v (commit 8c3eb0365c8c; itself from proofs/libreac/fuzz_decode/lib/A/Prog/DecodePa.v, from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v through proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v) for reac-repacer/fuzz_uci's image B, as fuzz_decode's released lib/B/Prog/DecodeBPa.v twins its lib/A/Prog/DecodePa.v: the listing is image B's (uci_listing over usym of lib/B/Prog/UciPList.v, generated from fuzz_uci.asan-ubsan by provenance/prog-gen/B/run.sh), the image range is lib/B/YImgTop.v's IMG_LO .. IMG_TOP, the listing's 10 objects (uci_nobj of lib/B/Prog/UciPAddr.v) and uci_xcalls (the listing's 5 program functions); the image-generic Pa engine stays lib/A/Prog's. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms UciPList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable usym) := mkPAListing {
pl_tpi : ptree usym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition uci_tpi : ptree usym := ptree_of_list uci_listing.
Definition uci_tw : ctable := Eval vm_compute in (tw_of 0 uci_listing).
#[global] Instance PL_uci : PAListing uci_listing :=
{| pl_tpi := uci_tpi; pl_tpi_eq := eq_refl; pl_tw := uci_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition uci_xcalls : list (usym * Z) :=
[ (US_check_no_overread, AF_check_no_overread);
(US_check_value, AF_check_value);
(US_check_clamp, AF_check_clamp);
(US_rp_hot_clamp, AF_rp_hot_clamp);
(US_rp_uci_int, AF_rp_uci_int) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable usym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : usym -> Z;
pa_cert : pi_check usym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, layout_ok ly -> ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 10)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) uci_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable usym} {PI : PAImg L}.
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
Lemma pa_sigma_check_no_overread : pa_sigma US_check_no_overread = pa_val A_TEXT + AF_check_no_overread.
Proof. apply pa_xcalls. cbn [In uci_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_value : pa_sigma US_check_value = pa_val A_TEXT + AF_check_value.
Proof. apply pa_xcalls. cbn [In uci_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_clamp : pa_sigma US_check_clamp = pa_val A_TEXT + AF_check_clamp.
Proof. apply pa_xcalls. cbn [In uci_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_hot_clamp : pa_sigma US_rp_hot_clamp = pa_val A_TEXT + AF_rp_hot_clamp.
Proof. apply pa_xcalls. cbn [In uci_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_uci_int : pa_sigma US_rp_uci_int = pa_val A_TEXT + AF_rp_uci_int.
Proof. apply pa_xcalls. cbn [In uci_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
