(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_scene's program walk: one listing (scene_listing over ssym), fuzz_scene.asan's image range 0x10000..0x5f9000 and 18 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied by path from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v (a working branch acae397d926) for libreac/fuzz_scene's program walk; the module path and the listing's names changed. The listing is scene_listing over ssym, the image range is fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026)'s 0x10000..0x5f9000 and its 18 objects, and scene_xcalls fixes the addresses of the 7 program functions that a slot of the listing calls (SceneList.v's AF_<fn>, from the image's .symtab). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable ssym) := mkPAListing {
pl_tpi : ptree ssym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition scene_tpi : ptree ssym := ptree_of_list scene_listing.
Definition scene_tw : ctable := Eval vm_compute in (tw_of 0 scene_listing).
#[global] Instance PL_scene : PAListing scene_listing :=
{| pl_tpi := scene_tpi; pl_tpi_eq := eq_refl; pl_tw := scene_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition scene_xcalls : list (ssym * Z) :=
[ (SS_check_step, AF_check_step);
(SS_reac_ctrl_checksum_verify, AF_reac_ctrl_checksum_verify);
(SS_reac_ctrl_build_scene_step, AF_reac_ctrl_build_scene_step);
(SS_reac_ctrl_scene_set_mac, AF_reac_ctrl_scene_set_mac);
(SS_reac_ctrl_scene_build, AF_reac_ctrl_scene_build);
(SS_reac_ctrl_parse, AF_reac_ctrl_parse);
(SS_kind_of_link1, AF_kind_of_link1) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable ssym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : ssym -> Z;
pa_cert : pi_check ssym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> 0x10000 <= a < 0x5f9000;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x5f9000 <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 18)%nat -> 0x10000 <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= 0x5f9000;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) scene_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable ssym} {PI : PAImg L}.
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
Lemma pa_sigma_check_step : pa_sigma SS_check_step = pa_val A_TEXT + AF_check_step.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_checksum_verify : pa_sigma SS_reac_ctrl_checksum_verify = pa_val A_TEXT + AF_reac_ctrl_checksum_verify.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_build_scene_step : pa_sigma SS_reac_ctrl_build_scene_step = pa_val A_TEXT + AF_reac_ctrl_build_scene_step.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_scene_set_mac : pa_sigma SS_reac_ctrl_scene_set_mac = pa_val A_TEXT + AF_reac_ctrl_scene_set_mac.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_scene_build : pa_sigma SS_reac_ctrl_scene_build = pa_val A_TEXT + AF_reac_ctrl_scene_build.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_parse : pa_sigma SS_reac_ctrl_parse = pa_val A_TEXT + AF_reac_ctrl_parse.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kind_of_link1 : pa_sigma SS_kind_of_link1 = pa_val A_TEXT + AF_kind_of_link1.
Proof. apply pa_xcalls. cbn [In scene_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
