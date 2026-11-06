(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantPa.v (a working branch d98082bd58b): the listing is lib/B/Prog's (5889 slots from 0x80a3c, 37 objects), the image range is IMG_LO_B..IMG_TOP_B of GrantTop.v (computed from image B's PT_LOADs), pa_obj_img covers the 37 objects, and grant_xcalls lists the 27 program functions image B's listing calls (A's 22 plus want_of, reac_ctrl_block_cksum_stamp, reac_ctrl_record_cksum_stamp, dt1_head, name_field; A's build_dt1_single kept); image A's file was made from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable gsym) := mkPAListing {
pl_tpi : ptree gsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition grant_tpi : ptree gsym := ptree_of_list grant_listing.
Definition grant_tw : ctable := Eval vm_compute in (tw_of 0 grant_listing).
#[global] Instance PL_grant : PAListing grant_listing :=
{| pl_tpi := grant_tpi; pl_tpi_eq := eq_refl; pl_tw := grant_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions image B's listing calls, each with its offset from the listing's base (the 27 program
   names of lib/B/Prog/GrantSyms.v; A's listing calls 22). pa_obj_img covers image B's 37 objects (grant_nobj,
   lib/B/Prog/GrantAddr.v; GrantImg.v checks the number). *)
Definition grant_xcalls : list (gsym * Z) :=
[ (GS_check_groupa, AF_check_groupa);
(GS_want_of, AF_want_of);
(GS_reac_ctrl_block_cksum_stamp, AF_reac_ctrl_block_cksum_stamp);
(GS_reac_ctrl_checksum_verify, AF_reac_ctrl_checksum_verify);
(GS_reac_ctrl_record_cksum_stamp, AF_reac_ctrl_record_cksum_stamp);
(GS_reac_ctrl_parse, AF_reac_ctrl_parse);
(GS_kind_of_link1, AF_kind_of_link1);
(GS_reac_ctrl_stamp_headamp, AF_reac_ctrl_stamp_headamp);
(GS_reac_ctrl_headamp_record_verify, AF_reac_ctrl_headamp_record_verify);
(GS_reac_ctrl_identity_poll_block, AF_reac_ctrl_identity_poll_block);
(GS_reac_ctrl_build_grant_sweep, AF_reac_ctrl_build_grant_sweep);
(GS_ctrl_lay_block, AF_ctrl_lay_block);
(GS_ctrl_finish, AF_ctrl_finish);
(GS_reac_box_model_block, AF_reac_box_model_block);
(GS_build_dt1_single, AF_build_dt1_single);
(GS_dt1_head, AF_dt1_head);
(GS_name_field, AF_name_field);
(GS_reac_grant_alloc_fits, AF_reac_grant_alloc_fits);
(GS_reac_grant_allocate, AF_reac_grant_allocate);
(GS_reac_grant_build_sweep, AF_reac_grant_build_sweep);
(GS_reac_headamp_tx_init, AF_reac_headamp_tx_init);
(GS_reac_headamp_tx_set, AF_reac_headamp_tx_set);
(GS_reac_headamp_default, AF_reac_headamp_default);
(GS_reac_headamp_tx_effective, AF_reac_headamp_tx_effective);
(GS_reac_headamp_tx_arm_scene, AF_reac_headamp_tx_arm_scene);
(GS_reac_headamp_tx_set_resweep, AF_reac_headamp_tx_set_resweep);
(GS_reac_headamp_tx_next, AF_reac_headamp_tx_next) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable gsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : gsym -> Z;
pa_cert : pi_check gsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO_B <= a < IMG_TOP_B;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO_B /\ IMG_TOP_B <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 37)%nat -> IMG_LO_B <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP_B;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) grant_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable gsym} {PI : PAImg L}.
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
Lemma pa_sigma_check_groupa : pa_sigma GS_check_groupa = pa_val A_TEXT + AF_check_groupa.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_want_of : pa_sigma GS_want_of = pa_val A_TEXT + AF_want_of.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_block_cksum_stamp : pa_sigma GS_reac_ctrl_block_cksum_stamp = pa_val A_TEXT + AF_reac_ctrl_block_cksum_stamp.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_checksum_verify : pa_sigma GS_reac_ctrl_checksum_verify = pa_val A_TEXT + AF_reac_ctrl_checksum_verify.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_record_cksum_stamp : pa_sigma GS_reac_ctrl_record_cksum_stamp = pa_val A_TEXT + AF_reac_ctrl_record_cksum_stamp.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_parse : pa_sigma GS_reac_ctrl_parse = pa_val A_TEXT + AF_reac_ctrl_parse.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kind_of_link1 : pa_sigma GS_kind_of_link1 = pa_val A_TEXT + AF_kind_of_link1.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_stamp_headamp : pa_sigma GS_reac_ctrl_stamp_headamp = pa_val A_TEXT + AF_reac_ctrl_stamp_headamp.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_headamp_record_verify : pa_sigma GS_reac_ctrl_headamp_record_verify = pa_val A_TEXT + AF_reac_ctrl_headamp_record_verify.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_identity_poll_block : pa_sigma GS_reac_ctrl_identity_poll_block = pa_val A_TEXT + AF_reac_ctrl_identity_poll_block.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_build_grant_sweep : pa_sigma GS_reac_ctrl_build_grant_sweep = pa_val A_TEXT + AF_reac_ctrl_build_grant_sweep.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_ctrl_lay_block : pa_sigma GS_ctrl_lay_block = pa_val A_TEXT + AF_ctrl_lay_block.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_ctrl_finish : pa_sigma GS_ctrl_finish = pa_val A_TEXT + AF_ctrl_finish.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_model_block : pa_sigma GS_reac_box_model_block = pa_val A_TEXT + AF_reac_box_model_block.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_build_dt1_single : pa_sigma GS_build_dt1_single = pa_val A_TEXT + AF_build_dt1_single.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_dt1_head : pa_sigma GS_dt1_head = pa_val A_TEXT + AF_dt1_head.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_name_field : pa_sigma GS_name_field = pa_val A_TEXT + AF_name_field.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_grant_alloc_fits : pa_sigma GS_reac_grant_alloc_fits = pa_val A_TEXT + AF_reac_grant_alloc_fits.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_grant_allocate : pa_sigma GS_reac_grant_allocate = pa_val A_TEXT + AF_reac_grant_allocate.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_grant_build_sweep : pa_sigma GS_reac_grant_build_sweep = pa_val A_TEXT + AF_reac_grant_build_sweep.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_init : pa_sigma GS_reac_headamp_tx_init = pa_val A_TEXT + AF_reac_headamp_tx_init.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_set : pa_sigma GS_reac_headamp_tx_set = pa_val A_TEXT + AF_reac_headamp_tx_set.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_default : pa_sigma GS_reac_headamp_default = pa_val A_TEXT + AF_reac_headamp_default.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_effective : pa_sigma GS_reac_headamp_tx_effective = pa_val A_TEXT + AF_reac_headamp_tx_effective.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_arm_scene : pa_sigma GS_reac_headamp_tx_arm_scene = pa_val A_TEXT + AF_reac_headamp_tx_arm_scene.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_set_resweep : pa_sigma GS_reac_headamp_tx_set_resweep = pa_val A_TEXT + AF_reac_headamp_tx_set_resweep.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_headamp_tx_next : pa_sigma GS_reac_headamp_tx_next = pa_val A_TEXT + AF_reac_headamp_tx_next.
Proof. apply pa_xcalls. cbn [In grant_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
