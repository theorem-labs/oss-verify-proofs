(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_grant's program walk: one listing (grant_listing over gsym), fuzz_grant.asan's image range 0x10000..0x5fa000 and 34 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v of a working branch ca2ec2ecd18 for libreac/fuzz_ctrl's program walk: module paths and names re-keyed to fuzz_ctrl (ctrl_listing, CtrlSyms, CtrlList), the image range is fuzz_ctrl.asan's 0x10000..0x5fe000, the object count is 32, and ctrl_xcalls holds fuzz_ctrl's own 23 program functions. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaRun PaShadow CtrlSyms CtrlList.
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
Definition ctrl_tpi : ptree gsym := ptree_of_list ctrl_listing.
Definition ctrl_tw : ctable := Eval vm_compute in (tw_of 0 ctrl_listing).
#[global] Instance PL_ctrl : PAListing ctrl_listing :=
{| pl_tpi := ctrl_tpi; pl_tpi_eq := eq_refl; pl_tw := ctrl_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition ctrl_xcalls : list (gsym * Z) :=
[ (GS_declaration_of, AF_declaration_of);
(GS_reac_ctrl_classify_box_frame, AF_reac_ctrl_classify_box_frame);
(GS_reac_ctrl_checksum_verify, AF_reac_ctrl_checksum_verify);
(GS_reac_ctrl_kind_name, AF_reac_ctrl_kind_name);
(GS_reac_ctrl_parse, AF_reac_ctrl_parse);
(GS_kind_of_link1, AF_kind_of_link1);
(GS_reac_ctrl_identity_reply, AF_reac_ctrl_identity_reply);
(GS_reac_box_catalogue, AF_reac_box_catalogue);
(GS_reac_box_catalogue_match, AF_reac_box_catalogue_match);
(GS_reac_ctrl_build_as, AF_reac_ctrl_build_as);
(GS_ctrl_emit_as, AF_ctrl_emit_as);
(GS_reac_ctrl_headamp_record_verify, AF_reac_ctrl_headamp_record_verify);
(GS_reac_ctrl_identity_fragment, AF_reac_ctrl_identity_fragment);
(GS_ctrl_lay_block, AF_ctrl_lay_block);
(GS_ctrl_finish, AF_ctrl_finish);
(GS_reac_box_model_block, AF_reac_box_model_block);
(GS_reac_box_model_upstream_width, AF_reac_box_model_upstream_width);
(GS_build_dt1_single, AF_build_dt1_single);
(GS_reac_braid_encode, AF_reac_braid_encode);
(GS_reac_identity_init, AF_reac_identity_init);
(GS_reac_identity_ingest, AF_reac_identity_ingest);
(GS_reac_ports_parse, AF_reac_ports_parse);
(GS_reac_ports_unknown, AF_reac_ports_unknown) ].
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
pa_img_range : forall a, in_img pa_segs a -> 0x10000 <= a < 0x5fe000;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x5fe000 <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 32)%nat -> 0x10000 <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= 0x5fe000;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) ctrl_xcalls -> pa_sigma s = pa_val A_TEXT + k
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
Lemma pa_sigma_declaration_of : pa_sigma GS_declaration_of = pa_val A_TEXT + AF_declaration_of.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_classify_box_frame : pa_sigma GS_reac_ctrl_classify_box_frame = pa_val A_TEXT + AF_reac_ctrl_classify_box_frame.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_checksum_verify : pa_sigma GS_reac_ctrl_checksum_verify = pa_val A_TEXT + AF_reac_ctrl_checksum_verify.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_kind_name : pa_sigma GS_reac_ctrl_kind_name = pa_val A_TEXT + AF_reac_ctrl_kind_name.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_parse : pa_sigma GS_reac_ctrl_parse = pa_val A_TEXT + AF_reac_ctrl_parse.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kind_of_link1 : pa_sigma GS_kind_of_link1 = pa_val A_TEXT + AF_kind_of_link1.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_identity_reply : pa_sigma GS_reac_ctrl_identity_reply = pa_val A_TEXT + AF_reac_ctrl_identity_reply.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_catalogue : pa_sigma GS_reac_box_catalogue = pa_val A_TEXT + AF_reac_box_catalogue.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_catalogue_match : pa_sigma GS_reac_box_catalogue_match = pa_val A_TEXT + AF_reac_box_catalogue_match.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_build_as : pa_sigma GS_reac_ctrl_build_as = pa_val A_TEXT + AF_reac_ctrl_build_as.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_ctrl_emit_as : pa_sigma GS_ctrl_emit_as = pa_val A_TEXT + AF_ctrl_emit_as.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_headamp_record_verify : pa_sigma GS_reac_ctrl_headamp_record_verify = pa_val A_TEXT + AF_reac_ctrl_headamp_record_verify.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_identity_fragment : pa_sigma GS_reac_ctrl_identity_fragment = pa_val A_TEXT + AF_reac_ctrl_identity_fragment.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_ctrl_lay_block : pa_sigma GS_ctrl_lay_block = pa_val A_TEXT + AF_ctrl_lay_block.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_ctrl_finish : pa_sigma GS_ctrl_finish = pa_val A_TEXT + AF_ctrl_finish.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_model_block : pa_sigma GS_reac_box_model_block = pa_val A_TEXT + AF_reac_box_model_block.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_model_upstream_width : pa_sigma GS_reac_box_model_upstream_width = pa_val A_TEXT + AF_reac_box_model_upstream_width.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_build_dt1_single : pa_sigma GS_build_dt1_single = pa_val A_TEXT + AF_build_dt1_single.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_braid_encode : pa_sigma GS_reac_braid_encode = pa_val A_TEXT + AF_reac_braid_encode.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_identity_init : pa_sigma GS_reac_identity_init = pa_val A_TEXT + AF_reac_identity_init.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_identity_ingest : pa_sigma GS_reac_identity_ingest = pa_val A_TEXT + AF_reac_identity_ingest.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ports_parse : pa_sigma GS_reac_ports_parse = pa_val A_TEXT + AF_reac_ports_parse.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ports_unknown : pa_sigma GS_reac_ports_unknown = pa_val A_TEXT + AF_reac_ports_unknown.
Proof. apply pa_xcalls. cbn [In ctrl_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
