(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/DecodePa.v (itself from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v through proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v) for reac-repacer/fuzz_uci's image A: module paths and the listing's names changed (one listing, uci_listing over usym of lib/A/Prog/UciPList.v), fuzz_uci.asan's image range (lib/Reusable/YImgTop.v IMG_LO .. IMG_TOP), the listing's 10 objects (uci_nobj of lib/A/Prog/UciPAddr.v) and uci_xcalls (the listing's 5 program functions). *)
(* Modified by Theorem Labs, 2026-10: copied from reac-repacer/fuzz_uci's lib/A/Prog/UciPPa.v (recipes commit 0295462466b2) for reac-repacer/fuzz_wire's image A, the image-A twin of this unit's lib/B/Prog/WirePPa.v: the listing is image A's (wire_listing over wsym of lib/A/Prog/WirePList.v), the image range is lib/Reusable/YImgTop.v's IMG_LO .. IMG_TOP, the listing's 14 objects (wire_nobj of lib/A/Prog/WirePAddr.v) and wire_xcalls (the listing's 19 called program functions, in address order); names changed (usym -> wsym, US_ -> WS_, uci_ -> wire_, PL_uci -> PL_wire). Image A's PAImg instance is PI_wire of lib/A/Prog/WirePPaImg.v. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable wsym) := mkPAListing {
pl_tpi : ptree wsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition wire_tpi : ptree wsym := ptree_of_list wire_listing.
Definition wire_tw : ctable := Eval vm_compute in (tw_of 0 wire_listing).
#[global] Instance PL_wire : PAListing wire_listing :=
{| pl_tpi := wire_tpi; pl_tpi_eq := eq_refl; pl_tw := wire_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition wire_xcalls : list (wsym * Z) :=
[ (WS_check_forward, AF_check_forward);
(WS_check_ret, AF_check_ret);
(WS_check_downstream, AF_check_downstream);
(WS_check_meter, AF_check_meter);
(WS_check_counter, AF_check_counter);
(WS_check_width, AF_check_width);
(WS_check_read, AF_check_read);
(WS_check_copy, AF_check_copy);
(WS_rp_fwd_class, AF_rp_fwd_class);
(WS_rp_ret_accept, AF_rp_ret_accept);
(WS_rp_ds_accept, AF_rp_ds_accept);
(WS_rp_meter_counter, AF_rp_meter_counter);
(WS_rp_counter, AF_rp_counter);
(WS_rp_frame_channels, AF_rp_frame_channels);
(WS_rp_copy_untag, AF_rp_copy_untag);
(WS_rp_slot_width, AF_rp_slot_width);
(WS_rp_slot_read, AF_rp_slot_read);
(WS_reac_frame_is_reac, AF_reac_frame_is_reac);
(WS_reac_frame_clean_len, AF_reac_frame_clean_len) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable wsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : wsym -> Z;
pa_cert : pi_check wsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, layout_ok ly -> ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 14)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) wire_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable wsym} {PI : PAImg L}.
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
Lemma pa_sigma_check_forward : pa_sigma WS_check_forward = pa_val A_TEXT + AF_check_forward.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_ret : pa_sigma WS_check_ret = pa_val A_TEXT + AF_check_ret.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_downstream : pa_sigma WS_check_downstream = pa_val A_TEXT + AF_check_downstream.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_meter : pa_sigma WS_check_meter = pa_val A_TEXT + AF_check_meter.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_counter : pa_sigma WS_check_counter = pa_val A_TEXT + AF_check_counter.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_width : pa_sigma WS_check_width = pa_val A_TEXT + AF_check_width.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_read : pa_sigma WS_check_read = pa_val A_TEXT + AF_check_read.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_copy : pa_sigma WS_check_copy = pa_val A_TEXT + AF_check_copy.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_fwd_class : pa_sigma WS_rp_fwd_class = pa_val A_TEXT + AF_rp_fwd_class.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_ret_accept : pa_sigma WS_rp_ret_accept = pa_val A_TEXT + AF_rp_ret_accept.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_ds_accept : pa_sigma WS_rp_ds_accept = pa_val A_TEXT + AF_rp_ds_accept.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_meter_counter : pa_sigma WS_rp_meter_counter = pa_val A_TEXT + AF_rp_meter_counter.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_counter : pa_sigma WS_rp_counter = pa_val A_TEXT + AF_rp_counter.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_frame_channels : pa_sigma WS_rp_frame_channels = pa_val A_TEXT + AF_rp_frame_channels.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_copy_untag : pa_sigma WS_rp_copy_untag = pa_val A_TEXT + AF_rp_copy_untag.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_slot_width : pa_sigma WS_rp_slot_width = pa_val A_TEXT + AF_rp_slot_width.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rp_slot_read : pa_sigma WS_rp_slot_read = pa_val A_TEXT + AF_rp_slot_read.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_frame_is_reac : pa_sigma WS_reac_frame_is_reac = pa_val A_TEXT + AF_reac_frame_is_reac.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_frame_clean_len : pa_sigma WS_reac_frame_clean_len = pa_val A_TEXT + AF_reac_frame_clean_len.
Proof. apply pa_xcalls. cbn [In wire_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
