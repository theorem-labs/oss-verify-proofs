(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_disco's program walk, taken from libreac/fuzz_grant's copy (lib/A/Prog/GrantPa.v, 3ac49e35db5): one listing (disco_listing over dsym), fuzz_disco.asan's image range IMG_LO..IMG_TOP (YImgTop) and its disco_nobj (68) objects (DiscoAddr), and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls (disco_xcalls: the 35 dsym names with an AF_ offset in DiscoList, one pa_sigma lemma each); module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoAddr DiscoRoList.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
(* Removes the plain image's sink and shape instances from every context of this walk layer (Reusable/PlainHintsOff.v). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require PlainHintsOff.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable dsym) := mkPAListing {
pl_tpi : ptree dsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition disco_tpi : ptree dsym := ptree_of_list disco_listing.
Definition disco_tw : ctable := Eval vm_compute in (tw_of 0 disco_listing).
#[global] Instance PL_disco : PAListing disco_listing :=
{| pl_tpi := disco_tpi; pl_tpi_eq := eq_refl; pl_tw := disco_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition disco_xcalls : list (dsym * Z) :=
[ (DS_reac_disco_table_init, AF_reac_disco_table_init);
(DS_reac_disco_gate_init, AF_reac_disco_gate_init);
(DS_reac_disco_peer_lock_init, AF_reac_disco_peer_lock_init);
(DS_reac_hunt_init, AF_reac_hunt_init);
(DS_reac_hunt_pin, AF_reac_hunt_pin);
(DS_reac_hunt_silence_proven, AF_reac_hunt_silence_proven);
(DS_reac_disco_table_age, AF_reac_disco_table_age);
(DS_check_table, AF_check_table);
(DS_reac_disco_table_json, AF_reac_disco_table_json);
(DS_reac_disco_classify, AF_reac_disco_classify);
(DS_reac_disco_classify_on_segment, AF_reac_disco_classify_on_segment);
(DS_check_sighting, AF_check_sighting);
(DS_reac_disco_gate_should_push, AF_reac_disco_gate_should_push);
(DS_find_entry, AF_find_entry);
(DS_json_scalar, AF_json_scalar);
(DS_jtok_is, AF_jtok_is);
(DS_reac_hunt_observe, AF_reac_hunt_observe);
(DS_reac_disco_table_observe, AF_reac_disco_table_observe);
(DS_reac_box_name, AF_reac_box_name);
(DS_reac_hunt_step, AF_reac_hunt_step);
(DS_reac_hunt_verdict_name, AF_reac_hunt_verdict_name);
(DS_reac_hunt_role, AF_reac_hunt_role);
(DS_reac_hunt_heard_anything, AF_reac_hunt_heard_anything);
(DS_sb_dec, AF_sb_dec);
(DS_classify_core, AF_classify_core);
(DS_reac_ctrl_parse, AF_reac_ctrl_parse);
(DS_reac_ctrl_checksum_verify, AF_reac_ctrl_checksum_verify);
(DS_reac_ports_parse, AF_reac_ports_parse);
(DS_kind_of_link1, AF_kind_of_link1);
(DS_reac_frame_clean_len, AF_reac_frame_clean_len);
(DS_reac_arbitrate, AF_reac_arbitrate);
(DS_reac_sender_kind, AF_reac_sender_kind);
(DS_reac_rival_kind_of, AF_reac_rival_kind_of);
(DS_reac_rate_snap, AF_reac_rate_snap);
(DS_reac_master_only_cadence_ns, AF_reac_master_only_cadence_ns) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable dsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : dsym -> Z;
pa_cert : pi_check dsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < disco_nobj)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_obj_val : forall i, (i < disco_nobj)%nat -> pa_val (A_OBJ i) = disco_obj i;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_ro_ok : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz ->
(exists s, In s pa_segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= x < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (pa_relro_lo <= x < pa_relro_hi);
pa_rom_ok : forall q sz x, In (q, sz) (disco_ro_extra ++ disco_glob_tails) -> q <= x < q + sz -> in_rom pa_segs x;
pa_ro_present : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz -> seg_rom pa_segs (Z_to_bv 64 x) <> None;
pa_xcalls : forall s k, In (s, k) disco_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable dsym} {PI : PAImg L}.
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
Lemma pa_sigma_reac_disco_table_init : pa_sigma DS_reac_disco_table_init = pa_val A_TEXT + AF_reac_disco_table_init.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_gate_init : pa_sigma DS_reac_disco_gate_init = pa_val A_TEXT + AF_reac_disco_gate_init.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_peer_lock_init : pa_sigma DS_reac_disco_peer_lock_init = pa_val A_TEXT + AF_reac_disco_peer_lock_init.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_init : pa_sigma DS_reac_hunt_init = pa_val A_TEXT + AF_reac_hunt_init.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_pin : pa_sigma DS_reac_hunt_pin = pa_val A_TEXT + AF_reac_hunt_pin.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_silence_proven : pa_sigma DS_reac_hunt_silence_proven = pa_val A_TEXT + AF_reac_hunt_silence_proven.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_age : pa_sigma DS_reac_disco_table_age = pa_val A_TEXT + AF_reac_disco_table_age.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_table : pa_sigma DS_check_table = pa_val A_TEXT + AF_check_table.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_json : pa_sigma DS_reac_disco_table_json = pa_val A_TEXT + AF_reac_disco_table_json.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_classify : pa_sigma DS_reac_disco_classify = pa_val A_TEXT + AF_reac_disco_classify.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_classify_on_segment : pa_sigma DS_reac_disco_classify_on_segment = pa_val A_TEXT + AF_reac_disco_classify_on_segment.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_sighting : pa_sigma DS_check_sighting = pa_val A_TEXT + AF_check_sighting.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_gate_should_push : pa_sigma DS_reac_disco_gate_should_push = pa_val A_TEXT + AF_reac_disco_gate_should_push.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_find_entry : pa_sigma DS_find_entry = pa_val A_TEXT + AF_find_entry.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_json_scalar : pa_sigma DS_json_scalar = pa_val A_TEXT + AF_json_scalar.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_jtok_is : pa_sigma DS_jtok_is = pa_val A_TEXT + AF_jtok_is.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_observe : pa_sigma DS_reac_hunt_observe = pa_val A_TEXT + AF_reac_hunt_observe.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_disco_table_observe : pa_sigma DS_reac_disco_table_observe = pa_val A_TEXT + AF_reac_disco_table_observe.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_box_name : pa_sigma DS_reac_box_name = pa_val A_TEXT + AF_reac_box_name.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_step : pa_sigma DS_reac_hunt_step = pa_val A_TEXT + AF_reac_hunt_step.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_verdict_name : pa_sigma DS_reac_hunt_verdict_name = pa_val A_TEXT + AF_reac_hunt_verdict_name.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_role : pa_sigma DS_reac_hunt_role = pa_val A_TEXT + AF_reac_hunt_role.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_hunt_heard_anything : pa_sigma DS_reac_hunt_heard_anything = pa_val A_TEXT + AF_reac_hunt_heard_anything.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_sb_dec : pa_sigma DS_sb_dec = pa_val A_TEXT + AF_sb_dec.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_classify_core : pa_sigma DS_classify_core = pa_val A_TEXT + AF_classify_core.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_parse : pa_sigma DS_reac_ctrl_parse = pa_val A_TEXT + AF_reac_ctrl_parse.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ctrl_checksum_verify : pa_sigma DS_reac_ctrl_checksum_verify = pa_val A_TEXT + AF_reac_ctrl_checksum_verify.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_ports_parse : pa_sigma DS_reac_ports_parse = pa_val A_TEXT + AF_reac_ports_parse.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kind_of_link1 : pa_sigma DS_kind_of_link1 = pa_val A_TEXT + AF_kind_of_link1.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_frame_clean_len : pa_sigma DS_reac_frame_clean_len = pa_val A_TEXT + AF_reac_frame_clean_len.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_arbitrate : pa_sigma DS_reac_arbitrate = pa_val A_TEXT + AF_reac_arbitrate.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_sender_kind : pa_sigma DS_reac_sender_kind = pa_val A_TEXT + AF_reac_sender_kind.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_rival_kind_of : pa_sigma DS_reac_rival_kind_of = pa_val A_TEXT + AF_reac_rival_kind_of.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_rate_snap : pa_sigma DS_reac_rate_snap = pa_val A_TEXT + AF_reac_rate_snap.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_master_only_cadence_ns : pa_sigma DS_reac_master_only_cadence_ns = pa_val A_TEXT + AF_reac_master_only_cadence_ns.
Proof. apply pa_xcalls. cbn [In disco_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
