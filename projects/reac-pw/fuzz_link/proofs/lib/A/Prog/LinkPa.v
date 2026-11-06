(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_pcap's program walk: one listing (pcap_listing over psym), fuzz_pcap.asan's (v1.9.0) image range 0x10000..pcap_img_end (Reusable/PcapImgEnd.v, 0x5f7000, checked against the image by lib/A/PcapImgEndCheck.v) and 17 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow LinkSyms LinkList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 512.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable lsym) := mkPAListing {
pl_tpi : ptree lsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition link_tpi : ptree lsym := ptree_of_list link_listing.
Definition link_tw : ctable := Eval vm_compute in (tw_of 0 link_listing).
#[global] Instance PL_link : PAListing link_listing :=
{| pl_tpi := link_tpi; pl_tpi_eq := eq_refl; pl_tw := link_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition link_xcalls : list (lsym * Z) :=
[ (LS_fuzz_socket, AF_fuzz_socket);
(LS_fuzz_send, AF_fuzz_send);
(LS_fuzz_recv, AF_fuzz_recv);
(LS_fuzz_close, AF_fuzz_close);
(LS_fuzz_if_nametoindex, AF_fuzz_if_nametoindex);
(LS_kernel, AF_kernel);
(LS_text_buf, AF_text_buf);
(LS_model_read, AF_model_read);
(LS_check_socket, AF_check_socket);
(LS_index_of, AF_index_of);
(LS_check_refused, AF_check_refused);
(LS_check_bounds, AF_check_bounds);
(LS_check_read, AF_check_read);
(LS_check_requests, AF_check_requests);
(LS_attr_text, AF_attr_text);
(LS_nl_error, AF_nl_error);
(LS_talk, AF_talk);
(LS_text_of, AF_text_of);
(LS_model_write, AF_model_write);
(LS_check_write, AF_check_write);
(LS_mark_quietly, AF_mark_quietly);
(LS_check_mark, AF_check_mark);
(LS_check_marks, AF_check_marks);
(LS_model_decide, AF_model_decide);
(LS_check_verdict, AF_check_verdict);
(LS_reac_link_alias_read, AF_reac_link_alias_read);
(LS_nl_talk, AF_nl_talk);
(LS_reac_link_alias_write, AF_reac_link_alias_write);
(LS_copy_attr, AF_copy_attr);
(LS_reac_served_say_to, AF_reac_served_say_to);
(LS_reac_served_decide, AF_reac_served_decide);
(LS_reac_served_mark, AF_reac_served_mark);
(LS_reac_code_emit, AF_reac_code_emit);
(LS_remember, AF_remember);
(LS_reac_served_unmark_all, AF_reac_served_unmark_all) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable lsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : lsym -> Z;
pa_cert : pi_check lsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> 0x10000 <= a < pcap_img_end;
pa_img_cover : forall ly S md, ALedger pa_segs ly S md -> fst (ly_img ly) <= 0x10000 /\ pcap_img_end <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 66)%nat -> 0x10000 <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= pcap_img_end;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) link_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable lsym} {PI : PAImg L}.
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
Lemma pa_sigma_fuzz_socket : pa_sigma LS_fuzz_socket = pa_val A_TEXT + AF_fuzz_socket.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_fuzz_send : pa_sigma LS_fuzz_send = pa_val A_TEXT + AF_fuzz_send.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_fuzz_recv : pa_sigma LS_fuzz_recv = pa_val A_TEXT + AF_fuzz_recv.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_fuzz_close : pa_sigma LS_fuzz_close = pa_val A_TEXT + AF_fuzz_close.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_fuzz_if_nametoindex : pa_sigma LS_fuzz_if_nametoindex = pa_val A_TEXT + AF_fuzz_if_nametoindex.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_kernel : pa_sigma LS_kernel = pa_val A_TEXT + AF_kernel.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_text_buf : pa_sigma LS_text_buf = pa_val A_TEXT + AF_text_buf.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_model_read : pa_sigma LS_model_read = pa_val A_TEXT + AF_model_read.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_socket : pa_sigma LS_check_socket = pa_val A_TEXT + AF_check_socket.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_index_of : pa_sigma LS_index_of = pa_val A_TEXT + AF_index_of.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_refused : pa_sigma LS_check_refused = pa_val A_TEXT + AF_check_refused.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_bounds : pa_sigma LS_check_bounds = pa_val A_TEXT + AF_check_bounds.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_read : pa_sigma LS_check_read = pa_val A_TEXT + AF_check_read.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_requests : pa_sigma LS_check_requests = pa_val A_TEXT + AF_check_requests.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_attr_text : pa_sigma LS_attr_text = pa_val A_TEXT + AF_attr_text.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_nl_error : pa_sigma LS_nl_error = pa_val A_TEXT + AF_nl_error.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_talk : pa_sigma LS_talk = pa_val A_TEXT + AF_talk.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_text_of : pa_sigma LS_text_of = pa_val A_TEXT + AF_text_of.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_model_write : pa_sigma LS_model_write = pa_val A_TEXT + AF_model_write.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_write : pa_sigma LS_check_write = pa_val A_TEXT + AF_check_write.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_mark_quietly : pa_sigma LS_mark_quietly = pa_val A_TEXT + AF_mark_quietly.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_mark : pa_sigma LS_check_mark = pa_val A_TEXT + AF_check_mark.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_marks : pa_sigma LS_check_marks = pa_val A_TEXT + AF_check_marks.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_model_decide : pa_sigma LS_model_decide = pa_val A_TEXT + AF_model_decide.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_verdict : pa_sigma LS_check_verdict = pa_val A_TEXT + AF_check_verdict.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_link_alias_read : pa_sigma LS_reac_link_alias_read = pa_val A_TEXT + AF_reac_link_alias_read.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_nl_talk : pa_sigma LS_nl_talk = pa_val A_TEXT + AF_nl_talk.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_link_alias_write : pa_sigma LS_reac_link_alias_write = pa_val A_TEXT + AF_reac_link_alias_write.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_copy_attr : pa_sigma LS_copy_attr = pa_val A_TEXT + AF_copy_attr.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_served_say_to : pa_sigma LS_reac_served_say_to = pa_val A_TEXT + AF_reac_served_say_to.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_served_decide : pa_sigma LS_reac_served_decide = pa_val A_TEXT + AF_reac_served_decide.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_served_mark : pa_sigma LS_reac_served_mark = pa_val A_TEXT + AF_reac_served_mark.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_code_emit : pa_sigma LS_reac_code_emit = pa_val A_TEXT + AF_reac_code_emit.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_remember : pa_sigma LS_remember = pa_val A_TEXT + AF_remember.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_reac_served_unmark_all : pa_sigma LS_reac_served_unmark_all = pa_val A_TEXT + AF_reac_served_unmark_all.
Proof. apply pa_xcalls. cbn [In link_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
