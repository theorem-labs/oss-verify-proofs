(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_decode's program walk: one listing (decode_listing over dsym), fuzz_decode.asan's image range (lib/Reusable/YImgTop.v IMG_LO .. IMG_TOP) and the listing's 15 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v, file sha256 aa6587cc3b6c; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePa.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPa.v (file sha256 0bbc41c8338c; donor not released): the listing is fuzz_decode.asan-ubsan's decodeb_listing over dbsym (lib/B/Prog/DecodeBList.v, DecodeBSyms.v); pa_obj_img covers its 16 objects (lib/B/Prog/DecodeBAddr.v decodeb_nobj, one more than image A's 15); decodeb_xcalls names the same 11 program functions as image A, at image B's offsets; boxreg's removal of the YI5b / YI5c hints is left out, as in image A's file; module paths changed. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 1024.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable tbsym) := mkPAListing {
pl_tpi : ptree tbsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition transportb_tpi : ptree tbsym := ptree_of_list transportb_listing.
Definition transportb_tw : ctable := Eval vm_compute in (tw_of 0 transportb_listing).
#[global] Instance PL_transportb : PAListing transportb_listing :=
{| pl_tpi := transportb_tpi; pl_tpi_eq := eq_refl; pl_tw := transportb_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition transportb_xcalls : list (tbsym * Z) :=
[ (TB_receive, AF_receive);
(TB_m_tick, AF_m_tick);
(TB_settle, AF_settle);
(TB_m_wake, AF_m_wake);
(TB_check_state_wake_code, AF_check_state_wake_code);
(TB_spec_read_frame, AF_spec_read_frame);
(TB_check_sent_frame, AF_check_sent_frame);
(TB_check_ack_frame, AF_check_ack_frame);
(TB_check_latest_control, AF_check_latest_control);
(TB_check_inflight_retry, AF_check_inflight_retry);
(TB_check_state_wake, AF_check_state_wake);
(TB_check_inflight_new, AF_check_inflight_new);
(TB_tagged_of, AF_tagged_of);
(TB_check_latest_frame, AF_check_latest_frame);
(TB_check_keepalive_due, AF_check_keepalive_due);
(TB_check_latest_sent, AF_check_latest_sent);
(TB_check_latest_display, AF_check_latest_display);
(TB_m_rx, AF_m_rx);
(TB_host_offset, AF_host_offset);
(TB_desk_named, AF_desk_named);
(TB_m_maybe_online, AF_m_maybe_online);
(TB_m_set, AF_m_set);
(TB_check_state_online, AF_check_state_online);
(TB_check_inflight_acked, AF_check_inflight_acked);
(TB_check_inflight_lost, AF_check_inflight_lost);
(TB_check_state_desk, AF_check_state_desk);
(TB_check_state_data, AF_check_state_data);
(TB_build_and_receive, AF_build_and_receive);
(TB_check_ack_settle, AF_check_ack_settle);
(TB_check_state_settle, AF_check_state_settle);
(TB_check_inflight_settle, AF_check_inflight_settle);
(TB_check_keepalive_settle, AF_check_keepalive_settle);
(TB_check_latest_queue, AF_check_latest_queue);
(TB_check_latest_drain, AF_check_latest_drain);
(TB_check_refusal_submit, AF_check_refusal_submit);
(TB_check_latest_submit, AF_check_latest_submit);
(TB_diginet_session_config_default, AF_diginet_session_config_default);
(TB_diginet_session_init, AF_diginet_session_init);
(TB_diginet_session_wake, AF_diginet_session_wake);
(TB_send_control, AF_send_control);
(TB_set_state, AF_set_state);
(TB_diginet_session_close, AF_diginet_session_close);
(TB_diginet_session_rx, AF_diginet_session_rx);
(TB_on_announce, AF_on_announce);
(TB_on_ack, AF_on_ack);
(TB_on_data, AF_on_data);
(TB_diginet_session_tick, AF_diginet_session_tick);
(TB_diginet_session_submit, AF_diginet_session_submit);
(TB_send_data, AF_send_data);
(TB_take, AF_take);
(TB_diginet_session_deadline, AF_diginet_session_deadline);
(TB_diginet_session_poll, AF_diginet_session_poll);
(TB_maybe_online, AF_maybe_online);
(TB_diginet_sum16, AF_diginet_sum16);
(TB_diginet_mac_is_digidesign, AF_diginet_mac_is_digidesign);
(TB_diginet_frame_is_keepalive, AF_diginet_frame_is_keepalive);
(TB_diginet_frame_parse, AF_diginet_frame_parse);
(TB_rd32, AF_rd32);
(TB_diginet_frame_build, AF_diginet_frame_build);
(TB_diginet_announce_parse, AF_diginet_announce_parse);
(TB_copy_strz, AF_copy_strz);
(TB_diginet_personality_from_name, AF_diginet_personality_from_name);
(TB_diginet_body_check, AF_diginet_body_check);
(TB_diginet_cursor_init, AF_diginet_cursor_init);
(TB_diginet_msg_next, AF_diginet_msg_next) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable tbsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : tbsym -> Z;
pa_cert : pi_check tbsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, layout_ok ly -> ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 97)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) transportb_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable tbsym} {PI : PAImg L}.
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
Lemma pa_sigma_receive : pa_sigma TB_receive = pa_val A_TEXT + AF_receive.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_tick : pa_sigma TB_m_tick = pa_val A_TEXT + AF_m_tick.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_settle : pa_sigma TB_settle = pa_val A_TEXT + AF_settle.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_wake : pa_sigma TB_m_wake = pa_val A_TEXT + AF_m_wake.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_wake_code : pa_sigma TB_check_state_wake_code = pa_val A_TEXT + AF_check_state_wake_code.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_spec_read_frame : pa_sigma TB_spec_read_frame = pa_val A_TEXT + AF_spec_read_frame.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_sent_frame : pa_sigma TB_check_sent_frame = pa_val A_TEXT + AF_check_sent_frame.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_ack_frame : pa_sigma TB_check_ack_frame = pa_val A_TEXT + AF_check_ack_frame.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_control : pa_sigma TB_check_latest_control = pa_val A_TEXT + AF_check_latest_control.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_retry : pa_sigma TB_check_inflight_retry = pa_val A_TEXT + AF_check_inflight_retry.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_wake : pa_sigma TB_check_state_wake = pa_val A_TEXT + AF_check_state_wake.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_new : pa_sigma TB_check_inflight_new = pa_val A_TEXT + AF_check_inflight_new.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_tagged_of : pa_sigma TB_tagged_of = pa_val A_TEXT + AF_tagged_of.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_frame : pa_sigma TB_check_latest_frame = pa_val A_TEXT + AF_check_latest_frame.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_keepalive_due : pa_sigma TB_check_keepalive_due = pa_val A_TEXT + AF_check_keepalive_due.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_sent : pa_sigma TB_check_latest_sent = pa_val A_TEXT + AF_check_latest_sent.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_display : pa_sigma TB_check_latest_display = pa_val A_TEXT + AF_check_latest_display.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_rx : pa_sigma TB_m_rx = pa_val A_TEXT + AF_m_rx.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_host_offset : pa_sigma TB_host_offset = pa_val A_TEXT + AF_host_offset.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_desk_named : pa_sigma TB_desk_named = pa_val A_TEXT + AF_desk_named.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_maybe_online : pa_sigma TB_m_maybe_online = pa_val A_TEXT + AF_m_maybe_online.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_set : pa_sigma TB_m_set = pa_val A_TEXT + AF_m_set.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_online : pa_sigma TB_check_state_online = pa_val A_TEXT + AF_check_state_online.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_acked : pa_sigma TB_check_inflight_acked = pa_val A_TEXT + AF_check_inflight_acked.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_lost : pa_sigma TB_check_inflight_lost = pa_val A_TEXT + AF_check_inflight_lost.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_desk : pa_sigma TB_check_state_desk = pa_val A_TEXT + AF_check_state_desk.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_data : pa_sigma TB_check_state_data = pa_val A_TEXT + AF_check_state_data.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_build_and_receive : pa_sigma TB_build_and_receive = pa_val A_TEXT + AF_build_and_receive.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_ack_settle : pa_sigma TB_check_ack_settle = pa_val A_TEXT + AF_check_ack_settle.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_settle : pa_sigma TB_check_state_settle = pa_val A_TEXT + AF_check_state_settle.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_settle : pa_sigma TB_check_inflight_settle = pa_val A_TEXT + AF_check_inflight_settle.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_keepalive_settle : pa_sigma TB_check_keepalive_settle = pa_val A_TEXT + AF_check_keepalive_settle.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_queue : pa_sigma TB_check_latest_queue = pa_val A_TEXT + AF_check_latest_queue.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_drain : pa_sigma TB_check_latest_drain = pa_val A_TEXT + AF_check_latest_drain.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_refusal_submit : pa_sigma TB_check_refusal_submit = pa_val A_TEXT + AF_check_refusal_submit.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_submit : pa_sigma TB_check_latest_submit = pa_val A_TEXT + AF_check_latest_submit.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_config_default : pa_sigma TB_diginet_session_config_default = pa_val A_TEXT + AF_diginet_session_config_default.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_init : pa_sigma TB_diginet_session_init = pa_val A_TEXT + AF_diginet_session_init.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_wake : pa_sigma TB_diginet_session_wake = pa_val A_TEXT + AF_diginet_session_wake.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_send_control : pa_sigma TB_send_control = pa_val A_TEXT + AF_send_control.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_set_state : pa_sigma TB_set_state = pa_val A_TEXT + AF_set_state.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_close : pa_sigma TB_diginet_session_close = pa_val A_TEXT + AF_diginet_session_close.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_rx : pa_sigma TB_diginet_session_rx = pa_val A_TEXT + AF_diginet_session_rx.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_announce : pa_sigma TB_on_announce = pa_val A_TEXT + AF_on_announce.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_ack : pa_sigma TB_on_ack = pa_val A_TEXT + AF_on_ack.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_data : pa_sigma TB_on_data = pa_val A_TEXT + AF_on_data.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_tick : pa_sigma TB_diginet_session_tick = pa_val A_TEXT + AF_diginet_session_tick.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_submit : pa_sigma TB_diginet_session_submit = pa_val A_TEXT + AF_diginet_session_submit.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_send_data : pa_sigma TB_send_data = pa_val A_TEXT + AF_send_data.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_take : pa_sigma TB_take = pa_val A_TEXT + AF_take.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_deadline : pa_sigma TB_diginet_session_deadline = pa_val A_TEXT + AF_diginet_session_deadline.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_poll : pa_sigma TB_diginet_session_poll = pa_val A_TEXT + AF_diginet_session_poll.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_maybe_online : pa_sigma TB_maybe_online = pa_val A_TEXT + AF_maybe_online.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_sum16 : pa_sigma TB_diginet_sum16 = pa_val A_TEXT + AF_diginet_sum16.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_mac_is_digidesign : pa_sigma TB_diginet_mac_is_digidesign = pa_val A_TEXT + AF_diginet_mac_is_digidesign.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_is_keepalive : pa_sigma TB_diginet_frame_is_keepalive = pa_val A_TEXT + AF_diginet_frame_is_keepalive.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_parse : pa_sigma TB_diginet_frame_parse = pa_val A_TEXT + AF_diginet_frame_parse.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_rd32 : pa_sigma TB_rd32 = pa_val A_TEXT + AF_rd32.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_build : pa_sigma TB_diginet_frame_build = pa_val A_TEXT + AF_diginet_frame_build.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_announce_parse : pa_sigma TB_diginet_announce_parse = pa_val A_TEXT + AF_diginet_announce_parse.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_copy_strz : pa_sigma TB_copy_strz = pa_val A_TEXT + AF_copy_strz.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_personality_from_name : pa_sigma TB_diginet_personality_from_name = pa_val A_TEXT + AF_diginet_personality_from_name.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_body_check : pa_sigma TB_diginet_body_check = pa_val A_TEXT + AF_diginet_body_check.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_cursor_init : pa_sigma TB_diginet_cursor_init = pa_val A_TEXT + AF_diginet_cursor_init.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_msg_next : pa_sigma TB_diginet_msg_next = pa_val A_TEXT + AF_diginet_msg_next.
Proof. apply pa_xcalls. cbn [In transportb_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
