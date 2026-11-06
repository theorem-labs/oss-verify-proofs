(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC4a.v for libreac/fuzz_grant's program walk: one listing (grant_listing over gsym), fuzz_grant.asan's image range and 34 objects, and pa_xcalls in place of PAImg2, fixing the addresses of the program functions the listing calls; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from port-grant's copy (origin/cold/pg-prog cb6eddd4032, proofs/libreac/fuzz_grant/lib/A/Prog/GrantPa.v) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed; one listing (decode_listing over dsym),
   fuzz_decode.asan's image range (lib/Reusable/YImgTop.v IMG_LO .. IMG_TOP), the listing's 15 objects, decode_xcalls
   (the listing's 11 program functions); pa_img_cover takes layout_ok ly, because image A's last PT_LOAD does not end
   on a page, so the page above it comes only from layout_ok's lo_img (lib/Reusable/YG0f.v:320). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow DgnTransportSyms DgnTransportList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_LIM : nat := 1024.
Lemma A_LIM_text : (A_TEXT < A_LIM)%nat.
Proof. unfold A_TEXT, A_LIM. lia. Qed.
Class PAListing (L : ptable tsym) := mkPAListing {
pl_tpi : ptree tsym;
pl_tpi_eq : ptree_of_list L = pl_tpi;
pl_tw : ctable;
pl_tw_eq : tw_of 0 L = pl_tw;
pl_lim : forallb (pinstr_atoms_ltb A_LIM) L = true;
pl_len : 4 * Z.of_nat (length L) <= 2 ^ 40;
pl_slot0 : match plookup (ptree_of_list L) 0 with Some _ => True | None => False end
}.
Definition transport_tpi : ptree tsym := ptree_of_list transport_listing.
Definition transport_tw : ctable := Eval vm_compute in (tw_of 0 transport_listing).
#[global] Instance PL_transport : PAListing transport_listing :=
{| pl_tpi := transport_tpi; pl_tpi_eq := eq_refl; pl_tw := transport_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])); pl_slot0 := ltac:(vm_compute; exact I) |}.
(* The program functions the listing calls, each with its offset from the listing's base. *)
Definition transport_xcalls : list (tsym * Z) :=
[ (TS_receive, AF_receive);
(TS_m_tick, AF_m_tick);
(TS_settle, AF_settle);
(TS_m_wake, AF_m_wake);
(TS_check_state_wake_code, AF_check_state_wake_code);
(TS_check_sent_frame, AF_check_sent_frame);
(TS_check_ack_frame, AF_check_ack_frame);
(TS_check_latest_control, AF_check_latest_control);
(TS_check_inflight_retry, AF_check_inflight_retry);
(TS_check_state_wake, AF_check_state_wake);
(TS_check_inflight_new, AF_check_inflight_new);
(TS_check_latest_frame, AF_check_latest_frame);
(TS_check_keepalive_due, AF_check_keepalive_due);
(TS_check_latest_sent, AF_check_latest_sent);
(TS_check_latest_display, AF_check_latest_display);
(TS_m_rx, AF_m_rx);
(TS_desk_named, AF_desk_named);
(TS_m_lost, AF_m_lost);
(TS_m_maybe_online, AF_m_maybe_online);
(TS_check_state_online, AF_check_state_online);
(TS_check_inflight_acked, AF_check_inflight_acked);
(TS_check_inflight_lost, AF_check_inflight_lost);
(TS_check_state_desk, AF_check_state_desk);
(TS_check_state_data, AF_check_state_data);
(TS_build_and_receive, AF_build_and_receive);
(TS_check_ack_settle, AF_check_ack_settle);
(TS_check_state_settle, AF_check_state_settle);
(TS_check_inflight_settle, AF_check_inflight_settle);
(TS_check_keepalive_settle, AF_check_keepalive_settle);
(TS_check_latest_queue, AF_check_latest_queue);
(TS_check_latest_drain, AF_check_latest_drain);
(TS_check_refusal_submit, AF_check_refusal_submit);
(TS_check_latest_submit, AF_check_latest_submit);
(TS_diginet_session_config_default, AF_diginet_session_config_default);
(TS_diginet_session_init, AF_diginet_session_init);
(TS_diginet_session_wake, AF_diginet_session_wake);
(TS_send_control, AF_send_control);
(TS_diginet_session_close, AF_diginet_session_close);
(TS_diginet_session_rx, AF_diginet_session_rx);
(TS_on_announce, AF_on_announce);
(TS_on_ack, AF_on_ack);
(TS_on_data, AF_on_data);
(TS_session_lost, AF_session_lost);
(TS_diginet_session_tick, AF_diginet_session_tick);
(TS_diginet_session_submit, AF_diginet_session_submit);
(TS_send_data, AF_send_data);
(TS_take, AF_take);
(TS_diginet_session_deadline, AF_diginet_session_deadline);
(TS_diginet_session_poll, AF_diginet_session_poll);
(TS_maybe_online, AF_maybe_online);
(TS_diginet_mac_is_digidesign, AF_diginet_mac_is_digidesign);
(TS_diginet_frame_is_keepalive, AF_diginet_frame_is_keepalive);
(TS_diginet_frame_parse, AF_diginet_frame_parse);
(TS_diginet_frame_build, AF_diginet_frame_build);
(TS_diginet_announce_parse, AF_diginet_announce_parse);
(TS_diginet_personality_from_name, AF_diginet_personality_from_name);
(TS_diginet_body_check, AF_diginet_body_check);
(TS_diginet_cursor_init, AF_diginet_cursor_init);
(TS_diginet_msg_next, AF_diginet_msg_next) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Class PAImg (L : ptable tsym) := mkPAImg {
pa_segs : list Segment;
pa_tbl : ctable;
pa_tbl_ok : table_ok pa_segs pa_tbl;
pa_val : nat -> Z;
pa_sigma : tsym -> Z;
pa_cert : pi_check tsym (clookup pa_tbl) pa_val pa_sigma L = true;
pa_B_ok : 0 <= pa_val A_TEXT /\ pa_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pa_val A_TEXT mod 4 = 0;
pa_val_range : forall a, 0 <= pa_val a < 2 ^ 64;
pa_wx : wx_segs_nowrap pa_segs;
pa_segs_low : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd;
pa_img_range : forall a, in_img pa_segs a -> IMG_LO <= a < IMG_TOP;
pa_img_cover : forall ly S md, layout_ok ly -> ALedger pa_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly);
pa_obj_img : forall i, (i < 95)%nat -> IMG_LO <= pa_val (A_OBJ i) /\ pa_val (A_OBJ i) + 8 <= IMG_TOP;
pa_relro_lo : Z;
pa_relro_hi : Z;
pa_relro_img : forall a, pa_relro_lo <= a < pa_relro_hi -> in_img pa_segs a;
pa_xcalls : forall s k, In (s, k) transport_xcalls -> pa_sigma s = pa_val A_TEXT + k
}.
Section c.
Context {L : ptable tsym} {PI : PAImg L}.
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
Lemma pa_sigma_receive : pa_sigma TS_receive = pa_val A_TEXT + AF_receive.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_tick : pa_sigma TS_m_tick = pa_val A_TEXT + AF_m_tick.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_settle : pa_sigma TS_settle = pa_val A_TEXT + AF_settle.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_wake : pa_sigma TS_m_wake = pa_val A_TEXT + AF_m_wake.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_wake_code : pa_sigma TS_check_state_wake_code = pa_val A_TEXT + AF_check_state_wake_code.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_sent_frame : pa_sigma TS_check_sent_frame = pa_val A_TEXT + AF_check_sent_frame.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_ack_frame : pa_sigma TS_check_ack_frame = pa_val A_TEXT + AF_check_ack_frame.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_control : pa_sigma TS_check_latest_control = pa_val A_TEXT + AF_check_latest_control.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_retry : pa_sigma TS_check_inflight_retry = pa_val A_TEXT + AF_check_inflight_retry.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_wake : pa_sigma TS_check_state_wake = pa_val A_TEXT + AF_check_state_wake.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_new : pa_sigma TS_check_inflight_new = pa_val A_TEXT + AF_check_inflight_new.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_frame : pa_sigma TS_check_latest_frame = pa_val A_TEXT + AF_check_latest_frame.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_keepalive_due : pa_sigma TS_check_keepalive_due = pa_val A_TEXT + AF_check_keepalive_due.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_sent : pa_sigma TS_check_latest_sent = pa_val A_TEXT + AF_check_latest_sent.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_display : pa_sigma TS_check_latest_display = pa_val A_TEXT + AF_check_latest_display.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_rx : pa_sigma TS_m_rx = pa_val A_TEXT + AF_m_rx.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_desk_named : pa_sigma TS_desk_named = pa_val A_TEXT + AF_desk_named.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_lost : pa_sigma TS_m_lost = pa_val A_TEXT + AF_m_lost.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_m_maybe_online : pa_sigma TS_m_maybe_online = pa_val A_TEXT + AF_m_maybe_online.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_online : pa_sigma TS_check_state_online = pa_val A_TEXT + AF_check_state_online.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_acked : pa_sigma TS_check_inflight_acked = pa_val A_TEXT + AF_check_inflight_acked.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_lost : pa_sigma TS_check_inflight_lost = pa_val A_TEXT + AF_check_inflight_lost.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_desk : pa_sigma TS_check_state_desk = pa_val A_TEXT + AF_check_state_desk.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_data : pa_sigma TS_check_state_data = pa_val A_TEXT + AF_check_state_data.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_build_and_receive : pa_sigma TS_build_and_receive = pa_val A_TEXT + AF_build_and_receive.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_ack_settle : pa_sigma TS_check_ack_settle = pa_val A_TEXT + AF_check_ack_settle.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_state_settle : pa_sigma TS_check_state_settle = pa_val A_TEXT + AF_check_state_settle.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_inflight_settle : pa_sigma TS_check_inflight_settle = pa_val A_TEXT + AF_check_inflight_settle.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_keepalive_settle : pa_sigma TS_check_keepalive_settle = pa_val A_TEXT + AF_check_keepalive_settle.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_queue : pa_sigma TS_check_latest_queue = pa_val A_TEXT + AF_check_latest_queue.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_drain : pa_sigma TS_check_latest_drain = pa_val A_TEXT + AF_check_latest_drain.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_refusal_submit : pa_sigma TS_check_refusal_submit = pa_val A_TEXT + AF_check_refusal_submit.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_check_latest_submit : pa_sigma TS_check_latest_submit = pa_val A_TEXT + AF_check_latest_submit.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_config_default : pa_sigma TS_diginet_session_config_default = pa_val A_TEXT + AF_diginet_session_config_default.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_init : pa_sigma TS_diginet_session_init = pa_val A_TEXT + AF_diginet_session_init.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_wake : pa_sigma TS_diginet_session_wake = pa_val A_TEXT + AF_diginet_session_wake.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_send_control : pa_sigma TS_send_control = pa_val A_TEXT + AF_send_control.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_close : pa_sigma TS_diginet_session_close = pa_val A_TEXT + AF_diginet_session_close.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_rx : pa_sigma TS_diginet_session_rx = pa_val A_TEXT + AF_diginet_session_rx.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_announce : pa_sigma TS_on_announce = pa_val A_TEXT + AF_on_announce.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_ack : pa_sigma TS_on_ack = pa_val A_TEXT + AF_on_ack.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_on_data : pa_sigma TS_on_data = pa_val A_TEXT + AF_on_data.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_session_lost : pa_sigma TS_session_lost = pa_val A_TEXT + AF_session_lost.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_tick : pa_sigma TS_diginet_session_tick = pa_val A_TEXT + AF_diginet_session_tick.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_submit : pa_sigma TS_diginet_session_submit = pa_val A_TEXT + AF_diginet_session_submit.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_send_data : pa_sigma TS_send_data = pa_val A_TEXT + AF_send_data.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_take : pa_sigma TS_take = pa_val A_TEXT + AF_take.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_deadline : pa_sigma TS_diginet_session_deadline = pa_val A_TEXT + AF_diginet_session_deadline.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_session_poll : pa_sigma TS_diginet_session_poll = pa_val A_TEXT + AF_diginet_session_poll.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_maybe_online : pa_sigma TS_maybe_online = pa_val A_TEXT + AF_maybe_online.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_mac_is_digidesign : pa_sigma TS_diginet_mac_is_digidesign = pa_val A_TEXT + AF_diginet_mac_is_digidesign.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_is_keepalive : pa_sigma TS_diginet_frame_is_keepalive = pa_val A_TEXT + AF_diginet_frame_is_keepalive.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_parse : pa_sigma TS_diginet_frame_parse = pa_val A_TEXT + AF_diginet_frame_parse.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_frame_build : pa_sigma TS_diginet_frame_build = pa_val A_TEXT + AF_diginet_frame_build.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_announce_parse : pa_sigma TS_diginet_announce_parse = pa_val A_TEXT + AF_diginet_announce_parse.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_personality_from_name : pa_sigma TS_diginet_personality_from_name = pa_val A_TEXT + AF_diginet_personality_from_name.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_body_check : pa_sigma TS_diginet_body_check = pa_val A_TEXT + AF_diginet_body_check.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_cursor_init : pa_sigma TS_diginet_cursor_init = pa_val A_TEXT + AF_diginet_cursor_init.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
Lemma pa_sigma_diginet_msg_next : pa_sigma TS_diginet_msg_next = pa_val A_TEXT + AF_diginet_msg_next.
Proof. apply pa_xcalls. cbn [In transport_xcalls]. repeat (first [left; reflexivity | right]). Qed.
End c.
End b.
