(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 830 of its 891 lines of code are new or changed and 1078 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_fly.v, with its module paths and module names changed; 1458 of its 1569 lines of code are new or changed and 780 lines of the source are left out. *)
(* io_send_seg_data: the DATA arm's head of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt),
   from the cut at 0x83160 = transport_text + IOS_AT 0x400 to the two exits 0x832cc (the keepalive case) and
   0x83304 (the check_latest_sent case).

   The code (io_send_cg.v header, lines 120-134; listing slots of lib/A/Prog/DgnTransportList.v):
     0x83160 - 0x83188, 0x833bc - 0x833c8  s2 = f.body_len (the 8-byte load at sp + 64); s6 = 1 when
                        body_len = 1 AND the CHECKED 1-byte load of body[0] at f.body (the 8-byte load at sp + 56)
                        is 0 AND f.ncmds = 1, else 0 (the model's keepalive flag io_send_segs.v ios_ka frame);
     0x8318c            `jal` check_inflight_new (0x84398), return address 0x83190, no argument;
     0x83190 - 0x831a4  s7 = the %hi of g_raw (TA_g_raw + 176); g_raw (the 4-byte load at 0x5df0e0) <> 0 or s6 <> 0
                        goes to 0x83298 with a1 = f.ncmds; body_len = 0 goes to 0x8329c with a1 = 0; else the
                        command count loop at 0x831a8 = transport_text + IOS_LOOP (ANOTHER segment);
     0x83298 - 0x832a0  a1 = f.ncmds (the 1-byte load at sp + 49) when the first branch came here; a0 = sp + 8;
                        `jal` check_latest_frame (0x843e0), return address 0x832a4;
     0x832a4 - 0x832c8  a1 = f.send (the 4-byte load at sp + 40); g_raw loaded again through s7; s4 = M
                        (0x5df160); the 4-byte stores of f.send at M + 84 (M.host_counter) and at g_last_counter
                        (0x5df140); g_raw = 0 AND s6 <> 0 goes on to 0x832cc, else to 0x83304.
   `sp` here is the walk's sp (the entry sp less IOSEND_FRAME = 160).

   The error path this stretch must refute is 0x834ac, the checked load of body[0] = p + 30: the byte lies in
   [p, p + len) (lib/A/Prog/io_send_seg_frm.v ios_len60 and ios_body_len), which trans_src_ok marks usable. The
   token engine of lib/A/Prog/PaShadow.v decides it: the shadow byte's load leaves a token, the `bnez` on it is the
   ASan slow block, and the obligation it leaves is range_addressable of [p + 30, p + 31), which decode_rd_ok
   (DgnTransportCg.v trans_src_ok_rd) gives.

   The walk: four runs of TransportGRunA.v paj_run_x over the caller's G journal, and two leaf calls through
   TransportGCg.v gx_call_leaf and the leaf bridge DgnTransportLeafb.v decode_leafb_journal.
     run A (0x83160 .. 0x8318c)  the keepalive flag; no store (every region read-only, so the memory is the call's);
     check_inflight_new          lib/A/Prog/check_inflight_new_cg.v, through transport_leaf_at (no argument);
     run B (0x83190 .. 0x832a0)  the three branches and, on two of them, the call of check_latest_frame;
     run C (0x8329c .. 0x832a0)  the loop's exit joins here (a1 = cmds);
     check_latest_frame          lib/A/Prog/check_latest_frame_cg.v, a0 = sp + 8, a1 = cmds;
     run D (0x832a4 .. 0x832c8)  the two 4-byte stores into G and the last branch.
   Each store is a byte of G (W_journalG.v awr_ok_x's G case) and of io_send_cg.v iosend_wr
   (io_send_seg_world.v ios_wr_hostc / ios_wr_lastc); the world after the pair is two TWorldG.v tw_write steps at
   the rows TMAP_A_M and TMAP_A_g_last_counter, which is exactly the model's
   B5 = set_g_last_counter (set_M_host_counter (ios_B0 Bw) send) send.

   THE CUT this file starts at is iod_in: io_send_seg_cut.v ios_at_csf at 0x83160 and f.cmd in s5. The pieces are
   stated each in continuation form; lib/A/Prog/io_send_seg_dpost.v ios_data_post joins them with
   io_send_seg_loop.v ios_loop, io_send_seg_tail.v ios_tail_seg and io_send_seg_join.v ios_fly_post into the DATA
   arm from the cut to the walk's post. Proved here:
     iod_entryA   the symbolic state at the cut 0x83160 (the two regions the stretch reads: io_send's own frame
                  with f.ncmds, f.body and f.body_len, and the frame's byte body[0] at p + 30);
     iod_runA     0x83160 .. 0x8318c, all three paths (body_len <> 1; body_len = 1 with body[0] <> 0; and
                  0x833bc - 0x833c8 with body[0] = 0), the ASan check of body[0] refuted from trans_src_ok, and
                  s6 = the model's `ios_ka frame` on each of them;
     iod_call_cin the call of check_inflight_new through gx_call_leaf and decode_leafb_journal;
     iod_headA    the two joined: from the cut to the return 0x83190, handing on the journal, the bytes the leaf
                  kept (everything outside its own ESTACK window), the memory it kept present, the registers it
                  preserved, and s2 = f.body_len and s6 = ios_ka frame;
     iod_entryB, iod_runB0  0x83190 .. 0x831a8, all four paths: g_raw <> 0 and the keepalive flag to IOS_CMDS with
                  a1 = f.ncmds, body_len = 0 to IOS_CMDS with a1 = 0, else to IOS_LOOP with a1 = 0;
     iod_call_clf the call of check_latest_frame (a0 = sp + 8, a1 = cmds);
     iod_callC    0x8329c .. 0x832a0 joined to that call, from IOS_CMDS to the return 0x832a4;
     iod_entryD   the symbolic state at 0x832a4 (f.send, g_raw through s7, and the two words of G it stores);
     iod_runD     0x832a4 .. 0x832c8: the two 4-byte stores of f.send into G (M + 84 and g_last_counter), the
                  world after them, and the last branch `beq ((g_raw <u 1) & s6), 0` at 0x832c8, giving the two
                  exits 0x832cc (IOS_KA) and 0x83304 (IOS_SENT) with the case fact io_send_seg_tail.v ios_tail_seg
                  takes. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportLeafb LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_inflight_new_cg check_latest_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_cut io_send_seg_world io_send_seg_frm io_send_seg_src io_send_seg_ack.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_cg.
Module LLF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_cg.
Module LINc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_new_c.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LLFc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_frame_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The addresses of the stretch                                        *)
(* ------------------------------------------------------------------ *)

(* The cut this file starts at (0x83160), the return of check_inflight_new (0x83190), the join a1 = f.ncmds takes
   (0x83298), the return of check_latest_frame (0x832a4) and the two exits (0x832cc, 0x83304). *)
Definition IOS_DATA : Z := IOS_AT 0x400.
Definition IOS_CIN_RET : Z := IOS_AT 0x430.
Definition IOS_NCMDS : Z := IOS_AT 0x538.
Definition IOS_CLF_RET : Z := IOS_AT 0x544.
Definition IOS_KA : Z := IOS_AT 0x56c.
Definition IOS_SENT : Z := IOS_AT 0x5a4.

Lemma iod_addrs :
  transport_text + IOS_DATA = 0x83160 /\ transport_text + IOS_CIN_RET = 0x83190 /\
  transport_text + IOS_NCMDS = 0x83298 /\ transport_text + IOS_CLF_RET = 0x832a4 /\
  transport_text + IOS_KA = 0x832cc /\ transport_text + IOS_SENT = 0x83304.
Proof. repeat split; reflexivity. Qed.

(* The keepalive flag as the machine holds it in s6. *)
Definition iod_kaz (frame : list byte) : Z := if ios_ka frame then 1 else 0.

(* The value s7 holds from 0x83190 on: the %hi of g_raw (the listing's A_HI 55). *)
Definition IOD_S7 : Z := TA_g_raw + 176.

(* ------------------------------------------------------------------ *)
(* Reading the struct and the frame                                    *)
(* ------------------------------------------------------------------ *)

(* Byte j of the little-endian value of a byte list of n bytes. *)
Lemma iod_le_byte_n : forall (l : list byte) (n j : nat) d, length l = n -> (j < n)%nat ->
  YO0f.le_byte (bytes_le_to_Z l) n j = bv_unsigned (nth j l d).
Proof. intros l n j d <- Hj. exact (tw_le_byte_ble l j d Hj). Qed.

(* Byte j of the n-byte field at offset k of a byte list. *)
Lemma iod_u_at_byte : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  YO0f.le_byte (TW.u_at L (Z.of_nat k) n) n j = bv_unsigned (nth (k + j) L (Z_to_bv 8 0)).
Proof.
intros L k n j Hkn Hj.
assert (HL : length (TW.sub L (Z.of_nat k) n) = n) by (apply TWL.length_sub; lia).
unfold TW.u_at.
rewrite (iod_le_byte_n (TW.sub L (Z.of_nat k) n) n j (Z_to_bv 8 0) HL Hj).
rewrite (tw_nth_sub L (Z.of_nat k) n j (Z_to_bv 8 0) ltac:(lia) Hj ltac:(lia)).
replace (Z.to_nat (Z.of_nat k) + j)%nat with (k + j)%nat by lia. reflexivity.
Qed.

(* The n-byte field at offset k of a byte list the view shows at q, as a chunk value. *)
Lemma iod_val_of_garr8 : forall (mm : word -> option byte) q (L : list byte) (k n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> (k + n <= length L)%nat ->
  YI04.val_mem tfibsegs mm (q + Z.of_nat k) n (TW.u_at L (Z.of_nat k) n).
Proof.
intros mm q L k n Hg Hkn j Hj.
assert (Hj2 : (k + j < length (map DSpec.bz L))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte tfibsegs mm q (map DSpec.bz L) (k + j) Hg Hj2) as Hm.
replace (q + Z.of_nat k + Z.of_nat j) with (q + Z.of_nat (k + j)) by lia.
rewrite Hm. f_equal. f_equal.
rewrite (iod_u_at_byte L k n j Hkn Hj).
change (nth (k + j) (map DSpec.bz L) 0) with (nth (k + j) (map DSpec.bz L) (DSpec.bz (Z_to_bv 8 0))).
rewrite map_nth. reflexivity.
Qed.

(* The raw bytes of that field, as the leaf contracts read them (Mem.bytes_at of the model's put). *)
Lemma iod_bytes_of_garr8 : forall (W : world tfibsegs) mem q (L : list byte) (k n : nat),
  garr8 tfibsegs (mrestrict (w_H W) mem) q (map DSpec.bz L) -> (k + n <= length L)%nat ->
  0 <= q -> q + Z.of_nat (length L) <= 2 ^ 64 ->
  bytes_at rsegs mem (q + Z.of_nat k) (TW.put n (TW.u_at L (Z.of_nat k) n)).
Proof.
intros W mem q L k n Hg Hkn Hq Ht.
split; [lia|]. rewrite TWL.length_put. split; [lia|].
intros i Hi.
assert (Hi2 : (k + i < length (map DSpec.bz L))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte tfibsegs (mrestrict (w_H W) mem) q (map DSpec.bz L) (k + i) Hg Hi2) as Hm.
assert (Ev : w_H W (Z_to_bv 64 (q + Z.of_nat (k + i))) = false)
  by exact (decode_leafb_mbyte_vis W mem _ _ Hm).
replace (q + Z.of_nat k + Z.of_nat i) with (q + Z.of_nat (k + i)) by lia.
assert (Erd : mrd rsegs mem (wa (q + Z.of_nat (k + i))) =
              mbyte tfibsegs (mrestrict (w_H W) mem) (q + Z.of_nat (k + i)))
  by (unfold mrd, wa, mbyte, mrestrict; rewrite Ev; reflexivity).
rewrite Erd, Hm.
unfold TW.put. rewrite (decode_leafb_nth_le_bytes n (TW.u_at L (Z.of_nat k) n) i Hi).
f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256.
change (nth (k + i) (map DSpec.bz L) 0) with (nth (k + i) (map DSpec.bz L) (DSpec.bz (Z_to_bv 8 0))).
rewrite map_nth. unfold DSpec.bz.
rewrite <- (iod_u_at_byte L k n i Hkn Hi). unfold YO0f.le_byte.
rewrite (Z.mod_small (TW.u_at L (Z.of_nat k) n) (2 ^ (8 * Z.of_nat n))) by apply TWL.u_at_range.
change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The same two, with the offset as a Z (how the struct's fields are named). *)
Lemma iod_val_at : forall (mm : word -> option byte) q (L : list byte) (k : Z) (n : nat),
  garr8 tfibsegs mm q (map DSpec.bz L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  YI04.val_mem tfibsegs mm (q + k) n (TW.u_at L k n).
Proof.
intros mm q L k n Hg Hk Hkn. replace k with (Z.of_nat (Z.to_nat k)) by lia.
apply (iod_val_of_garr8 mm q L (Z.to_nat k) n Hg). lia.
Qed.

Lemma iod_bytes_at : forall (W : world tfibsegs) mem q (L : list byte) (k : Z) (n : nat),
  garr8 tfibsegs (mrestrict (w_H W) mem) q (map DSpec.bz L) -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length L) -> 0 <= q -> q + Z.of_nat (length L) <= 2 ^ 64 ->
  bytes_at rsegs mem (q + k) (TW.put n (TW.u_at L k n)).
Proof.
intros W mem q L k n Hg Hk Hkn Hq Ht. replace k with (Z.of_nat (Z.to_nat k)) by lia.
apply (iod_bytes_of_garr8 W mem q L (Z.to_nat k) n Hg ltac:(lia) Hq Ht).
Qed.

(* An aview equality is an mbyte equality of the restricted memories. *)
Lemma iod_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory that keeps the range's bytes. *)
Lemma iod_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q l,
  garr8 tfibsegs (mrestrict H m) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m') q l.
Proof.
intros H m m' q l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (iod_mbyte_of_aview H m m' (q + Z.of_nat j + Z.of_nat 0)); [exact (Hv 0%nat Hi) | apply Hk; lia].
Qed.

(* An 8-byte word of a view, kept by a step that keeps its eight bytes. *)
Lemma iod_rdword_kept : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
        (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

(* bv_eqb of two 64-bit literals. *)
Lemma iod_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
intros x y Hx Hy. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic states of the four runs                                *)
(* ------------------------------------------------------------------ *)

(* run A (0x83160 .. 0x8318c). Atoms: 0 .. 31 the registers at the cut (2 = sp, 9 = s1 = p, 20 = s4 = the shadow
   base), 32 = f.body_len, 33 = f.ncmds, 34 = the byte body[0]. Regions: io_send's own 160-byte frame above sp
   (read-only here: the stretch stores nothing) with the three fields it reads, and the frame's byte body[0] at
   p + 30, whose chunk is atom 34. *)
Definition iod_frameA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 0 0
    [YP09.mkChunk 49 (CVal 1 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 9 30));
     YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
(* The value a 1-byte unsigned load leaves: the atom, zero-extended. *)
Lemma iod_zext8_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 u.
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small u) by lia. apply Z.mod_small. lia.
Qed.

(* The value a signed 4-byte load leaves, and equality of a signed 64-bit literal with zero. *)
Lemma iod_sext32_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma iod_eqb0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
rewrite Z.mod_0_l by lia.
destruct (Z.eqb_spec x 0) as [->|Hne]; [rewrite Z.mod_0_l by lia; reflexivity|].
apply Z.eqb_neq.
destruct (Z_lt_le_dec x 0) as [Hlt|Hge].
- assert (Hm : x mod 18446744073709551616 = x + 18446744073709551616).
  { rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mul_1_l.
    apply Z.mod_small. lia. }
  rewrite Hm. lia.
- rewrite Z.mod_small by lia. exact Hne.
Qed.

(* The two ALU steps that build the keepalive flag (`addi -1` then `sltiu 1`). *)
Lemma iod_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma iod_sltu_den : forall (x y : word),
  alu64 ALU_SLTU x y = Z_to_bv 64 (if bv_unsigned x <? bv_unsigned y then 1 else 0).
Proof.
intros x y. cbn [alu64 alu]. rewrite bv_ltu_unsigned.
destruct (bv_unsigned x <? bv_unsigned y); reflexivity.
Qed.

(* A signed wrap does not change the low bytes a store writes. *)
Lemma iod_swrap_mod : forall (n : N) z, bv_swrap n z mod 2 ^ Z.of_N n = z mod 2 ^ Z.of_N n.
Proof.
intros n z. unfold bv_swrap, bv_wrap, bv_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma iod_le_byte_swrap : forall (n : N) (w j : nat) v, Z.of_N n = 8 * Z.of_nat w ->
  YO0f.le_byte (bv_swrap n v) w j = YO0f.le_byte v w j.
Proof.
intros n w j v Hn. unfold YO0f.le_byte. rewrite <- Hn, iod_swrap_mod. reflexivity.
Qed.

(* The last branch's condition, 0x832b8 - 0x832c8: g_raw = 0 AND the keepalive flag. *)
Lemma iod_andb_den : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if ((a =? 1) && (b =? 1))%bool then 1 else 0).
Proof.
intros a b Ha Hb.
assert (Ea : a = 0 \/ a = 1) by lia. assert (Eb : b = 0 \/ b = 1) by lia.
destruct Ea as [Ea0|Ea1]; destruct Eb as [Eb0|Eb1]; subst; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma iod_cond_den : forall E n m (gs s : Z), sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 gs ->
  - 2 ^ 31 <= gs < 2 ^ 31 -> ew E m = Z_to_bv 64 s -> 0 <= s <= 1 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SExt true 32 (SOff n 0)) (SLit 1)) (SOff m 0))
    = Z_to_bv 64 (if (negb (TC.truth gs) && (s =? 1))%bool then 1 else 0).
Proof.
intros E n m gs s Hg Hr Hm Hs.
change (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SExt true 32 (SOff n 0)) (SLit 1)) (SOff m 0)))
  with (alu64 ALU_AND (alu64 ALU_SLTU (sv_denot E (SExt true 32 (SOff n 0))) (Z_to_bv 64 1))
          (sv_denot E (SOff m 0))).
assert (Hden : sv_denot E (SOff m 0) = Z_to_bv 64 s)
  by (cbn [sv_denot]; rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rewrite Hg, Hden, iod_sltu_den.
assert (Hlt : (bv_unsigned (Z_to_bv 64 gs) <? bv_unsigned (Z_to_bv 64 1)) = negb (TC.truth gs)).
{ change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. unfold TC.truth.
  destruct (Z.eqb_spec gs 0) as [->|Hne]; [reflexivity|].
  destruct (Z_lt_le_dec gs 0) as [Hl|Hge].
  - assert (Hm2 : gs mod 18446744073709551616 = gs + 18446744073709551616).
    { rewrite <- (Z.mod_add gs 1 18446744073709551616) by lia. rewrite Z.mul_1_l. apply Z.mod_small. lia. }
    rewrite Hm2. cbn [negb]. apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. cbn [negb]. apply Z.ltb_ge. lia. }
rewrite Hlt.
rewrite (iod_andb_den (if negb (TC.truth gs) then 1 else 0) s
  ltac:(destruct (negb (TC.truth gs)); lia) Hs).
f_equal. destruct (TC.truth gs); cbn [negb]; destruct (Z.eqb_spec s 1); cbn [andb]; reflexivity.
Qed.

(* s6 after 0x833bc - 0x833c4: 1 exactly when f.ncmds is 1. *)
Lemma iod_s6_den : forall E n ncm, ew E n = Z_to_bv 64 ncm -> 0 <= ncm < 256 ->
  sv_denot E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff n 0)) (SLit (-1))) (SLit 1))
    = Z_to_bv 64 (if ncm =? 1 then 1 else 0).
Proof.
intros E n ncm Hn Hncm.
change (sv_denot E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff n 0)) (SLit (-1))) (SLit 1)))
  with (alu64 ALU_SLTU (alu64 ALU_ADD (sv_denot E (SExt false 8 (SOff n 0))) (Z_to_bv 64 (-1)))
          (Z_to_bv 64 1)).
rewrite (iod_zext8_den E n ncm Hn Hncm), (iod_add_den ncm (-1)), iod_sltu_den.
f_equal. change (bv_unsigned (Z_to_bv 64 1)) with 1.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616.
destruct (Z.eqb_spec ncm 1) as [->|Hne]; [reflexivity|].
destruct (Z.eq_dec ncm 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.mod_small (ncm + -1)) by lia.
destruct (Z.ltb_spec (ncm + -1) 1); [lia | reflexivity].
Qed.
Definition iod_bodyA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 30 31 0 0 [YP09.mkChunk 30 (CVal 1 (SOff 34 0))].
Definition iod_regionsA : smem := [iod_frameA; iod_bodyA].
Definition iod_factsA : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 (2 ^ 47 - 60) 0);
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_iodA : sstate := mkSS IOS_DATA sr_atoms iod_regionsA None iod_factsA.

(* The token engine's shadow base (s4) and its shadow entries (none: the only instrumented check of the stretch is
   decided by the obligation the token leaves). *)
Definition IOD_Bx : sv := SOff 20 0.
Definition IOD_SH : list shent := [].

(* run B (0x83190 .. 0x832a0). Atoms: 32 = g_raw, 33 = f.ncmds. Regions: g_raw's 4 bytes (the listing's object 29)
   and io_send's frame, both read-only. *)
Definition iod_rawB : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 29)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition iod_frameB : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 0 0 [YP09.mkChunk 49 (CVal 1 (SOff 33 0))].
Definition iod_regionsB : smem := [iod_frameB; iod_rawB].
Definition iod_factsB : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 29, mkAF TA_g_raw TA_g_raw 5)] [] [].
Definition ss_iodB : sstate := mkSS IOS_CIN_RET sr_atoms iod_regionsB None iod_factsB.

(* run C (0x8329c .. 0x832a0), the join the command count loop leaves at: two moves, no memory. *)
Definition iod_factsC : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_iodC : sstate := mkSS IOS_CMDS sr_atoms [] None iod_factsC.

(* run D (0x832a4 .. 0x832c8). Atoms: 32 = f.send, 33 = g_raw. Regions: io_send's frame (read-only), g_raw read
   through s7 (atom 23, which holds TA_g_raw + 176 from run B on), M's host_counter (writable) and g_last_counter through its %hi
   (A_HI 59, 384 above it; writable). *)
Definition iod_frameD : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 160 0 0 [YP09.mkChunk 40 (CVal 4 (SOff 32 0))].
Definition iod_rawD : YP09.region :=
  YP09.mkRegion (Some 23%nat) (-176) (-172) 0 0 [YP09.mkChunk (-176) (CVal 4 (SOff 33 0))].
Definition iod_hostD : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 84 88 84 88 [].
Definition iod_lastD : YP09.region := YP09.mkRegion (Some (A_HI 59)) (-384) (-380) (-384) (-380) [].
Definition iod_regionsD : smem := [iod_frameD; iod_rawD; iod_hostD].
Definition iod_factsD : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (23%nat, mkAF (TA_g_raw + 176) (TA_g_raw + 176) 4);
           (A_OBJ 8, mkAF TA_M TA_M 5);
           (A_HI 59, mkAF (TA_g_last_counter + 384) (TA_g_last_counter + 384) 6)] [] [].
Definition ss_iodD : sstate := mkSS IOS_CLF_RET sr_atoms iod_regionsD None iod_factsD.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac iod_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "iod_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac iod_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The struct's body pointer at a parse that succeeded: the frame's byte 30. *)
Lemma iod_sf_body : forall (fa : Z) (frame : list byte), DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK ->
  TCt.sf_ptr fa (TC.rf frame) (DSpec.sf_body (TC.rf frame)) = fa + 30.
Proof.
intros fa frame HOK.
destruct (ios_fields frame HOK)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbody & _ & _ & _).
unfold TCt.sf_ptr. rewrite HOK, Z.eqb_refl. cbv iota. rewrite Fbody. reflexivity.
Qed.

(* The write rights of a run whose regions are all read-only. *)
Ltac iod_awrA :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Ltac iod_show_reg HS r :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ss _ => let e := eval vm_compute in (sr_get (ss_regs ss) r) in idtac "REG:" e
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ ?ss _ =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in idtac "REG:" e
  end.

(* ------------------------------------------------------------------ *)
(* What the leaf calls need of the harness globals                     *)
(* ------------------------------------------------------------------ *)

(* Every payload byte of the 18 harness globals lies in a loaded segment of image A, so no world hides it. *)
Lemma iod_hull_vis : forall (W : world tfibsegs) x,
  TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W x Hx. apply (decode_vis_seg W).
apply (decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x); [vm_compute; reflexivity | lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory the leaf reads. *)
Lemma iod_tw_csw : forall (W : world tfibsegs) mem Bx,
  tw_at TMAP_A (aview tfibsegs (w_H W) mem) Bx -> tw_at TMAP_A (csw_view mem) Bx.
Proof.
intros W mem Bx H. apply (tw_kept TMAP_A _ _ Bx H). intros x Hx.
unfold csw_view. rewrite (decode_aview_mrd W mem x (iod_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

(* A range of the harness globals' hull is visible, so a leaf's footprint may read it. *)
Lemma iod_rng_hull : forall (W : world tfibsegs) lo len, TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
intros W lo len H1 H2.
apply (decode_rng W); [unfold TG.G_HARNESS_LO in *; lia | unfold TG.G_HARNESS_HI in *; lia |].
intros b Hb. apply iod_hull_vis. lia.
Qed.

Section dataw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut 0x83160                               *)
(* ------------------------------------------------------------------ *)

(* The walk's valuation for run A: the registers at the cut, and f.body_len, f.ncmds, body[0] as atoms 32, 33, 34. *)
Definition iod_EA (regs2 : bvmap 5 word) (blen ncm b0 : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 [Z_to_bv 64 blen; Z_to_bv 64 ncm; Z_to_bv 64 b0]).

Lemma iod_entryA : forall (W2 : world segs) mem2 (regs2 : bvmap 5 word) (sp p blen ncm b0 : Z),
  YK11.getr regs2 2 = w64 sp -> YK11.getr regs2 9 = w64 p -> YK11.getr regs2 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  4096 <= p -> p + 60 <= 2 ^ 47 -> (p + 31 <= sp \/ sp + 160 <= p) ->
  0 <= blen < 2 ^ 64 -> 0 <= ncm < 256 -> 0 <= b0 < 256 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 49) 1 ncm ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 56) 8 (p + 30) ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 64) 8 blen ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (p + 30) 1 b0 ->
  st_ok_pi segs VAL (iod_EA regs2 blen ncm b0) ss_iodA
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_DATA)) mem2 (YK11.seg_rom segs)))
  /\ sh_ok segs IOD_Bx IOD_SH (iod_EA regs2 blen ncm b0) (mrestrict (w_H W2) mem2).
Proof.
intros W2 mem2 regs2 sp p blen ncm b0 H2 H9 H20 Hs1 Hs2 Hs16 Hp1 Hp2 Hdisj Hbl Hnc Hb0 V49 V56 V64 V30.
set (E := iod_EA regs2 blen ncm b0).
assert (E2 : ew E 2 = YK11.getr regs2 2) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E9 : ew E 9 = YK11.getr regs2 9) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs2 20) by (unfold E, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = p) by (rewrite E9, H9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 blen)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ncm)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 b0)
  by (unfold E, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
split; [|unfold sh_ok, IOD_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_iodA, iod_regionsA.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold iod_frameA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val segs E _ sp 49 1 (SOff 33 0) ncm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V49].
    * apply (chunk_ok_val segs E _ sp 56 8 (SOff 9 30) (p + 30));
        [cbn [sv_denot]; rewrite U9; reflexivity | cbn; lia | lia | exact V56].
    * apply (chunk_ok_val segs E _ sp 64 8 (SOff 32 0) blen);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V64].
  + unfold iod_bodyA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ p 30 1 (SOff 34 0) b0);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V30].
- apply pairwise_disjoint_of_extents.
  unfold iod_frameA, iod_bodyA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold iod_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U20.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The cuts                                                            *)
(* ------------------------------------------------------------------ *)

(* The cut at 0x83160: exactly the state io_send_seg_cut.v ios_at_csf names (the dispatch reaches the DATA arm's
   head with the struct, the frame and the world of the return of check_sent_frame), and f.cmd in s5. *)
Definition iod_in (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) : Prop :=
  ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 /\
  YK11.getr regs2 21 = w64 (DSpec.sf_cmd (TC.rf frame)).

(* ------------------------------------------------------------------ *)
(* The leaf call of check_inflight_new                                 *)
(* ------------------------------------------------------------------ *)

(* check_inflight_new at 0x84398 (call at 0x8318c), no argument. *)
Lemma iod_call_cin : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp : Z) (Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_check_inflight_new_cg) fx') ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  iak_call_win STK sp0 sp ->
  tw_at TMAP_A (aview segs (w_H W2) memT) Bx -> TC.check_inflight_new_m Bx = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       iak_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp Bx HCELLS LAWS LEAF HJ
    R2 Rra R3 R4 (Hal & Hlo & Hhi) HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  apply (gx_call_leaf segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (iak_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  unfold iak_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LINc.CHECK_INFLIGHT_NEW None [] (fun _ => Bx = Bx) HJS).
  - change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))). rewrite SPu. lia.
  - rewrite Zminus_mod, Hal, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact Rra.
  - exact R3.
  - exact R4.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, LIN.transport_check_inflight_new_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    + exact (iak_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LINc.CHECK_INFLIGHT_NEW_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu.
      unfold LINc.CHECK_INFLIGHT_NEW_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LINc.CHECK_INFLIGHT_NEW_FRAME) LINc.CHECK_INFLIGHT_NEW_FRAME HJS);
        unfold LINc.CHECK_INFLIGHT_NEW_FRAME; lia.
    + apply iak_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_STATE, TA_M, TW.A_M_state, TW.OFF_M,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply iak_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_FLY_ON, TA_M, TW.A_M_fly_on, TW.OFF_M,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply iak_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_NOW, TA_g_now,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply iak_rng_hull; unfold LINc.CHECK_INFLIGHT_NEW_BACKOFF, TA_M, TW.A_M_backoff_until, TW.OFF_M,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* run A: the keepalive flag, 0x83160 .. 0x8318c                       *)
(* ------------------------------------------------------------------ *)

Lemma iod_nth_skipn : forall (m : nat) (l : list byte) d, nth 0 (skipn m l) d = nth m l d.
Proof.
induction m as [|m IH]; intros l d; [reflexivity|].
destruct l as [|x l]; cbn; [reflexivity | apply IH].
Qed.

(* The byte body[0] the stretch loads, as the model's at8 of the body. *)
Lemma iod_b0 : forall frame, DSpec.sf_code (TC.rf frame) = DSpec.SPEC_OK -> (31 <= length frame)%nat ->
  TW.u_at frame 30 1 = DSpec.at8 (ios_body frame) 0.
Proof.
intros frame HOK Hl.
destruct (ios_body_len frame HOK) as (EB & _ & _ & _).
unfold DSpec.at8, DSpec.bz, DSpec.b8. rewrite EB, iod_nth_skipn.
pose proof (iod_u_at_byte frame 30 1 0 ltac:(lia) ltac:(lia)) as Hb.
change (Z.of_nat 30) with 30 in Hb. change (30 + 0)%nat with 30%nat in Hb.
rewrite <- Hb.
pose proof (TWL.u_at_range frame 30 1) as R. change (8 * Z.of_nat 1) with 8 in R.
symmetry. exact (tw_le_byte1 (TW.u_at frame 30 1) ltac:(lia)).
Qed.

(* The registers run A leaves untouched (io_send's own, less s2 and s6, which it sets). *)
Definition IOD_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25; 26; 27]%bv.

(* The state at the call of check_inflight_new (0x8318c): the memory of the cut (run A stores nothing), the cut's
   registers but for s2 = f.body_len, s6 = the keepalive flag, and ra = the return address 0x83190. *)
Definition iod_at_cin (regs2 regs3 : bvmap 5 word) (frame : list byte) : Prop :=
  (forall r, In r IOD_KEEP -> YK11.getr regs3 r = YK11.getr regs2 r) /\
  YK11.getr regs3 18 = w64 (ios_blen frame) /\
  YK11.getr regs3 22 = w64 (iod_kaz frame) /\
  YK11.getr regs3 1 = Z_to_bv 64 (BASE + IOS_CIN_RET).

(* The keepalive flag, branch by branch. *)
Lemma iod_kaz_val : forall frame,
  iod_kaz frame = (if ios_blen frame =? 1
                   then (if DSpec.at8 (ios_body frame) 0 =? 0
                         then (if DSpec.sf_ncmds (TC.rf frame) =? 1 then 1 else 0) else 0) else 0).
Proof.
intros frame. unfold iod_kaz, ios_ka.
destruct (ios_blen frame =? 1); cbn [andb]; [|reflexivity].
destruct (DSpec.at8 (ios_body frame) 0 =? 0); cbn [andb]; [|reflexivity].
destruct (DSpec.sf_ncmds (TC.rf frame) =? 1); reflexivity.
Qed.

(* env_agree survives the token engine's extra atoms. *)
Lemma iod_agree_ext : forall rg (l : list word) (E : env) n w, (32 <= n)%nat ->
  env_agree 32 (Ereg rg l) E -> env_agree 32 (Ereg rg l) (ewset E n w).
Proof.
intros rg l E n w Hn (H1 & H2). split; [| exact H2].
intros m Hm. rewrite ew_ewset_other by lia. exact (H1 m Hm).
Qed.

Lemma iod_base : forall o : Z, BASE + o = transport_text + o.
Proof. intros o. f_equal. Qed.

(* The registers run D keeps: io_send's own but s4, which it loads with M. *)
Definition IOD_KEEPD : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.

(* The eight bytes of G run D writes. *)
Definition IOD_WR (a : Z) : Prop :=
  (TA_M + 84 <= a < TA_M + 88) \/ (TA_g_last_counter <= a < TA_g_last_counter + 4).

(* The close of one exit of run D: the memory is the one after the two stores, the world is at B5. It leaves
   the kept registers, s4 = M and the case fact. *)
Ltac iod_fin HS HJ Em HK pc K1 K2 G1 G2 HTW :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sg (transport_text + pc) rgx mm mdx) Qx) end;
  rewrite Em in HJ |- *;
  apply HK;
  [ exact HJ
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn; unfold IOD_WR in Hn;
    rewrite (K2 a Ha ltac:(intros X; apply Hn; right; exact X));
    apply K1; [lia | intros X; apply Hn; left; exact X]
  | let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; apply G2; apply G1; exact Hp
  | idtac | idtac | exact HTW | idtac ].

(* Normalize a symbolic state in place. *)
Ltac iod_rw HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* A register index is callee-saved: compute its number, then compare. *)
Ltac iod_cs :=
  unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end);
  lia.

(* The value of a register of a stopped run, as the symbolic value its state names. *)
Ltac iod_rv HS :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      lazymatch goal with
      | |- YK11.getr (ms_regs _) ?r = _ =>
          let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
          refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx r HS) _);
          change (sv_denot Ex (sr_get (ss_regs ssx) r)) with (sv_denot Ex e)
      end
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      lazymatch goal with
      | |- YK11.getr (ms_regs _) ?r = _ =>
          let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
          refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
          change (sv_denot Ex (sr_get (ss_regs ssx) r)) with (sv_denot Ex e)
      end
  end.

(* The registers run B keeps: it sets s7, a0 and a1 only. *)
Definition IOD_KEEPB : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(* The close of one path of run B: the memory is the one it started from, the registers of IOD_KEEPB are kept. *)
Ltac iod_closeB HS HJ Em HK AG pc :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sg (transport_text + pc) rgx mm mdx) Qx) end;
  rewrite Em in HJ |- *;
  apply HK;
  [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ IOD_KEEPB HS AG ltac:(vm_compute; reflexivity))
  | idtac | idtac | exact HJ | idtac .. ].

(* The close of one path of run A: the memory is the cut's, the registers are the cut's but for s2, s6 and ra.
   It leaves exactly one goal, the value of s6 on that path. *)
Ltac iod_closeA HS HJ Em HK HE32 HF56 AG :=
  pmkst HS;
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) mm rom) mdx) Qx) end;
  rewrite Em in HJ |- *;
  apply HK; [ | exact HJ ];
  split; [ | split; [ | split ] ];
  [ eapply (regs_kept_of_st_ok segs _ _ _ _ _ IOD_KEEP HS);
      [ repeat (apply iod_agree_ext; [lia|]); exact AG | vm_compute; reflexivity ]
  | iod_rv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite HE32, Z.add_0_r, Z_to_bv_bv_unsigned;
    unfold w64, ios_blen; rewrite HF56; reflexivity
  | iod_rv HS
  | iod_rv HS; apply codeptr_val; assumption ].

Lemma iod_runA : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  iod_in STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  (forall md3 (regs3 : bvmap 5 word),
     iod_at_cin regs2 regs3 frame ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem2 md3 (k + 0) ->
     SRr segs W2
       (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 LINc.CHECK_INFLIGHT_NEW) mem2 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_DATA) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HF HIN HCSF HK.
destruct HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
  & HKD & HCLS & HLD & HAI1).
destruct HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
destruct HIN as (HST & HS5).
destruct HST as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
destruct HCUR as (HJ2 & Hfrs & Hperm & Hmo & HKEPT).
destruct HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS0.
pose proof HJ2 as (HSTK2 & _ & (memS2 & HJ2i & _) & _).
rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
clear HJ2i memS2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
(* the frame's length and where it lies *)
pose proof (ios_len60 (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HL60.
pose proof (ios_sf_code (ios_B0 Bw) frame (ios_B0 Bw) HCSF) as HOK.
assert (Hpp : 4096 <= p /\ p + 60 <= 2 ^ 47).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR0 Hsrc ltac:(lia))
    as [Hpl | Hpl]; lia. }
destruct Hpp as (Hp1 & Hp2).
assert (EFO : IOS_F_OFF = 8) by reflexivity.
assert (ESF : SF_SIZE = 80) by reflexivity.
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
assert (Hdj : p + 31 <= sp \/ sp + 160 <= p)
  by (unfold decode_off_win in Hoff; destruct Hoff as [Hf1|Hf1]; [left | right]; lia).
(* the struct spec_frame at sp + 8 *)
rewrite EFO in HSF, HSFsrc.
destruct HSF as (Hfp0 & Hfp8 & SBl & HSB & HSBlen & F0 & F8 & F16 & F24 & F26 & F28 & F30 & F32 & F36 & F40 &
  F41 & F48 & F56 & F64 & F72).
assert (HSBl : Z.of_nat (length SBl) = 80) by (rewrite HSBlen; reflexivity).
(* the three fields run A reads, and the byte body[0] *)
assert (V49 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 49) 1 (TW.u_at SBl 41 1)).
{ replace (sp + 49) with (sp + 8 + 41) by lia.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 41 1 HSB); [lia | cbn; lia]. }
assert (V56 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 56) 8 (p + 30)).
{ replace (sp + 56) with (sp + 8 + 48) by lia.
  rewrite <- (iod_sf_body p frame HOK), <- F48.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 48 8 HSB); [lia | cbn; lia]. }
assert (V64 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp + 64) 8 (TW.u_at SBl 56 8)).
{ replace (sp + 64) with (sp + 8 + 56) by lia.
  apply (iod_val_at (mrestrict (w_H W2) mem2) (sp + 8) SBl 56 8 HSB); [lia | cbn; lia]. }
assert (V30 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (p + 30) 1 (TW.u_at frame 30 1))
  by exact (iod_val_at (mrestrict (w_H W2) mem2) p frame 30 1 HGARR ltac:(lia) ltac:(cbn; lia)).
(* the ranges of the three atoms *)
pose proof (TWL.u_at_range SBl 56 8) as R56. change (8 * Z.of_nat 8) with 64 in R56.
pose proof (TWL.u_at_range SBl 41 1) as R41. change (8 * Z.of_nat 1) with 8 in R41.
pose proof (TWL.u_at_range frame 30 1) as R30. change (8 * Z.of_nat 1) with 8 in R30.
(* the symbolic state at the cut *)
set (EA := iod_EA regs2 (TW.u_at SBl 56 8) (TW.u_at SBl 41 1) (TW.u_at frame 30 1)) in *.
assert (E32 : ew EA 32 = Z_to_bv 64 (TW.u_at SBl 56 8))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew EA 33 = Z_to_bv 64 (TW.u_at SBl 41 1))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew EA 34 = Z_to_bv 64 (TW.u_at frame 30 1))
  by (unfold EA, iod_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (D32 : sv_denot EA (SOff 32 0) = Z_to_bv 64 (TW.u_at SBl 56 8))
  by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (D33 : sv_denot EA (SOff 33 0) = Z_to_bv 64 (TW.u_at SBl 41 1))
  by (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (D34 : sv_denot EA (SOff 34 0) = Z_to_bv 64 (TW.u_at frame 30 1))
  by (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
destruct (iod_entryA W2 mem2 regs2 sp p (TW.u_at SBl 56 8) (TW.u_at SBl 41 1) (TW.u_at frame 30 1)
  R2 R9 R20 ltac:(lia) ltac:(lia) ltac:(rewrite Esp, Zminus_mod, Hsp16, FF; reflexivity) Hp1 Hp2
  Hdj ltac:(lia) ltac:(cbn in R41; lia) ltac:(cbn in R30; lia)
  V49 V56 V64 V30) as [HS SHOK].
fold EA in HS, SHOK.
assert (HEI : img_env VAL A_LIM EA) by (unfold EA, iod_EA; apply Eimg_env).
assert (AGbase : env_agree 32
  (Ereg regs2 [Z_to_bv 64 (TW.u_at SBl 56 8); Z_to_bv 64 (TW.u_at SBl 41 1); Z_to_bv 64 (TW.u_at frame 30 1)]) EA)
  by (unfold EA, iod_EA; apply iak_agree).
(* the frame's bytes are addressable (the obligation the checked load of body[0] leaves) *)
destruct (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
  as (HRDv & HRA & HRH & HRM & HR0 & HR63).
assert (E9 : ew EA 9 = YK11.getr regs2 9) by (unfold EA, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew EA 20 = YK11.getr regs2 20) by (unfold EA, iod_EA; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U9 : bv_unsigned (ew EA 9) = p) by (rewrite E9, R9; apply unsigned_lit_small; lia).
assert (UX : U EA (SOff 9 30) = p + 30) by (rewrite U_SOff, U9; apply zcanon_id; unfold M64; lia).
assert (UB : U EA IOD_Bx = SHADOW_OFF).
{ unfold IOD_Bx. rewrite U_SOff, E20, R20. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply zcanon_id. unfold SHADOW_OFF, M64. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUN.
pose proof (paj_branch (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_DATA)) mem2 (YK11.seg_rom segs)) md2) Qx)
end.
paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
{ iod_awrA. }
rename ms into msa.
assert (Ema : ms_mem msa = mem2).
{ eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: rewrite D32 in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (iod_eqb (TW.u_at SBl 56 8) 1 ltac:(lia) ltac:(lia)) in Hc.
all: set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *.
all: clearbody md1.
all: clear mat.
- (* f.body_len <> 1: the keepalive flag is 0 *)
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hblen.
  paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
  { iod_awrA. }
  rename ms into msc. assert (Emc : ms_mem msc = mem2).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG. iod_closeA HS HJ2 Emc HK E32 F56 AGbase.
  + (* s6 = 0: the body is not one byte long *)
    change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0).
    unfold w64. f_equal. rewrite iod_kaz_val. unfold ios_blen. rewrite <- F56.
    destruct (Z.eqb_spec (TW.u_at SBl 56 8) 1) as [Hz|_]; [exfalso; exact (Hblen Hz) | reflexivity].
- (* f.body_len = 1: the checked load of body[0] *)
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hblen.
  paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
  { rewrite Ema. eapply obl_of_range; [exact HRA | exact UB | rewrite UX; lia | rewrite UX; lia]. }
  { iod_awrA. }
  rename ms into msb.
  assert (Emb : ms_mem msb = mem2).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  all: lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let E34x := fresh "E34x" in
    assert (E34x : ew Ex 34 = Z_to_bv 64 (TW.u_at frame 30 1))
      by (rewrite ?ew_ewset_other by lia; exact E34);
    rewrite (iod_zext8_den Ex 34 (TW.u_at frame 30 1) E34x ltac:(lia)) in Hc end.
  all: cbn [branch_taken sv_denot] in Hc.
  all: rewrite (iod_eqb (TW.u_at frame 30 1) 0 ltac:(lia) ltac:(lia)) in Hc.
  + (* body[0] = 0: the keepalive flag is f.ncmds = 1 *)
    apply Z.eqb_eq in Hc. rename Hc into Hb0.
    paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
    { iod_awrA. }
    rename ms into msd. assert (Emd : ms_mem msd = mem2).
    { rewrite <- Emb. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG. iod_closeA HS HJ2 Emd HK E32 F56 AGbase.
    * lazymatch goal with |- sv_denot ?Ex _ = _ =>
        let E33x := fresh "E33x" in
        assert (E33x : ew Ex 33 = Z_to_bv 64 (TW.u_at SBl 41 1))
          by (rewrite ?ew_ewset_other by lia; exact E33);
        rewrite (iod_s6_den Ex 33 (TW.u_at SBl 41 1) E33x ltac:(cbn in R41; lia)) end.
      unfold w64. f_equal. rewrite iod_kaz_val. unfold ios_blen. rewrite <- F56, Hblen.
      rewrite <- (iod_b0 frame HOK ltac:(lia)), Hb0. rewrite <- F41. reflexivity.
  + (* body[0] <> 0: the keepalive flag is 0 *)
    apply Z.eqb_neq in Hc. rename Hc into Hb0.
    paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
    { iod_awrA. }
    rename ms into mse. assert (Eme : ms_mem mse = mem2).
    { rewrite <- Emb. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG. iod_closeA HS HJ2 Eme HK E32 F56 AGbase.
    * change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0).
      unfold w64. f_equal. rewrite iod_kaz_val.
      rewrite <- (iod_b0 frame HOK ltac:(lia)).
      destruct (Z.eqb_spec (ios_blen frame) 1) as [_|_]; [|reflexivity].
      destruct (Z.eqb_spec (TW.u_at frame 30 1) 0) as [Hz|_]; [exfalso; exact (Hb0 Hz) | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The leaf call of check_latest_frame                                 *)
(* ------------------------------------------------------------------ *)

(* check_latest_frame at 0x843e0 (call at 0x832a0), a0 = sp + 8, a1 = cmds (sign-extended from 32 bits). It reads
   f.send, f.ncmds and f.body_len of the struct at sp + 8. *)
Lemma iod_call_clf : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp p cmds : Z) (fr Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLF.transport_check_latest_frame_cg) fx') ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (sp + 8) ->
  YK11.getr regsT (Z_to_bv 5 11) = Z_to_bv 64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  iak_call_win STK sp0 sp ->
  trans_sframe_at W2 memT (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_A (aview segs (w_H W2) memT) Bx -> TC.check_latest_frame_m Bx fr cmds = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LLFc.CHECK_LATEST_FRAME) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
         ly2 S2 W2 mem3 md3 k /\
       iak_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp p cmds fr Bx HCELLS LAWS LEAF HJ
    R2 R10 R11 Hcm Rra R3 R4 (Hal & Hlo & Hhi) HSF HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  destruct HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & _ & Fsend & _ & _ & Fncm & _ & Fblen & _).
  apply (gx_call_leaf segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (iak_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  unfold iak_lr.
  apply (decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LLFc.CHECK_LATEST_FRAME None [] (fun _ => Bx = Bx) HJS).
  - change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))). rewrite SPu. lia.
  - rewrite Zminus_mod, Hal, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact Rra.
  - exact R3.
  - exact R4.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, LLF.transport_check_latest_frame_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx (sp + 8) fr cmds HPRE).
    cbv zeta in LF.
    assert (HRA : forall o n, 0 <= o -> o + n <= 80 -> 0 <= n ->
      range_addressable (aview segs (w_H W2) memT) SHADOW_OFF (sp + 8 + o) n)
      by (intros o n Ho Hon Hn; apply (can_stack_addressable segs B ly2 S2 W2 memT mdT (sp + 8 + o) n HAR); lia).
    assert (HAD : forall o n, 0 <= o -> o + n <= 80 -> 0 <= n -> ACells.addressable memT (sp + 8 + o) n).
    { intros o n Ho Hon Hn. apply (decode_leafb_addressable W2 memT (sp + 8 + o) n (HRA o n Ho Hon Hn));
        [lia | lia | unfold ACells.APPMEM_END; lia |].
      intros i Hi. apply (@decode_leafb_app_stack rc). lia. }
    assert (HRS : forall o n, 0 <= o -> 0 < n -> o mod 8 + n <= 8 -> o + n <= 80 ->
      ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) (ACells.shadow_addr (sp + 8 + o)) 1).
    { intros o n Ho Hn Hm Hon.
      pose proof (decode_leafb_rng_shadow W2 memT (sp + 8 + o) n (HRA o n Ho Hon ltac:(lia)) ltac:(lia) ltac:(lia)
        ltac:(lia)) as Hr.
      rewrite (iak_shadow_one (sp + 8) o n) in Hr by first [exact Hfp8 | lia]. exact Hr. }
    assert (HRJ : forall o n, 0 <= o -> o + n <= 80 -> ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) (sp + 8 + o) n)
      by (intros o n Ho Hon;
          apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k (sp + 8 + o) n HJS);
          lia).
    assert (HBY : forall k0 (n : nat) v, 0 <= k0 -> k0 + Z.of_nat n <= 80 -> TW.u_at SB k0 n = v ->
      LMem.bytes_at segs memT (sp + 8 + k0) (TW.put n v)).
    { intros k0 n v Hk Hkn Hv.
      apply (decode_leafb_bytes_garr8 W2 memT (sp + 8 + k0) (TW.put n v)); [| lia | rewrite TWL.length_put; lia].
      exact (iak_field _ (sp + 8) SB k0 n v HG Hk ltac:(rewrite HLSB; exact Hkn) Hv). }
    apply LF; clear LF.
    + exact R10.
    + exact R11.
    + exact Hcm.
    + lia.
    + exact Hfp8.
    + exact (HBY 32 4%nat _ ltac:(lia) ltac:(cbn; lia) Fsend).
    + exact (HBY 41 1%nat _ ltac:(lia) ltac:(cbn; lia) Fncm).
    + exact (HBY 56 8%nat _ ltac:(lia) ltac:(cbn; lia) Fblen).
    + exact (iak_tw_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT mdT HAR).
    + rewrite SPu. apply (@decode_leafb_app_stack rc). unfold LLFc.CHECK_LATEST_FRAME_FRAME. lia.
    + rewrite SPu. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME, ACells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLFc.CHECK_LATEST_FRAME_FRAME, ACells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 56 8 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 41 1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + exact (HAD 32 4 ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite SPu. apply (decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LLFc.CHECK_LATEST_FRAME_FRAME) LLFc.CHECK_LATEST_FRAME_FRAME HJS);
        unfold LLFc.CHECK_LATEST_FRAME_FRAME; lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + exact (HRS 56 8 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 56 8 ltac:(lia) ltac:(lia)).
    + apply iak_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_MAXBODY, TA_g_cfg, TW.A_Cfg_max_body, TW.OFF_g_cfg,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (HRS 41 1 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + exact (HRJ 41 1 ltac:(lia) ltac:(lia)).
    + apply iak_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_MAXCMDS, TA_g_cfg, TW.A_Cfg_max_cmds, TW.OFF_g_cfg,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + apply iak_rng_hull; unfold TA_g_raw, TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (HRS 32 4 ltac:(lia) ltac:(lia) ltac:(vm_compute; let H := fresh in intro H; discriminate H) ltac:(lia)).
    + apply iak_rng_hull; unfold LLFc.CHECK_LATEST_FRAME_HOST, TA_M, TW.A_M_host_counter, TW.OFF_M,
        TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
    + exact (HRJ 32 4 ltac:(lia) ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the return 0x83190                            *)
(* ------------------------------------------------------------------ *)

(* run B's valuation: the registers there, g_raw as atom 32 and f.ncmds as atom 33. *)
Definition iod_EB (regs3 : bvmap 5 word) (graw ncm : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs3 [Z_to_bv 64 graw; Z_to_bv 64 ncm]).

Lemma iod_entryB : forall (W2 : world segs) mem3 (regs3 : bvmap 5 word) (sp graw ncm : Z),
  YK11.getr regs3 2 = w64 sp -> YK11.getr regs3 20 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= graw < 2 ^ 32 -> 0 <= ncm < 256 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) TA_g_raw 4 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 49) 1 ncm ->
  st_ok_pi segs VAL (iod_EB regs3 graw ncm) ss_iodB
    (restrict (w_H W2) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_CIN_RET)) mem3 (YK11.seg_rom segs)))
  /\ sh_ok segs IOD_Bx IOD_SH (iod_EB regs3 graw ncm) (mrestrict (w_H W2) mem3).
Proof.
intros W2 mem3 regs3 sp graw ncm H2 H20 Hs1 Hs2 Hs16 Hgr Hnc V0 V49.
set (E := iod_EB regs3 graw ncm).
assert (E2 : ew E 2 = YK11.getr regs3 2) by (unfold E, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs3 20) by (unfold E, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 graw)
  by (unfold E, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ncm)
  by (unfold E, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EO : ew E (A_OBJ 29) = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (unfold E, iod_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VO : VAL (A_OBJ 29) = TA_g_raw) by (vm_compute; reflexivity).
assert (UO : bv_unsigned (ew E (A_OBJ 29)) = TA_g_raw)
  by (rewrite EO, VO; apply unsigned_lit_small; unfold TA_g_raw; lia).
split; [|unfold sh_ok, IOD_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_iodB, iod_regionsB.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold iod_frameB, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp 49 1 (SOff 33 0) ncm);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V49].
  + unfold iod_rawB, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UO. split; [unfold TA_g_raw; lia|]. split; [unfold TA_g_raw; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_g_raw 0 4 (SOff 32 0) graw);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia
      | rewrite Z.add_0_r; exact V0].
- apply pairwise_disjoint_of_extents.
  unfold iod_frameB, iod_rawB, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, UO.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | unfold TA_g_raw; lia].
- unfold iod_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U20, UO.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [lia | unfold SHADOW_OFF; lia | unfold TA_g_raw; lia | vm_compute; reflexivity].
Qed.

(* run B, 0x83190 .. 0x831a8: s7 = the %hi of g_raw, then the three branches. It ends at transport_text +
   IOS_CMDS with a1 = f.ncmds (g_raw <> 0 or the keepalive flag), at IOS_CMDS with a1 = 0 (body_len = 0), or at
   transport_text + IOS_LOOP with a1 = 0 (the command count loop). *)
Lemma iod_runB0 : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem3 md3 k
    (regs3 : bvmap 5 word) (sp graw ncm : Z) (frame Bw : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 k ->
  YK11.getr regs3 2 = w64 sp -> YK11.getr regs3 20 = w64 SHADOW_OFF ->
  YK11.getr regs3 18 = w64 (ios_blen frame) -> YK11.getr regs3 22 = w64 (iod_kaz frame) ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= graw < 2 ^ 32 -> 0 <= ncm < 256 -> 0 <= ios_blen frame < 2 ^ 64 ->
  TW.g_raw (ios_B0 Bw) = bv_swrap 32 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) TA_g_raw 4 graw ->
  YI04.val_mem segs (mrestrict (w_H W2) mem3) (sp + 49) 1 ncm ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 23 = w64 IOD_S7 -> YK11.getr regs4 11 = w64 ncm ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     (TC.truth (TW.g_raw (ios_B0 Bw)) = true \/ ios_ka frame = true) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CMDS) regs4 mem3 md4) Q) ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 23 = w64 IOD_S7 -> YK11.getr regs4 11 = w64 0 ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame = 0 ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CMDS) regs4 mem3 md4) Q) ->
  (forall md4 (regs4 : bvmap 5 word),
     (forall r, In r IOD_KEEPB -> YK11.getr regs4 r = YK11.getr regs3 r) ->
     YK11.getr regs4 23 = w64 IOD_S7 -> YK11.getr regs4 11 = w64 0 ->
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md4 k ->
     TC.truth (TW.g_raw (ios_B0 Bw)) = false -> ios_ka frame = false -> ios_blen frame <> 0 ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_LOOP) regs4 mem3 md4) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CIN_RET) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem3 md3 k regs3 sp graw ncm frame Bw Q
  HL HJ R2 R20 R18 R22 Hs1 Hs2 Hs16 Hgr Hnc Hbl HGR V0 V49 HKn HKz HKl.
pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
  & HKD & HCLS & HLD & HAI1).
set (EB := iod_EB regs3 graw ncm) in *.
assert (E32 : ew EB 32 = Z_to_bv 64 graw)
  by (unfold EB, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew EB 33 = Z_to_bv 64 ncm)
  by (unfold EB, iod_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E18 : ew EB 18 = YK11.getr regs3 18) by (unfold EB, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E22 : ew EB 22 = YK11.getr regs3 22) by (unfold EB, iod_EB; apply ew_Eimg_Ereg_nat; reflexivity).
assert (AGB : env_agree 32 (Ereg regs3 [Z_to_bv 64 graw; Z_to_bv 64 ncm]) EB)
  by (unfold EB, iod_EB; apply iak_agree).
destruct (iod_entryB W2 mem3 regs3 sp graw ncm R2 R20 Hs1 Hs2 Hs16 Hgr Hnc V0 V49) as [HS SHOK].
fold EB in HS, SHOK.
assert (HEI : img_env VAL A_LIM EB) by (unfold EB, iod_EB; apply Eimg_env).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_CIN_RET)) mem3 (YK11.seg_rom segs)) md3)
    Qx) end.
assert (Hgrr : - 2 ^ 63 <= TW.g_raw (ios_B0 Bw) < 2 ^ 63).
{ pose proof (TWL.s32_range (ios_B0 Bw) TW.OFF_g_raw) as Hr. unfold TW.g_raw. lia. }
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ iod_awrA. }
rename ms into msa.
assert (Ema : ms_mem msa = mem3).
{ eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
clear HF HFr HG.
assert (EH55 : ew EB (A_HI 55) = Z_to_bv 64 IOD_S7).
{ unfold EB, iod_EB. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  assert (VH : VAL (A_HI 55) = IOD_S7) by (vm_compute; reflexivity). rewrite VH. reflexivity. }
assert (QS7 : forall (ssx : sstate) (Ex : env) (msx : machine_state),
  st_ok_pi segs VAL Ex ssx (restrict (w_H W2) msx) -> ew Ex (A_HI 55) = Z_to_bv 64 IOD_S7 ->
  sr_get (ss_regs ssx) 23 = SOff (A_HI 55) 0 -> YK11.getr (ms_regs msx) 23 = w64 IOD_S7).
{ intros ssx Ex msx HSx HEx Hget.
  refine (eq_trans (st_ok_pi_restrict_reg (w_H W2) Ex ssx msx 23 HSx) _). rewrite Hget.
  cbn [sv_denot]. rewrite HEx, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  let E32x := fresh "E32x" in
  assert (E32x : ew Ex 32 = Z_to_bv 64 graw) by (rewrite ?ew_ewset_other by lia; exact E32);
  rewrite (iod_sext32_den Ex 32 graw E32x ltac:(lia)) in Hc end.
all: rewrite <- HGR in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (iod_eqb0 (TW.g_raw (ios_B0 Bw)) Hgrr) in Hc.
all: change (negb (TW.g_raw (ios_B0 Bw) =? 0)) with (TC.truth (TW.g_raw (ios_B0 Bw))) in Hc.
all: set (md1 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
all: clearbody md1. all: clear mat.
- (* g_raw <> 0: a1 = f.ncmds *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2038.
  { iod_awrA. }
  rename ms into msb. assert (Emb : ms_mem msb = mem3).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG. iod_closeB HS HJ Emb HKn AGB IOS_CMDS.
  + exact (QS7 _ _ _ HS EH55 ltac:(vm_compute; reflexivity)).
  + iod_rv HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
      let E33x := fresh "E33x" in
      assert (E33x : ew Ex 33 = Z_to_bv 64 ncm) by (rewrite ?ew_ewset_other by lia; exact E33);
      exact (iod_zext8_den Ex 33 ncm E33x ltac:(lia)) end.
  + left. exact Hc.
- (* g_raw = 0 *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { iod_awrA. }
  rename ms into msc. assert (Emc : ms_mem msc = mem3).
  { rewrite <- Ema. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  all: lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    let E22x := fresh "E22x" in
    assert (E22x : ew Ex 22 = w64 (iod_kaz frame))
      by (rewrite ?ew_ewset_other by lia; rewrite E22; exact R22);
    cbn [branch_taken sv_denot] in Hc0; rewrite E22x in Hc0 end.
  all: unfold w64 in Hc0. all: rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc0.
  all: rewrite (iod_eqb (iod_kaz frame) 0 ltac:(unfold iod_kaz; destruct (ios_ka frame); lia) ltac:(lia)) in Hc0.
  all: unfold iod_kaz in Hc0.
  + (* the keepalive flag is set: a1 = f.ncmds *)
    destruct (ios_ka frame) eqn:HKA; [|cbn in Hc0; discriminate Hc0].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2038.
    { iod_awrA. }
    rename ms into msd. assert (Emd : ms_mem msd = mem3).
    { rewrite <- Emc. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG. iod_closeB HS HJ Emd HKn AGB IOS_CMDS.
    * exact (QS7 _ _ _ HS EH55 ltac:(vm_compute; reflexivity)).
    * iod_rv HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
        let E33x := fresh "E33x" in
        assert (E33x : ew Ex 33 = Z_to_bv 64 ncm) by (rewrite ?ew_ewset_other by lia; exact E33);
        exact (iod_zext8_den Ex 33 ncm E33x ltac:(lia)) end.
    * right. reflexivity.
  + (* the keepalive flag is clear *)
    destruct (ios_ka frame) eqn:HKA; [cbn in Hc0; discriminate Hc0|].
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { iod_awrA. }
    rename ms into mse. assert (Eme : ms_mem mse = mem3).
    { rewrite <- Emc. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    all: lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      let E18x := fresh "E18x" in
      assert (E18x : ew Ex 18 = w64 (ios_blen frame))
        by (rewrite ?ew_ewset_other by lia; rewrite E18; exact R18);
      cbn [branch_taken sv_denot] in Hc1; rewrite E18x in Hc1 end.
    all: unfold w64 in Hc1. all: rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc1.
    all: rewrite (iod_eqb (ios_blen frame) 0 ltac:(lia) ltac:(lia)) in Hc1.
    * (* body_len = 0: a1 = 0 *)
      apply Z.eqb_eq in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2038.
      { iod_awrA. }
      rename ms into msf. assert (Emf : ms_mem msf = mem3).
      { rewrite <- Eme. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
      clear HF HFr HG. iod_closeB HS HJ Emf HKz AGB IOS_CMDS.
      -- exact (QS7 _ _ _ HS EH55 ltac:(vm_compute; reflexivity)).
      -- iod_rv HS. change (sv_denot EB (SLit 0)) with (Z_to_bv 64 0). reflexivity.
      -- exact Hc.
      -- reflexivity.
      -- exact Hc1.
    * (* body_len <> 0: the command count loop *)
      apply Z.eqb_neq in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1f44.
      { iod_awrA. }
      rename ms into msg. assert (Emg : ms_mem msg = mem3).
      { rewrite <- Eme. eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
      clear HF HFr HG. iod_closeB HS HJ Emg HKl AGB IOS_LOOP.
      -- exact (QS7 _ _ _ HS EH55 ltac:(vm_compute; reflexivity)).
      -- iod_rv HS. change (sv_denot EB (SLit 0)) with (Z_to_bv 64 0). reflexivity.
      -- exact Hc.
      -- reflexivity.
      -- exact Hc1.
Qed.

(* ------------------------------------------------------------------ *)
(* run A and the call: 0x83160 to the return 0x83190                   *)
(* ------------------------------------------------------------------ *)

(* What the leaf leaves behind: the journal, the bytes outside its own ESTACK window, the memory it keeps
   present, the registers it preserves, and s2 and s6 of run A. *)
Lemma iod_headA : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  iod_in STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  TC.check_inflight_new_m (ios_B0 Bw) = Some (ios_B0 Bw, tt) ->
  (forall mem3 md3 (regs3 : bvmap 5 word),
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem3 md3 (k + 0) ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (spZ regs - IOSEND_FRAME - ESTACK <= a < spZ regs - IOSEND_FRAME) ->
        aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
     (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
     (forall r, In r IOD_KEEP -> YK11.getr regs3 r = YK11.getr regs2 r) ->
     YK11.getr regs3 18 = w64 (ios_blen frame) ->
     YK11.getr regs3 22 = w64 (iod_kaz frame) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CIN_RET) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_DATA) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HFX HIN HCSF HM HK.
pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
  & HKD & HCLS & HLD & HAI1).
pose proof HFX as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & Hinv1 & Hinv2 & Hnev).
pose proof HIN as (HST & HS5).
pose proof HST as (HCUR & HSAV & HREG & HS811 & HSF & HSFsrc & HGARR & HSRC & HTW).
pose proof HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
pose proof HJ as (HSTK & _ & (memS0 & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp : 2 ^ 46 + IOSEND_STK <= spZ regs <= 2 ^ 47) by lia.
apply (iod_runA STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw
  ly2 S2 W2 mem2 md2 regs2 Q HL HFX HIN HCSF).
intros md3 regs3 (RK & R18 & R22 & R1) HJ3.
assert (Q2 : YK11.getr regs3 2 = w64 (spZ regs - IOSEND_FRAME)).
{ rewrite <- R2. apply RK. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Q3 : YK11.getr regs3 3 = w64 (as_gp B)).
{ rewrite <- Hgp, <- R3. apply RK. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Q4 : YK11.getr regs3 4 = w64 (as_tp B)).
{ rewrite <- Htp, <- R4. apply RK. unfold IOD_KEEP. cbn [In]. auto 20. }
assert (Qra : YK0s.ret_ok (YK11.getr regs3 1)).
{ rewrite R1. unfold IOS_CIN_RET, IOS_AT, AF_io_send.
  apply (@ret_ok_codeptr_v rc transport_listing PI_transport); [lia | reflexivity]. }
assert (HWIN : iak_call_win STK sp0 (spZ regs - IOSEND_FRAME)).
{ split; [rewrite Zminus_mod, Hsp16, FF; reflexivity | split; lia]. }
eapply SRr_bind.
{ exact (iod_call_cin STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem2 md3 (k + 0) regs3
    (spZ regs - IOSEND_FRAME) (ios_B0 Bw) HCELLS LAWS HIN2 HJ3 Q2 Qra Q3 Q4 HWIN HTW HM). }
intros W3 c3 _ (-> & rg4 & mem4 & md4 & -> & HJ4 & HP4 & _ & HK4 & HG4 & _).
change (YK11.getr regs3 (Z_to_bv 5 1)) with (YK11.getr regs3 1). rewrite R1.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) _ =>
  change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CIN_RET) rgx mm mdx) Q) end.
assert (SP3 : spZ regs3 = spZ regs - IOSEND_FRAME)
  by (change (spZ regs3) with (bv_unsigned (YK11.getr regs3 2)); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
apply HK.
- exact HJ4.
- intros a Ha Hn. apply (HK4 a Ha ltac:(rewrite SP3; exact Hn) ltac:(intros X; inversion X)).
- exact HG4.
- intros r Hr. rewrite (iak_ap regs3 rg4 r HP4 ltac:(unfold IOD_KEEP in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [iod_cs |]); destruct Hr)). exact (RK r Hr).
- rewrite (iak_ap regs3 rg4 18 HP4 ltac:(iod_cs)). exact R18.
- rewrite (iak_ap regs3 rg4 22 HP4 ltac:(iod_cs)). exact R22.
Qed.

(* ------------------------------------------------------------------ *)
(* run C and the call: 0x8329c to the return 0x832a4                   *)
(* ------------------------------------------------------------------ *)

(* The registers kept from IOS_CMDS to the return of check_latest_frame: io_send's own (callee-saved). *)
Definition IOD_KEEPC : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* 0x8329c: a0 = sp + 8; 0x832a0: `jal` check_latest_frame with a1 = cmds; it returns to 0x832a4. *)
Lemma iod_callC : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem3 md3 k
    (regs4 : bvmap 5 word) (sp p cmds : Z) (frame Bx : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem3 md3 k ->
  YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regs4 (Z_to_bv 5 3) = w64 (as_gp B) ->
  YK11.getr regs4 (Z_to_bv 5 4) = w64 (as_tp B) ->
  YK11.getr regs4 (Z_to_bv 5 11) = Z_to_bv 64 (bv_swrap 32 cmds) -> 0 <= cmds < 2 ^ 32 ->
  iak_call_win STK sp0 sp -> 2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 ->
  trans_sframe_at W2 mem3 (sp + 8) p (TC.rf frame) ->
  tw_at TMAP_A (aview segs (w_H W2) mem3) Bx -> TC.check_latest_frame_m Bx frame cmds = Some (Bx, tt) ->
  (forall mem5 md5 (regs5 : bvmap 5 word),
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem5 md5 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W2) mem5 a = aview segs (w_H W2) mem3 a) ->
     (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem5 a) ->
     (forall r, In r IOD_KEEPC -> YK11.getr regs5 r = YK11.getr regs4 r) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CLF_RET) regs5 mem5 md5) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CMDS) regs4 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem3 md3 k regs4 sp p cmds frame Bx Q
    HL HJ R2 R3 R4 R11 Hcm HWIN Hs1 Hs2 HSF HTW HM HK.
  pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
    & HKD & HCLS & HLD & HAI1).
  pose proof HWIN as (Hal & Hlo & Hhi).
  pose proof (@paj_run_x fx rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
    HGX 0 []) as RUN.
  pose proof (iak_entry0 W2 regs4 mem3 IOS_CMDS) as HS.
  assert (HEI : img_env VAL A_LIM (iak_E0 regs4)) by (unfold iak_E0; apply Eimg_env).
  assert (SHOK : sh_ok segs IAK_Bx (@nil shent) (iak_E0 regs4) (mrestrict (w_H W2) mem3)) by constructor.
  unfold cfg_at.
  change (SRr segs W2 (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + IOS_CMDS)) mem3 (YK11.seg_rom segs)) md3) Q).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { apply awr_ok_x_nil. }
  set (md1 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md1. clear mat.
  rename ms into ms1.
  assert (K1 : forall x, ms_mem ms1 x = mem3 x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
  clear HF HFr HG.
  pose proof (aregs_preserved_of_st_ok segs (w_H W2) (iak_E0 regs4) _ ms1 regs4 [] HS (iak_agree regs4 [])
    ltac:(vm_compute; reflexivity)) as P1.
  iod_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + IOS_CLF_RET)) Q1 ltac:(apply codeptr_val; assumption).
  iod_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (sp + 8)) Q10 ltac:(unfold iak_E0; apply iak_den_sp; [exact R2 | lia]).
  iod_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (bv_swrap 32 cmds)) Q11
    ltac:(cbn [sv_denot]; rewrite (iak_E_reg regs4 [] 11 (Z_to_bv 5 11) eq_refl), R11, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  assert (Q2 : YK11.getr (ms_regs ms1) (Z_to_bv 5 2) = Z_to_bv 64 sp)
    by (rewrite (P1 2 ltac:(unfold acallee_saved; lia)); exact R2).
  assert (Q3 : YK11.getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B))
    by (rewrite (P1 3 ltac:(unfold acallee_saved; lia)); exact R3).
  assert (Q4 : YK11.getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B))
    by (rewrite (P1 4 ltac:(unfold acallee_saved; lia)); exact R4).
  assert (Qra : YK0s.ret_ok (YK11.getr (ms_regs ms1) (Z_to_bv 5 1))).
  { rewrite Q1. unfold IOS_CLF_RET, IOS_AT, AF_io_send.
    apply (@ret_ok_codeptr_v rc transport_listing PI_transport); [lia | reflexivity]. }
  assert (HSF1 : trans_sframe_at W2 (ms_mem ms1) (sp + 8) p (TC.rf frame))
    by (apply (iak_sframe_kept W2 mem3 (ms_mem ms1) (sp + 8) p (TC.rf frame));
        [intros a _; apply iak_aview_ext; exact K1 | exact HSF]).
  assert (HTW1 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms1)) Bx)
    by (apply (tw_kept TMAP_A _ _ Bx HTW); intros x _; apply iak_aview_ext; exact K1).
  assert (KC : forall r, In r IOD_KEEPC -> YK11.getr (ms_regs ms1) r = YK11.getr regs4 r).
  { eapply (regs_kept_of_st_ok segs _ _ _ _ _ IOD_KEEPC HS); [exact (iak_agree regs4 []) | vm_compute; reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (YK11.mkst rgx (Z_to_bv 64 LLFc.CHECK_LATEST_FRAME) mm rom) mdx) Qx) end.
  eapply SRr_bind.
  { exact (iod_call_clf STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 (ms_mem ms1) _ k (ms_regs ms1) sp p cmds
      frame Bx HCELLS LAWS HLF HJ Q2 Q10 Q11 Hcm Qra Q3 Q4 HWIN HSF1 HTW1 HM). }
  intros W3 c3 _ (-> & rg5 & mem5 & md5 & -> & HJ5 & HP5 & _ & HK5 & HG5 & _).
  rewrite Q1.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rgx _ ?mm ?rom) ?mdx) _ =>
    change (SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CLF_RET) rgx mm mdx) Q) end.
  assert (SP1 : spZ (ms_regs ms1) = sp)
    by (change (spZ (ms_regs ms1)) with (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2))); rewrite Q2;
        apply unsigned_lit_small; lia).
  apply HK.
  - exact HJ5.
  - intros a Ha Hn. rewrite (HK5 a Ha ltac:(rewrite SP1; exact Hn) ltac:(intros X; inversion X)).
    apply iak_aview_ext. exact K1.
  - intros a Hp. apply HG5. apply (iak_present_ext _ _ _ a K1). exact Hp.
  - intros r Hr. rewrite (iak_ap _ rg5 r HP5 ltac:(unfold IOD_KEEPC in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [iod_cs |]); destruct Hr)). exact (KC r Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the return 0x832a4                            *)
(* ------------------------------------------------------------------ *)

(* run D's valuation: the registers there, f.send as atom 32 and g_raw as atom 33. *)
Definition iod_ED (regs5 : bvmap 5 word) (send graw : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs5 [Z_to_bv 64 send; Z_to_bv 64 graw]).

Lemma iod_entryD : forall (W2 : world segs) mem5 (regs5 : bvmap 5 word) (sp send graw : Z),
  YK11.getr regs5 2 = w64 sp -> YK11.getr regs5 20 = w64 SHADOW_OFF -> YK11.getr regs5 23 = w64 IOD_S7 ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= send < 2 ^ 32 -> 0 <= graw < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) (sp + 40) 4 send ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) TA_g_raw 4 graw ->
  st_ok_pi segs VAL (iod_ED regs5 send graw) ss_iodD
    (restrict (w_H W2) (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + IOS_CLF_RET)) mem5 (YK11.seg_rom segs)))
  /\ sh_ok segs IOD_Bx IOD_SH (iod_ED regs5 send graw) (mrestrict (w_H W2) mem5).
Proof.
intros W2 mem5 regs5 sp send graw H2 H20 H23 Hs1 Hs2 Hs16 Hsd Hgr V40 V0.
set (E := iod_ED regs5 send graw).
assert (E2 : ew E 2 = YK11.getr regs5 2) by (unfold E, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = YK11.getr regs5 20) by (unfold E, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2, H2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20, H20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 send)
  by (unfold E, iod_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 graw)
  by (unfold E, iod_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
assert (UM : bv_unsigned (ew E (A_OBJ 8)) = TA_M).
{ unfold E, iod_ED. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (V : VAL (A_OBJ 8) = TA_M) by (vm_compute; reflexivity). rewrite V.
  apply unsigned_lit_small. unfold TA_M; lia. }
assert (E23 : ew E 23 = YK11.getr regs5 23) by (unfold E, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (U55 : bv_unsigned (ew E 23) = TA_g_raw + 176)
  by (rewrite E23, H23; unfold w64, IOD_S7; apply unsigned_lit_small; unfold TA_g_raw; lia).
assert (U59 : bv_unsigned (ew E (A_HI 59)) = TA_g_last_counter + 384).
{ unfold E, iod_ED. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  assert (V : VAL (A_HI 59) = TA_g_last_counter + 384) by (vm_compute; reflexivity). rewrite V.
  apply unsigned_lit_small. unfold TA_g_last_counter; lia. }
split; [|unfold sh_ok, IOD_SH; constructor].
rewrite restrict_mkst_fx. unfold ss_iodD, iod_regionsD.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold iod_frameD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp 40 4 (SOff 32 0) send);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V40].
  + unfold iod_rawD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U55. split; [unfold TA_g_raw; lia|]. split; [unfold TA_g_raw; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (TA_g_raw + 176) (-176) 4 (SOff 33 0) graw);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | unfold TA_g_raw; lia
      | replace (TA_g_raw + 176 + -176) with TA_g_raw by lia; exact V0].
  + unfold iod_hostD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UM. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|].
    split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw).
    apply (ios_inG_row _ _ _ _ TMAP_A_M). unfold TW.SZ_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold iod_frameD, iod_rawD, iod_hostD, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, UM, U55.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | unfold TA_g_raw, TA_M, TA_g_last_counter; lia].
- unfold iod_factsD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U20, UM, U55, U59.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [lia | unfold SHADOW_OFF; lia | unfold TA_g_raw; lia | unfold TA_M; lia | unfold TA_g_last_counter; lia
          | vm_compute; reflexivity].
Qed.

(* The write rights of run D: the two words it stores are bytes of G (M.host_counter, g_last_counter). *)
Ltac iod_awrD UM U59 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite UM in Ha; apply (ios_inG_row _ _ _ a TMAP_A_M); unfold TW.SZ_M in *; lia
            | rewrite U59 in Ha; apply (ios_inG_row _ _ _ a TMAP_A_g_last_counter);
              unfold TW.SZ_g_last_counter in *; lia ]
    |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* run D: the two stores into G and the last branch, 0x832a4 .. 0x832c8 *)
(* ------------------------------------------------------------------ *)

Lemma iod_runD : forall STK sp0 FP ly Sa (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem5 md5 k
    (regs5 : bvmap 5 word) (sp send graw kaz : Z) (Bx : list byte) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
    ly2 S2 W2 mem5 md5 k ->
  YK11.getr regs5 2 = w64 sp -> YK11.getr regs5 20 = w64 SHADOW_OFF -> YK11.getr regs5 23 = w64 IOD_S7 ->
  YK11.getr regs5 22 = w64 kaz -> 0 <= kaz <= 1 ->
  2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= send < 2 ^ 32 -> 0 <= graw < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) (sp + 40) 4 send ->
  YI04.val_mem segs (mrestrict (w_H W2) mem5) TA_g_raw 4 graw ->
  tw_at TMAP_A (aview segs (w_H W2) mem5) Bx -> TW.g_raw Bx = bv_swrap 32 graw ->
  (forall mem7 md7 (regs7 : bvmap 5 word) (pc : Z),
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sa W0 mem0 md0 own
       ly2 S2 W2 mem7 md7 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ IOD_WR a ->
        aview segs (w_H W2) mem7 a = aview segs (w_H W2) mem5 a) ->
     (forall a, apresent (w_H W2) mem5 a -> apresent (w_H W2) mem7 a) ->
     (forall r, In r IOD_KEEPD -> YK11.getr regs7 r = YK11.getr regs5 r) ->
     YK11.getr regs7 20 = w64 TA_M ->
     tw_at TMAP_A (aview segs (w_H W2) mem7)
       (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send) ->
     (pc = IOS_KA /\ TC.truth (TW.g_raw Bx) = false /\ kaz = 1 \/
      pc = IOS_SENT /\ YK11.getr regs7 10 = w64 (TW.g_raw Bx) /\
        (TC.truth (TW.g_raw Bx) = false -> kaz = 0)) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + pc) regs7 mem7 md7) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_CLF_RET) regs5 mem5 md5) Q.
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own ly2 S2 W2 mem5 md5 k regs5 sp send graw kaz Bx Q
  HL HJ R2 R20 R23 R22 Hkz Hs1 Hs2 Hs16 Hsd Hgr V40 V0 HTW HGR HK.
pose proof HL as (HCELLS & HIOC & LAWS & MTL & HGX & HGE & HAI0 & HCSFc & HAF & HLC & HCIR & HSW & HIN2 & HLF
  & HKD & HCLS & HLD & HAI1).
set (ED := iod_ED regs5 send graw) in *.
assert (E32 : ew ED 32 = Z_to_bv 64 send)
  by (unfold ED, iod_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew ED 33 = Z_to_bv 64 graw)
  by (unfold ED, iod_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
assert (E22 : ew ED 22 = YK11.getr regs5 22) by (unfold ED, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
assert (UM : bv_unsigned (ew ED (A_OBJ 8)) = TA_M).
{ unfold ED, iod_ED. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (V : VAL (A_OBJ 8) = TA_M) by (vm_compute; reflexivity). rewrite V.
  apply unsigned_lit_small. unfold TA_M; lia. }
assert (U59 : bv_unsigned (ew ED (A_HI 59)) = TA_g_last_counter + 384).
{ unfold ED, iod_ED. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  assert (V : VAL (A_HI 59) = TA_g_last_counter + 384) by (vm_compute; reflexivity). rewrite V.
  apply unsigned_lit_small. unfold TA_g_last_counter; lia. }
assert (U2 : bv_unsigned (ew ED 2) = sp).
{ assert (E2 : ew ED 2 = YK11.getr regs5 2) by (unfold ED, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
  rewrite E2, R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U23 : bv_unsigned (ew ED 23) = TA_g_raw + 176).
{ assert (E23 : ew ED 23 = YK11.getr regs5 23) by (unfold ED, iod_ED; apply ew_Eimg_Ereg_nat; reflexivity).
  rewrite E23, R23. unfold w64, IOD_S7. apply unsigned_lit_small. unfold TA_g_raw; lia. }
destruct (iod_entryD W2 mem5 regs5 sp send graw R2 R20 R23 Hs1 Hs2 Hs16 Hsd Hgr V40 V0) as [HS SHOK].
fold ED in HS, SHOK.
assert (UMn : bv_unsigned (ew ED 249%nat) = TA_M) by exact UM.
assert (U59n : bv_unsigned (ew ED 459%nat) = TA_g_last_counter + 384) by exact U59.
assert (HEI : img_env VAL A_LIM ED) by (unfold ED, iod_ED; apply Eimg_env).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + IOS_CLF_RET)) mem5 (YK11.seg_rom segs)) md5)
    Qx) end.
(* 0x832a4 .. 0x832b4: a1 = f.send, a0 = g_raw, s4 = M, the store at M + 84 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x2054.
{ iod_awrD UMn U59n. }
set (md1 := with_vm_backing (m_vm_lazy md5) mat md5) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 84 <= a < TA_M + 88) ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem5 a).
{ apply (kept_of_frame _ _ _ _ _ (fun a => TA_M + 84 <= a < TA_M + 88) HFr).
  intros b wlo whi x Hin Hx. iod_win Hin Hx ltac:(rewrite ?U2, ?U23, ?UMn in Hx; unfold TA_M in *; lia). }
assert (G1 : forall a, apresent (w_H W2) mem5 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the word the first store left at M + 84 *)
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let r0 := eval vm_compute in (nth 2 (ss_mem ssx) iod_hostD) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh m) 2 r0 HS ltac:(vm_compute; reflexivity)) as RG1 end.
cbn [ms_mem restrict] in RG1.
assert (DS : sv_denot ED (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (bv_swrap 32 send))
  by exact (iod_sext32_den ED 32 send E32 ltac:(lia)).
assert (DG : sv_denot ED (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 graw))
  by exact (iod_sext32_den ED 33 graw E33 ltac:(lia)).
pose proof (iak_region_rd4 ED (w_H W2) (ms_mem ms1) 249%nat 84 88 84 88 84 (SExt true 32 (SOff 32 0))
  (bv_swrap 32 send) TA_M RG1 UMn DS) as V1.
(* the world after the first store *)
assert (HTW1 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms1)) (TW.set_M_host_counter Bx send)).
{ change (TW.set_M_host_counter Bx send) with (TW.upd Bx (TW.OFF_M + 84) (TW.put 4 send)).
  apply (tw_write TMAP_A (aview segs (w_H W2) mem5) _ Bx TW.OFF_M TA_M TW.SZ_M 84 4 send
    TMAP_A_ok HTW TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn; lia)).
  - intros j Hj. rewrite (V1 j Hj). f_equal. apply (iod_le_byte_swrap 32 4 j send). reflexivity.
  - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply K1; [lia | cbn in Hn; lia]. }
(* the second store's region, added now so the first store's world step stands *)
assert (RGL : region_ok segs ED (mrestrict (w_H W2) (ms_mem ms1)) iod_lastD).
{ unfold iod_lastD, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U59. split; [unfold TA_g_last_counter; lia|]. split; [unfold TA_g_last_counter; lia|].
  split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw).
  apply (ios_inG_row _ _ _ _ TMAP_A_g_last_counter). unfold TW.SZ_g_last_counter. lia. }
assert (DJL : all_disjoint ED iod_lastD [iod_frameD; iod_rawD]).
{ unfold iod_lastD, iod_frameD, iod_rawD. cbn [all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23, U59.
  repeat split; try exact I; unfold TA_M, TA_g_raw, TA_g_last_counter; lia. }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let rs := eval vm_compute in (firstn 2 (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ex ssx (restrict Hh m) rs HS
    ltac:(vm_compute; apply submem_keep; [apply subregion_refl|];
          apply submem_keep; [apply subregion_refl|]; constructor)
    ltac:(vm_compute; reflexivity)) as HSd end.
lazymatch type of HSd with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  pose proof (st_ok_pi_add_region Ex ssx (restrict Hh m) iod_lastD HSd ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_mem restrict]; exact RGL) ltac:(exact DJL)) as HSL end.
clear HS HSd RG1. iod_rw HSL.
(* 0x832b8 .. 0x832c8: the store at g_last_counter, then the branch *)
paj_run_to_tok RUNTO HSL HJ SHOK YC4b.Bspan 0x2064.
{ iod_awrD UMn U59n. }
set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
rename ms into ms2.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_last_counter <= a < TA_g_last_counter + 4) ->
  aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) (ms_mem ms1) a).
{ apply (kept_of_frame _ _ _ _ _ (fun a => TA_g_last_counter <= a < TA_g_last_counter + 4) HFr).
  intros b wlo whi x Hin Hx.
  iod_win Hin Hx ltac:(rewrite ?U2, ?U23, ?UMn, ?U59n in Hx; unfold TA_M, TA_g_last_counter in *; lia). }
assert (G2 : forall a, apresent (w_H W2) (ms_mem ms1) a -> apresent (w_H W2) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HSL with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) iod_lastD) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh m) 0 r0 HSL ltac:(vm_compute; reflexivity)) as RG2 end.
cbn [ms_mem restrict] in RG2.
pose proof (iak_region_rd4 ED (w_H W2) (ms_mem ms2) 459%nat (-384) (-380) (-384) (-380) (-384)
  (SExt true 32 (SOff 32 0)) (bv_swrap 32 send) (TA_g_last_counter + 384) RG2 U59n DS) as V2.
assert (HTW2 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms2))
  (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send)).
{ change (TW.set_g_last_counter (TW.set_M_host_counter Bx send) send)
    with (TW.upd (TW.set_M_host_counter Bx send) (TW.OFF_g_last_counter + 0) (TW.put 4 send)).
  apply (tw_write TMAP_A (aview segs (w_H W2) (ms_mem ms1)) _ (TW.set_M_host_counter Bx send)
    TW.OFF_g_last_counter TA_g_last_counter TW.SZ_g_last_counter 0 4 send
    TMAP_A_ok HTW1 TMAP_A_g_last_counter ltac:(lia) ltac:(unfold TW.SZ_g_last_counter; cbn; lia)).
  - intros j Hj.
    replace (TA_g_last_counter + 0 + Z.of_nat j) with (TA_g_last_counter + 384 + -384 + Z.of_nat j) by lia.
    rewrite (V2 j Hj). f_equal. apply (iod_le_byte_swrap 32 4 j send). reflexivity.
  - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply K2; [lia | cbn in Hn; lia]. }
assert (Hgs : - 2 ^ 31 <= TW.g_raw Bx < 2 ^ 31)
  by (pose proof (TWL.s32_range Bx TW.OFF_g_raw) as Hr; unfold TW.g_raw; lia).
(* both regions of G are done with; keep only the two read-only ones, so the exits' runs touch no memory *)
lazymatch type of HSL with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?m) =>
  let rs := eval vm_compute in (skipn 1 (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ex ssx (restrict Hh m) rs HSL
    ltac:(vm_compute; apply submem_drop; apply submem_refl)
    ltac:(vm_compute; reflexivity)) as HSr end.
clear HSL RG2. iod_rw HSr.
psrr_branch_tok RUN BR HSr SHOK YC4b.Bspan.
all: rewrite (iod_cond_den ED 33 22 (TW.g_raw Bx) kaz ltac:(rewrite HGR; exact DG) Hgs
  ltac:(rewrite E22, R22; reflexivity) Hkz) in Hc.
all: cbn [branch_taken sv_denot] in Hc.
all: rewrite (iod_eqb (if (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool then 1 else 0) 0
  ltac:(destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool; lia) ltac:(lia)) in Hc.
- (* the condition is 0: to 0x83304, the check_latest_sent case *)
  apply Z.eqb_eq in Hc.
  destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool eqn:Hcc; [discriminate Hc|].
  paj_run_to_tok RUNTO HSr HJ SHOK YC4b.Bspan 0x20a0.
  { iod_awrA. }
  rename ms into ms3. assert (Em3 : ms_mem ms3 = ms_mem ms2).
  { eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  iod_fin HSr HJ Em3 HK IOS_SENT K1 K2 G1 G2 HTW2.
  + exact (regs_kept_of_st_ok_pi _ _ _ _ _ IOD_KEEPD HSr ltac:(unfold ED, iod_ED; apply iak_agree)
      ltac:(vm_compute; reflexivity)).
  + iod_rv HSr. cbn [sv_denot]. rewrite UMn, Z.add_0_r. reflexivity.
  + right. split; [reflexivity|]. split.
    * iod_rv HSr. rewrite HGR. exact DG.
    * intros Ht. rewrite Ht in Hcc. cbn [negb] in Hcc.
      destruct (Z.eqb_spec kaz 1) as [Hk1|Hk0]; [cbn [andb] in Hcc; discriminate Hcc | lia].
- (* the condition is 1: on to 0x832cc, the keepalive case *)
  apply Z.eqb_neq in Hc.
  destruct (negb (TC.truth (TW.g_raw Bx)) && (kaz =? 1))%bool eqn:Hcc; [|exfalso; apply Hc; reflexivity].
  apply andb_prop in Hcc as (Hc1 & Hc2). apply negb_true_iff in Hc1. apply Z.eqb_eq in Hc2.
  paj_run_to_tok RUNTO HSr HJ SHOK YC4b.Bspan 0x2068.
  { iod_awrA. }
  rename ms into ms3. assert (Em3 : ms_mem ms3 = ms_mem ms2).
  { eapply frame_of_read_only; [| exact HF]. vm_compute. reflexivity. }
  clear HF HFr HG.
  iod_fin HSr HJ Em3 HK IOS_KA K1 K2 G1 G2 HTW2.
  + exact (regs_kept_of_st_ok_pi _ _ _ _ _ IOD_KEEPD HSr ltac:(unfold ED, iod_ED; apply iak_agree)
      ltac:(vm_compute; reflexivity)).
  + iod_rv HSr. cbn [sv_denot]. rewrite UMn, Z.add_0_r. reflexivity.
  + left. split; [reflexivity | split; [exact Hc1 | exact Hc2]].

Qed.

End dataw.
