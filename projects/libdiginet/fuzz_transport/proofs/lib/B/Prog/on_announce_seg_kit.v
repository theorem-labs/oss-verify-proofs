(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v, with its module paths and module names changed; 976 of its 1083 lines of code are new or changed and 742 lines of the source are left out. *)
(* on_announce_seg_kit: the shared lemmas of the pieces of on_announce's image-B G-form walk (the cut contract
   lib/B/Prog/OnannCutB.v, the statement lib/B/Prog/on_announce_cg.v; fuzz_transport.asan-ubsan 0x87cc8 .. 0x8858c).
   It proves no piece; each piece file on_announce_seg_<piece>.v Requires it. Image B's twin of
   lib/A/Prog/on_announce_seg_kit.v (same names, image B's G, world table, image and class-3 frame of 512 bytes).
   Lemmas of note:
   - onann_wr_G / onann_wr_lowmem / onann_wr_nframe: the written range onann_wr lies in G, below kLowMemEnd, off the
     frames and their shadow; the inclusions of the callees' written ranges (onann_wr_dntc, onann_wr_fntc,
     onann_wr_slost, onann_wr_wake, onann_wr_mo, and the code's own g_s stores onann_wr_rxign .. onann_wr_e1nu) and
     of their TF apart clauses (onann_apart_ntc, onann_apart_sstate, onann_apart_wake, onann_apart_mo);
   - the model: onann_dn_world / onann_fg_world (an N_DESK / N_FOREIGN call_notify sets GOT.desk / GOT.foreign
     only), onann_pv_res (personality_from_name's result is onann_pv timg_B b), onann_ign_false (an accepted frame
     has cmd 0xe0 or 0xe1 and a body of 33 bytes or more), onann_same and its cases (the reads every piece needs are
     kept by the stores of :192-193, :201, :213-214, :216 and the two notices), onann_ri_upd / onann_gfn_upd, the
     world fields at their numeral offsets (the onann_rd_ and onann_st_ lemmas);
   - onann_cur_ar: from onann_fix and onann_cur, AR at the entry and at the cut state, the layout facts (stack bounds,
     frame_addr / flag_addr of the cut layout are the entry's), the own class-3 frame and its flag byte;
   - onann_src_kept / onann_tf_call / onann_rom_call: a range placed by trans_src_ok at the entry and outside G is
     placed at the cut state (own frame on top of the entry's frames) with its bytes kept (SlostNtcKit.v sn_tframe,
     generalised); trans_tframe_at at a call state; trans_rom_view_rd at the cut memory; and their forms read
     directly off onann_fix and onann_cur (onann_src_cur, onann_tf_cur, onann_rom_cur);
   - onann_f30: f's 64 bytes at the cut memory are the entry's (the byte of f + 30 is fr_cmd b, its shadow byte is 0,
     the 16 bytes at f + 32 are the body pointer and length diginet_announce_parse reads), and the frame bytes at buf
     are placed at the cut state. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The world: fields at their numeral offsets, what the stores keep *)
(* ------------------------------------------------------------------ *)

(* The reads and stores of g_s and GOT the pieces make, at their numeral offsets (no accessor is left for the kernel
   to unfold). *)
Lemma onann_rd_state : forall X, TW.S_state X = TW.s32_at X (TW.OFF_g_s + 112).
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_notify : forall X, TW.S_notify X = TW.u_at X (TW.OFF_g_s + 96) 8.
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_notify_ctx : forall X, TW.S_notify_ctx X = TW.u_at X (TW.OFF_g_s + 104) 8.
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_auto_wake : forall X, TW.S_cfg_auto_wake X = TW.s32_at X (TW.OFF_g_s + 16).
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_foreign : forall X, TW.S_foreign X = TW.s32_at X (TW.OFF_g_s + 136).
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_rxign : forall X, TW.S_stats_rx_ignored X = TW.u_at X (TW.OFF_g_s + 18184) 8.
Proof. intros X. reflexivity. Qed.
Lemma onann_rd_host_mac : forall X, TW.S_cfg_host_mac X = TW.sub X (TW.OFF_g_s + 0) 6.
Proof. intros X. reflexivity. Qed.
Lemma onann_st_rxign : forall X v, TW.set_S_stats_rx_ignored X v = TW.upd X (TW.OFF_g_s + 18184) (TW.put 8 v).
Proof. intros X v. reflexivity. Qed.
Lemma onann_st_pers : forall X v, TW.set_S_personality X v = TW.upd X (TW.OFF_g_s + 128) (TW.put 8 v).
Proof. intros X v. reflexivity. Qed.
Lemma onann_st_foreign : forall X v, TW.set_S_foreign X v = TW.upd X (TW.OFF_g_s + 136) (TW.put 4 v).
Proof. intros X v. reflexivity. Qed.
Lemma onann_st_e1nu : forall X v, TW.set_S_e1_named_us X v = TW.upd X (TW.OFF_g_s + 140) (TW.put 4 v).
Proof. intros X v. reflexivity. Qed.
Lemma onann_st_desk : forall X v, TW.set_GOT_desk X v = TW.upd X (TW.OFF_GOT + 208) (TW.put 4 v).
Proof. intros X v. reflexivity. Qed.
Lemma onann_st_gforeign : forall X v, TW.set_GOT_foreign X v = TW.upd X (TW.OFF_GOT + 212) (TW.put 4 v).
Proof. intros X v. reflexivity. Qed.

(* What the stores of this walk keep of a world X: its length and the reads the pieces and the callees' premises
   make (g_s's state, notify, notify_ctx, cfg.auto_wake, cfg.host_mac; GOT.n; g_fail_next; the run invariants). *)
Definition onann_same (X Y : list byte) : Prop :=
  length Y = length X /\ TW.S_state Y = TW.S_state X /\ TW.S_notify Y = TW.S_notify X /\
  TW.S_notify_ctx Y = TW.S_notify_ctx X /\ TW.S_cfg_auto_wake Y = TW.S_cfg_auto_wake X /\
  TW.S_cfg_host_mac Y = TW.S_cfg_host_mac X /\ TW.GOT_n Y = TW.GOT_n X /\
  TW.g_fail_next Y = TW.g_fail_next X /\ (onann_ri Y <-> onann_ri X).

(* A read of X outside a store's bytes is X's. *)
Lemma onann_upd_rd : forall X k (n : nat) v k' m, length X = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') ->
  TW.u_at (TW.upd X k (TW.put n v)) k' m = TW.u_at X k' m.
Proof.
  intros X k n v k' m L Hk Hn Hk' Hd.
  apply rd_upd_W; [exact L | exact Hk | rewrite TWL.length_put; exact Hn | exact Hk' | rewrite TWL.length_put; exact Hd].
Qed.
Lemma onann_upd_sub : forall X k (n : nat) v k' m, length X = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') ->
  TW.sub (TW.upd X k (TW.put n v)) k' m = TW.sub X k' m.
Proof.
  intros X k n v k' m L Hk Hn Hk' Hd.
  apply TWL.sub_upd_out; [exact Hk | exact Hk' | rewrite TWL.length_put; exact Hd |].
  rewrite TWL.length_put, L, Z2Nat.id by (unfold TW.W_LEN; lia). exact Hn.
Qed.
Lemma onann_upd_len : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  0 <= k -> k + Z.of_nat n <= TW.W_LEN -> length (TW.upd X k (TW.put n v)) = Z.to_nat TW.W_LEN.
Proof.
  intros X k n v L Hk Hn. rewrite TWL.length_upd_put; [exact L | exact Hk |].
  rewrite L, Z2Nat.id by (unfold TW.W_LEN; lia). exact Hn.
Qed.

Local Ltac onann_offs :=
  unfold TW.A_M_fly_on, TW.A_M_fly_len, TW.OFF_M, TW.OFF_g_ncmd, TW.A_Cmd_st, TW.A_Cmd_len, TW.OFF_g_cmd,
    TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.SZ_GOT, TW.W_LEN, TW.A_S_state, TW.A_S_notify, TW.A_S_notify_ctx,
    TW.A_S_cfg_auto_wake, TW.A_S_cfg_host_mac, TW.A_GOT_n, TW.OFF_g_fail_next, TC.CMDS_MAX in *.

(* A store inside g_s's payload, or inside GOT's desk and foreign words, keeps the run invariants: the fly fields of
   M lie below g_s, g_ncmd between g_cmd and GOT, and the command fields Cmd_st s / Cmd_len s of an index
   s < g_ncmd <= CMDS_MAX lie in g_cmd, after g_s and before GOT. *)
Lemma onann_ri_upd2 : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s <= k /\ k + Z.of_nat n <= TW.OFF_g_s + TW.SZ_g_s \/
   TW.OFF_GOT + 208 <= k /\ k + Z.of_nat n <= TW.OFF_GOT + 216) ->
  (onann_ri (TW.upd X k (TW.put n v)) <-> onann_ri X).
Proof.
  intros X k n v L Hr.
  assert (Hk : 0 <= k /\ k + Z.of_nat n <= TW.W_LEN) by (onann_offs; lia).
  destruct Hk as [Hk Hn].
  set (Y := TW.upd X k (TW.put n v)).
  assert (R : forall k' m, 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') -> TW.u_at Y k' m = TW.u_at X k' m)
    by (intros k' m H1 H2; exact (onann_upd_rd X k n v k' m L Hk Hn H1 H2)).
  assert (E1 : TW.M_fly_on Y = TW.M_fly_on X)
    by (unfold TW.M_fly_on, TW.s32_at; rewrite R; [reflexivity | onann_offs; lia | onann_offs; lia]).
  assert (E2 : TW.M_fly_len Y = TW.M_fly_len X)
    by (unfold TW.M_fly_len; rewrite R; [reflexivity | onann_offs; lia | onann_offs; lia]).
  assert (E3 : TW.g_ncmd Y = TW.g_ncmd X)
    by (unfold TW.g_ncmd; rewrite R; [reflexivity | onann_offs; lia | onann_offs; lia]).
  assert (E4 : forall s, 0 <= s < TC.CMDS_MAX -> TW.Cmd_st Y s = TW.Cmd_st X s)
    by (intros s Hs; unfold TW.Cmd_st, TW.s32_at; rewrite R; [reflexivity | onann_offs; lia | onann_offs; lia]).
  assert (E5 : forall s, 0 <= s < TC.CMDS_MAX -> TW.Cmd_len Y s = TW.Cmd_len X s)
    by (intros s Hs; unfold TW.Cmd_len; rewrite R; [reflexivity | onann_offs; lia | onann_offs; lia]).
  unfold onann_ri. rewrite E1, E2, E3. clear Hr.
  split; intros (P1 & P2 & P3); (split; [exact P1 | split; [| exact P3]]); intros s Hs Hst.
  - rewrite <- E5 by lia. apply P2; [exact Hs | rewrite E4 by lia; exact Hst].
  - rewrite E5 by lia. apply P2; [exact Hs | rewrite <- E4 by lia; exact Hst].
Qed.

(* The stores of this walk outside g_s's first 120 bytes: inside g_s, or GOT's desk and foreign words. *)
Lemma onann_same_upd : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s + 120 <= k /\ k + Z.of_nat n <= TW.OFF_g_s + TW.SZ_g_s \/
   TW.OFF_GOT + 208 <= k /\ k + Z.of_nat n <= TW.OFF_GOT + 216) ->
  onann_same X (TW.upd X k (TW.put n v)).
Proof.
  intros X k n v L Hr.
  assert (Hk : 0 <= k /\ k + Z.of_nat n <= TW.W_LEN)
    by (destruct Hr as [[H1 H2]|[H1 H2]]; onann_offs; lia).
  destruct Hk as [Hk Hn].
  (* the reads of this walk lie in g_s's first 120 bytes, in GOT.n, or at g_fail_next: each apart from the store *)
  assert (Dlo : forall A (m : nat), 0 <= A -> A + Z.of_nat m <= TW.OFF_g_s + 120 ->
                A + Z.of_nat m <= k \/ k + Z.of_nat n <= A)
    by (intros A m HA HB; left; destruct Hr as [[H1 H2]|[H1 H2]]; onann_offs; lia).
  assert (Dhi : forall A (m : nat), TW.OFF_g_cmd <= A -> A + Z.of_nat m <= TW.OFF_GOT + 4 ->
                A + Z.of_nat m <= k \/ k + Z.of_nat n <= A)
    by (intros A m HA HB; destruct Hr as [[H1 H2]|[H1 H2]]; [right | left]; onann_offs; lia).
  assert (R : forall k' m, 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') ->
    TW.u_at (TW.upd X k (TW.put n v)) k' m = TW.u_at X k' m)
    by (intros k' m H1 H2; exact (onann_upd_rd X k n v k' m L Hk Hn H1 H2)).
  unfold onann_same.
  split; [rewrite (onann_upd_len X k n v L Hk Hn), L; reflexivity|].
  split; [unfold TW.S_state, TW.s32_at;
          rewrite (R TW.A_S_state 4%nat ltac:(wnum) (Dlo TW.A_S_state 4%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  split; [unfold TW.S_notify;
          rewrite (R TW.A_S_notify 8%nat ltac:(wnum) (Dlo TW.A_S_notify 8%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  split; [unfold TW.S_notify_ctx;
          rewrite (R TW.A_S_notify_ctx 8%nat ltac:(wnum) (Dlo TW.A_S_notify_ctx 8%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  split; [unfold TW.S_cfg_auto_wake, TW.s32_at;
          rewrite (R TW.A_S_cfg_auto_wake 4%nat ltac:(wnum)
                     (Dlo TW.A_S_cfg_auto_wake 4%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  split; [unfold TW.S_cfg_host_mac;
          exact (onann_upd_sub X k n v TW.A_S_cfg_host_mac 6%nat L Hk Hn ltac:(wnum)
                   (Dlo TW.A_S_cfg_host_mac 6%nat ltac:(wnum) ltac:(wnum)))|].
  split; [unfold TW.GOT_n, TW.s32_at;
          rewrite (R TW.A_GOT_n 4%nat ltac:(wnum) (Dhi TW.A_GOT_n 4%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  split; [unfold TW.g_fail_next;
          rewrite (R TW.OFF_g_fail_next 1%nat ltac:(wnum)
                     (Dhi TW.OFF_g_fail_next 1%nat ltac:(wnum) ltac:(wnum)));
          reflexivity|].
  clear R Dlo Dhi.
  apply onann_ri_upd2; [exact L|].
  destruct Hr as [[H1 H2]|[H1 H2]]; [left | right]; split; onann_offs; lia.
Qed.

Lemma onann_same_refl : forall X, onann_same X X.
Proof.
  intros X. unfold onann_same.
  exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
    (conj eq_refl (conj (fun H : onann_ri X => H) (fun H : onann_ri X => H)))))))))).
Qed.
Lemma onann_same_trans : forall X Y X3, onann_same X Y -> onann_same Y X3 -> onann_same X X3.
Proof.
  intros X Y X3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  exact (conj (eq_trans B1 A1) (conj (eq_trans B2 A2) (conj (eq_trans B3 A3) (conj (eq_trans B4 A4)
    (conj (eq_trans B5 A5) (conj (eq_trans B6 A6) (conj (eq_trans B7 A7) (conj (eq_trans B8 A8)
    (iff_trans B9 A9))))))))).
Qed.
(* :192-193: the personality store. *)
Lemma onann_same_w1 : forall (I : TI.timg) (Bw b : list byte), length Bw = Z.to_nat TW.W_LEN ->
  onann_same Bw (onann_w1 I Bw b).
Proof.
  intros I Bw b L. unfold onann_w1. destruct (TN.diginet_personality_from_name (onann_name b));
    [| exact (onann_same_refl Bw)].
  unfold TW.set_S_personality. apply onann_same_upd; [exact L|]. left. unfold TW.A_S_personality. onann_offs. lia.
Qed.
(* The desk notice's store of GOT.desk, the foreign notice's of GOT.foreign. *)
Lemma onann_same_desk : forall X d, length X = Z.to_nat TW.W_LEN -> onann_same X (TW.set_GOT_desk X d).
Proof.
  intros X d L. unfold TW.set_GOT_desk. apply onann_same_upd; [exact L|]. right. unfold TW.A_GOT_desk. onann_offs.
  lia.
Qed.
Lemma onann_same_gforeign : forall X d, length X = Z.to_nat TW.W_LEN -> onann_same X (TW.set_GOT_foreign X d).
Proof.
  intros X d L. unfold TW.set_GOT_foreign. apply onann_same_upd; [exact L|]. right. unfold TW.A_GOT_foreign.
  onann_offs. lia.
Qed.
(* :201 / :213 / :216: g_s.foreign; :214: g_s.e1_named_us. *)
Lemma onann_same_foreign : forall X v, length X = Z.to_nat TW.W_LEN -> onann_same X (TW.set_S_foreign X v).
Proof.
  intros X v L. unfold TW.set_S_foreign. apply onann_same_upd; [exact L|]. left. unfold TW.A_S_foreign. onann_offs.
  lia.
Qed.
Lemma onann_same_e1nu : forall X v, length X = Z.to_nat TW.W_LEN -> onann_same X (TW.set_S_e1_named_us X v).
Proof.
  intros X v L. unfold TW.set_S_e1_named_us. apply onann_same_upd; [exact L|]. left. unfold TW.A_S_e1_named_us.
  onann_offs. lia.
Qed.

(* A store inside g_s's payload keeps the run invariants (onann_ri_upd2's first case); a store inside g_s or GOT
   keeps g_fail_next. *)
Lemma onann_ri_upd : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  TW.OFF_g_s <= k -> k + Z.of_nat n <= TW.OFF_g_s + TW.SZ_g_s ->
  (onann_ri (TW.upd X k (TW.put n v)) <-> onann_ri X).
Proof. intros X k n v L H1 H2. apply onann_ri_upd2; [exact L | left; split; [exact H1 | exact H2]]. Qed.
Lemma onann_gfn_upd : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  (TW.OFF_g_s <= k /\ k + Z.of_nat n <= TW.OFF_g_s + TW.SZ_g_s \/
   TW.OFF_GOT <= k /\ k + Z.of_nat n <= TW.OFF_GOT + TW.SZ_GOT) ->
  TW.g_fail_next (TW.upd X k (TW.put n v)) = TW.g_fail_next X.
Proof.
  intros X k n v L Hr.
  assert (Hk : 0 <= k /\ k + Z.of_nat n <= TW.W_LEN) by (onann_offs; lia).
  destruct Hk as [Hk Hn].
  unfold TW.g_fail_next. apply (onann_upd_rd X k n v); [exact L | exact Hk | exact Hn | onann_offs; lia |].
  onann_offs. lia.
Qed.

(* The worlds' lengths. *)
Lemma onann_w1_len : forall (I : TI.timg) (Bw b : list byte), length Bw = Z.to_nat TW.W_LEN ->
  length (onann_w1 I Bw b) = Z.to_nat TW.W_LEN.
Proof. intros I Bw b L. pose proof (onann_same_w1 I Bw b L) as (H & _). rewrite H. exact L. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* A frame the parse accepts has cmd 0xe0 or 0xe1 and a body of 33 bytes or more. *)
Lemma onann_ign_false : forall b, onann_ign b = false ->
  (DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE \/ DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE_SESSION) /\
  33 <= DSpec.fr_body_len b.
Proof.
  intros b H. unfold onann_ign, DSpec.ann_code, DSpec.ann_cmd, DLib.DIGINET_OK in H.
  destruct (Z.eqb_spec (DSpec.fr_cmd b) 0xe0) as [E0|E0]; cbn [orb] in H.
  - split; [left; exact E0|].
    destruct (Z.ltb_spec (DSpec.fr_body_len b) 33) as [Hb|Hb]; cbn [negb] in H; [discriminate H | lia].
  - destruct (Z.eqb_spec (DSpec.fr_cmd b) 0xe1) as [E1|E1]; cbn [orb negb] in H; [|discriminate H].
    split; [right; exact E1|].
    destruct (Z.ltb_spec (DSpec.fr_body_len b) 33) as [Hb|Hb]; cbn [negb] in H; [discriminate H | lia].
Qed.

(* The bytes copy_strz keeps hold no NUL, so cstring stops at the NUL ann_field writes (the text of
   lib/Prog/T/on_announce_lem.v oa_cstring_nz, oa_z_list_eqb, oa_from_name_z). *)
Lemma onann_cstring_nz : forall n (l : list byte) rest,
  CC.cstring (CC.zb (firstn (DSpec.nz_run (firstn n l)) l ++ DSpec.b8 0 :: rest)) =
  CC.zb (firstn (DSpec.nz_run (firstn n l)) l).
Proof.
  induction n as [|n IH]; intros [|x l] rest; try reflexivity.
  cbn [firstn DSpec.nz_run].
  destruct (Z.eqb_spec (DSpec.bz x) 0) as [E|E]; [reflexivity|].
  cbn [firstn app]. unfold CC.zb in *. cbn [map CC.cstring].
  unfold DSpec.bz in E. apply Z.eqb_neq in E. rewrite E. f_equal. apply IH.
Qed.

Lemma onann_z_list_eqb : forall x y, TN.z_list_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|c y] H; cbn in H; try discriminate H; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst c. f_equal. apply IH. exact H2.
Qed.

Lemma onann_from_name_z : forall z,
  (if list_eq_dec Z.eq_dec z CC.NAME_C24 then TRANS_PERS
   else if list_eq_dec Z.eq_dec z CC.NAME_PC then TRANS_PERS + 24 else 0) =
  match TN.personality_name_find DLib.personalities 0 z with Some i => TRANS_PERS + 24 * i | None => 0 end.
Proof.
  intros z.
  destruct (list_eq_dec Z.eq_dec z CC.NAME_C24) as [E1|E1]; [subst z; reflexivity|].
  destruct (list_eq_dec Z.eq_dec z CC.NAME_PC) as [E2|E2]; [subst z; reflexivity|].
  unfold DLib.personalities. cbn [TN.personality_name_find DLib.dp_announce_name].
  repeat match goal with |- context [TN.z_list_eqb z ?l] =>
    let H := fresh "H" in destruct (TN.z_list_eqb z l) eqn:H;
    [apply onann_z_list_eqb in H; subst z; exfalso; first [apply E1; reflexivity | apply E2; reflexivity] |]
  end.
  reflexivity.
Qed.

(* personality_from_name's result on a.name (the 10 bytes at a + 10 the parse left: TSess.v ann_field of the body
   from 24) is the personality pointer the model computes (onann_pv). *)
Lemma onann_pv_res : forall b, trans_pfrom_res (TSS.ann_field (skipn 24 (DSpec.fr_body b))) = onann_pv timg_B b.
Proof.
  intros b. unfold trans_pfrom_res, onann_pv, onann_name, TSS.ann_field, TN.diginet_personality_from_name.
  change (DSpec.copy_len 10 9 (skipn 24 (DSpec.fr_body b)))
    with (DSpec.nz_run (firstn 9 (skipn 24 (DSpec.fr_body b)))).
  rewrite (onann_cstring_nz 9 (skipn 24 (DSpec.fr_body b)) []).
  change (TI.ti_personalities timg_B) with TRANS_PERS.
  exact (onann_from_name_z (CC.zb (firstn (DSpec.nz_run (firstn 9 (skipn 24 (DSpec.fr_body b))))
    (skipn 24 (DSpec.fr_body b))))).
Qed.

(* check_state_desk returns its world. *)
Lemma onann_desk_same : forall (I : TI.timg) (F : option TI.tframe) X (n : TI.ntc) Y u,
  TC.check_state_desk_m I F X n = Some (Y, u) -> Y = X.
Proof.
  intros I F X n Y u. destruct u. unfold TC.check_state_desk_m.
  repeat (cbv beta iota zeta; match goal with |- context [match ?c with _ => _ end] => destruct c end);
    intros H; cbv beta iota zeta in H; try discriminate H; symmetry; exact (onann_some_inv _ _ H).
Qed.
(* An N_DESK notice changes GOT.desk only; an N_FOREIGN notice GOT.foreign only. *)
Lemma onann_notice_desk : forall (I : TI.timg) (F : option TI.tframe) Bx (n : TI.ntc) B2,
  TI.n_kind n = TC.N_DESK -> TC.notice_m I F Bx n = Some (B2, tt) -> exists d, B2 = TW.set_GOT_desk Bx d.
Proof.
  intros I F Bx n B2 K H. unfold TC.notice_m in H. rewrite K in H.
  cbn [Z.eqb TC.N_STATE TC.N_ACKED TC.N_ACK_LOST TC.N_DESK Pos.eqb] in H.
  destruct (TC.int_inc (TW.GOT_desk Bx)) as [d|]; [|discriminate H].
  exists d. exact (onann_desk_same I F (TW.set_GOT_desk Bx d) n B2 tt H).
Qed.
Lemma onann_notice_fg : forall (I : TI.timg) (F : option TI.tframe) Bx (n : TI.ntc) B3,
  TI.n_kind n = TC.N_FOREIGN -> TC.notice_m I F Bx n = Some (B3, tt) -> exists d, B3 = TW.set_GOT_foreign Bx d.
Proof.
  intros I F Bx n B3 K H. unfold TC.notice_m in H. rewrite K in H.
  cbn [Z.eqb TC.N_STATE TC.N_ACKED TC.N_ACK_LOST TC.N_DESK TC.N_DATA TC.N_FOREIGN Pos.eqb] in H.
  destruct (TC.int_inc (TW.GOT_foreign Bx)) as [d|]; [|discriminate H].
  cbv beta iota in H. exists d. symmetry. exact (onann_some_inv _ _ H).
Qed.
(* The desk notice's call_notify returns set_GOT_desk of its world. *)
Lemma onann_dn_world : forall (Fr : option TI.tframe) (Bx b B2 : list byte),
  TSS.call_notify timg_B Fr Bx (onann_dntc timg_B Bx b) = Some (B2, tt) -> exists d, B2 = TW.set_GOT_desk Bx d.
Proof.
  intros Fr Bx b B2 H. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bx =? TI.ti_notice timg_B); [|discriminate H].
  exact (onann_notice_desk timg_B Fr Bx (onann_dntc timg_B Bx b) B2 eq_refl H).
Qed.
(* The foreign notice's call_notify returns set_GOT_foreign of its world. *)
Lemma onann_fg_world : forall (Fr : option TI.tframe) (Bf b B3 : list byte),
  TSS.call_notify timg_B Fr Bf (onann_fntc Bf b) = Some (B3, tt) -> exists d, B3 = TW.set_GOT_foreign Bf d.
Proof.
  intros Fr Bf b B3 H. unfold TSS.call_notify in H.
  destruct (TW.S_notify Bf =? TI.ti_notice timg_B); [|discriminate H].
  exact (onann_notice_fg timg_B Fr Bf (onann_fntc Bf b) B3 eq_refl H).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The written range onann_wr lies in G                             *)
(* ------------------------------------------------------------------ *)

(* A field of a TMAP_B row's payload is a range of G. *)
Lemma onann_fld_G : forall o bs sz A n a, In (o, bs, sz) TMAP_B -> o <= A -> A + n <= o + sz ->
  twb_fld o bs A n a -> inG TG.G_HARNESS_B a.
Proof.
  intros o bs sz A n a Hin H1 H2 H. unfold inG. apply Exists_exists. exists (bs, sz).
  split; [exact (TMAP_B_in_G o bs sz Hin) | unfold in_zr, twb_fld in *; cbn [fst snd]; lia].
Qed.

(* A closed numeric goal (no world, no variable): decided by vm_compute. *)
Local Ltac kp_closed :=
  vm_compute; first [congruence | reflexivity | (left; congruence) | (right; congruence) |
                     (split; congruence)].
Local Ltac kp_row R H := refine (onann_fld_G _ _ _ _ _ _ R _ _ H); kp_closed.

Lemma onann_ntc_wr_G : forall X (n : TI.ntc) a, notice_wr X n a -> inG TG.G_HARNESS_B a.
Proof.
  intros X n a H. unfold notice_wr in H.
  destruct H as [(_ & [(G & H) | H]) | [(_ & H) | [(_ & H) | [(_ & H) | [(_ & H) | (_ & H)]]]]].
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_B_GOT _ _ H).
    + unfold TW.A_GOT_t_state, TW.OFF_GOT, TC.TRANS_MAX in *. lia.
    + unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT, TC.TRANS_MAX in *. lia.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_GOT H.
Qed.

Lemma onann_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof.
  intros n a H. unfold iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]].
  - kp_row TMAP_B_g_fail_next H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_GOT H.
  - kp_row TMAP_B_g_last_counter H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - kp_row TMAP_B_M H.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_B_M _ _ H); [kp_closed|].
    unfold TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME. lia.
  - refine (onann_fld_G _ _ _ _ _ _ TMAP_B_g_cmd _ _ H).
    + unfold TW.A_Cmd_st, TW.OFF_g_cmd, TC.CMDS_MAX in *. lia.
    + unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX in *. lia.
  - kp_row TMAP_B_g_q H.
  - kp_row TMAP_B_g_nq H.
Qed.

Lemma onann_wake_wr_G : forall X a, wake_wr X a -> inG TG.G_HARNESS_B a.
Proof.
  intros X a H. unfold wake_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|(_ & [H|H])]]]]]]]]]]]]].
  1-12: kp_row TMAP_B_g_s H.
  - exact (onann_iosend_wr_G _ a H).
  - kp_row TMAP_B_g_s H.
  - exact (onann_ntc_wr_G _ _ a H).
Qed.

Lemma onann_sstate_wr_G : forall X st why a, sstate_wr X st why a -> inG TG.G_HARNESS_B a.
Proof.
  intros X st why a H. unfold sstate_wr in H.
  destruct H as (_ & [H | H]); [kp_row TMAP_B_g_s H | exact (onann_ntc_wr_G _ _ a H)].
Qed.

Lemma onann_mo_wr_G : forall X a, maybeon_wr X a -> inG TG.G_HARNESS_B a.
Proof.
  intros X a H. unfold maybeon_wr in H.
  destruct H as (_ & [H | (_ & [H | H])]); [kp_row TMAP_B_g_s H | kp_row TMAP_B_g_s H | exact (onann_ntc_wr_G _ _ a H)].
Qed.

(* Every byte on_announce may store is a byte of G. *)
Lemma onann_wr_G : forall (Bw b : list byte) (a : Z), onann_wr Bw b a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw b a H. unfold onann_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[(Bx & H)|[H|[H|[H|H]]]]]]]]]]].
  - kp_row TMAP_B_g_s H.
  - kp_row TMAP_B_g_s H.
  - exact (onann_ntc_wr_G _ _ a H).
  - kp_row TMAP_B_g_s H.
  - kp_row TMAP_B_g_s H.
  - kp_row TMAP_B_g_s H.
  - exact (onann_sstate_wr_G _ _ _ a H).
  - exact (onann_wake_wr_G _ a H).
  - kp_row TMAP_B_g_s H.
  - exact (onann_mo_wr_G _ a H).
  - exact (onann_ntc_wr_G _ _ a H).
  - exact (onann_sstate_wr_G _ _ _ a H).
Qed.

(* ... so it lies in G's hull, below kLowMemEnd and below every shadow byte. *)
Lemma onann_wr_lowmem : forall (Bw b : list byte) (a : Z), onann_wr Bw b a ->
  TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI /\ a < kLowMemEnd /\ (forall x, 0 <= x -> a < shadow_addr x).
Proof.
  intros Bw b a H. pose proof (inG_G_HARNESS_hull a (onann_wr_G Bw b a H)) as Gh. clear H.
  split; [exact Gh|]. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Gh.
  split; [unfold kLowMemEnd; lia|].
  intros x Hx. pose proof (Z.div_pos x 8 Hx ltac:(lia)). unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* The code's own stores into g_s. *)
Lemma onann_wr_rxign : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_rx_ignored 8 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. left. exact H. Qed.
Lemma onann_wr_pers : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_personality 8 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. right; left. exact H. Qed.
Lemma onann_wr_foreign : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_foreign 4 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. do 3 right; left. exact H. Qed.
Lemma onann_wr_inflight : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_inflight 4 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. do 4 right; left. exact H. Qed.
Lemma onann_wr_dcv : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_desk_counter_valid 4 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. do 5 right; left. exact H. Qed.
Lemma onann_wr_e1nu : forall Bw b a, twb_fld TW.OFF_g_s TB_g_s TW.A_S_e1_named_us 4 a -> onann_wr Bw b a.
Proof. intros Bw b a H. unfold onann_wr. do 8 right; left. exact H. Qed.

Lemma onann_ntc_desk_wr : forall X (n : TI.ntc) a, TI.n_kind n = TC.N_DESK -> notice_wr X n a ->
  twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_desk 4 a.
Proof.
  intros X n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(E & _) | [(E & _) | [(E & _) | [(_ & H) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  exact H.
Qed.
Lemma onann_ntc_fg_wr : forall X (n : TI.ntc) a, TI.n_kind n = TC.N_FOREIGN -> notice_wr X n a ->
  twb_fld TW.OFF_GOT TB_GOT TW.A_GOT_foreign 4 a.
Proof.
  intros X n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(E & _) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (_ & H)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  exact H.
Qed.
Lemma onann_ntc_state_wr : forall X Y (n m : TI.ntc) a, TI.n_kind n = TC.N_STATE -> TI.n_kind m = TC.N_STATE ->
  TW.GOT_n X = TW.GOT_n Y -> notice_wr X n a -> notice_wr Y m a.
Proof.
  intros X Y n m a Kn Km Eg H. unfold notice_wr in H |- *. rewrite Kn in H. rewrite Km, <- Eg.
  destruct H as [(_ & H) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]].
  - left. split; [reflexivity | exact H].
  - unfold TC.N_STATE, TC.N_ACKED in E. discriminate E.
  - unfold TC.N_STATE, TC.N_ACK_LOST in E. discriminate E.
  - unfold TC.N_STATE, TC.N_DESK in E. discriminate E.
  - unfold TC.N_STATE, TC.N_DATA in E. discriminate E.
  - unfold TC.N_STATE, TC.N_FOREIGN in E. discriminate E.
Qed.

Lemma onann_wr_dntc : forall X Y (Bw b : list byte) a,
  notice_wr X (onann_dntc timg_B Y b) a -> onann_wr Bw b a.
Proof.
  intros X Y Bw b a H. pose proof (onann_ntc_desk_wr X (onann_dntc timg_B Y b) a eq_refl H) as Hd.
  unfold onann_wr. right; right; left. unfold notice_wr. right; right; right; left.
  split; [reflexivity | exact Hd].
Qed.
Lemma onann_wr_fntc : forall X Y (Bw b : list byte) a,
  notice_wr X (onann_fntc Y b) a -> onann_wr Bw b a.
Proof.
  intros X Y Bw b a H. pose proof (onann_ntc_fg_wr X (onann_fntc Y b) a eq_refl H) as Hd.
  unfold onann_wr. do 10 right. left. unfold notice_wr. do 5 right.
  split; [reflexivity | exact Hd].
Qed.
Lemma onann_wr_wake : forall Bx (Bw b : list byte) a, wake_wr Bx a -> onann_wr Bw b a.
Proof. intros Bx Bw b a H. unfold onann_wr. do 7 right. left. exists Bx. exact H. Qed.

(* set_state's store of the state keeps GOT.n. *)
Lemma onann_sstate_gotn : forall Y st, length Y = Z.to_nat TW.W_LEN -> TW.GOT_n (sstate_w Y st) = TW.GOT_n Y.
Proof.
  intros Y st LY. unfold sstate_w, TW.set_S_state, TW.GOT_n, TW.s32_at.
  rewrite (onann_upd_rd Y TW.A_S_state 4%nat st TW.A_GOT_n 4%nat LY ltac:(kp_closed) ltac:(kp_closed)
    ltac:(kp_closed) ltac:(right; kp_closed)).
  reflexivity.
Qed.

Lemma onann_sl_same : forall X, length X = Z.to_nat TW.W_LEN -> onann_same X (slost_w1 X).
Proof.
  intros X L. unfold slost_w1.
  assert (L1 : length (TW.set_S_inflight X 0) = Z.to_nat TW.W_LEN)
    by (unfold TW.set_S_inflight; apply onann_upd_len; [exact L | kp_closed | kp_closed]).
  refine (onann_same_trans X (TW.set_S_inflight X 0) _ _ _).
  - unfold TW.set_S_inflight. apply onann_same_upd; [exact L | left; split; kp_closed].
  - unfold TW.set_S_desk_counter_valid. apply onann_same_upd; [exact L1 | left; split; kp_closed].
Qed.
Lemma onann_sl_state : forall X, length X = Z.to_nat TW.W_LEN -> TW.S_state (slost_w1 X) = TW.S_state X.
Proof. intros X L. exact (proj1 (proj2 (onann_sl_same X L))). Qed.
Lemma onann_sl_gotn : forall X, length X = Z.to_nat TW.W_LEN -> TW.GOT_n (slost_w1 X) = TW.GOT_n X.
Proof. intros X L. pose proof (onann_sl_same X L) as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma onann_sl_len : forall X, length X = Z.to_nat TW.W_LEN -> length (slost_w1 X) = Z.to_nat TW.W_LEN.
Proof. intros X L. pose proof (onann_sl_same X L) as (H & _). rewrite H. exact L. Qed.

Lemma onann_wr_slost : forall (Bw b Bx : list byte) why a,
  length Bx = Z.to_nat TW.W_LEN -> length Bw = Z.to_nat TW.W_LEN ->
  TW.GOT_n Bx = TW.GOT_n Bw -> TW.S_state Bx = TW.S_state Bw ->
  sstate_wr (slost_w1 Bx) TS0.DIGINET_S_IDLE why a -> onann_wr Bw b a.
Proof.
  intros Bw b Bx why a Lx Lw Eg Es H.
  assert (Es1 : TW.S_state (slost_w1 Bx) = TW.S_state (slost_w1 Bw))
    by (rewrite (onann_sl_state Bx Lx), (onann_sl_state Bw Lw); exact Es).
  assert (Es2 : TW.GOT_n (sstate_w (slost_w1 Bx) TS0.DIGINET_S_IDLE) =
                TW.GOT_n (sstate_w (slost_w1 Bw) TS0.DIGINET_S_IDLE)).
  { rewrite (onann_sstate_gotn _ _ (onann_sl_len Bx Lx)), (onann_sstate_gotn _ _ (onann_sl_len Bw Lw)).
    rewrite (onann_sl_gotn Bx Lx), (onann_sl_gotn Bw Lw). exact Eg. }
  unfold onann_wr. do 6 right. left.
  unfold sstate_wr in H |- *. destruct H as (Hne & [H | H]).
  - split; [rewrite <- Es1; exact Hne | left; exact H].
  - split; [rewrite <- Es1; exact Hne | right].
    exact (onann_ntc_state_wr (sstate_w (slost_w1 Bx) TS0.DIGINET_S_IDLE)
      (sstate_w (slost_w1 Bw) TS0.DIGINET_S_IDLE)
      (sstate_ntc (slost_w1 Bx) TS0.DIGINET_S_IDLE why)
      (sstate_ntc (slost_w1 Bw) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE) a eq_refl eq_refl Es2 H).
Qed.

Lemma onann_mo_w1_same : forall X, length X = Z.to_nat TW.W_LEN -> onann_same X (maybeon_w1 X).
Proof.
  intros X L. unfold maybeon_w1, TW.set_S_next_keepalive_us.
  apply onann_same_upd; [exact L | left; split; kp_closed].
Qed.
Lemma onann_mo_w2_gotn : forall X, length X = Z.to_nat TW.W_LEN -> TW.GOT_n (maybeon_w2 X) = TW.GOT_n X.
Proof.
  intros X L. pose proof (onann_mo_w1_same X L) as Hs1.
  assert (L1 : length (maybeon_w1 X) = Z.to_nat TW.W_LEN) by (rewrite (proj1 Hs1); exact L).
  change (maybeon_w2 X) with (sstate_w (maybeon_w1 X) TS0.DIGINET_S_ONLINE).
  rewrite (onann_sstate_gotn _ _ L1).
  pose proof Hs1 as (_ & _ & _ & _ & _ & _ & Hg & _). exact Hg.
Qed.
Lemma onann_mo_wr_desk : forall Y d a, length Y = Z.to_nat TW.W_LEN ->
  maybeon_wr (TW.set_GOT_desk Y d) a -> maybeon_wr Y a.
Proof.
  intros Y d a L H.
  pose proof (onann_same_desk Y d L) as Hs.
  assert (L2 : length (TW.set_GOT_desk Y d) = Z.to_nat TW.W_LEN) by (rewrite (proj1 Hs); exact L).
  assert (R : forall k' m, 0 <= k' -> k' + Z.of_nat m <= TW.A_GOT_desk ->
            TW.u_at (TW.set_GOT_desk Y d) k' m = TW.u_at Y k' m).
  { intros k' m H1 H2. unfold TW.set_GOT_desk.
    exact (onann_upd_rd Y TW.A_GOT_desk 4%nat d k' m L ltac:(kp_closed) ltac:(kp_closed) H1 (or_introl H2)). }
  assert (Ego : maybeon_go (TW.set_GOT_desk Y d) = maybeon_go Y).
  { unfold maybeon_go, TW.S_state, TW.S_wake_acked, TW.S_e1_named_us, TW.s32_at.
    rewrite (R TW.A_S_state 4%nat ltac:(kp_closed) ltac:(kp_closed)).
    rewrite (R TW.A_S_wake_acked 4%nat ltac:(kp_closed) ltac:(kp_closed)).
    rewrite (R TW.A_S_e1_named_us 4%nat ltac:(kp_closed) ltac:(kp_closed)).
    reflexivity. }
  clear R.
  assert (Es : TW.S_state (TW.set_GOT_desk Y d) = TW.S_state Y) by exact (proj1 (proj2 Hs)).
  assert (Es1 : TW.S_state (maybeon_w1 (TW.set_GOT_desk Y d)) = TW.S_state (maybeon_w1 Y)).
  { rewrite (proj1 (proj2 (onann_mo_w1_same _ L2))), (proj1 (proj2 (onann_mo_w1_same Y L))). exact Es. }
  assert (Eg : TW.GOT_n (maybeon_w2 (TW.set_GOT_desk Y d)) = TW.GOT_n (maybeon_w2 Y)).
  { rewrite (onann_mo_w2_gotn _ L2), (onann_mo_w2_gotn Y L).
    pose proof Hs as (_ & _ & _ & _ & _ & _ & Hg & _). exact Hg. }
  unfold maybeon_wr in H |- *. destruct H as (Hgo & H). rewrite Ego in Hgo. split; [exact Hgo|].
  rewrite Es1 in H.
  destruct H as [H | (Hne & [H | H])].
  - left. exact H.
  - right. split; [exact Hne | left; exact H].
  - right. split; [exact Hne | right].
    exact (onann_ntc_state_wr (maybeon_w2 (TW.set_GOT_desk Y d)) (maybeon_w2 Y)
      (maybeon_ntc (TW.set_GOT_desk Y d)) (maybeon_ntc Y) a eq_refl eq_refl Eg H).
Qed.

(* The stores of :213 and :214 commute with the desk notice's store of GOT.desk. *)
Lemma onann_mo_comm : forall W1 d, length W1 = Z.to_nat TW.W_LEN ->
  TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk W1 d) 0) 1 =
  TW.set_GOT_desk (TW.set_S_e1_named_us (TW.set_S_foreign W1 0) 1) d.
Proof.
  intros W1 d L. unfold TW.set_S_e1_named_us, TW.set_S_foreign, TW.set_GOT_desk.
  assert (L1 : length (TW.upd W1 TW.A_S_foreign (TW.put 4 0)) = Z.to_nat TW.W_LEN)
    by exact (onann_upd_len W1 TW.A_S_foreign 4%nat 0 L ltac:(kp_closed) ltac:(kp_closed)).
  rewrite (upd_comm_W W1 (TW.put 4 d) (TW.put 4 0) TW.A_GOT_desk TW.A_S_foreign L) by
    (rewrite ?TWL.length_put; kp_closed).
  rewrite (upd_comm_W (TW.upd W1 TW.A_S_foreign (TW.put 4 0)) (TW.put 4 d) (TW.put 4 1) TW.A_GOT_desk
    TW.A_S_e1_named_us L1) by (rewrite ?TWL.length_put; kp_closed).
  reflexivity.
Qed.

Lemma onann_wr_mo : forall (Bw b : list byte) d a, length Bw = Z.to_nat TW.W_LEN ->
  maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_B Bw b) d) 0) 1) a ->
  onann_wr Bw b a.
Proof.
  intros Bw b d a L H.
  pose proof (onann_w1_len timg_B Bw b L) as L1.
  rewrite (onann_mo_comm _ d L1) in H.
  assert (L3 : length (TW.set_S_foreign (onann_w1 timg_B Bw b) 0) = Z.to_nat TW.W_LEN)
    by (rewrite (proj1 (onann_same_foreign _ 0 L1)); exact L1).
  assert (L2 : length (TW.set_S_e1_named_us (TW.set_S_foreign (onann_w1 timg_B Bw b) 0) 1) = Z.to_nat TW.W_LEN)
    by (rewrite (proj1 (onann_same_e1nu _ 1 L3)); exact L3).
  pose proof (onann_mo_wr_desk _ d a L2 H) as H2.
  unfold onann_wr. do 9 right. left. exact H2.
Qed.

Lemma onann_apart_ntc : forall (TF : option TI.tframe) (Bw b : list byte) (E : Z -> Prop),
  onann_apart TF Bw b -> (forall x, E x -> onann_wr Bw b x) ->
  forall x, E x ->
    forall fr, TF = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).
Proof. intros TF Bw b E Hap Hs x Hx. exact (Hap x (Hs x Hx)). Qed.
Lemma onann_apart_wake : forall (TF : option TI.tframe) (Bw b Bx : list byte),
  onann_apart TF Bw b -> wake_apart TF Bx.
Proof. intros TF Bw b Bx Hap x Hx. exact (Hap x (onann_wr_wake Bx Bw b x Hx)). Qed.
Lemma onann_apart_mo : forall (TF : option TI.tframe) (Bw b : list byte) d, length Bw = Z.to_nat TW.W_LEN ->
  onann_apart TF Bw b ->
  maybeon_apart TF (TW.set_S_e1_named_us (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_B Bw b) d) 0) 1).
Proof. intros TF Bw b d L Hap x Hx. exact (Hap x (onann_wr_mo Bw b d x L Hx)). Qed.
Lemma onann_apart_sstate : forall (TF : option TI.tframe) (Bw b Bx : list byte) why,
  length Bx = Z.to_nat TW.W_LEN -> length Bw = Z.to_nat TW.W_LEN ->
  TW.GOT_n Bx = TW.GOT_n Bw -> TW.S_state Bx = TW.S_state Bw ->
  onann_apart TF Bw b -> sstate_apart TF (slost_w1 Bx) TS0.DIGINET_S_IDLE why.
Proof.
  intros TF Bw b Bx why Lx Lw Eg Es Hap x Hx. exact (Hap x (onann_wr_slost Bw b Bx why x Lx Lw Eg Es Hx)).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The frame bytes diginet_announce_parse reads                     *)
(* ------------------------------------------------------------------ *)

(* A parse that answered 0 saw at least the 30 header bytes (on_ack_seg_head.v ohd_blen). *)
Lemma kp_blen : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
  intros b H. destruct (Nat.ltb_spec (length b) 30) as [Hlt | Hge]; [|exact Hge].
  exfalso. unfold DSpec.fr_code in H.
  replace ((length b <? 30)%nat) with true in H by (symmetry; apply Nat.ltb_lt; exact Hlt).
  discriminate H.
Qed.

Lemma kp_flen : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat.
Proof.
  intros buf b fj H0 HL. pose proof (kp_blen b H0) as HB.
  assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
  assert (L2 : length (DSpec.fr_src b) = 6%nat)
    by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
  assert (L4 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
  assert (L5 : length (skipn 59 fj) = 5%nat) by (rewrite length_skipn, HL; reflexivity).
  unfold frame_f_bytes, frame_f_cells. rewrite H0. cbn [Z.eqb].
  rewrite length_map. unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
  rewrite !length_app, ?Mem.length_le2, ?Mem.length_le4, ?Mem.length_le8, L1, L2, L4, L5.
  cbn [length]. lia.
Qed.

(* The byte at f + 30 is the command (parse_cells' tenth cell, after 6+6+2+2+2+2+4+4+2 = 30 bytes). *)
Lemma kp_nth30 : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  nth 30 (frame_f_bytes buf b fj) 0 = DSpec.fr_cmd b.
Proof.
  intros buf b fj H0 HL. pose proof (kp_blen b H0) as HB.
  assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
  assert (L2 : length (DSpec.fr_src b) = 6%nat)
    by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
  assert (L4 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
  assert (RC : 0 <= DSpec.fr_cmd b < 256)
    by (unfold DSpec.fr_cmd, DSpec.at8, DSpec.bz; apply bv_unsigned_in_range).
  unfold frame_f_bytes, frame_f_cells. rewrite H0. cbn [Z.eqb].
  unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
  rewrite !map_app.
  rewrite app_nth2 by (rewrite length_map, L1; lia). rewrite length_map, L1.
  rewrite app_nth2 by (rewrite length_map, L2; lia). rewrite length_map, L2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, L4; lia). rewrite length_map, L4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le4; lia). rewrite length_map, Mem.length_le4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le4; lia). rewrite length_map, Mem.length_le4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  cbn [map nth length].
  unfold DSpec.bz, DSpec.b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  cbn [Z.of_N]. apply Z.mod_small. exact RC.
Qed.

(* The 16 bytes at f + 32 are the body pointer and the body length diginet_announce_parse reads. *)
Lemma kp_nth32 : forall buf b fj k, DSpec.fr_code b = 0 -> length fj = 64%nat -> (k < 16)%nat ->
  nth (32 + k) (frame_f_bytes buf b fj) 0 = nth k (trans_anp_f32_bytes (buf + 30) (DSpec.fr_body b)) 0.
Proof.
  intros buf b fj k H0 HL Hk. pose proof (kp_blen b H0) as HB.
  assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
  assert (L2 : length (DSpec.fr_src b) = 6%nat)
    by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
  assert (L4 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
  assert (EB : Z.of_nat (length (DSpec.fr_body b)) = DSpec.fr_body_len b).
  { unfold DSpec.fr_body, DSpec.fr_body_len in *.
    destruct (DSpec.fr_code_ok b H0) as (LN & _ & N1 & N2).
    rewrite length_firstn, length_skipn. lia. }
  unfold frame_f_bytes, frame_f_cells. rewrite H0. cbn [Z.eqb].
  unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
  rewrite !map_app.
  rewrite app_nth2 by (rewrite length_map, L1; lia). rewrite length_map, L1.
  rewrite app_nth2 by (rewrite length_map, L2; lia). rewrite length_map, L2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, L4; lia). rewrite length_map, L4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le4; lia). rewrite length_map, Mem.length_le4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le4; lia). rewrite length_map, Mem.length_le4.
  rewrite app_nth2 by (rewrite length_map, Mem.length_le2; lia). rewrite length_map, Mem.length_le2.
  rewrite app_nth2 by (cbn [map length]; lia). cbn [map length].
  rewrite app_nth2 by (cbn [map length]; lia). cbn [map length].
  replace (32 + k - 6 - 6 - 2 - 2 - 2 - 2 - 4 - 4 - 2 - 1 - 1)%nat with k by lia.
  unfold trans_anp_f32_bytes. cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r.
  rewrite map_app, EB, app_assoc.
  rewrite app_nth1 by (rewrite length_app, !length_map, !Mem.length_le8; lia).
  reflexivity.
Qed.

(* A sub-range of a garr8 list, at an offset. *)
Lemma kp_garr8_sub : forall (mem : word -> option byte) base l i l',
  garr8 tfibsegs mem base l -> (i + length l' <= length l)%nat ->
  (forall k, (k < length l')%nat -> nth (i + k) l 0 = nth k l' 0) ->
  garr8 tfibsegs mem (base + Z.of_nat i) l'.
Proof.
  intros mem base l i l' Hg Hi Hn j Hj.
  destruct (Hg (i + j)%nat ltac:(lia)) as [Hv Hr]. rewrite (Hn j Hj) in Hv, Hr.
  split; [|exact Hr].
  replace (base + Z.of_nat i + Z.of_nat j) with (base + Z.of_nat (i + j)) by lia. exact Hv.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.

(* ... and off every live side-stack frame and its shadow bytes. *)
Lemma onann_wr_nframe : AR_laws segs B ->
  forall ly S (W : world segs) mem md cid pos (Bw b : list byte) (a : Z),
  @AR rc segs B ly S W mem md -> In (cid, pos) (frames S) -> onann_wr Bw b a ->
  ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
  ~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
  intros LAWS ly S W mem md cid pos Bw b a HAR Hin H.
  pose proof (onann_wr_G Bw b a H) as HG.
  destruct (onann_wr_lowmem Bw b a H) as (_ & _ & Hsh). clear H.
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (F1 & _ & _).
  pose proof (Hsh (frame_addr ly cid pos) ltac:(lia)) as Hs0.
  split.
  - intro Hr. exact (frm_img segs B LAWS ly S W mem md cid pos a HAR Hin Hr (trans_g_img a HG)).
  - intro Hs. unfold in_zr in Hs. cbn [fst snd] in Hs. lia.
Qed.

(* What every piece takes from onann_fix and onann_cur. *)
Lemma onann_cur_ar :
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e},
  AR_laws segs B ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @AR rc segs B lyc Sc W memc mdc /\ @AR rc segs B ly2 S2 W2 mem2 md2 /\
  ly_stk_lo ly2 = ly_stk_lo lyc /\ ly_stk_hi ly2 = ly_stk_hi lyc /\
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) /\ (forall c p, flag_addr ly2 c p = flag_addr lyc c p) /\
  In (ONANN_CID, pos) (frames S2) /\ frame_addr ly2 ONANN_CID pos = F /\
  (forall a, F <= a < F + 512 -> apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a) /\
  (forall i, 0 <= i < 64 ->
     apresent (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) /\ ~ aowned B ly2 S2 (SHADOW_OFF + F / 8 + i)) /\
  (forall a, F <= a < F + 512 -> ~ inG TG.G_HARNESS_B a) /\
  4096 <= F /\ F mod 64 = 0 /\ F + 512 <= alloc_ceiling /\ in_app F 512 /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc <= spZ regs - ONANN_STK /\ spZ regs <= ly_stk_hi lyc /\
  ly_stk_hi lyc <= 2 ^ 47 /\
  apresent (w_H W2) mem2 (flag_addr lyc ONANN_CID pos) /\ aowned B ly2 S2 (flag_addr lyc ONANN_CID pos) /\
  4096 <= flag_addr lyc ONANN_CID pos < alloc_ceiling /\
  (flag_addr lyc ONANN_CID pos < F \/ F + 512 <= flag_addr lyc ONANN_CID pos) /\
  (flag_addr lyc ONANN_CID pos < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 64 <= flag_addr lyc ONANN_CID pos) /\
  spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0 /\ 2 ^ 46 <= sp1.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e LAWS HFIX HCUR.
  destruct HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  destruct HCUR as (HJ1 & _ & Hfrs & _ & HlyF & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ELO & EHI & _).
  pose proof HJ1 as (_ & _ & (memS2 & HJi2 & _) & _).
  destruct HJi2 as (_ & Hlyle2 & _).
  destruct Hlyle2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ELO2 & EHI2 & _).
  clear HJ0 HJ1.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EFA : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
    by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (EFL : forall c p, flag_addr ly2 c p = flag_addr lyc c p)
    by (intros c p; unfold flag_addr; rewrite HlyF; reflexivity).
  assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EF2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EFA; symmetry; exact EF).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
  rewrite EF2 in HFb, HFsh.
  change (fs_frame_bytes ONANN_CID) with 512 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 64 in HFsh.
  assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
  rewrite ESH in HFsh.
  destruct (al_flag _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (HFLp & HFLo & HFLapp & HFLc).
  rewrite EFL in HFLp, HFLo, HFLapp, HFLc.
  destruct HFLapp as [HFL4096 _].
  assert (HFLF : flag_addr lyc ONANN_CID pos < F \/ F + 512 <= flag_addr lyc ONANN_CID pos).
  { destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) F) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (F + 512)) as [h2|h2]; [|right; exact h2].
    exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
  assert (HFLS : flag_addr lyc ONANN_CID pos < SHADOW_OFF + F / 8 \/
                 SHADOW_OFF + F / 8 + 64 <= flag_addr lyc ONANN_CID pos).
  { destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
    destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (SHADOW_OFF + F / 8 + 64)) as [h2|h2]; [|right; exact h2].
    exfalso. pose proof (proj2 (HFsh (flag_addr lyc ONANN_CID pos - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
    replace (SHADOW_OFF + F / 8 + (flag_addr lyc ONANN_CID pos - (SHADOW_OFF + F / 8)))
      with (flag_addr lyc ONANN_CID pos) in Hno by lia.
    exact (Hno HFLo). }
  assert (HFG : forall a, F <= a < F + 512 -> ~ inG TG.G_HARNESS_B a).
  { intros a Ha HG. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos a HAR2 Hin).
    - rewrite EF2. change (fs_frame_bytes ONANN_CID) with 512. lia.
    - exact (trans_g_img a HG). }
  unfold ONANN_FBYTES in HFc, HFapp.
  (* the realigned sp1 *)
  assert (HSTK208 : 208 <= ONANN_STK) by (vm_compute; congruence).
  assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
  { rewrite Esp1. unfold ONANN_FRAME.
    pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
    pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
    set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
    split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
  (* the facts of the cut state, in the order onann_cur_ar states them *)
  split; [exact HARc|]. split; [exact HAR2|].
  split; [rewrite ELO2, ELO; reflexivity|]. split; [rewrite EHI2, EHI; reflexivity|].
  split; [exact EFA|]. split; [exact EFL|]. split; [exact Hin|]. split; [exact EF2|].
  split; [exact HFb|]. split; [exact HFsh|]. split; [exact HFG|].
  split; [exact HF0|]. split; [exact HF64|]. split; [exact HFc|]. split; [exact HFapp|].
  split; [rewrite ELO; exact Hceil|].
  split; [rewrite ELO; lia|].
  split; [rewrite EHI; lia|].
  split; [rewrite EHI; exact H47|].
  split; [exact HFLp|]. split; [exact HFLo|]. split; [split; [exact HFL4096 | exact HFLc]|].
  split; [exact HFLF|]. split; [exact HFLS|].
  split; [exact (proj1 Hsp1)|]. split; [exact (proj2 Hsp1)|].
  lia.
Qed.

(* trans_rom_view_rd at the cut memory. *)
Lemma onann_rom_call : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_rom_view_rd W memc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi E Hrom (_ & _ & K3 & _) a Ha.
  rewrite <- (Hrom a Ha).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* A range placed at the entry, off G and outside the window, at the cut state. *)
Lemma onann_src_kept : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 pos slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  (forall a, q <= a < q + n -> ~ inG TG.G_HARNESS_B a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos slo shi E q n HAR HAR2 Hfr Hperm Hfa Elo Ehi
    HK HEG HnG Hoff Hs Hn.
  pose proof HK as (K1 & K2 & K3 & K4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HnE : forall a, q <= a < q + n -> ~ E a) by (intros a Ha He; exact (HnG a Ha (HEG a He))).
  assert (KS : forall cid p s, In (cid, p) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid p), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid p s Hin Hs'. apply (K4 cid p s Hin (or_intror Hs')). intro He.
    pose proof (inG_G_HARNESS_hull s (HEG s He)) as Gh.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HAR Hin) as (F1 & _ & _).
    pose proof (Z.div_pos (frame_addr lyc cid p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF in Hs'. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Gh. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (HnG a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2].
        apply K1; [lia|]. destruct Hoff as [Ho|Ho]; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        exact (K3 a (trans_ro_img a Ra) (HnG a Ha) Ho He). }
  split; [|exact KV].
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (Hf : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - assert (Hrd2 : decode_rd_ok W2 mem2 q n).
    { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - exact (decode_rd_ok_fake_kept_ge0 B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn KV KS).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (stack_zshadow_ra_ge0 B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
                    ltac:(rewrite Ehi; lia)) as [Ha Hh].
        exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
    exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hf Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* The current heap frame TF at a call state of the walk. *)
Lemma onann_tf_call : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 pos
    (regs regsC : bvmap 5 word) (K : Z) (TF : option TI.tframe) (Bw b : list byte),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) ->
  trans_tf_off_g TF ->
  spZ regs - ONANN_STK <= spZ regsC - K -> spZ regsC <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs ONANN_STK TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos regs regsC K TF Bw b HAR HAR2 Hfr Hperm Hfa Elo
    Ehi HK HTFo Hw1 Hw2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  assert (Hn0 : 0 <= Z.of_nat (length (TI.tf_bytes fr))) by lia.
  assert (HnG : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    ~ inG TG.G_HARNESS_B a) by (intros a Ha; exact (HTFo fr eq_refl a Ha)).
  destruct (onann_src_kept LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b) (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) HAR HAR2 Hfr Hperm Hfa Elo Ehi HK
    (onann_wr_G Bw b) HnG Hoff Hsrc Hn0) as [Hs2 KV].
  split; [exact Ha0|]. split.
  { apply (garr8_frame segs _ _ _ _ Hg8). intros a Ha. rewrite length_map in Ha.
    apply mbyte_of_aview. exact (KV a Ha). }
  split; [exact Hs2|]. unfold decode_off_win in *. lia.
Qed.

(* The three, read directly off onann_fix and onann_cur at a cut state. *)
Lemma onann_rom_cur : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  trans_rom_view_rd W2 mem2.
Proof.
  intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e HFIX HCUR.
  destruct HLAWS as (_ & _ & _ & _ & _ & HRU & HRE & LAWS & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
  pose proof HCUR as (_ & _ & _ & _ & _ & _ & HKa & _).
  exact (onann_rom_call HRU HRE lyc Sc W memc W2 mem2 _ _ _ Hrom HKa).
Qed.

Lemma onann_tf_cur : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regsC : bvmap 5 word) (K : Z),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  spZ regs - ONANN_STK <= spZ regsC - K -> spZ regsC <= spZ regs ->
  trans_tframe_at B ly2 S2 W2 mem2 regsC K TF.
Proof.
  intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regsC K HFIX HCUR Hw1 Hw2.
  pose proof HLAWS as (_ & _ & _ & _ & _ & HRU & HRE & LAWS & _).
  destruct (onann_cur_ar LAWS HFIX HCUR) as (HARc & HAR2 & Elo & Ehi & Hfa & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTF & HTFo & _).
  pose proof HCUR as (_ & _ & Hfrs & Hperm & _ & _ & HKa & _).
  exact (onann_tf_call LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos regs regsC K TF Bw b
    HARc HAR2 Hfrs Hperm Hfa Elo Ehi HKa HTFo Hw1 Hw2 HTF).
Qed.

Lemma onann_src_cur : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (q n : Z),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  (forall a, q <= a < q + n -> ~ inG TG.G_HARNESS_B a) ->
  (q + n <= spZ regs - ONANN_STK \/ spZ regs <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e q n HFIX HCUR HnG Hoff Hs Hn.
  pose proof HLAWS as (_ & _ & _ & _ & _ & HRU & HRE & LAWS & _).
  destruct (onann_cur_ar LAWS HFIX HCUR) as (HARc & HAR2 & Elo & Ehi & Hfa & _).
  pose proof HCUR as (_ & _ & Hfrs & Hperm & _ & _ & HKa & _).
  exact (onann_src_kept LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos _ _ (onann_wr Bw b) q n
    HARc HAR2 Hfrs Hperm Hfa Elo Ehi HKa (onann_wr_G Bw b) HnG Hoff Hs Hn).
Qed.

(* f (the struct diginet_frame at fp) at a cut state. *)
Lemma onann_f30 : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regsC : bvmap 5 word) (K : Z),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  spZ regs - ONANN_STK <= spZ regsC - K -> spZ regsC <= spZ regs ->
  4096 <= fp /\ fp + FRAME_F_SIZE <= alloc_ceiling /\ fp mod 8 = 0 /\
  (fp + FRAME_F_SIZE <= F \/ F + ONANN_FBYTES <= fp) /\
  garr8 segs (mrestrict (w_H W2) mem2) fp (frame_f_bytes buf b fj) /\
  decode_in_fake ly2 S2 fp FRAME_F_SIZE /\
  decode_rd_ok W2 mem2 fp FRAME_F_SIZE /\
  decode_off_win regsC K fp FRAME_F_SIZE /\
  0 <= DSpec.fr_cmd b < 2 ^ 8 /\
  aview segs (w_H W2) mem2 (fp + 30) = Some (DSpec.fr_cmd b) /\
  garr8 segs (mrestrict (w_H W2) mem2) (fp + 30) [DSpec.fr_cmd b] /\
  aview segs (w_H W2) mem2 (SHADOW_OFF + (fp + 30) / 8) = Some 0 /\
  garr8 segs (mrestrict (w_H W2) mem2) (fp + 32) (trans_anp_f32_bytes (buf + 30) (DSpec.fr_body b)) /\
  0 < buf /\
  garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b) /\
  trans_src_ok B ly2 S2 W2 mem2 buf (Z.of_nat (length b)) /\
  decode_off_win regsC K buf (Z.of_nat (length b)) /\
  (forall x, buf <= x < buf + Z.of_nat (length b) -> ~ inG TG.G_HARNESS_B x).
Proof.
  intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regsC K HFIX HCUR Hw1 Hw2.
  pose proof HLAWS as (_ & _ & _ & _ & _ & HRU & HRE & LAWS & _).
  destruct (onann_cur_ar LAWS HFIX HCUR) as (HARc & HAR2 & Elo & Ehi & Hfa & _ & Hin2 & EF2 & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDF & _).
  pose proof HCUR as (_ & _ & Hfrs & Hperm & _).
  destruct HDF as (Hcode & Hbuf0 & Hgbuf & Hsbuf & Hobuf & HbufG & Hfp0 & Hfp8 & Hfjlen & Hgfp & Hfake & Hrdfp &
    Hofp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  (* f's range is placed by trans_src_ok at the entry (the FAKE case) and lies off G *)
  assert (Hsfp : trans_src_ok B lyc Sc W memc fp FRAME_F_SIZE)
    by (right; split; [left; exact Hfake | exact Hrdfp]).
  destruct Hfake as (cidf & posf & Hinf & Hf1 & Hf2).
  assert (HfpG : forall a, fp <= a < fp + FRAME_F_SIZE -> ~ inG TG.G_HARNESS_B a).
  { intros a Ha HG. apply (frm_img segs B LAWS lyc Sc W memc mdc cidf posf a HARc Hinf);
      [unfold FRAME_F_SIZE in *; lia | exact (trans_g_img a HG)]. }
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cidf posf HARc Hinf) as (HFf1 & HFf2 & _).
  (* f's bytes at the cut state *)
  destruct (onann_src_cur HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 md2 e fp FRAME_F_SIZE HFIX HCUR HfpG Hofp Hsfp ltac:(unfold FRAME_F_SIZE; lia))
    as [Hsfp2 KVf].
  destruct (onann_src_cur HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 md2 e buf (Z.of_nat (length b)) HFIX HCUR HbufG Hobuf Hsbuf (Nat2Z.is_nonneg _))
    as [Hsbuf2 KVb].
  assert (Hgfp2 : garr8 segs (mrestrict (w_H W2) mem2) fp (frame_f_bytes buf b fj)).
  { apply (garr8_frame segs _ _ _ _ Hgfp). intros a Ha.
    rewrite (kp_flen buf b fj Hcode Hfjlen) in Ha. cbn [Z.of_nat] in Ha.
    apply mbyte_of_aview. apply KVf. unfold FRAME_F_SIZE. lia. }
  assert (Hgbuf2 : garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b)).
  { apply (garr8_frame segs _ _ _ _ Hgbuf). intros a Ha. unfold TW.zs in Ha. rewrite length_map in Ha.
    apply mbyte_of_aview. exact (KVb a Ha). }
  assert (Hrdfp2 : decode_rd_ok W2 mem2 fp FRAME_F_SIZE)
    by (apply (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 fp FRAME_F_SIZE HAR2 Hsfp2); unfold FRAME_F_SIZE; lia).
  assert (Hfake2 : decode_in_fake ly2 S2 fp FRAME_F_SIZE)
    by (exists cidf, posf; rewrite !Hfa; split; [rewrite Hfrs; right; exact Hinf | lia]).
  (* the bytes at f + 30 and f + 32 *)
  assert (RC : 0 <= DSpec.fr_cmd b < 256)
    by (unfold DSpec.fr_cmd, DSpec.at8, DSpec.bz; apply bv_unsigned_in_range).
  assert (Hg30 : garr8 segs (mrestrict (w_H W2) mem2) (fp + 30) [DSpec.fr_cmd b]).
  { replace (fp + 30) with (fp + Z.of_nat 30) by (cbn [Z.of_nat]; lia).
    apply (kp_garr8_sub _ fp (frame_f_bytes buf b fj) 30 [DSpec.fr_cmd b] Hgfp2).
    - rewrite (kp_flen buf b fj Hcode Hfjlen). cbn [length]. lia.
    - intros j Hj. cbn [length] in Hj. assert (Ej : j = 0%nat) by lia. subst j.
      rewrite Nat.add_0_r. cbn [nth]. exact (kp_nth30 buf b fj Hcode Hfjlen). }
  assert (Hg32 : garr8 segs (mrestrict (w_H W2) mem2) (fp + 32)
                   (trans_anp_f32_bytes (buf + 30) (DSpec.fr_body b))).
  { assert (L32 : length (trans_anp_f32_bytes (buf + 30) (DSpec.fr_body b)) = 16%nat)
      by (unfold trans_anp_f32_bytes; cbn [LC.cells_bytes LC.cbytes]; rewrite length_map, !length_app,
          !Mem.length_le8; reflexivity).
    replace (fp + 32) with (fp + Z.of_nat 32) by (cbn [Z.of_nat]; lia).
    apply (kp_garr8_sub _ fp (frame_f_bytes buf b fj) 32 _ Hgfp2).
    - rewrite (kp_flen buf b fj Hcode Hfjlen), L32. lia.
    - intros j Hj. rewrite L32 in Hj. exact (kp_nth32 buf b fj j Hcode Hfjlen Hj). }
  assert (Hav30 : aview segs (w_H W2) mem2 (fp + 30) = Some (DSpec.fr_cmd b)).
  { destruct (Hg30 0%nat ltac:(cbn [length]; lia)) as [Hv Hr]. cbn [nth] in Hv, Hr.
    replace (fp + 30 + Z.of_nat 0) with (fp + 30) in Hv by (cbn [Z.of_nat]; lia).
    exact (aview_of_val_mem1 (w_H W2) mem2 (fp + 30) (DSpec.fr_cmd b) Hv Hr). }
  (* the granule of f + 30 has shadow 0: the byte f + 31 of the same granule is addressable *)
  assert (Hsh0 : aview segs (w_H W2) mem2 (SHADOW_OFF + (fp + 30) / 8) = Some 0).
  { destruct Hrdfp2 as (_ & Hra & _).
    destruct (Hra (fp + 31) ltac:(unfold FRAME_F_SIZE; lia)) as (sv & Hsv & Hok).
    assert (E8 : (fp + 30) / 8 = (fp + 31) / 8).
    { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hfp8, Z.add_0_r in D.
      replace (fp + 30) with (fp / 8 * 8 + 30) by lia. replace (fp + 31) with (fp / 8 * 8 + 31) by lia.
      rewrite !Z.div_add_l by lia. reflexivity. }
    assert (Em : (fp + 31) mod 8 = 7).
    { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hfp8, Z.add_0_r in D.
      replace (fp + 31) with (fp / 8 * 8 + 31) by lia.
      rewrite Z.add_comm, Z.mod_add by lia. reflexivity. }
    rewrite E8. unfold shadow_of_addr in Hsv. rewrite Hsv. f_equal.
    destruct Hok as [-> | (H1 & H2)]; [reflexivity | rewrite Em in H1; lia]. }
  (* the frame f is apart from the own frame F *)
  assert (HFsep : fp + FRAME_F_SIZE <= F \/ F + ONANN_FBYTES <= fp).
  { destruct (trans_src_ok_disj_own B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ONANN_CID pos fp FRAME_F_SIZE
      HARc HAR2 Hfrs Hperm Hfa Hsfp ltac:(unfold FRAME_F_SIZE; lia)) as [H|H]; rewrite EF2 in H;
      [left; exact H | right; unfold ONANN_FBYTES; change (fs_frame_bytes ONANN_CID) with 512 in H; lia]. }
  split; [unfold FRAME_F_SIZE in *; lia|].
  split; [unfold FRAME_F_SIZE in *; lia|].
  split; [exact Hfp8|].
  split; [exact HFsep|].
  split; [exact Hgfp2|].
  split; [exact Hfake2|].
  split; [exact Hrdfp2|].
  split; [unfold decode_off_win in *; lia|].
  split; [change (2 ^ 8) with 256; exact RC|].
  split; [exact Hav30|].
  split; [exact Hg30|].
  split; [exact Hsh0|].
  split; [exact Hg32|].
  split; [exact Hbuf0|].
  split; [exact Hgbuf2|].
  split; [exact Hsbuf2|].
  split; [unfold decode_off_win in *; lia|].
  exact HbufG.
Qed.

End k.
