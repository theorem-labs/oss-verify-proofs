(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v; 408 of its 508 lines of code are new or changed and 1110 lines of the source are left out. *)
(* TickKa_kit: what the keepalive piece of the image-A walk of diginet_session_tick (TickKa_rest.v, TickKa.v) uses
   beyond the kit, and the symbolic states of its three runs:
   - the model: tka_vk, the value the two stores of :451-453 leave in g_s.next_keepalive_us; tka_w_eq, TickCut.v
     tick_ka_w as two stores (next_keepalive_us := tka_vk, stats.tx_keepalives := its value + 1: the plain walk's
     ka_world in image A's terms); g_fail_next and the run invariants (1) and (4) are the same before and after them;
   - the written range: every byte of send_data_cg.v senddata_wr is a byte of G (so not a byte of a frame), and a row
     of tick_wr;
   - the stores: a val_mem read byte by byte through the view; the world relation after the two stores of
     next_keepalive_us and stats.tx_keepalives (tka_tw_two, two TWorldG.v tw_write); one byte with shadow byte 1
     addressable (tka_ra_one);
   - the symbolic states: at the cut +0x8d8 (ka's shadow byte, ka, the shadow byte and the 4 bytes of s + 24, now at
     s1 + 56), at +0x91c (the shadow bytes and the 8 bytes of s + 184 and s + 18216, now) and at +0x95c, the return of
     send_data (ka's shadow byte), with their entry lemmas from the world relation, the record's zero shadow of g_s
     and the frame's presence. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostNtcKit SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The first sum (:451) and the value next_keepalive_us holds after :451-453. *)
Definition tka_v1 (B0 : list byte) : Z :=
  TS0.u64 (TW.S_next_keepalive_us B0 + TS0.ms_m (TW.S_cfg_keepalive_ms B0)).
Definition tka_vk (B0 : list byte) (now : Z) : Z :=
  if tka_v1 B0 <=? now then TS0.u64 (now + TS0.ms_m (TW.S_cfg_keepalive_ms B0)) else tka_v1 B0.

(* The numeric side goals on the offsets of the stores and of the fields read. *)
Ltac tka_off :=
  unfold TW.A_S_next_keepalive_us, TW.A_S_stats_tx_keepalives, TW.A_S_cfg_keepalive_ms, TW.OFF_g_s, TW.W_LEN,
    TW.A_Cmd_st, TW.A_Cmd_len, TW.OFF_g_cmd in *;
  rewrite ?TWL.length_put; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma tka_rd_put : forall (B : list byte) k (n : nat) v, length B = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> TW.u_at (TW.upd B k (TW.put n v)) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros B k n v L Hk Hn. apply TWL.u_at_upd_put; [exact Hk|]. rewrite L, Z2Nat.id by (unfold TW.W_LEN; lia). exact Hn.
Qed.

(* tick_ka_w as two stores. *)
Lemma tka_w_eq : forall B0 now, length B0 = Z.to_nat TW.W_LEN ->
  tick_ka_w B0 now =
  TW.upd (TW.upd B0 TW.A_S_next_keepalive_us (TW.put 8 (tka_vk B0 now)))
    TW.A_S_stats_tx_keepalives (TW.put 8 (TS0.u64 (TW.S_stats_tx_keepalives B0 + 1))).
Proof.
  intros B0 now L. unfold tick_ka_w. cbv zeta. fold (tka_v1 B0).
  assert (N1 : TW.S_next_keepalive_us (TW.set_S_next_keepalive_us B0 (tka_v1 B0)) = tka_v1 B0).
  { unfold TW.S_next_keepalive_us, TW.set_S_next_keepalive_us.
    rewrite tka_rd_put by first [exact L | tka_off].
    unfold tka_v1, TS0.u64. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Zmod_mod. }
  assert (K1 : TW.S_cfg_keepalive_ms (TW.set_S_next_keepalive_us B0 (tka_v1 B0)) = TW.S_cfg_keepalive_ms B0).
  { unfold TW.S_cfg_keepalive_ms, TW.set_S_next_keepalive_us. apply rd_upd_W; first [exact L | tka_off]. }
  rewrite N1, K1. unfold tka_vk.
  destruct (tka_v1 B0 <=? now).
  - set (v2 := TS0.u64 (now + TS0.ms_m (TW.S_cfg_keepalive_ms B0))).
    assert (E2 : TW.set_S_next_keepalive_us (TW.set_S_next_keepalive_us B0 (tka_v1 B0)) v2 =
                 TW.upd B0 TW.A_S_next_keepalive_us (TW.put 8 v2)).
    { unfold TW.set_S_next_keepalive_us. apply TWL.upd_upd_same.
      - tka_off.
      - rewrite !TWL.length_put. reflexivity.
      - rewrite L, Z2Nat.id by (unfold TW.W_LEN; lia). tka_off. }
    rewrite E2.
    assert (T2 : TW.S_stats_tx_keepalives (TW.upd B0 TW.A_S_next_keepalive_us (TW.put 8 v2)) =
                 TW.S_stats_tx_keepalives B0).
    { unfold TW.S_stats_tx_keepalives. apply rd_upd_W; first [exact L | tka_off]. }
    rewrite T2. reflexivity.
  - assert (T2 : TW.S_stats_tx_keepalives (TW.set_S_next_keepalive_us B0 (tka_v1 B0)) =
                 TW.S_stats_tx_keepalives B0).
    { unfold TW.S_stats_tx_keepalives, TW.set_S_next_keepalive_us. apply rd_upd_W; first [exact L | tka_off]. }
    rewrite T2. reflexivity.
Qed.

Lemma tka_len : forall B0 now, length B0 = Z.to_nat TW.W_LEN -> length (tick_ka_w B0 now) = Z.to_nat TW.W_LEN.
Proof.
  intros B0 now L. rewrite (tka_w_eq B0 now L).
  apply len_upd_W; [apply len_upd_W; first [exact L | tka_off] | tka_off | tka_off].
Qed.

(* A read at k' of n bytes outside both stores. *)
Lemma tka_rd_out : forall B0 now k' (n : nat), length B0 = Z.to_nat TW.W_LEN -> 0 <= k' ->
  (k' + Z.of_nat n <= TW.A_S_next_keepalive_us \/
   (TW.A_S_next_keepalive_us + 8 <= k' /\ k' + Z.of_nat n <= TW.A_S_stats_tx_keepalives) \/
   TW.A_S_stats_tx_keepalives + 8 <= k') ->
  TW.u_at (tick_ka_w B0 now) k' n = TW.u_at B0 k' n.
Proof.
  intros B0 now k' n L Hk Hd. rewrite (tka_w_eq B0 now L).
  assert (L1 : length (TW.upd B0 TW.A_S_next_keepalive_us (TW.put 8 (tka_vk B0 now))) = Z.to_nat TW.W_LEN)
    by (apply len_upd_W; first [exact L | tka_off]).
  rewrite rd_upd_W; [| exact L1 | tka_off | tka_off | exact Hk | rewrite TWL.length_put; tka_off].
  apply rd_upd_W; [exact L | tka_off | tka_off | exact Hk | rewrite TWL.length_put; tka_off].
Qed.

Lemma tka_gfn : forall B0 now, length B0 = Z.to_nat TW.W_LEN -> TW.g_fail_next (tick_ka_w B0 now) = TW.g_fail_next B0.
Proof.
  intros B0 now L. unfold TW.g_fail_next. apply tka_rd_out; [exact L | unfold TW.OFF_g_fail_next; lia |].
  right; right. unfold TW.OFF_g_fail_next. tka_off.
Qed.

(* The invariants send_data asks, (1) and (4), read no byte of the two stores. *)
Lemma tka_inv : forall B0 now, length B0 = Z.to_nat TW.W_LEN -> tick_runinv B0 ->
  (TW.M_fly_on (tick_ka_w B0 now) <> 0 -> TW.M_fly_len (tick_ka_w B0 now) <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd (tick_ka_w B0 now) -> TW.Cmd_st (tick_ka_w B0 now) s = TC.PENDING ->
     TW.Cmd_len (tick_ka_w B0 now) s <= DSpec.SPEC_CMD_MAX).
Proof.
  intros B0 now L (I1 & _ & I4 & _).
  assert (Fo : TW.M_fly_on (tick_ka_w B0 now) = TW.M_fly_on B0).
  { unfold TW.M_fly_on, TW.s32_at. f_equal. apply tka_rd_out; [exact L | unfold TW.A_M_fly_on, TW.OFF_M; lia |].
    left. unfold TW.A_M_fly_on, TW.OFF_M. tka_off. }
  assert (Fl : TW.M_fly_len (tick_ka_w B0 now) = TW.M_fly_len B0).
  { unfold TW.M_fly_len. apply tka_rd_out; [exact L | unfold TW.A_M_fly_len, TW.OFF_M; lia |].
    left. unfold TW.A_M_fly_len, TW.OFF_M. tka_off. }
  assert (Fn : TW.g_ncmd (tick_ka_w B0 now) = TW.g_ncmd B0).
  { unfold TW.g_ncmd. apply tka_rd_out; [exact L | unfold TW.OFF_g_ncmd; lia |].
    right; right. unfold TW.OFF_g_ncmd. tka_off. }
  rewrite Fo, Fl, Fn. split; [exact I1|].
  intros s Hs Hst.
  assert (Fs : TW.Cmd_st (tick_ka_w B0 now) s = TW.Cmd_st B0 s).
  { unfold TW.Cmd_st, TW.s32_at. f_equal. apply tka_rd_out; [exact L | tka_off |]. right; right. tka_off. }
  assert (Fc : TW.Cmd_len (tick_ka_w B0 now) s = TW.Cmd_len B0 s).
  { unfold TW.Cmd_len. apply tka_rd_out; [exact L | tka_off |]. right; right. tka_off. }
  rewrite Fs in Hst. rewrite Fc. exact (I4 s Hs Hst).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written range                                                *)
(* ------------------------------------------------------------------ *)

Ltac tka_cst :=
  unfold TW.A_S_host_counter, TW.A_S_inflight_frame, TW.A_S_inflight_len, TW.A_S_inflight, TW.A_S_inflight_counter,
    TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.A_S_stats_tx_data, TW.A_S_stats_tx_frames, SENDDATA_CAP,
    TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka, TW.A_M_last_display,
    TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter, TW.A_M_fly_retries, TW.A_M_fly_sent,
    TW.A_M_fly_len, TW.A_M_fly_frame, TC.SPEC_MAX_FRAME, TC.CMDS_MAX, TW.A_Cmd_st in *;
  unfold TA_g_s, TA_GOT, TA_M, TA_g_fail_next, TA_g_last_counter, TA_g_cmd, TA_g_q, TA_g_nq,
    TW.OFF_g_s, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_fail_next, TW.OFF_g_last_counter, TW.OFF_g_cmd, TW.OFF_g_q,
    TW.OFF_g_nq, TW.SZ_g_s, TW.SZ_GOT, TW.SZ_M, TW.SZ_g_last_counter, TW.SZ_g_cmd, TW.SZ_g_q, TW.SZ_g_nq in *.

(* Every byte send_data may store is a byte of G. *)
Lemma tka_sdwr_G : forall a, senddata_wr a -> inG TG.G_HARNESS a.
Proof.
  intros a H.
  assert (HG : forall o b n, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a)
    by (intros o b n Hin Hr; unfold inG; apply Exists_exists; exists (b, n);
        split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]).
  unfold senddata_wr, iosend_wr in H.
  repeat match type of H with _ \/ _ => destruct H as [H | H] end;
  try match type of H with ex _ => destruct H as (s & Hs & H) end;
  unfold twa_fld in H;
  first
  [ apply (HG _ _ _ TMAP_A_g_s); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_GOT); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_M); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_g_fail_next); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_g_last_counter); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_g_cmd); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_g_q); tka_cst; lia
  | apply (HG _ _ _ TMAP_A_g_nq); tka_cst; lia ].
Qed.

(* send_data's written range is a row of tick_wr. *)
Lemma tka_sdwr_tick : forall Bw a, senddata_wr a -> tick_wr Bw a.
Proof. intros Bw a H. unfold tick_wr. do 19 right. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The program points after the cut: +0x91c (the join after the keepalive test) and +0x95c (send_data's return). *)
Definition TKA_C : Z := AF_diginet_session_tick + 0x91c.
Definition TKA_R : Z := AF_diginet_session_tick + 0x95c.
(* The shadow bytes of s + 24, s + 184 and s + 18216. *)
Definition TKA_SH24 : Z := 2148220731.
Lemma TKA_SH24_eq : TKA_SH24 = SHADOW_OFF + (TICK_S + 24) / 8.
Proof. reflexivity. Qed.
Definition TKA_SH184 : Z := 2148220751.
Lemma TKA_SH184_eq : TKA_SH184 = SHADOW_OFF + (TICK_S + 184) / 8.
Proof. reflexivity. Qed.
Definition TKA_SH18216 : Z := 2148223005.
Lemma TKA_SH18216_eq : TKA_SH18216 = SHADOW_OFF + (TICK_S + 18216) / 8.
Proof. reflexivity. Qed.

(* The two bytes the run from the cut stores: ka's shadow byte and ka. *)
Definition tka_Z (F a : Z) : Prop := a = SHADOW_OFF + F / 8 + 46 \/ a = F + 368.
(* The two words the run from +0x91c stores: g_s.next_keepalive_us and g_s.stats.tx_keepalives. *)
Definition tka_Zc (a : Z) : Prop := (TICK_S + 184 <= a < TICK_S + 192) \/ (TICK_S + 18216 <= a < TICK_S + 18224).

Definition TKA_Bx : sv := SLit 0.
Definition TKA_B0 : Z * Z := (0, 0).

(* At the cut: s3 (atom 19) the frame's shadow address, s11 (atom 27) the frame, s1 (atom 9) the realigned sp; atom 32
   g_s.cfg.keepalive_ms, atom 33 now. *)
Definition tka_rA_sh : YP09.region := YP09.mkRegion (Some 19%nat) 46 47 46 47 [].
Definition tka_rA_ka : YP09.region := YP09.mkRegion (Some 27%nat) 368 369 368 369 [].
Definition tka_rA_shc : YP09.region :=
  YP09.mkRegion None TKA_SH24 (TKA_SH24 + 1) 0 0 [YP09.mkChunk TKA_SH24 (YP09.CVal 1 (SLit 0))].
Definition tka_rA_cfg : YP09.region :=
  YP09.mkRegion None (TICK_S + 24) (TICK_S + 28) 0 0 [YP09.mkChunk (TICK_S + 24) (YP09.CVal 4 (SOff 32 0))].
Definition tka_r_now : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 33 0))].
Definition TKA_FACTS_A : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (27%nat, mkAF 4096 (2 ^ 47) 6); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition TKA_REGS_A : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tkaA : sstate :=
  mkSS TICK_KA TKA_REGS_A [tka_rA_sh; tka_rA_ka; tka_rA_shc; tka_rA_cfg; tka_r_now] None TKA_FACTS_A.
Definition tka_valsA (B0 : list byte) (now : Z) : list word :=
  [Z_to_bv 64 (TW.S_cfg_keepalive_ms B0); Z_to_bv 64 now].

(* At +0x91c: a3 = the shadow address of s + 184, a7 = s + 18144, s4 = s, s8 = the shadow base; atom 32
   g_s.stats.tx_keepalives, atom 33 now. *)
Definition tka_rC_shnk : YP09.region :=
  YP09.mkRegion None TKA_SH184 (TKA_SH184 + 1) 0 0 [YP09.mkChunk TKA_SH184 (YP09.CVal 1 (SLit 0))].
Definition tka_rC_nk : YP09.region :=
  YP09.mkRegion None (TICK_S + 184) (TICK_S + 192) (TICK_S + 184) (TICK_S + 192) [].
Definition tka_rC_shtx : YP09.region :=
  YP09.mkRegion None TKA_SH18216 (TKA_SH18216 + 1) 0 0 [YP09.mkChunk TKA_SH18216 (YP09.CVal 1 (SLit 0))].
Definition tka_rC_tx : YP09.region :=
  YP09.mkRegion None (TICK_S + 18216) (TICK_S + 18224) (TICK_S + 18216) (TICK_S + 18224)
    [YP09.mkChunk (TICK_S + 18216) (YP09.CVal 8 (SOff 32 0))].
Definition TKA_FACTS_C : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition TKA_REGS_C : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 13) (SLit TKA_SH184)) (Z_to_bv 5 17) (SLit (TICK_S + 18144)))
    (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tkaC : sstate :=
  mkSS TKA_C TKA_REGS_C [tka_rC_shnk; tka_rC_nk; tka_rC_shtx; tka_rC_tx; tka_r_now] None TKA_FACTS_C.
Definition tka_valsC (B0 : list byte) (now : Z) : list word :=
  [Z_to_bv 64 (TW.S_stats_tx_keepalives B0); Z_to_bv 64 now].

(* At +0x95c: ka's shadow byte, written once more. *)
Definition ss_tkaD : sstate :=
  mkSS TKA_R sr_atoms [tka_rA_sh] None (mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).

(* A one-byte view of v is the stored byte v. *)
Lemma tka_vm_aview : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
  intros H m a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0.
  rewrite Z.add_0_r in H0. rewrite H0. cbn [option_map]. rewrite (tw_le_byte1 v Hr).
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* One byte at an 8-aligned address whose shadow byte is 1 is addressable. *)
Lemma tka_ra_one : forall (rd : Z -> option Z) q, q mod 8 = 0 -> rd (SHADOW_OFF + q / 8) = Some 1 ->
  range_addressable rd SHADOW_OFF q 1.
Proof.
  intros rd q Hq Hs x Hx. assert (x = q) by lia. subst x.
  exists 1. split; [unfold shadow_of_addr; exact Hs |]. right. rewrite Hq. lia.
Qed.

(* A val_mem of n bytes, read byte by byte through the view. *)
Lemma tka_vm_rd : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v j,
  val_mem tfibsegs (mrestrict H m) a n v -> (j < n)%nat -> aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
  unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The world relation after the two stores of g_s.next_keepalive_us (8 bytes of v1) and g_s.stats.tx_keepalives
   (8 bytes of v2), every other byte of the table kept. *)
Lemma tka_tw_two : forall (rd0 rd2 : Z -> option Z) Bx v1 v2,
  tw_at TMAP_A rd0 Bx ->
  (forall j, (j < 8)%nat -> rd2 (TA_g_s + 184 + Z.of_nat j) = Some (YO0f.le_byte v1 8 j)) ->
  (forall j, (j < 8)%nat -> rd2 (TA_g_s + 18216 + Z.of_nat j) = Some (YO0f.le_byte v2 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ tka_Zc x -> rd2 x = rd0 x) ->
  tw_at TMAP_A rd2
    (TW.upd (TW.upd Bx TW.A_S_next_keepalive_us (TW.put 8 v1)) TW.A_S_stats_tx_keepalives (TW.put 8 v2)).
Proof.
  intros rd0 rd2 Bx v1 v2 Htw N1 N2 K.
  set (rdM := fun x => if (TICK_S + 18216 <=? x) && (x <? TICK_S + 18224) then rd0 x else rd2 x).
  change TW.A_S_stats_tx_keepalives with (TW.OFF_g_s + 18216).
  change TW.A_S_next_keepalive_us with (TW.OFF_g_s + 184).
  apply (tw_write TMAP_A rdM rd2 _ TW.OFF_g_s TA_g_s TW.SZ_g_s 18216 8 v2 TMAP_A_ok);
    [| exact TMAP_A_g_s | lia | unfold TW.SZ_g_s; lia | exact N2 |].
  - apply (tw_write TMAP_A rd0 rdM Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 184 8 v1 TMAP_A_ok Htw TMAP_A_g_s);
      [lia | unfold TW.SZ_g_s; lia | |].
    + intros j Hj. unfold rdM.
      replace ((TICK_S + 18216 <=? TA_g_s + 184 + Z.of_nat j) && (TA_g_s + 184 + Z.of_nat j <? TICK_S + 18224))
        with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; unfold TICK_S; lia).
      exact (N1 j Hj).
    + intros x Hx Hn. unfold rdM.
      destruct ((TICK_S + 18216 <=? x) && (x <? TICK_S + 18224)) eqn:Et; [reflexivity|].
      apply K; [exact Hx|]. intros [Hz | Hz]; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hn; unfold TICK_S in *; lia|].
      apply andb_false_iff in Et. destruct Et as [Et | Et]; [apply Z.leb_gt in Et | apply Z.ltb_ge in Et]; lia.
  - intros x Hx Hn. unfold rdM.
    replace ((TICK_S + 18216 <=? x) && (x <? TICK_S + 18224)) with false; [reflexivity|].
    symmetry. apply andb_false_iff. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hn. unfold TICK_S in *.
    destruct (Z_lt_le_dec x (TA_g_s + 18216)) as [h|h]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of a run: the 32 registers, then the values vals. *)
Definition tka_E (regs : bvmap 5 word) (vals : list word) : env := Eimg (PI := PI_transport) (Ereg regs vals).

Lemma tka_entryA0 : forall ly S (W : world segs) regs mem md B0 now sp1 F,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B0 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 27 = w64 F ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) -> F + 2048 <= sp1 ->
  apresent (w_H W) mem (F + 368) -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + 46) ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tka_E regs (tka_valsA B0 now))
    (mkSS TICK_KA sr_atoms [tka_rA_sh; tka_rA_ka; tka_rA_shc; tka_rA_cfg; tka_r_now] None TKA_FACTS_A)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_KA)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md B0 now sp1 F HTC HAR Htw R9 R19 R27 Hs1 Hs2 Hs3 HF0 HF64 HFc HFapp HFG HFs Hpk Hpsh Rn
    Hnow.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := tka_E regs (tka_valsA B0 now)).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tka_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U27 : bv_unsigned (ew E 27) = F)
    by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (tka_valsA B0 now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tka_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth tka_valsA] in E32, E33.
  assert (Rk : 0 <= TW.S_cfg_keepalive_ms B0 < 2 ^ 32) by exact (TWL.u_at_range B0 TW.A_S_cfg_keepalive_ms 4).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : aview segs (w_H W) mem TKA_SH24 = Some 0).
  { replace TKA_SH24 with (FCells.shadow_addr (TICK_S + 24)) by reflexivity.
    apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR);
      [reflexivity | lia | unfold TW.SZ_g_s; lia | exact HTC]. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks tka_rA_sh tka_rA_ka tka_rA_shc
        tka_rA_cfg tka_r_now base_val]; rewrite ?U9, ?U19, ?U27.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs).
      replace (SHADOW_OFF + F / 8 + o) with (SHADOW_OFF + F / 8 + 46) by lia. exact Hpsh.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). replace (F + o) with (F + 368) by lia. exact Hpk.
    + split; [unfold TKA_SH24; lia|]. split; [unfold TKA_SH24; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TKA_SH24 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (AE2y.val_mem1_of_aview _ _ _ _ ZSH).
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 24) 4 (SOff 32 0) (TW.S_cfg_keepalive_ms B0));
        [apply DEN; [exact E32 | lia] | exact Rk | lia |].
      replace (0 + (TICK_S + 24)) with (TA_g_s + 24) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_A B0 TW.OFF_g_s TA_g_s TW.SZ_g_s 24 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 33 0) now); [apply DEN; [exact E33 | exact Rn] | exact Rn | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem (sp1 + 56) now Hnow).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, tka_rA_sh, tka_rA_ka, tka_rA_shc, tka_rA_cfg, tka_r_now.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, TKA_SH24, SHADOW_OFF, TICK_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold TKA_FACTS_A, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U19, U27, E32.
    rewrite (unsigned_lit_small (TW.S_cfg_keepalive_ms B0)) by lia.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    rewrite ?Z.mod_1_r. unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tka_entryA : forall ly S (W : world segs) regs mem md B0 now sp1 F,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B0 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 27 = w64 F ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) -> F + 2048 <= sp1 ->
  apresent (w_H W) mem (F + 368) -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + 46) ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tka_E regs (tka_valsA B0 now)) ss_tkaA
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_KA)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md B0 now sp1 F HTC HAR Htw R9 R19 R27 R20 R24 Hs1 Hs2 Hs3 HF0 HF64 HFc HFapp HFG HFs Hpk
    Hpsh Rn Hnow.
  rewrite restrict_mkst_fx.
  pose proof (tka_entryA0 ly S W regs mem md B0 now sp1 F HTC HAR Htw R9 R19 R27 Hs1 Hs2 Hs3 HF0 HF64 HFc HFapp HFG
    HFs Hpk Hpsh Rn Hnow) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

Lemma tka_entryC0 : forall ly S (W : world segs) regs mem md B0 now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B0 ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tka_E regs (tka_valsC B0 now))
    (mkSS TKA_C sr_atoms [tka_rC_shnk; tka_rC_nk; tka_rC_shtx; tka_rC_tx; tka_r_now] None TKA_FACTS_C)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKA_C)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md B0 now sp1 HTC HAR Htw R9 Hs1 Hs2 Hs3 Rn Hnow.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := tka_E regs (tka_valsC B0 now)).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tka_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (tka_valsC B0 now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tka_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth tka_valsC] in E32, E33.
  assert (Rx : 0 <= TW.S_stats_tx_keepalives B0 < 2 ^ 64)
    by exact (TWL.u_at_range B0 TW.A_S_stats_tx_keepalives 8).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZS1 : aview segs (w_H W) mem TKA_SH184 = Some 0).
  { replace TKA_SH184 with (FCells.shadow_addr (TICK_S + 184)) by reflexivity.
    apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR);
      [reflexivity | lia | unfold TW.SZ_g_s; lia | exact HTC]. }
  assert (ZS2 : aview segs (w_H W) mem TKA_SH18216 = Some 0).
  { replace TKA_SH18216 with (FCells.shadow_addr (TICK_S + 18216)) by reflexivity.
    apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR);
      [reflexivity | lia | unfold TW.SZ_g_s; lia | exact HTC]. }
  assert (WG : forall o, TICK_S <= o < TICK_S + TW.SZ_g_s -> writable_at segs (mrestrict (w_H W) mem) (0 + o)).
  { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
    unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TICK_S in *; cbn [fst snd]; lia]. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks tka_rC_shnk tka_rC_nk tka_rC_shtx
        tka_rC_tx tka_r_now base_val]; rewrite ?U9.
    + split; [unfold TKA_SH184; lia|]. split; [unfold TKA_SH184; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TKA_SH184 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (AE2y.val_mem1_of_aview _ _ _ _ ZS1).
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply WG. unfold TW.SZ_g_s. lia.
    + split; [unfold TKA_SH18216; lia|]. split; [unfold TKA_SH18216; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TKA_SH18216 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (AE2y.val_mem1_of_aview _ _ _ _ ZS2).
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|].
      split; [intros o Ho; apply WG; unfold TW.SZ_g_s; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 18216) 8 (SOff 32 0) (TW.S_stats_tx_keepalives B0));
        [apply DEN; [exact E32 | exact Rx] | exact Rx | lia |].
      replace (0 + (TICK_S + 18216)) with (TA_g_s + 18216) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_A B0 TW.OFF_g_s TA_g_s TW.SZ_g_s 18216 8 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 33 0) now); [apply DEN; [exact E33 | exact Rn] | exact Rn | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem (sp1 + 56) now Hnow).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, tka_rC_shnk, tka_rC_nk, tka_rC_shtx, tka_rC_tx, tka_r_now.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TKA_SH184, TKA_SH18216, TICK_S, TA_g_s in *.
    repeat split; first [exact I | lia].
  - unfold TKA_FACTS_C, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tka_entryC : forall ly S (W : world segs) regs mem md B0 now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B0 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 13 = w64 TKA_SH184 -> YK11.getr regs 17 = w64 (TICK_S + 18144) ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tka_E regs (tka_valsC B0 now)) ss_tkaC
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKA_C)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md B0 now sp1 HTC HAR Htw R9 R13 R17 R20 R24 Hs1 Hs2 Hs3 Rn Hnow.
  rewrite restrict_mkst_fx.
  pose proof (tka_entryC0 ly S W regs mem md B0 now sp1 HTC HAR Htw R9 Hs1 Hs2 Hs3 Rn Hnow) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 13) TKA_SH184 H0 R13 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 17) (TICK_S + 18144) H1 R17 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H2 R20 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H3 R24 eq_refl) as H4.
  exact H4.
Qed.

Lemma tka_entryD : forall (W : world segs) regs mem F,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  apresent (w_H W) mem (SHADOW_OFF + F / 8 + 46) ->
  st_ok_pi segs VAL (tka_E regs []) ss_tkaD
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKA_R)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R19 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := tka_E regs []).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (unfold E, tka_E; rewrite (ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; unfold w64;
        apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_tkaD.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks tka_rA_sh base_val]. rewrite U19.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs).
    replace (SHADOW_OFF + F / 8 + o) with (SHADOW_OFF + F / 8 + 46) by lia. exact Hpsh.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End k.
