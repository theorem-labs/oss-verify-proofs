(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 500 of its 595 lines of code are new or changed and 1115 lines of the source are left out. *)
(* TickBStep: Theorem tick_step : tick_step_stmt (lib/B/Prog/TickCutB.v), the step piece of the walk of
   diginet_session_tick on fuzz_transport.asan-ubsan (0x8909c = transportb_sigma TB_diginet_session_tick,
   AF_diginet_session_tick = 0x7dfc of lib/B/Prog/DgnTransportBList.v): code +0x2a4 .. +0x348 (0x89340 .. 0x893e4),
   the ack-timeout step of :430-443, from the step cut tick_step_at to the cuts tick_tail_at, tick_retx_at and
   tick_ackl_at. No call. The runs are the position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x over the caller's G journal, from one symbolic state whose registers s4 and s8 are pinned to s and
   the shadow base, and whose three regions hold the five g_s fields the step loads (s + 28 ack_timeout_ms, s + 32
   max_retries, s + 212 inflight, s + 1748 inflight_retries, s + 1752 inflight_sent_us: the world's bytes, TWorldG.v
   tw_read_val at TWorldB.v TMAP_B), the five shadow bytes of their checks (0: trans_tick_cells read by
   DgnTransportBCg.v decode_zshadow_rd), and the slots s1 + 40 .. s1 + 63 (now at s1 + 56: tick_run_cur;
   s1 + 40 .. s1 + 55 writable):
     run 1  +0x2a4 .. +0x2c8  t0 = s + 212, t1 = its shadow address, the check, inflight, a7 = s + 18144, `beqz a0`;
     run 2  +0x2cc .. +0x30c  the checks of s + 1752 (a3 = its shadow address) and s + 28, inflight_sent_us,
                              ack_timeout_ms, now, `bltu now - sent, ack * 1000`;
     run 3  +0x310 .. +0x348  the checks of s + 1748 (a4 = its shadow address) and s + 32, retries (t2), max_retries,
                              the stores of t0 at s1 + 48 and t1 at s1 + 40, `bgeu t2, a2`.
   No inflight frame (+0x2c8) or no ack timeout (+0x30c) go to the tail cut with B0 = Bw (TickCutB.v tick_go_eq); a
   timeout with a retry left falls through to the retransmit cut (tick_retx_m), else `bgeu` goes to the ack-lost cut
   (tick_ackl_m); both carry the two saved words (tick_t01_at, read off the run's stack region). The model's tests are
   the code's branches: the sign-extended inflight against 0, TModel/TSess0.v ms_m and u64 for the timeout (lib/A/Prog/
   m_tick.v mt_neg', image-free), and the uint32_t order of the two sign-extended retry loads. Only s1 + 40 .. s1 + 55
   change (ts_KW); the cut's facts move across them by TransportGCg.v dk_kept_step_g (ts_pre_move). The view lemmas,
   the run tactics and the sign-extension test come from lib/B/Prog/TickBTail.v, loaded by Require only (its theorem
   tick_tail would hide the model function tick_tail). The structure is image A's step piece (lib/A/Prog/TickStep.v)
   at image B's pcs and names. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YE2y YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TickBTail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut m_tick.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
Module TT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TickBTail.
Module MTA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_tick.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the symbolic state at the step cut ---- *)

(* The shadow byte of s + 28; s + 32, s + 212, s + 1748 and s + 1752 have bytes 1, 23, 215 and 216 after it. *)
Definition TS_SH : Z := SHADOW_OFF + (TICK_S + 28) / 8.
Lemma TS_SH_eq : TS_SH = 2148220619.
Proof. reflexivity. Qed.
Definition TS_R_gs : YP09.region :=
  YP09.mkRegion None (TICK_S + 28) (TICK_S + 1760) 0 0
    [YP09.mkChunk (TICK_S + 28) (YP09.CVal 4 (SOff 32 0)); YP09.mkChunk (TICK_S + 32) (YP09.CVal 4 (SOff 33 0));
     YP09.mkChunk (TICK_S + 212) (YP09.CVal 4 (SOff 34 0)); YP09.mkChunk (TICK_S + 1748) (YP09.CVal 4 (SOff 35 0));
     YP09.mkChunk (TICK_S + 1752) (YP09.CVal 8 (SOff 36 0))].
Definition TS_R_sh : YP09.region :=
  YP09.mkRegion None TS_SH (TS_SH + 217) 0 0
    [YP09.mkChunk TS_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TS_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TS_SH + 23) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TS_SH + 215) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TS_SH + 216) (YP09.CVal 1 (SLit 0))].
(* The slots s1 + 40 .. s1 + 63: now at s1 + 56 (atom 37), the two stores' slots writable. *)
Definition TS_R_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 64 40 56 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 37 0))].
Definition TS_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
(* s4 = s, s8 = the shadow base. *)
Definition TS_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_ts : sstate := mkSS TICK_STEP TS_REGS [TS_R_gs; TS_R_sh; TS_R_stk] None TS_FACTS.

(* ---- the tests, in the model's terms ---- *)

(* `beqz` of a sign-extended uint32_t load. *)
Lemma ts_br_eq : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (bv_swrap 32 v =? c).
Proof.
intros E n v c H R Hc. cbn [branch_taken]. rewrite (TT.tt_sext E n v H R).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c).
pose proof (TT.tt_swrap_range v). rewrite TT.tt_eqb_s by lia. reflexivity.
Qed.

(* v * 1000 (mod 2^64): the model's ms_m. *)
Lemma ts_ms : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SMd M_MUL (SOff n 0) (SLit 1000))) = TS0.ms_m x.
Proof.
intros E n x H Rx. cbn [sv_denot mul_div].
rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, TS0.ms_m, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)), (Z.mod_small 1000 (2 ^ 64)) by lia. reflexivity.
Qed.

(* The ack-timeout test (+0x30c, `bltu now - sent, ack * 1000`). *)
Lemma ts_br_tmo : forall E now sent ack,
  ew E 37 = Z_to_bv 64 now -> ew E 36 = Z_to_bv 64 sent -> ew E 32 = Z_to_bv 64 ack ->
  0 <= now < 2 ^ 64 -> 0 <= sent < 2 ^ 64 -> 0 <= ack < 2 ^ 32 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 36 0) (SLit (-1))) (SOff 37 0)))
    (sv_denot E (SMd M_MUL (SOff 32 0) (SLit 1000)))
  = negb (TS0.ms_m ack <=? TS0.u64 (now - sent)).
Proof.
intros E now sent ack H37 H36 H32 Rn Rs Ra. cbn [branch_taken]. unfold bv_ltu.
rewrite (MTA.mt_neg' E 37 36 now sent H37 H36 Rn Rs).
rewrite (ts_ms E 32 ack H32 ltac:(lia)).
rewrite Z.leb_antisym, negb_involutive. reflexivity.
Qed.

(* The retry test (+0x348, `bgeu` of two sign-extended uint32_t loads): the uint32_t order. *)
Lemma ts_br_retry : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
  0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  branch_taken BC_GEU (sv_denot E (SExt true 32 (SOff n1 0))) (sv_denot E (SExt true 32 (SOff n2 0)))
  = negb (x <? y).
Proof.
intros E n1 n2 x y H1 H2 R1 R2. cbn [branch_taken].
rewrite (TT.tt_sext E n1 x H1 R1), (TT.tt_sext E n2 y H2 R2). f_equal.
unfold bv_ltu. rewrite !Z_to_bv_unsigned.
unfold bv_swrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec x y) as [Lt | Ge]; [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* tick_go by branch (TickCutB.v tick_go_eq). *)
Lemma ts_go_tail0 : forall I F Bw now, TW.S_inflight Bw = 0 -> tick_go I F Bw now = tick_tail I F Bw now.
Proof. intros I F Bw now H. rewrite tick_go_eq, H. reflexivity. Qed.

Lemma ts_go_tail1 : forall I F Bw now,
  (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw)) = false ->
  tick_go I F Bw now = tick_tail I F Bw now.
Proof. intros I F Bw now H. rewrite tick_go_eq, H, andb_false_r. reflexivity. Qed.

Lemma ts_go_retx : forall I F Bw now, TW.S_inflight Bw <> 0 ->
  (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw)) = true ->
  (TW.S_inflight_retries Bw <? TW.S_cfg_max_retries Bw) = true ->
  tick_go I F Bw now = tick_retx_m I F Bw now.
Proof.
intros I F Bw now H1 H2 H3. rewrite tick_go_eq, H2, H3, (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma ts_go_ackl : forall I F Bw now, TW.S_inflight Bw <> 0 ->
  (TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw) <=? TS0.u64 (now - TW.S_inflight_sent_us Bw)) = true ->
  (TW.S_inflight_retries Bw <? TW.S_cfg_max_retries Bw) = false ->
  tick_go I F Bw now = tick_ackl_m I F Bw now.
Proof.
intros I F Bw now H1 H2 H3. rewrite tick_go_eq, H2, H3, (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Section ts. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The only bytes the piece writes: s1 + 40 .. s1 + 55 (t1 and t0, +0x340 .. +0x344). *)
Definition ts_Z (sp1 x : Z) : Prop := sp1 + 40 <= x < sp1 + 56.
(* What the piece keeps, from the cut's memory memc to a memory m: every other byte's view, and presence. *)
Definition ts_KW (W : world segs) (sp1 : Z) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ ts_Z sp1 a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma ts_KW_refl : forall (W : world segs) sp1 m, ts_KW W sp1 m m.
Proof. intros W sp1 m. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

(* A run whose writable windows lie in ts_Z keeps ts_KW. *)
Lemma ts_KW_step : forall E rs (W : world segs) sp1 memc (m m' : word -> option byte),
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= x < base_val E b + whi -> ts_Z sp1 x) ->
  ts_KW W sp1 memc m ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  ts_KW W sp1 memc m'.
Proof.
intros E rs W sp1 memc m m' Hw [K1 K2] Hfr Hg. split.
- intros a Ha Hn. rewrite (kept_of_frame E rs (w_H W) m m' (ts_Z sp1) Hfr Hw a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* The facts of the step cut move across the two stores at s1 + 40 .. s1 + 55: they lie in the call's stack window
   (TransportGCg.v dk_kept_step_g), below the 13 saved words and apart from now at s1 + 56, the frame's flag word, G
   and the world's bytes. *)
Lemma ts_pre_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs now Bw pos sp1 F
    S2 mem2 md2 mem3 md3,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - TICK_STK -> spZ regs - TICK_STK <= sp1 + 40 -> sp1 + 64 <= spZ regs - 104 ->
  spZ regs <= 2 ^ 47 -> 0 <= F -> F + TICK_FBYTES <= alloc_ceiling ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  ts_KW W sp1 mem2 mem3 ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3
  LAWS HGX HARc Hce Hw1 Hw2 H47 HF0 HFc
  (((HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) & Hnw) & Hbl & HGK & Htw) HJ3 [KP GR].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TCA.TICK_FBYTES in *.
refine (conj (conj (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))) _)
  (conj Hbl (conj _ _))).
- apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc mem2 mem3
    (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw) (ts_Z sp1) HARc HK).
  + intros a Ha Hn. exact (KP a Ha Hn).
  + exact GR.
  + intros a Ha _. unfold ts_Z in Ha. lia.
  + intros b m i Hb Hi Hz. exfalso. unfold ts_Z in Hz.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & H4096 & Hbc & _). lia.
  + intros a Ha Hi _ _ _. exfalso. unfold ts_Z in Ha. pose proof (transportb_segs_low a Hi) as Hl.
    unfold kLowMemEnd in *. lia.
  + intros cid pos0 a Hin Hr Ha. exfalso. unfold ts_Z in Ha.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HARc Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
- rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho). apply YCbq.rdword_ext.
  intros i Hi.
  assert (Hb : 8 <= fst o <= 104).
  { unfold TCA.TICK_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho. }
  apply KP; [lia | unfold ts_Z; lia].
- rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KP; [lia | unfold ts_Z; lia].
- rewrite <- Hnw. apply YCbq.rdword_ext. intros i Hi. apply KP; [lia | unfold ts_Z; lia].
- intros a Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd in Hl.
  rewrite (KP a ltac:(lia) ltac:(unfold ts_Z; lia)). exact (HGK a Hg).
- apply (tw_kept TMAP_B (aview segs (w_H W) mem2)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KP; [lia | unfold ts_Z; lia].
Qed.

(* The walk's valuation at the cut: the 32 registers, then ack_timeout_ms, max_retries, inflight (4 raw bytes),
   inflight_retries and inflight_sent_us of the world Bw, and now. *)
Definition ts_vals (Bw : list byte) (now : Z) : list word :=
  [Z_to_bv 64 (TW.S_cfg_ack_timeout_ms Bw); Z_to_bv 64 (TW.S_cfg_max_retries Bw);
   Z_to_bv 64 (TW.u_at Bw TW.A_S_inflight 4); Z_to_bv 64 (TW.S_inflight_retries Bw);
   Z_to_bv 64 (TW.S_inflight_sent_us Bw); Z_to_bv 64 now].
Definition ts_E (regs : bvmap 5 word) (Bw : list byte) (now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (ts_vals Bw now)).

Lemma ts_entry0 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  (forall a, sp1 + 40 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  st_ok_pi segs VAL (ts_E regs Bw now) (mkSS TICK_STEP sr_atoms [TS_R_gs; TS_R_sh; TS_R_stk] None TS_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_STEP)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw Hnw Rnow Hpw R9 Hsp Hsp32.
  set (E := ts_E regs Bw now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, ts_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (ts_vals Bw now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ts_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  cbn [Nat.add nth ts_vals] in E32, E33, E34, E35, E36, E37. clear EX.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 28) 4) as R32.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 32) 4) as R33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 212) 4) as R34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1748) 4) as R35.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1752) 8) as R36.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32, R33, R34, R35.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R36.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T H1 H2 H3. apply YE2y.val_mem1_of_aview.
    exact (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR H1 H2 H3 HTC). }
  assert (GS : forall o (n : nat), 0 <= o -> o + Z.of_nat n <= TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (0 + (TICK_S + o)) n (TW.u_at Bw (TW.OFF_g_s + o) n)).
  { intros o n Ho Hn. replace (0 + (TICK_S + o)) with (TB_g_s + o) by (unfold TICK_S; lia).
    exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s o n TMAP_B_ok Htw TMAP_B_g_s Ho Hn). }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TS_R_gs TS_R_sh TS_R_stk base_val];
      rewrite ?U9.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 28) 4 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 28) 4));
          [apply DEN; [exact E32 | lia] | exact R32 | lia |].
        exact (GS 28 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 32) 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 32) 4));
          [apply DEN; [exact E33 | lia] | exact R33 | lia |].
        exact (GS 32 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 212) 4 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 212) 4));
          [apply DEN; [exact E34 | lia] | exact R34 | lia |].
        exact (GS 212 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 1748) 4 (SOff 35 0) (TW.u_at Bw (TW.OFF_g_s + 1748) 4));
          [apply DEN; [exact E35 | lia] | exact R35 | lia |].
        exact (GS 1748 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 1752) 8 (SOff 36 0) (TW.u_at Bw (TW.OFF_g_s + 1752) 8));
          [apply DEN; [exact E36 | exact R36] | exact R36 | lia |].
        exact (GS 1752 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [rewrite TS_SH_eq; lia|]. split; [rewrite TS_SH_eq; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 TS_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + TS_SH) with (FCells.shadow_addr (TICK_S + 24)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TS_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TS_SH + 1)) with (FCells.shadow_addr (TICK_S + 32)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TS_SH + 23) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TS_SH + 23)) with (FCells.shadow_addr (TICK_S + 208)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TS_SH + 215) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TS_SH + 215)) with (FCells.shadow_addr (TICK_S + 1744)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TS_SH + 216) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TS_SH + 216)) with (FCells.shadow_addr (TICK_S + 1752)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
    + split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable segs). apply Hpw. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ sp1 56 8 (SOff 37 0) now);
          [apply DEN; [exact E37 | exact Rnow] | exact Rnow | lia |].
        exact (YCbq.val_mem_of_rdword segs (w_H W) mem (sp1 + 56) now Hnw).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TS_R_gs, TS_R_sh, TS_R_stk. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite TS_SH_eq. unfold TICK_S, TB_g_s. repeat split; first [exact I | lia].
  - unfold TS_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (A32 : 0 <= TW.S_cfg_ack_timeout_ms Bw < 2 ^ 32) by exact R32.
    assert (A33 : 0 <= TW.S_cfg_max_retries Bw < 2 ^ 32) by exact R33.
    assert (A34 : 0 <= TW.u_at Bw TW.A_S_inflight 4 < 2 ^ 32) by exact R34.
    assert (A35 : 0 <= TW.S_inflight_retries Bw < 2 ^ 32) by exact R35.
    rewrite U9, E32, E33, E34, E35, !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma ts_entry : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  (forall a, sp1 + 40 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (ts_E regs Bw now) ss_ts
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_STEP)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw Hnw Rnow Hpw R9 Hsp Hsp32 R20 R24.
  rewrite restrict_mkst_fx.
  pose proof (ts_entry0 ly S W regs mem md Bw now sp1 HTC HAR Htw Hnw Rnow Hpw R9 Hsp Hsp32) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

End ts.

(* After a run: the model generalized, ts_KW carried to the run's last memory (its windows: computed, each inside
   ts_Z sp1 by U9, the value of s1), the old machine states dropped, the current one named ms. *)
Ltac ts_after KW HS U9 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KW' := fresh "KWn" in let Hw := fresh "Hw" in
    lazymatch type of KW with ts_KW _ ?s1 _ _ =>
    assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows rs) ->
      base_val Ex b + wlo <= x < base_val Ex b + whi -> ts_Z s1 x)
    by (let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
        let Hin := fresh "Hin" in let Hx := fresh "Hx" in
        intros b wlo whi x Hin Hx;
        lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
        cbn [In] in Hin;
        repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9 in Hx;
          unfold ts_Z; lia |]);
        destruct Hin) end;
    pose proof (ts_KW_step Ex rs _ _ _ _ _ Hw KW HFr HG) as KW'; clear KW HFr HG Hw; rename KW' into KW end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.
(* The write rights of a run from ss_ts: the slots s1 + 40 .. s1 + 55 of the call's window. *)
Ltac ts_awr U9 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9 in Ha;
      first [lia | left; split; [unfold awr_byte; left; lia | lia]] |]);
  apply awr_ok_x_nil.

Section tsw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ts_holds : @tick_step_stmt fx rc B MT.
Proof.
unfold tick_step_stmt. intros TAIL RETX ACKL. unfold tick_step_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
  S2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof HFIX as (HJe & Hret & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf0 & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HPRE & Hm).
pose proof HPRE as (((HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFL) & Hnw) & Hbl & HGK & Htw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24) & R25).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TICK_STK = 8896) by reflexivity.
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47 /\ sp1 mod 32 = 0 /\ spZ regs - 224 <= sp1 <= spZ regs - 192).
{ rewrite Esp1. unfold TICK_FRAME, TICK_ALIGN in *.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  split; [lia|]. split; [rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity | lia]. }
assert (Hce : alloc_ceiling <= spZ regs - TICK_STK) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hpw : forall a, sp1 + 40 <= a < sp1 + 56 -> apresent (w_H W) mem2 a).
{ intros a Ha. destruct HK as (_ & _ & _ & _ & _ & K6). apply K6. lia. }
(* the moves of the cut's facts, from mem2 to the memory of a cut *)
assert (MOVE : forall mem3 md3,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  ts_KW W sp1 mem2 mem3 ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem3 md3).
{ intros mem3 md3 HJ3 KW3.
  exact (ts_pre_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3
    LAWS HGX HARc Hce ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFc HPRE HJ3 KW3). }
(* the valuation and the atoms *)
set (E0 := ts_E regs2 Bw now).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ts_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E0, ts_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (EX : forall j, (j < 6)%nat -> ew E0 (32 + j) = nth j (ts_vals Bw now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ts_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth ts_vals] in E32, E33, E34, E35, E36, E37. clear EX.
assert (R32 : 0 <= TW.S_cfg_ack_timeout_ms Bw < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_cfg_ack_timeout_ms 4).
assert (R33 : 0 <= TW.S_cfg_max_retries Bw < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_cfg_max_retries 4).
assert (R34 : 0 <= TW.u_at Bw TW.A_S_inflight 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_inflight 4).
assert (R35 : 0 <= TW.S_inflight_retries Bw < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_inflight_retries 4).
assert (R36 : 0 <= TW.S_inflight_sent_us Bw < 2 ^ 64) by exact (TWL.u_at_range Bw TW.A_S_inflight_sent_us 8).
pose proof (ts_entry B lyc S2 W regs2 mem2 md2 Bw now sp1 HTC HAR2 Htw Hnw Hnow Hpw R9
  ltac:(lia) ltac:(lia) R20 R24) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs TT.TT_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
assert (KW : ts_KW W sp1 mem2 mem2) by apply ts_KW_refl.
assert (Hwin : sp0 - STK <= sp1 + 40 /\ sp1 + 56 <= sp0) by lia.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1, +0x2a4 .. +0x2c8: t0, t1, the check of s + 212, inflight, a7, `beqz a0` *)
paj_run_tok RUN HS HJ SHOK TT.TT_B0.
{ ts_awr U9. }
ts_after KW HS U9.
psrr_branch_tok RUN BR HS SHOK TT.TT_B0.
- (* no frame in flight: to the tail cut *)
  rewrite (ts_br_eq E0 34 _ 0 E34 R34 ltac:(lia)) in Hc.
  change (bv_swrap 32 (TW.u_at Bw TW.A_S_inflight 4)) with (TW.S_inflight Bw) in Hc.
  apply Z.eqb_eq in Hc. rename Hc into Hinf0.
  paj_run_to_tok RUNTO HS HJ SHOK TT.TT_B0 TICK_TAIL.
  { ts_awr U9. }
  ts_after KW HS U9.
  TT.tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. TT.tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
  TT.tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. TT.tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
  TT.tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. TT.tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
  TT.tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. TT.tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
  TT.tt_kreg HS EE (21%bv : bv 5) 21%nat R21 Y21. TT.tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22.
  TT.tt_kreg HS EE (23%bv : bv 5) 23%nat R23 Y23.
  TT.tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
  TT.tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
  TT.tt_reg HS (5%bv : bv 5) (w64 (TICK_S + 212)) Y5 ltac:(reflexivity).
  TT.tt_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 212) / 8)) Y6 ltac:(reflexivity).
  TT.tt_reg HS (17%bv : bv 5) (w64 (TICK_S + 18144)) Y17 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_TAIL)) mm rom) mdx) Q) end.
  rewrite (ts_go_tail0 timg_B TF Bw now Hinf0) in Hm.
  pose proof (MOVE (ms_mem ms) _ HJ KW) as (HRC3 & _ & _ & Htw3).
  apply (TAIL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F Bw
    lyc S2 W (ms_mem ms) _ 0 (ms_regs ms) HFIX).
  + exact (conj HRC3 (conj Htw3 (conj Hgf0 (conj Hm (fun _ => Hinv))))).
  + exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
      (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) (conj Y5 (conj Y6 Y17))).
- (* a frame in flight *)
  rewrite (ts_br_eq E0 34 _ 0 E34 R34 ltac:(lia)) in Hc.
  change (bv_swrap 32 (TW.u_at Bw TW.A_S_inflight 4)) with (TW.S_inflight Bw) in Hc.
  apply Z.eqb_neq in Hc. rename Hc into Hinf.
  (* run 2, +0x2cc .. +0x30c: the checks of s + 1752 and s + 28, sent_us, ack_timeout_ms, now, `bltu` *)
  paj_run_tok RUN HS HJ SHOK TT.TT_B0.
  { ts_awr U9. }
  ts_after KW HS U9.
  psrr_branch_tok RUN BR HS SHOK TT.TT_B0.
  + (* no ack timeout: to the tail cut *)
    rewrite (ts_br_tmo E0 now (TW.S_inflight_sent_us Bw) (TW.S_cfg_ack_timeout_ms Bw) E37 E36 E32 Hnow R36 R32) in Hc.
    apply negb_true_iff in Hc. rename Hc into Htmo.
    paj_run_to_tok RUNTO HS HJ SHOK TT.TT_B0 TICK_TAIL.
    { ts_awr U9. }
    ts_after KW HS U9.
    TT.tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. TT.tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
    TT.tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. TT.tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
    TT.tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. TT.tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
    TT.tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. TT.tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
    TT.tt_kreg HS EE (21%bv : bv 5) 21%nat R21 Y21. TT.tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22.
    TT.tt_kreg HS EE (23%bv : bv 5) 23%nat R23 Y23.
    TT.tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
    TT.tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
    TT.tt_reg HS (5%bv : bv 5) (w64 (TICK_S + 212)) Y5 ltac:(reflexivity).
    TT.tt_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 212) / 8)) Y6 ltac:(reflexivity).
    TT.tt_reg HS (17%bv : bv 5) (w64 (TICK_S + 18144)) Y17 ltac:(reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_TAIL)) mm rom) mdx) Q) end.
    rewrite (ts_go_tail1 timg_B TF Bw now Htmo) in Hm.
    pose proof (MOVE (ms_mem ms) _ HJ KW) as (HRC3 & _ & _ & Htw3).
    apply (TAIL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F Bw
      lyc S2 W (ms_mem ms) _ 0 (ms_regs ms) HFIX).
    * exact (conj HRC3 (conj Htw3 (conj Hgf0 (conj Hm (fun _ => Hinv))))).
    * exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
        (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) (conj Y5 (conj Y6 Y17))).
  + (* the ack timed out *)
    rewrite (ts_br_tmo E0 now (TW.S_inflight_sent_us Bw) (TW.S_cfg_ack_timeout_ms Bw) E37 E36 E32 Hnow R36 R32) in Hc.
    apply negb_false_iff in Hc. rename Hc into Htmo.
    (* run 3, +0x310 .. +0x348: the checks of s + 1748 and s + 32, retries, max_retries, t0 and t1 saved at s1 + 48
       and s1 + 40, `bgeu t2, a2` *)
    paj_run_tok RUN HS HJ SHOK TT.TT_B0.
    { ts_awr U9. }
    ts_after KW HS U9.
    psrr_branch_tok RUN BR HS SHOK TT.TT_B0.
    * (* no retry left: to the ack-lost cut *)
      rewrite (ts_br_retry E0 35 33 _ _ E35 E33 R35 R33) in Hc.
      apply negb_true_iff in Hc. rename Hc into Hrt.
      paj_run_to_tok RUNTO HS HJ SHOK TT.TT_B0 TICK_ACKL.
      { ts_awr U9. }
      ts_after KW HS U9.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2. cbn [ms_mem restrict] in RS2.
      assert (T48 : rdword (aview segs (w_H W) (ms_mem ms)) (sp1 + 48) = Some (TICK_S + 212)).
      { apply YF0x.val_mem_rdword; [unfold TICK_S, TB_g_s; lia|].
        exact (can_field_of_region E0 _ 9 sp1 _ 40 64 40 56 48 8 (SLit (TICK_S + 212)) (TICK_S + 212) RS2 U9
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(unfold TICK_S, TB_g_s; cbn; lia)
          ltac:(cbn; lia)). }
      assert (T40 : rdword (aview segs (w_H W) (ms_mem ms)) (sp1 + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8)).
      { change (SHADOW_OFF + (TICK_S + 212) / 8) with 2148220642.
        apply YF0x.val_mem_rdword; [lia|].
        exact (can_field_of_region E0 _ 9 sp1 _ 40 64 40 56 40 8 (SLit 2148220642) 2148220642 RS2 U9
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
      clear RS2.
      TT.tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. TT.tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
      TT.tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. TT.tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
      TT.tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. TT.tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
      TT.tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. TT.tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
      TT.tt_kreg HS EE (21%bv : bv 5) 21%nat R21 Y21. TT.tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22.
      TT.tt_kreg HS EE (23%bv : bv 5) 23%nat R23 Y23. TT.tt_kreg HS EE (25%bv : bv 5) 25%nat R25 Y25.
      TT.tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
      TT.tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
      TT.tt_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 212) / 8)) Y6 ltac:(reflexivity).
      TT.tt_reg HS (17%bv : bv 5) (w64 (TICK_S + 18144)) Y17 ltac:(reflexivity).
      TT.tt_reg HS (7%bv : bv 5) (w64 (bv_swrap 32 (TW.S_inflight_retries Bw))) Y7
        ltac:(exact (TT.tt_sext E0 35 _ E35 R35)).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_ACKL)) mm rom) mdx) Q) end.
      rewrite (ts_go_ackl timg_B TF Bw now Hinf Htmo Hrt) in Hm.
      pose proof (MOVE (ms_mem ms) _ HJ KW) as HPRE3.
      apply (ACKL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
        S2 (ms_mem ms) _ (ms_regs ms) HFIX).
      -- exact (conj HPRE3 (conj (conj T48 T40) Hm)).
      -- exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
           (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) (conj Y25 (conj Y6 (conj Y7 Y17)))).
    * (* a retry left: to the retransmit cut *)
      rewrite (ts_br_retry E0 35 33 _ _ E35 E33 R35 R33) in Hc.
      apply negb_false_iff in Hc. rename Hc into Hrt.
      paj_run_to_tok RUNTO HS HJ SHOK TT.TT_B0 TICK_RETX.
      { ts_awr U9. }
      ts_after KW HS U9.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2. cbn [ms_mem restrict] in RS2.
      assert (T48 : rdword (aview segs (w_H W) (ms_mem ms)) (sp1 + 48) = Some (TICK_S + 212)).
      { apply YF0x.val_mem_rdword; [unfold TICK_S, TB_g_s; lia|].
        exact (can_field_of_region E0 _ 9 sp1 _ 40 64 40 56 48 8 (SLit (TICK_S + 212)) (TICK_S + 212) RS2 U9
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(unfold TICK_S, TB_g_s; cbn; lia)
          ltac:(cbn; lia)). }
      assert (T40 : rdword (aview segs (w_H W) (ms_mem ms)) (sp1 + 40) = Some (SHADOW_OFF + (TICK_S + 212) / 8)).
      { change (SHADOW_OFF + (TICK_S + 212) / 8) with 2148220642.
        apply YF0x.val_mem_rdword; [lia|].
        exact (can_field_of_region E0 _ 9 sp1 _ 40 64 40 56 40 8 (SLit 2148220642) 2148220642 RS2 U9
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
      clear RS2.
      TT.tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. TT.tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
      TT.tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. TT.tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
      TT.tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. TT.tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
      TT.tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. TT.tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
      TT.tt_kreg HS EE (21%bv : bv 5) 21%nat R21 Y21. TT.tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22.
      TT.tt_kreg HS EE (23%bv : bv 5) 23%nat R23 Y23.
      TT.tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
      TT.tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
      TT.tt_reg HS (13%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 1752) / 8)) Y13 ltac:(reflexivity).
      TT.tt_reg HS (14%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 1748) / 8)) Y14 ltac:(reflexivity).
      TT.tt_reg HS (17%bv : bv 5) (w64 (TICK_S + 18144)) Y17 ltac:(reflexivity).
      TT.tt_reg HS (7%bv : bv 5) (w64 (bv_swrap 32 (TW.S_inflight_retries Bw))) Y7
        ltac:(exact (TT.tt_sext E0 35 _ E35 R35)).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_RETX)) mm rom) mdx) Q) end.
      rewrite (ts_go_retx timg_B TF Bw now Hinf Htmo Hrt) in Hm.
      pose proof (MOVE (ms_mem ms) _ HJ KW) as HPRE3.
      apply (RETX LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
        S2 (ms_mem ms) _ (ms_regs ms) HFIX).
      -- exact (conj HPRE3 (conj (conj T48 T40) (conj Hinf Hm))).
      -- exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
           (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) (conj Y7 (conj Y13 (conj Y14 Y17)))).
Qed.
End tsw.

(* The step piece of the walk of diginet_session_tick (TickCutB.v tick_step_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_step : forall fx rc B MT, @tick_step_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ts_holds fx rc B MT). Qed.
Print Assumptions tick_step.
