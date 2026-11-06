(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 459 of its 560 lines of code are new or changed and 1109 lines of the source are left out. *)
(* TickBTail: Theorem tick_tail : tick_tail_stmt (lib/B/Prog/TickCutB.v), the tail piece of the walk of
   diginet_session_tick on fuzz_transport.asan-ubsan (0x8909c = transportb_sigma TB_diginet_session_tick,
   AF_diginet_session_tick = 0x7dfc of lib/B/Prog/DgnTransportBList.v): code +0x5c0 .. +0x604 (0x8965c .. 0x896a0) and
   +0x678 .. +0x694 (0x89714 .. 0x89730), from the tail cut tick_tail_at to the cuts tick_epi_at, tick_ka_at and
   tick_queue_at. No call and no store. The runs are the position-abstract runs of lib/B/Prog/TransportGRunB.v
   paj_run_x / paj_run_to_x over the caller's G journal, from one symbolic state whose registers s4, s5, s7, s8, t0 and
   t1 are pinned to their values at the cut (tick_regs_tail) and whose three regions hold, read-only, the four g_s
   fields the tail loads (s + 112 state, s + 184 next_keepalive_us, s + 192 backoff_until_us, s + 212 inflight; the
   world's bytes, TWorldG.v tw_read_val at TWorldB.v TMAP_B), the four shadow bytes of their checks (0:
   trans_tick_cells read by DgnTransportBCg.v decode_zshadow_rd) and the word now at s1 + 56 (tick_run_cur):
     run 1  +0x5c0 .. +0x5d0  the check of s + 112 (through s5), the load of the state (through s7), `bne a0, 2`;
     run 2  +0x5d4 .. +0x5e0  the check of s + 212 (through t1), the load of inflight (through t0), `bnez a0`;
     run 3  +0x5e4 .. +0x600  the check of s + 192, backoff_until_us and now, `bgeu now, backoff`;
     run 4  +0x678 .. +0x694  the check of s + 184 (a3 = its shadow address), next_keepalive_us (a4) and now,
                              `bgeu now, next_keepalive`.
   The three exits to +0x604 run `li s10, 0` to the epilogue cut with the model's result (B0, DIGINET_OK)
   (TickCutB.v tick_tail_eq, lib/A/Prog/TickCut.v tick_some_inv); `bgeu` at +0x694 goes to the keepalive cut
   (send_data_m at tick_ka_w B0 now) or falls through to the queue cut (tick_queue_m). Nothing is written, so every
   byte's view is the cut's (tt_KA) and the cut's facts move to the run's last memory (tt_cur_move); the run invariants
   at ka and queue come from the tail cut's guard, S_inflight B0 = 0 by run 2. The structure is image A's tail piece
   (lib/A/Prog/TickTail.v) at image B's pcs and registers (the shadow address of s + 112 is s5 here, s9 on image A). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YE2y.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the symbolic state at the tail cut ---- *)

(* The shadow byte of s + 112 (s5 at the cut); s + 184, s + 192 and s + 212 have bytes 9, 10 and 12 after it. *)
Definition TT_SH : Z := SHADOW_OFF + (TICK_S + 112) / 8.
Lemma TT_SH_eq : TT_SH = 2148220630.
Proof. reflexivity. Qed.
(* The four g_s fields the tail loads, as atoms 32 (state, 4 bytes), 35 (next_keepalive_us), 34 (backoff_until_us)
   and 33 (inflight, 4 bytes); their four shadow bytes; the word now at s1 + 56 (atom 36). No byte is writable. *)
Definition TT_R_gs : YP09.region :=
  YP09.mkRegion None (TICK_S + 112) (TICK_S + 216) 0 0
    [YP09.mkChunk (TICK_S + 112) (YP09.CVal 4 (SOff 32 0)); YP09.mkChunk (TICK_S + 184) (YP09.CVal 8 (SOff 35 0));
     YP09.mkChunk (TICK_S + 192) (YP09.CVal 8 (SOff 34 0)); YP09.mkChunk (TICK_S + 212) (YP09.CVal 4 (SOff 33 0))].
Definition TT_R_sh : YP09.region :=
  YP09.mkRegion None TT_SH (TT_SH + 13) 0 0
    [YP09.mkChunk TT_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TT_SH + 9) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TT_SH + 10) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TT_SH + 12) (YP09.CVal 1 (SLit 0))].
Definition TT_R_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 36 0))].
Definition TT_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
(* s4 = s, s8 = the shadow base, s5 = TT_SH, s7 = s + 112, t0 = s + 212, t1 = its shadow address. *)
Definition TT_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 21) (SLit (SHADOW_OFF + (TICK_S + 112) / 8))) (Z_to_bv 5 23) (SLit (TICK_S + 112)))
    (Z_to_bv 5 5) (SLit (TICK_S + 212))) (Z_to_bv 5 6) (SLit (SHADOW_OFF + (TICK_S + 212) / 8)).
Definition ss_tt : sstate := mkSS TICK_TAIL TT_REGS [TT_R_gs; TT_R_sh; TT_R_now] None TT_FACTS.
Definition TT_Bx : sv := SLit 0.
Definition TT_B0 : Z * Z := (0, 0).

(* ---- the tests, in the model's terms ---- *)

(* The sign-extended 4-byte load of an atom holding a uint32_t. *)
Lemma tt_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma tt_eqb_s : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec a b) as [-> | N]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

Lemma tt_swrap_range : forall v, - 2 ^ 31 <= bv_swrap 32 v < 2 ^ 31.
Proof.
intros v. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
pose proof (Z.mod_pos_bound (v + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

(* `bne` of a sign-extended uint32_t load and a small literal. *)
Lemma tt_br_ne : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = negb (bv_swrap 32 v =? c).
Proof.
intros E n v c H R Hc. cbn [branch_taken]. rewrite (tt_sext E n v H R).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c).
pose proof (tt_swrap_range v). rewrite tt_eqb_s by lia. reflexivity.
Qed.

(* `bgeu` of two atoms holding uint64_t values. *)
Lemma tt_br_geu : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = (y <=? x).
Proof.
intros E n1 n2 x y H1 H2 Rx Ry. cbn [branch_taken sv_denot]. rewrite H1, H2.
rewrite !unsigned_lit_small, !Z.add_0_r by lia. unfold bv_ltu. rewrite !unsigned_lit_small by lia.
rewrite Z.leb_antisym. reflexivity.
Qed.

(* The tail's three return tests (:445) give (B, DIGINET_OK). *)
Lemma tt_m_ret : forall I F B now,
  (negb (TW.S_state B =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B =? 0) || (now <? TW.S_backoff_until_us B))
    = true ->
  tick_tail I F B now = Some (B, DLib.DIGINET_OK).
Proof. intros I F B now H. rewrite tick_tail_eq, H. reflexivity. Qed.

(* The tests passed and the keepalive is due (:449-455). *)
Lemma tt_m_ka : forall I F B now, TW.S_state B = TS0.DIGINET_S_ONLINE -> TW.S_inflight B = 0 ->
  TW.S_backoff_until_us B <= now -> TW.S_next_keepalive_us B <= now ->
  tick_tail I F B now = TSS.send_data_m I F (tick_ka_w B now) [DSpec.b8 0] 1 now.
Proof.
intros I F B now H1 H2 H3 H4. rewrite tick_tail_eq, H1, H2, !Z.eqb_refl. cbn [negb orb].
rewrite (proj2 (Z.ltb_ge _ _) H3), (proj2 (Z.leb_le _ _) H4). reflexivity.
Qed.

(* The tests passed and the keepalive is not due: the queue (:458-471). *)
Lemma tt_m_queue : forall I F B now, TW.S_state B = TS0.DIGINET_S_ONLINE -> TW.S_inflight B = 0 ->
  TW.S_backoff_until_us B <= now -> now < TW.S_next_keepalive_us B ->
  tick_tail I F B now = tick_queue_m I F B now.
Proof.
intros I F B now H1 H2 H3 H4. rewrite tick_tail_eq, H1, H2, !Z.eqb_refl. cbn [negb orb].
rewrite (proj2 (Z.ltb_ge _ _) H3), (proj2 (Z.leb_gt _ _) H4). reflexivity.
Qed.

(* ---- nothing written: the view of every byte is the cut's ---- *)

Definition tt_nowin (rs : smem) : bool :=
  forallb (fun w : option nat * Z * Z => let '(_, wlo, whi) := w in whi <=? wlo) (windows rs).

Section tt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* What the piece keeps, from the cut's memory memc to a memory m: every byte's view, and presence. *)
Definition tt_KA (W : world segs) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma tt_KA_refl : forall (W : world segs) m, tt_KA W m m.
Proof. intros W m. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

(* A run from a state none of whose regions has a writable byte writes nothing. *)
Lemma tt_KA_step : forall E rs (W : world segs) memc (m m' : word -> option byte),
  tt_nowin rs = true -> tt_KA W memc m ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  tt_KA W memc m'.
Proof.
intros E rs W memc m m' Hnw [K1 K2] Hfr Hg. split.
- assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows rs) ->
    base_val E b + wlo <= x < base_val E b + whi -> (fun _ : Z => False) x).
  { intros b wlo whi x Hin Hx. unfold tt_nowin in Hnw. rewrite forallb_forall in Hnw.
    pose proof (Hnw _ Hin) as Hle. cbv beta iota in Hle. apply Z.leb_le in Hle. lia. }
  intros a Ha.
  rewrite (kept_of_frame E rs (w_H W) m m' (fun _ => False) Hfr Hw a Ha (fun x => x)).
  exact (K1 a Ha).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

Lemma tt_tw_move : forall (W : world segs) mem2 mem3 B0,
  tt_KA W mem2 mem3 -> tw_at TMAP_B (aview segs (w_H W) mem2) B0 -> tw_at TMAP_B (aview segs (w_H W) mem3) B0.
Proof.
intros W mem2 mem3 B0 [KA _] H. apply (tw_kept TMAP_B (aview segs (w_H W) mem2)); [exact H|].
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
apply KA. lia.
Qed.

Lemma tt_rdword_move : forall (W : world segs) mem2 mem3 a v,
  tt_KA W mem2 mem3 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview segs (w_H W) mem2) a = Some v -> rdword (aview segs (w_H W) mem3) a = Some v.
Proof.
intros W mem2 mem3 a v [KA _] Ha0 Ha1 H. rewrite <- H. apply rdword_ext. intros i Hi. apply KA. lia.
Qed.

(* The facts every cut carries move to a later memory with the same view and the journal there. *)
Lemma tt_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  tt_KA W2 mem2 mem3 ->
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 [KD GR].
assert (KD' : forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a. rewrite (aview_wrap64 segs _ mem3 a), (aview_wrap64 segs _ mem2 a).
  apply KD. apply Z.mod_pos_bound. lia. }
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD'. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD'. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD'. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD'. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD' _)). exact Ho.
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD' _)). exact HFL.
Qed.

(* The walk's valuation at the cut: the 32 registers, then state, inflight, backoff_until_us, next_keepalive_us of
   the world B0 and now. *)
Definition tt_vals (B0 : list byte) (now : Z) : list word :=
  [Z_to_bv 64 (TW.u_at B0 (TW.OFF_g_s + 112) 4); Z_to_bv 64 (TW.u_at B0 (TW.OFF_g_s + 212) 4);
   Z_to_bv 64 (TW.u_at B0 (TW.OFF_g_s + 192) 8); Z_to_bv 64 (TW.u_at B0 (TW.OFF_g_s + 184) 8); Z_to_bv 64 now].
Definition tt_E (regs : bvmap 5 word) (B0 : list byte) (now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (tt_vals B0 now)).

Lemma tt_entry0 : forall ly S (W : world segs) regs mem md B0 now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) B0 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  st_ok_pi segs VAL (tt_E regs B0 now) (mkSS TICK_TAIL sr_atoms [TT_R_gs; TT_R_sh; TT_R_now] None TT_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_TAIL)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md B0 now sp1 HTC HAR Htw Hnw Rnow R9 Hsp Hsp32.
  set (E := tt_E regs B0 now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tt_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (tt_vals B0 now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth tt_vals] in E32, E33, E34, E35, E36. clear EX.
  pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 112) 4) as R32.
  pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 212) 4) as R33.
  pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 192) 8) as R34.
  pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 184) 8) as R35.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32, R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34, R35.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> TICK_S <= T -> T + 8 <= TICK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T H1 H2 H3. apply YE2y.val_mem1_of_aview.
    exact (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) T HAR H1 H2 H3 HTC). }
  assert (GS : forall o (n : nat), 0 <= o -> o + Z.of_nat n <= TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (0 + (TICK_S + o)) n (TW.u_at B0 (TW.OFF_g_s + o) n)).
  { intros o n Ho Hn. replace (0 + (TICK_S + o)) with (TB_g_s + o) by (unfold TICK_S; lia).
    exact (tw_read_val segs _ TMAP_B B0 TW.OFF_g_s TB_g_s TW.SZ_g_s o n TMAP_B_ok Htw TMAP_B_g_s Ho Hn). }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TT_R_gs TT_R_sh TT_R_now base_val];
      rewrite ?U9.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 112) 4 (SOff 32 0) (TW.u_at B0 (TW.OFF_g_s + 112) 4));
          [apply DEN; [exact E32 | lia] | exact R32 | lia |].
        exact (GS 112 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 184) 8 (SOff 35 0) (TW.u_at B0 (TW.OFF_g_s + 184) 8));
          [apply DEN; [exact E35 | exact R35] | exact R35 | lia |].
        exact (GS 184 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 192) 8 (SOff 34 0) (TW.u_at B0 (TW.OFF_g_s + 192) 8));
          [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
        exact (GS 192 8%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 212) 4 (SOff 33 0) (TW.u_at B0 (TW.OFF_g_s + 212) 4));
          [apply DEN; [exact E33 | lia] | exact R33 | lia |].
        exact (GS 212 4%nat ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [rewrite TT_SH_eq; lia|].
      split; [rewrite TT_SH_eq; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 TT_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + TT_SH) with (FCells.shadow_addr (TICK_S + 112)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TT_SH + 9) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TT_SH + 9)) with (FCells.shadow_addr (TICK_S + 184)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TT_SH + 10) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TT_SH + 10)) with (FCells.shadow_addr (TICK_S + 192)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
      * apply (chunk_ok_val segs E _ 0 (TT_SH + 12) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        replace (0 + (TT_SH + 12)) with (FCells.shadow_addr (TICK_S + 208)) by (vm_compute; reflexivity).
        apply ZSH; unfold TICK_S, TB_g_s, TW.SZ_g_s; [reflexivity | lia | lia].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 36 0) now); [apply DEN; [exact E36 | exact Rnow] | exact Rnow | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem (sp1 + 56) now Hnw).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TT_R_gs, TT_R_sh, TT_R_now. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite TT_SH_eq. unfold TICK_S, TB_g_s. repeat split; first [exact I | lia].
  - unfold TT_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32, E33, !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tt_entry : forall ly S (W : world segs) regs mem md B0 now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) B0 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now -> 0 <= now < 2 ^ 64 ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 21 = w64 (SHADOW_OFF + (TICK_S + 112) / 8) -> YK11.getr regs 23 = w64 (TICK_S + 112) ->
  YK11.getr regs 5 = w64 (TICK_S + 212) -> YK11.getr regs 6 = w64 (SHADOW_OFF + (TICK_S + 212) / 8) ->
  st_ok_pi segs VAL (tt_E regs B0 now) ss_tt
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_TAIL)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md B0 now sp1 HTC HAR Htw Hnw Rnow R9 Hsp Hsp32 R20 R24 R21 R23 R5 R6.
  rewrite restrict_mkst_fx.
  pose proof (tt_entry0 ly S W regs mem md B0 now sp1 HTC HAR Htw Hnw Rnow R9 Hsp Hsp32) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 21) _ H2 R21 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) _ H3 R23 eq_refl) as H4.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 5) _ H4 R5 eq_refl) as H5.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 6) _ H5 R6 eq_refl) as H6.
  exact H6.
Qed.

End tt.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac tt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "tt_reg: no match for" T; fail
  end.
(* A register the runs left as its atom: its value at the cut, by the equation Q. *)
Ltac tt_kreg HS EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    tt_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The write rights of a run from a state with no writable byte. *)
Ltac tt_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* After a run: the model generalized, tt_KA carried to the run's last memory, the old machine states dropped, the
   current one named ms. *)
Ltac tt_after KA HS :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in let Hnw := fresh "Hnw" in
    assert (Hnw : tt_nowin rs = true) by (vm_compute; reflexivity);
    pose proof (tt_KA_step Ex rs _ _ _ _ Hnw KA HFr HG) as KA'; clear KA HFr HG Hnw;
    rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

Section tw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma tt_holds : @tick_tail_stmt fx rc B MT.
Proof.
unfold tick_tail_stmt. intros EPI KAc QUEUE. unfold tick_tail_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof HFIX as (HJe & Hret & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf0 & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HCU & Hnw) & Htw & Hgf & Hm & Hguard).
pose proof HCU as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFL).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24) & R5 & R6 & R17).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TICK_STK = 8896) by reflexivity.
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME, TICK_ALIGN in *.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
(* the valuation and the atoms *)
set (E0 := tt_E regs2 B0 now).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tt_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E0, tt_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (tt_vals B0 now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth tt_vals] in E32, E33, E34, E35, E36. clear EX.
pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 112) 4) as R32.
pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 212) 4) as R33.
pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 192) 8) as R34.
pose proof (TWL.u_at_range B0 (TW.OFF_g_s + 184) 8) as R35.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32, R33.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34, R35.
pose proof (tt_entry B ly2 S2 W2 regs2 mem2 md2 B0 now sp1 HTC HAR2 Htw Hnw Hnow R9 (proj1 Hsp1) (proj2 Hsp1)
  R20 R24 R21 R23 R5 R6) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs TT_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
assert (KA : tt_KA W2 mem2 mem2) by apply tt_KA_refl.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1, +0x5c0 .. +0x5d0: the check of s + 112 (through s5), the state (through s7), `bne a0, 2` *)
paj_run_tok RUN HS HJ SHOK TT_B0.
{ tt_awr. }
tt_after KA HS.
psrr_branch_tok RUN BR HS SHOK TT_B0.
- (* the state is not S_ONLINE: +0x604, s10 = 0, to the epilogue *)
  rewrite (tt_br_ne E0 32 _ 2 E32 R32 ltac:(lia)) in Hc.
  change (bv_swrap 32 (TW.u_at B0 (TW.OFF_g_s + 112) 4)) with (TW.S_state B0) in Hc.
  assert (Hcond : (negb (TW.S_state B0 =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B0 =? 0) ||
    (now <? TW.S_backoff_until_us B0)) = true) by (change TS0.DIGINET_S_ONLINE with 2; rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK TT_B0 TICK_EPI.
  { tt_awr. }
  tt_after KA HS.
  tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
  tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
  tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
  tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27.
  tt_reg HS (26%bv : bv 5) (w64 0) Y26 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end.
  rewrite (tt_m_ret timg_B TF B0 now Hcond) in Hm.
  destruct (tick_some_inv _ _ _ _ Hm) as [EB ER]. subst Bw' r.
  apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw B0
    pos sp1 F ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
  + refine (conj _ (conj (tt_tw_move W2 mem2 (ms_mem ms) B0 KA Htw) Hgf)).
    exact (tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA).
  + exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27)))))) Y26).
- (* S_ONLINE *)
  rewrite (tt_br_ne E0 32 _ 2 E32 R32 ltac:(lia)) in Hc.
  change (bv_swrap 32 (TW.u_at B0 (TW.OFF_g_s + 112) 4)) with (TW.S_state B0) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hon.
  (* run 2, +0x5d4 .. +0x5e0: the check of s + 212 (through t1), inflight (through t0), `bnez a0` *)
  paj_run_tok RUN HS HJ SHOK TT_B0.
  { tt_awr. }
  tt_after KA HS.
  psrr_branch_tok RUN BR HS SHOK TT_B0.
  + (* a frame in flight: +0x604, s10 = 0, to the epilogue *)
    rewrite (tt_br_ne E0 33 _ 0 E33 R33 ltac:(lia)) in Hc.
    change (bv_swrap 32 (TW.u_at B0 (TW.OFF_g_s + 212) 4)) with (TW.S_inflight B0) in Hc.
    assert (Hcond : (negb (TW.S_state B0 =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B0 =? 0) ||
      (now <? TW.S_backoff_until_us B0)) = true) by (rewrite Hc, orb_true_r; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK TT_B0 TICK_EPI.
    { tt_awr. }
    tt_after KA HS.
    tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
    tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
    tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
    tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27.
    tt_reg HS (26%bv : bv 5) (w64 0) Y26 ltac:(reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end.
    rewrite (tt_m_ret timg_B TF B0 now Hcond) in Hm.
    destruct (tick_some_inv _ _ _ _ Hm) as [EB ER]. subst Bw' r.
    apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw B0
      pos sp1 F ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
    * refine (conj _ (conj (tt_tw_move W2 mem2 (ms_mem ms) B0 KA Htw) Hgf)).
      exact (tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA).
    * exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27)))))) Y26).
  + (* no frame in flight *)
    rewrite (tt_br_ne E0 33 _ 0 E33 R33 ltac:(lia)) in Hc.
    change (bv_swrap 32 (TW.u_at B0 (TW.OFF_g_s + 212) 4)) with (TW.S_inflight B0) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hinf.
    (* run 3, +0x5e4 .. +0x600: the check of s + 192, backoff_until_us, now, `bgeu now, backoff` *)
    paj_run_tok RUN HS HJ SHOK TT_B0.
    { tt_awr. }
    tt_after KA HS.
    psrr_branch_tok RUN BR HS SHOK TT_B0.
    * (* now >= backoff_until_us: +0x678 *)
      rewrite (tt_br_geu E0 36 34 now _ E36 E34 Hnow R34) in Hc.
      change (TW.u_at B0 (TW.OFF_g_s + 192) 8) with (TW.S_backoff_until_us B0) in Hc.
      apply Z.leb_le in Hc. rename Hc into Hbk.
      (* run 4, +0x678 .. +0x694: the check of s + 184, next_keepalive_us, now, `bgeu now, next_keepalive` *)
      paj_run_tok RUN HS HJ SHOK TT_B0.
      { tt_awr. }
      tt_after KA HS.
      psrr_branch_tok RUN BR HS SHOK TT_B0.
      -- (* the keepalive is due: to the keepalive cut *)
         rewrite (tt_br_geu E0 36 35 now _ E36 E35 Hnow R35) in Hc.
         change (TW.u_at B0 (TW.OFF_g_s + 184) 8) with (TW.S_next_keepalive_us B0) in Hc.
         apply Z.leb_le in Hc. rename Hc into Hkd.
         paj_run_to_tok RUNTO HS HJ SHOK TT_B0 TICK_KA.
         { tt_awr. }
         tt_after KA HS.
         tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
         tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
         tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
         tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
         tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22. tt_kreg HS EE (17%bv : bv 5) 17%nat R17 Y17.
         tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
         tt_reg HS (21%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 112) / 8)) Y21 ltac:(reflexivity).
         tt_reg HS (23%bv : bv 5) (w64 (TICK_S + 112)) Y23 ltac:(reflexivity).
         tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
         tt_reg HS (13%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 184) / 8)) Y13 ltac:(reflexivity).
         tt_reg HS (14%bv : bv 5) (w64 (TW.S_next_keepalive_us B0)) Y14
           ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
         pmkst HS.
         lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
           change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_KA)) mm rom) mdx) Q) end.
         rewrite (tt_m_ka timg_B TF B0 now Hon Hinf Hbk Hkd) in Hm.
         apply (KAc LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
           pos sp1 F B0 ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
         ++ refine (conj (conj _ (tt_rdword_move W2 mem2 (ms_mem ms) (sp1 + 56) now KA ltac:(lia) ltac:(lia) Hnw))
              (conj (tt_tw_move W2 mem2 (ms_mem ms) B0 KA Htw) (conj Hgf (conj (Hguard Hinf) Hm)))).
            exact (tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA).
         ++ exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
              (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) (conj Y13 (conj Y14 Y17))).
      -- (* the keepalive is not due: to the queue cut *)
         rewrite (tt_br_geu E0 36 35 now _ E36 E35 Hnow R35) in Hc.
         change (TW.u_at B0 (TW.OFF_g_s + 184) 8) with (TW.S_next_keepalive_us B0) in Hc.
         apply Z.leb_gt in Hc. rename Hc into Hkd.
         paj_run_to_tok RUNTO HS HJ SHOK TT_B0 TICK_QUEUE.
         { tt_awr. }
         tt_after KA HS.
         tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
         tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
         tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
         tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27. tt_kreg HS EE (19%bv : bv 5) 19%nat R19 Y19.
         tt_kreg HS EE (22%bv : bv 5) 22%nat R22 Y22. tt_kreg HS EE (17%bv : bv 5) 17%nat R17 Y17.
         tt_reg HS (20%bv : bv 5) (w64 TICK_S) Y20 ltac:(reflexivity).
         tt_reg HS (21%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 112) / 8)) Y21 ltac:(reflexivity).
         tt_reg HS (23%bv : bv 5) (w64 (TICK_S + 112)) Y23 ltac:(reflexivity).
         tt_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
         pmkst HS.
         lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
           change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_QUEUE)) mm rom) mdx) Q) end.
         rewrite (tt_m_queue timg_B TF B0 now Hon Hinf Hbk Hkd) in Hm.
         apply (QUEUE LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
           pos sp1 F B0 ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
         ++ refine (conj (conj _ (tt_rdword_move W2 mem2 (ms_mem ms) (sp1 + 56) now KA ltac:(lia) ltac:(lia) Hnw))
              (conj (tt_tw_move W2 mem2 (ms_mem ms) B0 KA Htw) (conj Hgf (conj (Hguard Hinf) Hm)))).
            exact (tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA).
         ++ exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27))))))
              (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y23 Y24)))))) Y17).
    * (* now below backoff_until_us: +0x604, s10 = 0, to the epilogue *)
      rewrite (tt_br_geu E0 36 34 now _ E36 E34 Hnow R34) in Hc.
      change (TW.u_at B0 (TW.OFF_g_s + 192) 8) with (TW.S_backoff_until_us B0) in Hc.
      apply Z.leb_gt in Hc.
      assert (Hcond : (negb (TW.S_state B0 =? TS0.DIGINET_S_ONLINE) || negb (TW.S_inflight B0 =? 0) ||
        (now <? TW.S_backoff_until_us B0)) = true) by (rewrite (proj2 (Z.ltb_lt _ _) Hc), orb_true_r; reflexivity).
      paj_run_to_tok RUNTO HS HJ SHOK TT_B0 TICK_EPI.
      { tt_awr. }
      tt_after KA HS.
      tt_kreg HS EE (2%bv : bv 5) 2%nat R2 Y2. tt_kreg HS EE (3%bv : bv 5) 3%nat R3 Y3.
      tt_kreg HS EE (4%bv : bv 5) 4%nat R4 Y4. tt_kreg HS EE (8%bv : bv 5) 8%nat R8 Y8.
      tt_kreg HS EE (9%bv : bv 5) 9%nat R9 Y9. tt_kreg HS EE (18%bv : bv 5) 18%nat R18 Y18.
      tt_kreg HS EE (27%bv : bv 5) 27%nat R27 Y27.
      tt_reg HS (26%bv : bv 5) (w64 0) Y26 ltac:(reflexivity).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end.
      rewrite (tt_m_ret timg_B TF B0 now Hcond) in Hm.
      destruct (tick_some_inv _ _ _ _ Hm) as [EB ER]. subst Bw' r.
      apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw B0
        pos sp1 F ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
      -- refine (conj _ (conj (tt_tw_move W2 mem2 (ms_mem ms) B0 KA Htw) Hgf)).
         exact (tt_cur_move B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCU HJ KA).
      -- exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y27)))))) Y26).
Qed.

End tw.

(* The tail piece of the walk of diginet_session_tick (TickCutB.v tick_tail_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_tail : forall fx rc B MT, @tick_tail_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tt_holds fx rc B MT). Qed.
Print Assumptions tick_tail.
