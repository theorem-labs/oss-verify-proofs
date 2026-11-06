(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names and numbers changed; 995 of its 1105 lines of code are new or changed and 655 lines of the source are left out. *)
(* on_announce_seg_sl2: Theorem onann_piece_sl2 : onann_sl2_stmt (lib/A/Prog/OnannCut.v), the second inlined
   session_lost of the walk of on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce), code
   +0x65c .. +0x738 (0x880d0 .. 0x881ac; diginet_session.c:220, session_lost :162-164, set_state :83-85, why =
   DIGINET_R_FOREIGN), from the cut onann_sl2_at to the cut onann_fnrel_at (+0x73c). At the cut s4 = s, s8 = the
   shadow base, s9 = s + 104, s10 = the shadow byte's address of s + 112, s5 = S_state B3 (sign-extended), s2 = the
   frame F, s3 = its first shadow byte, s1 = sp1 (spill slots at +8, +16, +24, +48: OnannCut.v onann_slots_arm).
     run 1  +0x65c .. +0x6c0  the checks of the 4-byte stores at s + 212 and s + 168 (g_s's zero shadow,
                              trans_onann_cells) and the stores of 0 there (slost_w1 B3), s4 = n3 = F + 32, n3's shadow
                              bytes 4 .. 12 := 0, a0 = n3 + 16, a1 = 0, a2 = 56, `jal __asan_memset` (+0x6c0, through
                              TransportGCg.v gx_intrin_at: n3's bytes 16 .. 71 := 0);
     run 2  +0x6c4 .. +0x710  the stores of 2 (8 bytes) at n3, of s5 at n3 + 8 (old_state) and of 5 at n3 + 12
                              (reason), the check of the store at s + 112 through s10 and the store of 0 there (address
                              from sp1 + 48; slost_w2 B3), the checks of the 8-byte loads at s + 96 and s + 104 (shadow
                              addresses from sp1 + 8 and sp1 + 16), a2 = g_s.notify (address from sp1 + 24), a0 =
                              g_s.notify_ctx (address s9), a1 = n3, `jalr a2` (+0x710): notice at TI.ti_notice timg_A
                              with session_lost_cg.v slost_ntc B3 5 (the 72 bytes read by SlostNtc.v sn_nb, placed by
                              sl2_ntc_at), at the world slost_w2 B3 (sl2_tw_w2), TF by on_announce_seg_kit.v
                              onann_tf_call; notice's acall_kept_g folded by TransportGCg.v dk_kept_trans_nf_g, its
                              stores inside onann_wr by sl2_wr_ntc;
     run 3  +0x714 .. +0x738  n3's shadow bytes := 0xf8, to the cut onann_fnrel_at (+0x73c) with e = 0, notice's world
                              Bw' (g_fail_next kept: SlostNtcKit.v sn_gfn') and the release registers.
   The runs are TransportGRunA.v paj_run_x / paj_run_to_x from symbolic states whose regions are n3's shadow bytes and
   first 16 bytes, g_s's state / notify / ctx, desk_counter_valid and inflight fields (absolute), g_s's shadow bytes
   (literal 0) and the four spill slots; the steps keep acall_kept_g by TransportGFrame.v dk_kept_nfz_gw /
   dk_kept_nf_gw. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostCut SlostNtcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostNtc SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
(* SlostNtc.v's theorem slost_ntc shadows session_lost_cg.v's notice slost_ntc: take the definition back. *)
Import session_lost_cg.
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
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104, s + 112, s + 168 and s + 212 have SL2_SH + 1, + 2, + 9, + 14. *)
Definition SL2_SH : Z := 2148220740.
Lemma SL2_SH_eq : SL2_SH = SHADOW_OFF + (ONANN_S + 96) / 8.
Proof. reflexivity. Qed.
(* n3's shadow bytes 4 .. 12 (s3, atom 19) and its first 16 bytes (s2 = F, atom 18). *)
Definition SL2_R_sh : YP09.region := YP09.mkRegion (Some 19%nat) 4 13 4 13 [].
Definition SL2_R_p : YP09.region := YP09.mkRegion (Some 18%nat) 32 48 32 48 [].
(* g_s.notify, g_s.notify_ctx (atoms 32, 33) and g_s.state (written). *)
Definition SL2_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 116) (ONANN_S + 112) (ONANN_S + 116)
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 33 0))].
(* g_s.desk_counter_valid and g_s.inflight, written. *)
Definition SL2_R_dcv : YP09.region := YP09.mkRegion None (ONANN_S + 168) (ONANN_S + 172) (ONANN_S + 168) (ONANN_S + 172) [].
Definition SL2_R_inf : YP09.region := YP09.mkRegion None (ONANN_S + 212) (ONANN_S + 216) (ONANN_S + 212) (ONANN_S + 216) [].
(* The five shadow bytes the checks read, 0. *)
Definition SL2_R_shg : YP09.region :=
  YP09.mkRegion None SL2_SH (SL2_SH + 15) 0 0
    [YP09.mkChunk SL2_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SL2_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SL2_SH + 2) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SL2_SH + 9) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SL2_SH + 14) (YP09.CVal 1 (SLit 0))].
(* The four spill slots at sp1 (s1, atom 9). *)
Definition SL2_R_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 56 0 0
    [YP09.mkChunk 8 (YP09.CVal 8 (SLit SL2_SH)); YP09.mkChunk 16 (YP09.CVal 8 (SLit (SL2_SH + 1)));
     YP09.mkChunk 24 (YP09.CVal 8 (SLit (ONANN_S + 96))); YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition SL2_RS : smem := [SL2_R_sh; SL2_R_p; SL2_R_gs; SL2_R_dcv; SL2_R_inf; SL2_R_shg; SL2_R_sl].
Definition SL2_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 6);
           (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].
(* s4 = s, s8 = the shadow base, s9 = s + 104, s10 = the shadow byte of s + 112, pinned. *)
Definition SL2_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 25) (SLit (ONANN_S + 104))) (Z_to_bv 5 26) (SLit (SL2_SH + 2)).
Definition ss_sl2 : sstate := mkSS ONANN_SL2 SL2_REGS SL2_RS None SL2_FACTS.
Definition SL2_Bx : sv := SLit 0.
Definition SL2_B0 : Z * Z := (0, 0).
(* +0x714, after notice returns: the registers as atoms, n3's shadow bytes 4 .. 12. *)
Definition ss_sl23 : sstate := mkSS (ONANN_SL2 + 0xb8) sr_atoms [SL2_R_sh] None
  (mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).

(* The bytes runs 1 and 2 and the memset may change: n3's shadow bytes 4 .. 12, n3's 72 bytes, g_s.state,
   desk_counter_valid and inflight, and the stack window of __asan_memset below sp1. *)
Definition sl2_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (ONANN_S + 112 <= x < ONANN_S + 116) \/ (ONANN_S + 168 <= x < ONANN_S + 172) \/
  (ONANN_S + 212 <= x < ONANN_S + 216) \/ (sp1 - ESTACK <= x < sp1).

(* ------------------------------------------------------------------ *)
(* 2. The model and the written range                                  *)
(* ------------------------------------------------------------------ *)

Lemma sl2_len_upd : forall (X : list byte) k (n : nat) v, length X = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> length (TW.upd X k (TW.put n v)) = Z.to_nat TW.W_LEN.
Proof.
intros X k n v L Hk Hn. assert (LZ : Z.of_nat (length X) = TW.W_LEN) by (rewrite L; unfold TW.W_LEN; lia).
rewrite TWL.length_upd_put; [exact L | exact Hk | rewrite LZ; exact Hn].
Qed.

Lemma sl2_s32_upd : forall (X : list byte) k (n : nat) v k', length X = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> 0 <= k' -> (k' + 4 <= k \/ k + Z.of_nat n <= k') ->
  TW.s32_at (TW.upd X k (TW.put n v)) k' = TW.s32_at X k'.
Proof.
intros X k n v k' L Hk Hn Hk' Hd. assert (LZ : Z.of_nat (length X) = TW.W_LEN) by (rewrite L; unfold TW.W_LEN; lia).
apply TWL.s32_at_upd_out; [exact Hk | exact Hk' | rewrite TWL.length_put; exact Hd |].
rewrite TWL.length_put, LZ. exact Hn.
Qed.

Lemma sl2_u_upd : forall (X : list byte) k (n : nat) v k' m, length X = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat m <= k \/ k + Z.of_nat n <= k') ->
  TW.u_at (TW.upd X k (TW.put n v)) k' m = TW.u_at X k' m.
Proof.
intros X k n v k' m L Hk Hn Hk' Hd. assert (LZ : Z.of_nat (length X) = TW.W_LEN) by (rewrite L; unfold TW.W_LEN; lia).
apply TWL.u_at_upd_out; [exact Hk | exact Hk' | rewrite TWL.length_put; exact Hd |].
rewrite TWL.length_put, LZ. exact Hn.
Qed.

(* The foreign notice's world B3 = set_GOT_foreign (set_S_foreign (set_GOT_desk (onann_w1 ..) d') 1) d has Bw's
   state and GOT.n: none of the four stores touches them. *)
Lemma sl2_b3 : forall (Bw b : list byte) d d', length Bw = Z.to_nat TW.W_LEN ->
  TW.S_state (TW.set_GOT_foreign (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_A Bw b) d') 1) d) =
    TW.S_state Bw /\
  TW.GOT_n (TW.set_GOT_foreign (TW.set_S_foreign (TW.set_GOT_desk (onann_w1 timg_A Bw b) d') 1) d) =
    TW.GOT_n Bw.
Proof.
intros Bw b d d' L.
assert (KS : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN -> 0 <= k -> k + Z.of_nat n <= TW.W_LEN ->
  (TW.A_S_state + 4 <= k \/ k + Z.of_nat n <= TW.A_S_state) ->
  (TW.A_GOT_n + 4 <= k \/ k + Z.of_nat n <= TW.A_GOT_n) ->
  length (TW.upd X k (TW.put n v)) = Z.to_nat TW.W_LEN /\
  TW.S_state (TW.upd X k (TW.put n v)) = TW.S_state X /\ TW.GOT_n (TW.upd X k (TW.put n v)) = TW.GOT_n X).
{ intros X k n v LX Hk Hn H1 H2. split; [exact (sl2_len_upd X k n v LX Hk Hn)|].
  unfold TW.S_state, TW.GOT_n. split.
  - apply (sl2_s32_upd X k n v _ LX Hk Hn); [unfold TW.A_S_state, TW.OFF_g_s; lia | exact H1].
  - apply (sl2_s32_upd X k n v _ LX Hk Hn); [unfold TW.A_GOT_n, TW.OFF_GOT; lia | exact H2]. }
assert (K1 : length (onann_w1 timg_A Bw b) = Z.to_nat TW.W_LEN /\
  TW.S_state (onann_w1 timg_A Bw b) = TW.S_state Bw /\ TW.GOT_n (onann_w1 timg_A Bw b) = TW.GOT_n Bw).
{ unfold onann_w1.
  lazymatch goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x end;
    [| split; [exact L | split; reflexivity]].
  unfold TW.set_S_personality.
  apply (KS Bw _ 8%nat _ L); unfold TW.A_S_personality, TW.A_S_state, TW.A_GOT_n, TW.OFF_g_s, TW.OFF_GOT, TW.W_LEN;
    cbn [Z.of_nat Pos.of_succ_nat]; lia. }
destruct K1 as (L1 & S1 & G1).
unfold TW.set_GOT_desk.
pose proof (KS _ TW.A_GOT_desk 4%nat d' L1
  ltac:(unfold TW.A_GOT_desk, TW.OFF_GOT, TW.W_LEN; lia)
  ltac:(unfold TW.A_GOT_desk, TW.OFF_GOT, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_GOT_desk, TW.A_S_state, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_GOT_desk, TW.A_GOT_n, TW.OFF_GOT; cbn [Z.of_nat Pos.of_succ_nat]; lia)) as (L2 & S2 & G2).
unfold TW.set_S_foreign.
pose proof (KS _ TW.A_S_foreign 4%nat 1 L2
  ltac:(unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia)
  ltac:(unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_S_foreign, TW.A_S_state, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_S_foreign, TW.A_GOT_n, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia))
  as (L3 & S3 & G3).
unfold TW.set_GOT_foreign.
pose proof (KS _ TW.A_GOT_foreign 4%nat d L3
  ltac:(unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.W_LEN; lia)
  ltac:(unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_GOT_foreign, TW.A_S_state, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia)
  ltac:(unfold TW.A_GOT_foreign, TW.A_GOT_n, TW.OFF_GOT; cbn [Z.of_nat Pos.of_succ_nat]; lia)) as (L4 & S4 & G4).
split; [rewrite S4, S3, S2; exact S1 | rewrite G4, G3, G2; exact G1].
Qed.

(* The inlined session_lost's three stores (s + 212, s + 168, s + 112) keep GOT.n. *)
Lemma sl2_gotn_w2 : forall X, length X = Z.to_nat TW.W_LEN -> TW.GOT_n (slost_w2 X) = TW.GOT_n X.
Proof.
intros X L. unfold slost_w2, slost_w1, TW.set_S_state, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.GOT_n.
assert (L1 : length (TW.upd X TW.A_S_inflight (TW.put 4 0)) = Z.to_nat TW.W_LEN)
  by (apply sl2_len_upd; [exact L | unfold TW.A_S_inflight, TW.OFF_g_s; lia
                         | unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia]).
assert (L2 : length (TW.upd (TW.upd X TW.A_S_inflight (TW.put 4 0)) TW.A_S_desk_counter_valid (TW.put 4 0)) =
  Z.to_nat TW.W_LEN)
  by (apply sl2_len_upd; [exact L1 | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia
                         | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia]).
rewrite (sl2_s32_upd _ _ 4 _ _ L2);
  [| unfold TW.A_S_state, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | unfold TW.A_GOT_n, TW.A_S_state, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia].
rewrite (sl2_s32_upd _ _ 4 _ _ L1);
  [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia
   | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | unfold TW.A_GOT_n, TW.A_S_desk_counter_valid, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia].
rewrite (sl2_s32_upd _ _ 4 _ _ L);
  [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | unfold TW.A_GOT_n, TW.A_S_inflight, TW.OFF_GOT, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia].
Qed.

(* g_s.notify is not one of the two fields slost_w1 stores. *)
Lemma sl2_notify_w1 : forall X, length X = Z.to_nat TW.W_LEN ->
  TW.u_at (slost_w1 X) (TW.OFF_g_s + 96) 8 = TW.u_at X (TW.OFF_g_s + 96) 8.
Proof.
intros X L. unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight.
assert (L1 : length (TW.upd X TW.A_S_inflight (TW.put 4 0)) = Z.to_nat TW.W_LEN)
  by (apply sl2_len_upd; [exact L | unfold TW.A_S_inflight, TW.OFF_g_s; lia
                         | unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia]).
rewrite (sl2_u_upd _ _ 4 _ _ _ L1);
  [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia
   | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia
   | unfold TW.OFF_g_s; lia
   | unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia].
rewrite (sl2_u_upd _ _ 4 _ _ _ L);
  [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; cbn [Z.of_nat Pos.of_succ_nat]; lia
   | unfold TW.OFF_g_s; lia
   | unfold TW.A_S_inflight, TW.OFF_g_s; cbn [Z.of_nat Pos.of_succ_nat]; lia].
Qed.

(* The notice's stores at slost_w2 B3 are the copy's stores at Bw: an N_STATE notice reads its world through GOT.n
   only, and the state the code loaded is not S_IDLE (onann_wr's last row, slost_wr Bw DIGINET_R_FOREIGN). *)
Lemma sl2_wr_ntc : forall (Bw b B3 : list byte) x,
  TW.GOT_n (slost_w2 B3) = TW.GOT_n (slost_w2 Bw) ->
  TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE ->
  notice_wr (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) x -> onann_wr Bw b x.
Proof.
intros Bw b B3 x EG Hst Hx. unfold onann_wr.
right; right; right; right; right; right; right; right; right.
unfold slost_wr. right; right. split; [exact Hst|]. right.
unfold notice_wr in Hx |- *. unfold slost_ntc in Hx |- *. cbn [TI.n_kind] in Hx |- *.
rewrite <- EG. exact Hx.
Qed.

(* The world relation after the stores of 0 at s + 212, s + 168 and s + 112: slost_w2 B3. *)
Lemma sl2_tw_w2 : forall (rd rd' : Z -> option Z) B3,
  tw_at TMAP_A rd B3 ->
  (forall j, 0 <= j < 4 -> rd' (ONANN_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (ONANN_S + 168 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (ONANN_S + 112 + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (ONANN_S + 212 <= x < ONANN_S + 216) -> ~ (ONANN_S + 168 <= x < ONANN_S + 172) ->
     ~ (ONANN_S + 112 <= x < ONANN_S + 116) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (slost_w2 B3).
Proof.
intros rd rd' B3 Hat HI HD HS HO.
assert (CS : ONANN_S = TA_g_s) by reflexivity.
set (rdm := fun x => if ((ONANN_S + 112 <=? x) && (x <? ONANN_S + 116))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_A rdm (slost_w1 B3)).
{ apply (slh_tw_w1 rd rdm B3 Hat).
  - intros j Hj. unfold rdm.
    assert (Hb : ((ONANN_S + 112 <=? SLOST_S + 212 + j) && (SLOST_S + 212 + j <? ONANN_S + 116))%bool = false)
      by (apply andb_false_iff; right; apply Z.ltb_ge; unfold SLOST_S, ONANN_S; lia).
    rewrite Hb. exact (HI j Hj).
  - intros j Hj. unfold rdm.
    assert (Hb : ((ONANN_S + 112 <=? SLOST_S + 168 + j) && (SLOST_S + 168 + j <? ONANN_S + 116))%bool = false)
      by (apply andb_false_iff; right; apply Z.ltb_ge; unfold SLOST_S, ONANN_S; lia).
    rewrite Hb. exact (HD j Hj).
  - intros x Hx H2 H3. unfold rdm.
    destruct ((ONANN_S + 112 <=? x) && (x <? ONANN_S + 116))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | unfold SLOST_S, ONANN_S in *; lia | unfold SLOST_S, ONANN_S in *; lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite sn_w2_eq.
apply (tw_write TMAP_A rdm rd' _ TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 0 TMAP_A_ok H1 TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HS (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((ONANN_S + 112 <=? x) && (x <? ONANN_S + 116))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* A region cell of n bytes holding 0, read byte by byte through the view. *)
Lemma sl2_av0 : forall (H : word -> bool) (m : word -> option byte) a (n : nat),
  val_mem tfibsegs (mrestrict H m) a n 0 -> forall j, 0 <= j < Z.of_nat n -> aview tfibsegs H m (a + j) = Some 0.
Proof.
intros H m a n HV j Hj. pose proof (HV (Z.to_nat j) ltac:(lia)) as H0.
rewrite Z2Nat.id in H0 by lia. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
lazymatch goal with |- context [?f 0 n (Z.to_nat j)] => unfold f end.
rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma sl2_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The entry states, the notice, the write rights                   *)
(* ------------------------------------------------------------------ *)

Section sl2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of B3. *)
Definition sl2_vals (B3 : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at B3 (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at B3 (TW.OFF_g_s + 104) 8)].
Definition sl2_E (regs : bvmap 5 word) (B3 : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (sl2_vals B3)).

Lemma sl2_entry0 : forall ly2 S2 (W2 : world segs) regs mem2 md2 B3 F sp1,
  trans_onann_cells B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) B3 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= sp1 -> in_app F 1024 ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W2) mem2 a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W2) mem2 (SHADOW_OFF + F / 8 + i)) ->
  onann_slots_arm W2 mem2 sp1 ->
  st_ok_pi segs VAL (sl2_E regs B3) (mkSS ONANN_SL2 sr_atoms SL2_RS None SL2_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL2)) (mrestrict (w_H W2) mem2) (YK11.seg_rom segs)).
Proof.
  intros ly2 S2 W2 regs mem2 md2 B3 F sp1 HZC HAR Htw R9 R18 R19 HF0 HF64 HFsp HFapp Hsp Hsp32 HFG Hpf Hpsh
    (S8 & S16 & S24 & S48).
  unfold onann_slot in S8, S16, S24, S48.
  replace (SHADOW_OFF + (ONANN_S + 96) / 8) with SL2_SH in S8 by reflexivity.
  replace (SHADOW_OFF + (ONANN_S + 104) / 8) with (SL2_SH + 1) in S16 by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  set (E := sl2_E regs B3).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, sl2_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = F)
    by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (sl2_vals B3) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, sl2_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth sl2_vals] in E32, E33.
  pose proof (TWL.u_at_range B3 (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range B3 (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, 0 <= j < 15 -> val_mem segs (mrestrict (w_H W2) mem2) (SL2_SH + j) 1 0).
  { intros j Hj. apply AE2y.val_mem1_of_aview.
    replace (SL2_SH + j) with (FCells.shadow_addr (ONANN_S + 96 + 8 * j)).
    - apply (decode_zshadow_rd B ly2 S2 W2 mem2 md2 ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
      + replace (ONANN_S + 96 + 8 * j) with ((769860 + j) * 8) by (unfold ONANN_S, TA_g_s; lia).
        apply Z.mod_mul. lia.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, SL2_SH, ONANN_S, TA_g_s.
      replace (6158784 + 96 + 8 * j) with ((769860 + j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold SL2_RS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SL2_RS SL2_R_sh SL2_R_p SL2_R_gs
        SL2_R_dcv SL2_R_inf SL2_R_shg SL2_R_sl base_val]; rewrite ?U9, ?U18, ?U19.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        apply sl2_inG. unfold TW.SZ_g_s. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff 32 0) (TW.u_at B3 (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold ONANN_S, TA_g_s; lia |].
           replace (0 + (ONANN_S + 96)) with (TA_g_s + 96) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_A B3 TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 33 0) (TW.u_at B3 (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold ONANN_S, TA_g_s; lia |].
           replace (0 + (ONANN_S + 104)) with (TA_g_s + 104) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_A B3 TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply sl2_inG. unfold TW.SZ_g_s. lia.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply sl2_inG. unfold TW.SZ_g_s. lia.
    + split; [unfold SL2_SH; lia|]. split; [unfold SL2_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 SL2_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0 ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (SL2_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 1 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (SL2_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 2 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (SL2_SH + 9) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 9 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (SL2_SH + 14) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 14 ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ sp1 8 8 (SLit SL2_SH) SL2_SH);
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SL2_SH; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W2) mem2 _ _ S8).
      * apply (chunk_ok_val segs E _ sp1 16 8 (SLit (SL2_SH + 1)) (SL2_SH + 1));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SL2_SH; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W2) mem2 _ _ S16).
      * apply (chunk_ok_val segs E _ sp1 24 8 (SLit (ONANN_S + 96)) (ONANN_S + 96));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold ONANN_S, TA_g_s; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W2) mem2 _ _ S24).
      * apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold ONANN_S, TA_g_s; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W2) mem2 _ _ S48).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, SL2_RS, SL2_R_sh, SL2_R_p, SL2_R_gs, SL2_R_dcv, SL2_R_inf, SL2_R_shg, SL2_R_sl.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SL2_SH, SHADOW_OFF, ONANN_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold SL2_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U18, U19.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma sl2_entry : forall ly2 S2 (W2 : world segs) regs mem2 md2 B3 F sp1,
  trans_onann_cells B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) B3 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 25 = w64 (ONANN_S + 104) -> YK11.getr regs 26 = w64 (SL2_SH + 2) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= sp1 -> in_app F 1024 ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W2) mem2 a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W2) mem2 (SHADOW_OFF + F / 8 + i)) ->
  onann_slots_arm W2 mem2 sp1 ->
  st_ok_pi segs VAL (sl2_E regs B3) ss_sl2
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL2)) mem2 (YK11.seg_rom segs))).
Proof.
  intros ly2 S2 W2 regs mem2 md2 B3 F sp1 HZC HAR Htw R9 R18 R19 R20 R24 R25 R26 HF0 HF64 HFsp HFapp Hsp Hsp32 HFG
    Hpf Hpsh HSL.
  rewrite restrict_mkst_fx.
  pose proof (sl2_entry0 ly2 S2 W2 regs mem2 md2 B3 F sp1 HZC HAR Htw R9 R18 R19 HF0 HF64 HFsp HFapp Hsp Hsp32 HFG
    Hpf Hpsh HSL) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (ONANN_S + 104) H2 R25 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (SL2_SH + 2) H3 R26 eq_refl) as H4.
  exact H4.
Qed.

(* The symbolic state at +0x714 (after notice returns). *)
Lemma sl2_entry3 : forall (W : world segs) regs mem F,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_sl23
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (ONANN_SL2 + 0xb8))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R19 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [])).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_sl23.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SL2_R_sh base_val]. rewrite U19.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The notice at n3 = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma sl2_ntc_at : forall ly2 S2 (W2 : world segs) memN mdN (regsC : bvmap 5 word) B3 F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  F = frame_addr ly2 ONANN_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  F + 1024 <= spZ regsC - NOTICE_STK ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + 32)
    (map DSpec.bz (WN.ntc_state_bytes 0 (TW.S_state (slost_w1 B3)) TS0.DIGINET_R_FOREIGN)) ->
  trans_ntc_at B ly2 S2 W2 memN regsC NOTICE_STK (F + 32) (slost_ntc B3 TS0.DIGINET_R_FOREIGN).
Proof.
  intros ly2 S2 W2 memN mdN regsC B3 F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS ly2 S2 W2 memN mdN ONANN_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (old := TW.S_state (slost_w1 B3)) in *.
  assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes ONANN_CID) with 1024.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (TransportGNotice.frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 32) 72);
          [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes 0 old TS0.DIGINET_R_FOREIGN).
  split; [exact HNB|].
  unfold slost_ntc. fold old.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 TS0.DIGINET_R_FOREIGN ++
    repeat (DSpec.b8 0) 56) 48 8 = 0) by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
  split; [WN.ntc_field; apply WN.swrap32_mod; cbv [TS0.DIGINET_R_FOREIGN]; lia |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B ly2 S2 W2 memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT) are apart from n3 (a frame is not image), from its empty body,
   and from TF (onann_apart: they are bytes of onann_wr). *)
Lemma sl2_apart : forall ly2 S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe)
    (Bw b B3 : list byte) F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 -> In (ONANN_CID, pos) (frames S2) ->
  F = frame_addr ly2 ONANN_CID pos ->
  onann_apart TF Bw b ->
  (forall x, notice_wr (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) x -> onann_wr Bw b x) ->
  notice_apart W memN (F + 32) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) TF (slost_w2 B3).
Proof.
  intros ly2 S2 W2 mem2 md2 W memN TF Bw b B3 F pos LAWS HAR Hin EF Hap Hinc x Hx.
  pose proof (Hinc x Hx) as Hw.
  pose proof (TransportGNotice.notice_wr_G (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) x Hx) as Hg.
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes ONANN_CID) with 1024; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x Hg).
  - intros NB _ _. split.
    + unfold slost_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (SlostNtc.v sn_reg, which its section keeps local). *)
Ltac sn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sn_reg: no match for" T; fail
  end.

(* The write rights of runs 1 and 2 (the regions of SL2_RS): n3's shadow bytes and first bytes are bytes of the own
   frame, the three g_s fields bytes of G, the shadow bytes and the slots read only. *)
Ltac sl2_awr U19 U18 EFA :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes ONANN_CID / 8) with 128; lia |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes ONANN_CID) with 1024; lia |];
  do 3 (apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply sl2_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s; lia |]);
  do 2 (apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sl2_main : @onann_sl2_stmt fx rc B MT.
Proof.
unfold onann_sl2_stmt. intros REL. unfold onann_sl2_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B2 B3 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HONC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGN).
pose proof CALLEES as (CSM & CLEAF & CPF & CBCMP & CMS & CN & CWK & CMO & CSH).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
  Hm0 & HTF & Hoffg & Hrom & Hapart & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw2 & (Hb2a & d' & EB2) &
  Hn3 & (d & EB3) & HSt & Hm & Hgf3 & HSL).
pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R24 & R25 & R26) & R23) & R21).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ONANN_FBYTES in HFc, HFapp, HFLw.
replace (F + 1024 - 8) with (F + 1016) in HFLw by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _).
clear HJi memS.
destruct (onann_cur_ar B MT LAWS HFIX (proj1 HCUR)) as (_ & _ & Elo2 & Ehi2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & Hceil' & Hslo' & Hshi' & H47' & _).
assert (HSS : ONANN_STK = 208 + WAKE_STK) by reflexivity.
assert (HWS : NOTICE_STK + 144 <= WAKE_STK).
{ unfold WAKE_STK, WAKE_FRAME, WAKE_ALIGN.
  pose proof (Z.le_max_r ESTACK (Z.max SENDCTL_STK NOTICE_STK)).
  pose proof (Z.le_max_r SENDCTL_STK NOTICE_STK). lia. }
assert (HNS : NOTICE_STK = 48 + 2 * ESTACK) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HEV : ONANN_EV = 0) by reflexivity.
assert (Hsp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (HFsp : F + 1024 <= sp1) by lia.
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the own frame at the cut *)
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite Hfa2; symmetry; exact EF).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite EFA in HFb, HFsh.
change (fs_frame_bytes ONANN_CID) with 1024 in HFb. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
set (FL := flag_addr lyc ONANN_CID pos) in *.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL HAR2 Hfrs Hbl
  HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (HFG : F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 1024) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 1024 /\ ONANN_S <= x < ONANN_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONANN_S) as [h3|h3]; [exists ONANN_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos x HAR2 Hin);
    [rewrite EFA; change (fs_frame_bytes ONANN_CID) with 1024; lia|].
  exact (trans_g_img x (sl2_inG x Hx2)). }
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ rewrite DF. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
(* the model on this path *)
assert (HLB3 : length B3 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
assert (HLBw : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (slh_w1_facts B3 HLB3) as (EST1 & _).
destruct (slh_w1_facts Bw HLBw) as (ESTw & _).
assert (Hst1 : TW.S_state (slost_w1 B3) <> TS0.DIGINET_S_IDLE).
{ rewrite EST1. destruct HSt as [Hs | Hs]; rewrite Hs;
  cbv [TS0.DIGINET_S_IDLE TS0.DIGINET_S_ONLINE TS0.DIGINET_S_WAKING]; lia. }
clear HSt.
destruct (sn_model TF B3 TS0.DIGINET_R_FOREIGN Bw' Hm Hst1) as (HNT & HNM).
destruct (sl2_b3 Bw b d d' HLBw) as (EBS & EBG).
rewrite <- EB2, <- EB3 in EBS, EBG.
assert (EG2 : TW.GOT_n (slost_w2 B3) = TW.GOT_n (slost_w2 Bw)).
{ rewrite (sl2_gotn_w2 B3 HLB3), (sl2_gotn_w2 Bw HLBw). exact EBG. }
assert (Hstw : TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE) by (rewrite ESTw, <- EBS, <- EST1; exact Hst1).
assert (HWRN : forall x, notice_wr (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) x -> onann_wr Bw b x)
  by (intros x Hx; exact (sl2_wr_ntc Bw b B3 x EG2 Hstw Hx)).
(* +0x65c .. +0x6c0: the stores at s + 212 and s + 168, s4 = n3, n3's shadow bytes := 0, `jal __asan_memset` *)
assert (R26' : YK11.getr regs2 26 = w64 (SL2_SH + 2)) by (rewrite R26; reflexivity).
pose proof (sl2_entry ly2 S2 W2 regs2 mem2 md2 B3 F sp1 HONC HAR2 Htw2 R9 R18 R19 R20 R24 R25 R26' HF0 HF64 HFsp
  HFapp Hsp1b (proj2 Hsp1) HFG
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia)))) HSL) as HS.
set (E0 := sl2_E regs2 B3) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sl2_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, sl2_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew E0 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs SL2_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK SL2_B0.
{ sl2_awr U19 U18 EFA. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ sl2_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sl2_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(rewrite ?U19, ?U18 in Hx; unfold sl2_Z, ONANN_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
          | right; right; right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONANN_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite EFA, ESH in HFsh1. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh1.
pmkst HS.
sn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10 ltac:(cbn [sv_denot]; rewrite U18; reflexivity).
sn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
sn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28372)) Q1 ltac:(apply codeptr_val; exact HEI).
sn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
sn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x6c0: __asan_memset (n3 + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (CMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 md1
    (k + 0) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 28372)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + lia.
  - apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
  - apply (TransportGNotice.frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 48) 56);
      [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2x c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ sl2_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a)
  by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM
  [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 19%nat (SHADOW_OFF + F / 8)); [exact U19 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 18%nat F); [exact U18 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold SL2_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia].
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U19b : bv_unsigned (ew E1 19) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U19).
assert (U18b : bv_unsigned (ew E1 18) = F) by (rewrite E1lo by lia; exact U18).
assert (SHOK1 : sh_ok segs SL2_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
assert (ZMM : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 48) + (a - (F + 48))) by lia. rewrite (HsetM (a - (F + 48)) ltac:(lia)).
  reflexivity. }
clear dependent ms.
(* +0x6c4 .. +0x710: n3's first 16 bytes, the store of 0 at s + 112, the loads of g_s.notify and g_s.notify_ctx, up to
   `jalr a2` *)
paj_run_tok RUN HS HJ2 SHOK1 SL2_B0.
{ sl2_awr U19b U18b EFA. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ sl2_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sl2_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(rewrite ?U19b, ?U18b in Hx; unfold sl2_Z, ONANN_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
          | right; right; right; right; left; lia]). }
assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (ONANN_S + 112 <= x < ONANN_S + 116) \/
    (ONANN_S + 168 <= x < ONANN_S + 172) \/ (ONANN_S + 212 <= x < ONANN_S + 216) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13)) HFr); [| lia |].
  - intros b0 wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U19b, ?U18b in Hx; unfold ONANN_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
            | right; right; right; right; lia]).
  - cbv beta. unfold ONANN_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | [Hx | [Hx | Hx]]]]; [lia | destruct HFG as [Hg | Hg]; lia | destruct HFG as [Hg | Hg]; lia
      | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ sl2_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS3.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS4.
cbn [ms_mem restrict] in RS0, RS1, RS2, RS3, RS4.
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
set (old := TW.S_state B3) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
assert (D21 : sv_denot E1 (SOff 21 0) = Z_to_bv 64 old).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 32 8 (SLit 2) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 40 4 (SOff 21 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 44 4 (SLit 5) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP12.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158896 4 (SLit 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158952 4 (SLit 0) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VD.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158996 4 (SLit 0) RS4
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VI.
cbn [base_val] in VP0, VP8, VP12, VG, VD, VI. rewrite U18b in VP0, VP8, VP12. rewrite D21 in VP8.
change (N.to_nat 8) with 8%nat in VP0. change (N.to_nat 4) with 4%nat in VP8, VP12, VG, VD, VI.
change (bv_unsigned (sv_denot E1 (SLit 2)) mod 2 ^ (8 * Z.of_N 8)) with 2 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 5)) mod 2 ^ (8 * Z.of_N 4)) with TS0.DIGINET_R_FOREIGN in VP12.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG, VD, VI.
apply (sn_vm_w _ _ 4 old ltac:(lia)) in VP8. change (N.to_nat 4) with 4%nat in VP8.
pose proof (sn_nb (w_H W2) (ms_mem ms) F old TS0.DIGINET_R_FOREIGN VP0 VP8 VP12 ZMN) as HNB.
rewrite <- EST1 in HNB.
(* what the call kept, from its entry to the call of notice *)
assert (HSZ : forall a, sl2_Z F sp1 a ->
  (spZ regs - ONANN_STK <= a < spZ regs) \/ dkg_nf ONANN_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]].
  - right; left; right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - right; right. apply sl2_inG. unfold TW.SZ_g_s. lia.
  - right; right. apply sl2_inG. unfold TW.SZ_g_s. lia.
  - right; right. apply sl2_inG. unfold TW.SZ_g_s. lia.
  - left; lia. }
pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2
  mem2 (ms_mem ms) (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b) (sl2_Z F sp1)
  HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN) as KCN.
(* the world slost_w2 B3 at the call memory *)
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (ONANN_S + 212 <= x < ONANN_S + 216) ->
  ~ (ONANN_S + 168 <= x < ONANN_S + 172) -> ~ (ONANN_S + 112 <= x < ONANN_S + 116) -> ~ sl2_Z F sp1 x).
{ intros x Hx H1 H2 H3 Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes ONANN_CID) with 1024; lia | exact (trans_g_img x Hx)].
  - exact (H3 Hz).
  - exact (H2 Hz).
  - exact (H1 Hz).
  - lia. }
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (slost_w2 B3)).
{ apply (sl2_tw_w2 (aview segs (w_H W2) mem2) _ B3 Htw2).
  - intros j Hj. replace (ONANN_S + 212 + j) with (6158996 + j) by (unfold ONANN_S, TA_g_s; lia).
    exact (sl2_av0 _ _ _ 4 VI j ltac:(cbn; lia)).
  - intros j Hj. replace (ONANN_S + 168 + j) with (6158952 + j) by (unfold ONANN_S, TA_g_s; lia).
    exact (sl2_av0 _ _ _ 4 VD j ltac:(cbn; lia)).
  - intros j Hj. replace (ONANN_S + 112 + j) with (6158896 + j) by (unfold ONANN_S, TA_g_s; lia).
    exact (sl2_av0 _ _ _ 4 VG j ltac:(cbn; lia)).
  - intros x Hx H1 H2 H3. destruct Hx as (o & b0 & n0 & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x).
    { unfold inG. apply Exists_exists. exists (b0, n0).
      split; [exact (TMAP_A_in_G o b0 n0 Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    exact (NZG x HxG H1 H2 H3). }
(* the registers at `jalr a2` *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite E1lo by lia. unfold E0, sl2_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (sl2_vals B3) 0) as X. cbn [Nat.add nth sl2_vals] in X. rewrite X.
  rewrite <- (sl2_notify_w1 B3 HLB3), <- (sn_notify B3 HLB3), HNT. reflexivity. }
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U18b; reflexivity).
sn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
sn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
sn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
sn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sn_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sn_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) T19
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sn_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* +0x710: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E1 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (28448 + 4) = 0x88188) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (28448 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros E; apply Hr; rewrite E; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 32)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
eapply SRr_bind.
{ exact (CN fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + 0) regsC
    (F + 32) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) TF (slost_w2 B3) Bw'
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (sl2_ntc_at ly2 S2 W2 (ms_mem ms) md3 regsC B3 F pos LAWS HARN Hin (eq_sym EFA) HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) ZSN HNB)
    (onann_tf_call B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) md3 pos regs regsC NOTICE_STK TF Bw b
       HARc HARN Hfrs Hperm Hfa2 Elo2 Ehi2 KCN Hoffg ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_LO in Gh; lia)
    PTW HNM
    (sl2_apart ly2 S2 W2 mem2 md2 W2 (ms_mem ms) TF Bw b B3 F pos LAWS HAR2 Hin (eq_sym EFA) Hapart HWRN)
    ltac:(intros HD; exfalso; unfold slost_ntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
    ltac:(rewrite HEV in Hev; unfold NOTICE_EV; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by lia.
assert (Hin3 : In (ONANN_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
assert (EF3 : frame_addr ly3 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 ONANN_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. apply Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP3 19 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T19. exact R19. }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onann_wr Bw b)
    (notice_wr (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN)) (dkg_nf ONANN_CID F FL)).
  - lia.
  - lia.
  - exact Hfa2.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (HWRN a Ha). }
(* +0x714 .. +0x738: n3's shadow bytes := 0xf8, to the release cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + (28448 + 4))) with (Z_to_bv 64 (BASE + (ONANN_SL2 + 0xb8))).
pose proof (sl2_entry3 W3 regs3 mem3 F R3_19 HF0 HF64 ltac:(lia)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19c : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs SL2_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SL2_B0 ONANN_FNREL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U19c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_nf_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc ly3 S3 W3 mem3 md4 (ms_mem ms4)
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b) HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL
    KC3); [| exact GA4].
  intros a Ha Hn. apply KR4; [exact Ha|]. intros Hx. apply Hn. right. left.
  change (fs_frame_bytes ONANN_CID / 8) with 128. lia. }
pmkst HS3.
(* the registers the release reads *)
sn_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 19) (YK11.getr regs3 (Z_to_bv 5 19)) F19
  ltac:(cbn [sv_denot]; rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) F23
  ltac:(cbn [sv_denot]; rewrite (EE3 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words above sp1 and the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite USPC in K31. rewrite K31 by lia.
  apply KAN; [lia|]. unfold sl2_Z, ONANN_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 1016 + i) = aview segs (w_H W2) mem2 (F + 1016 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 ONANN_CID pos (F + 1016 + i) Hin).
  - apply KAN; [lia|]. unfold sl2_Z, ONANN_S, TA_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]];
      [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
      | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
      | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - intros Hw.
    pose proof (TransportGNotice.notice_wr_G (slost_w2 B3) (slost_ntc B3 TS0.DIGINET_R_FOREIGN) (F + 1016 + i) Hw)
      as Hg.
    apply (N2 (F + 1016 + i)); [left; change (fs_frame_bytes ONANN_CID) with 1024; lia|].
    exact (trans_g_img _ Hg). }
assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly3 S3 W3 (ms_mem ms4) md5 0 (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
    split; [rewrite HEV; lia|].
    split; [exact Hfrs3|].
    split; [exact (Permutation_trans Hperm3 Hperm)|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold ONANN_FBYTES. change (flag_addr lyc ONANN_CID pos) with FL. rewrite <- HFLw.
      replace (F + 1024 - 8) with (F + 1016) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite (sn_gfn' TF B3 TS0.DIGINET_R_FOREIGN Bw' HLB3 HNM). exact Hgf3.
- assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
  split; [split|].
  + exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2)).
  + split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
      (eq_trans T3 (eq_sym Hgp))))|].
    split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
      (eq_trans T4 (eq_sym Htp))))|].
    split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8)))|].
    split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)))|].
    split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate))
      (eq_trans T18 R18)))|].
    exact (eq_trans F19 (eq_trans (CH 19 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T19 R19))).
  + exact (eq_trans F23 (eq_trans (CH 23 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T23 R23))).
Qed.

End sl2.

Theorem onann_piece_sl2 : forall fx rc B MT, @onann_sl2_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@sl2_main fx rc B MT). Qed.

Print Assumptions onann_piece_sl2.
