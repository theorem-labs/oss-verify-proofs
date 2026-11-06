(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 1019 of its 1158 lines of code are new or changed and 626 lines of the source are left out. *)
(* on_announce_seg_sl1: Theorem onann_piece_sl1 : onann_sl1_stmt (lib/A/Prog/OnannCut.v), the first inlined
   session_lost of the walk of on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce), code
   +0x424 .. +0x514 (0x87e98 .. 0x87f88; diginet_session.c:203, :162-164, set_state :83-85) at the world
   Bx = set_S_foreign B2 0 with why = DIGINET_R_DESK_OFFLINE, from the cut onann_sl1_at to the cut onann_wk_at (+0x518).
   Registers: s4 = s, s8 = the shadow base, s9 = s + 104, s10 = the shadow byte of s + 112, s2 = the frame F, s3 = its
   first shadow byte, s1 = sp1 (spill slots: the shadow bytes of s + 96 and s + 104 at sp1 + 8 and sp1 + 16, s + 96 at
   sp1 + 24, s + 112 at sp1 + 48, now at sp1 + 0).
     run 1 +0x424 .. +0x488  the checked stores of 0 at s + 212 and s + 168 (slost_w1 Bx), s5 = n2 = F + 144, n2's
                             shadow bytes 18 .. 26 := 0, a0 = n2 + 16, a1 = 0, a2 = 56; `jal __asan_memset` (+0x488)
                             through TransportGCg.v gx_intrin_at;
     run 2 +0x48c .. +0x4dc  the 8-byte stores of 2 at n2 and of (3 << 32) + 2 at n2 + 8 (old_state 2 = S_ONLINE,
                             reason 3), the checked store of 0 at s + 112 (slost_w2 Bx), the checks of the 8-byte loads
                             at s + 96 and s + 104, a2 = notify, a0 = notify_ctx, a1 = n2; `jalr a2` (+0x4dc) calls
                             notice (notice_cg.v transport_notice_cg) with session_lost_cg.v slost_ntc Bx 3, whose result
                             B4 is session_lost_m's (SlostNtcKit.v sn_model); its acall_kept_g folds into the walk's by
                             TransportGCg.v dk_kept_trans_nf_g;
     run 3 +0x4e0 .. +0x514  n2's shadow bytes := 0xf8, the check of the 4-byte load at s + 112 (s10), a0 = the load at
                             s + 112 = S_state B4; the proof ends by onann_wk_at.
   Each run is TransportGRunA.v paj_run_x / paj_run_to_x over a symbolic state whose regions are the frame's bytes and
   shadow bytes it writes, the spill slots, the g_s fields (absolute) and g_s's literal-0 shadow bytes
   (trans_onann_cells); what the call keeps crosses each run by TransportGFrame.v dk_kept_nfz_gw. Lemmas of note:
   sl1_ntc_at (the notice as notice's statement reads it), sl1_tw_w2 (the world after the three g_s stores),
   on_announce_seg_kit.v onann_tf_call / onann_rom_call / onann_wr_slost / onann_slost_res. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostNtcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SlostHead SlostNtc TransportGNotice.
Module SN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.SlostNtc.
Module SH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YCbqM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YCbq.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104, s + 112, s + 168 and s + 212 have the bytes 1, 2, 9 and 14 after
   it. *)
Definition SL1_SH : Z := 2148220740.
Lemma sl1_sh_eq : SL1_SH = SHADOW_OFF + (ONANN_S + 96) / 8 /\ SL1_SH + 2 = SHADOW_OFF + (ONANN_S + 112) / 8 /\
  SL1_SH + 9 = SHADOW_OFF + (ONANN_S + 168) / 8 /\ SL1_SH + 14 = SHADOW_OFF + (ONANN_S + 212) / 8.
Proof. repeat split; reflexivity. Qed.

(* Runs 1 and 2 (+0x424 .. +0x4dc): n2's shadow bytes 18 .. 26 (s3, atom 19), n2's first 16 bytes (s2, atom 18), the
   spill slots (s1, atom 9), g_s.notify (atom 32), g_s.notify_ctx (atom 33) and g_s.state, g_s.desk_counter_valid,
   g_s.inflight (absolute), and the five shadow bytes of g_s the code reads (literal 0). *)
Definition SL1_R_sh : YP09.region := YP09.mkRegion (Some 19%nat) 18 27 18 27 [].
Definition SL1_R_n2 : YP09.region := YP09.mkRegion (Some 18%nat) 144 160 144 160 [].
Definition SL1_R_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 56 0 0
    [YP09.mkChunk 8 (YP09.CVal 8 (SLit SL1_SH)); YP09.mkChunk 16 (YP09.CVal 8 (SLit (SL1_SH + 1)));
     YP09.mkChunk 24 (YP09.CVal 8 (SLit (ONANN_S + 96))); YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition SL1_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 116) (ONANN_S + 112) (ONANN_S + 116)
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition SL1_R_dcv : YP09.region :=
  YP09.mkRegion None (ONANN_S + 168) (ONANN_S + 172) (ONANN_S + 168) (ONANN_S + 172) [].
Definition SL1_R_inf : YP09.region :=
  YP09.mkRegion None (ONANN_S + 212) (ONANN_S + 216) (ONANN_S + 212) (ONANN_S + 216) [].
Definition SL1_R_shg : YP09.region :=
  YP09.mkRegion None SL1_SH (SL1_SH + 15) 0 0
    [YP09.mkChunk SL1_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SL1_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SL1_SH + 2) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SL1_SH + 9) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SL1_SH + 14) (YP09.CVal 1 (SLit 0))].
Definition SL1_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 6);
           (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].
Definition SL1_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 25) (SLit (ONANN_S + 104))) (Z_to_bv 5 26) (SLit (SL1_SH + 2)).
Definition ss_sl1 : sstate :=
  mkSS ONANN_SL1 SL1_REGS [SL1_R_sh; SL1_R_n2; SL1_R_slot; SL1_R_gs; SL1_R_dcv; SL1_R_inf; SL1_R_shg] None SL1_FACTS.
Definition SL1_Bx : sv := SLit 0.
Definition SL1_B0 : Z * Z := (0, 0).

(* Run 3 (+0x4e0 .. +0x514, after notice returns): n2's shadow bytes, the slot sp1 + 48, g_s.state (atom 32) and the
   shadow byte of s + 112. *)
Definition SL1_C3 : Z := AF_on_announce + 0x4e0.
Definition SL1_R3_sh : YP09.region := YP09.mkRegion (Some 19%nat) 18 27 18 27 [].
Definition SL1_R3_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 56 0 0 [YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition SL1_R3_st : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition SL1_R3_shg : YP09.region :=
  YP09.mkRegion None (SL1_SH + 2) (SL1_SH + 3) 0 0 [YP09.mkChunk (SL1_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition SL1_FACTS3 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition SL1_REGS3 : list sv := sr_set sr_atoms (Z_to_bv 5 26) (SLit (SL1_SH + 2)).
Definition ss_sl13 : sstate :=
  mkSS SL1_C3 SL1_REGS3 [SL1_R3_sh; SL1_R3_slot; SL1_R3_st; SL1_R3_shg] None SL1_FACTS3.

(* The bytes runs 1 and 2 may write (the windows of ss_sl1's regions), and with them the memset's destination and the
   stack window of the intrinsic below sp1. *)
Definition sl1_W (F x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) \/ (F + 144 <= x < F + 160) \/
  (ONANN_S + 112 <= x < ONANN_S + 116) \/ (ONANN_S + 168 <= x < ONANN_S + 172) \/
  (ONANN_S + 212 <= x < ONANN_S + 216).
Definition sl1_Z (F sp1 x : Z) : Prop := sl1_W F x \/ (F + 160 <= x < F + 216) \/ (sp1 - ESTACK <= x < sp1).

(* ------------------------------------------------------------------ *)
(* 2. Small lemmas and tactics                                         *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma sl1_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
Qed.

Lemma sl1_le0 : forall (j : nat), YO0f.le_byte 0 4 j = 0.
Proof. intros j. unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. Qed.

(* A store of 4 zero bytes at g_s + k: the world relation after it (TWorldG.v tw_write). *)
Lemma sl1_tw_st0 : forall (rd rd' : Z -> option Z) Bx k,
  0 <= k -> k + 4 <= TW.SZ_g_s ->
  tw_at TMAP_A rd Bx ->
  (forall j, 0 <= j < 4 -> rd' (TA_g_s + k + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_s + k <= x < TA_g_s + k + 4) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.upd Bx (TW.OFF_g_s + k) (TW.put 4 0)).
Proof.
intros rd rd' Bx k Hk0 Hk Hat HI HO.
apply (tw_write TMAP_A rd rd' Bx TW.OFF_g_s TA_g_s TW.SZ_g_s k 4 0 TMAP_A_ok Hat TMAP_A_g_s); [lia | lia | |].
- intros j Hj. rewrite sl1_le0. exact (HI (Z.of_nat j) ltac:(lia)).
- intros x Hx Hn. apply HO; [exact Hx | lia].
Qed.

(* A reader that is r' on [lo, hi) and r elsewhere. *)
Definition sl1_mix (lo hi : Z) (r r' : Z -> option Z) (x : Z) : option Z :=
  if ((lo <=? x) && (x <? hi))%bool then r' x else r x.
Lemma sl1_mix_in : forall lo hi r r' x, lo <= x < hi -> sl1_mix lo hi r r' x = r' x.
Proof.
intros lo hi r r' x H. unfold sl1_mix.
replace ((lo <=? x) && (x <? hi))%bool with true; [reflexivity|].
symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma sl1_mix_out : forall lo hi r r' x, ~ (lo <= x < hi) -> sl1_mix lo hi r r' x = r x.
Proof.
intros lo hi r r' x H. unfold sl1_mix.
replace ((lo <=? x) && (x <? hi))%bool with false; [reflexivity|].
symmetry. apply andb_false_iff.
destruct (Z_le_gt_dec lo x) as [h|h]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
Qed.

(* The world relation after the three stores of the inlined session_lost (s + 212, s + 168, then s + 112). *)
Lemma sl1_tw_w2 : forall (rd rd' : Z -> option Z) Bx,
  tw_at TMAP_A rd Bx ->
  (forall j, 0 <= j < 4 -> rd' (TA_g_s + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (TA_g_s + 168 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (TA_g_s + 112 + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_s + 212 <= x < TA_g_s + 216) -> ~ (TA_g_s + 168 <= x < TA_g_s + 172) ->
     ~ (TA_g_s + 112 <= x < TA_g_s + 116) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (slost_w2 Bx).
Proof.
intros rd rd' Bx Hat HI HD HS HO.
set (r1 := sl1_mix (TA_g_s + 212) (TA_g_s + 216) rd rd').
set (r2 := sl1_mix (TA_g_s + 168) (TA_g_s + 172) r1 rd').
assert (EQ : slost_w2 Bx = TW.upd (TW.upd (TW.upd Bx (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0))
  (TW.OFF_g_s + 112) (TW.put 4 0)) by reflexivity.
rewrite EQ.
assert (T1 : tw_at TMAP_A r1 (TW.upd Bx (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (sl1_tw_st0 rd r1 Bx 212); [lia | unfold TW.SZ_g_s; lia | exact Hat | |].
  - intros j Hj. unfold r1. rewrite sl1_mix_in by lia. exact (HI j Hj).
  - intros x Hx Hn. unfold r1. apply sl1_mix_out. lia. }
assert (T2 : tw_at TMAP_A r2 (TW.upd (TW.upd Bx (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0))).
{ apply (sl1_tw_st0 r1 r2 _ 168); [lia | unfold TW.SZ_g_s; lia | exact T1 | |].
  - intros j Hj. unfold r2. rewrite sl1_mix_in by lia. exact (HD j Hj).
  - intros x Hx Hn. unfold r2. apply sl1_mix_out. lia. }
apply (sl1_tw_st0 r2 rd' _ 112); [lia | unfold TW.SZ_g_s; lia | exact T2 | exact HS |].
intros x Hx Hn. unfold r2, r1.
destruct (Z_le_gt_dec (TA_g_s + 168) x) as [h1|h1]; [destruct (Z_lt_ge_dec x (TA_g_s + 172)) as [h2|h2]|].
- rewrite sl1_mix_in by lia. reflexivity.
- rewrite sl1_mix_out by lia.
  destruct (Z_le_gt_dec (TA_g_s + 212) x) as [h3|h3]; [destruct (Z_lt_ge_dec x (TA_g_s + 216)) as [h4|h4]|].
  + rewrite sl1_mix_in by lia. reflexivity.
  + rewrite sl1_mix_out by lia. apply HO; [exact Hx | lia | lia | lia].
  + rewrite sl1_mix_out by lia. apply HO; [exact Hx | lia | lia | lia].
- rewrite sl1_mix_out by lia.
  destruct (Z_le_gt_dec (TA_g_s + 212) x) as [h3|h3]; [destruct (Z_lt_ge_dec x (TA_g_s + 216)) as [h4|h4]|].
  + rewrite sl1_mix_in by lia. reflexivity.
  + rewrite sl1_mix_out by lia. apply HO; [exact Hx | lia | lia | lia].
  + rewrite sl1_mix_out by lia. apply HO; [exact Hx | lia | lia | lia].
Qed.

(* The 8-byte store of (3 << 32) + 2 at n2 + 8: old_state 2, then reason 3. *)
Lemma sl1_split8 : forall (m : word -> option byte) a,
  val_mem tfibsegs m a 8 12884901890 -> val_mem tfibsegs m a 4 2 /\ val_mem tfibsegs m (a + 4) 4 3.
Proof.
intros m a H. split; intros kk Hk.
- rewrite (H kk ltac:(lia)). do 2 f_equal.
  destruct kk as [|[|[|[|kk]]]]; try lia; vm_compute; reflexivity.
- replace (a + 4 + Z.of_nat kk) with (a + Z.of_nat (4 + kk)) by lia.
  rewrite (H (4 + kk)%nat ltac:(lia)). do 2 f_equal.
  destruct kk as [|[|[|[|kk]]]]; try lia; vm_compute; reflexivity.
Qed.

(* The sign-extended 4-byte load of g_s's state (atom 32) is the model's S_state. *)
Lemma sl1_sext : forall E B4, ew E 32 = Z_to_bv 64 (TW.u_at B4 (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state B4).
Proof.
intros E B4 H. pose proof (TWL.u_at_range B4 (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* g_s.notify is not one of the three fields the inlined session_lost stores. *)
Lemma sl1_notify : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.S_notify (slost_w2 Bx) = TW.u_at Bx (TW.OFF_g_s + 96) 8.
Proof.
intros Bx L. rewrite (sn_notify Bx L).
unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight.
rewrite !rd_upd_W by wside. reflexivity.
Qed.

(* The world of the cut, Bx = set_S_foreign B2 0 with B2 = set_GOT_desk (onann_w1 ..) d, has Bw's GOT.n and state. *)
Lemma sl1_x_facts : forall Bw b B2 d Bx, length Bw = Z.to_nat TW.W_LEN ->
  B2 = TW.set_GOT_desk (onann_w1 timg_A Bw b) d -> Bx = TW.set_S_foreign B2 0 ->
  TW.GOT_n Bx = TW.GOT_n Bw /\ TW.S_state Bx = TW.S_state Bw.
Proof.
intros Bw b B2 d Bx L -> ->. unfold onann_w1.
destruct (TN.diginet_personality_from_name (onann_name b)) as [i|];
  unfold TW.set_S_foreign, TW.set_GOT_desk, TW.GOT_n, TW.S_state; try unfold TW.set_S_personality;
  split; rewrite !rd32_upd_W by wside; reflexivity.
Qed.

(* The rest of the model after the cut: session_lost_m's result B4, then the wake test. *)
Lemma sl1_k_split : forall (TF : option TI.tframe) Bx now Bw',
  onann_k_sl1 timg_A TF Bx now = Some (Bw', tt) ->
  exists B4, TSS.session_lost_m timg_A TF Bx TS0.DIGINET_R_DESK_OFFLINE = Some (B4, tt) /\
    onann_k_wk timg_A TF B4 now = Some (Bw', tt).
Proof.
intros TF Bx now Bw' H. unfold onann_k_sl1 in H. revert H.
destruct (TSS.session_lost_m timg_A TF Bx TS0.DIGINET_R_DESK_OFFLINE) as [[B4 u]|]; intros H; [|discriminate H].
destruct u. exists B4. split; [reflexivity | exact H].
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac sl1_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sl1_reg: no match for" T; fail
  end.
(* The valuation of a symbolic state HS (after a run that stops at a call, the state is in the st_ok form). *)
Ltac sl1_env HS X :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ _ => set (X := EF) in HS
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => set (X := EF) in HS
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac sl1_rnth HS i R :=
  first [ pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as R
        | pose proof (st_ok_region_nth _ _ _ i _ HS eq_refl) as R ];
  cbn [ms_mem restrict] in R.
(* A register the run left as it was (atom n of a valuation lo-equal to one whose atoms are the registers, EE). *)
Ltac sl1_kreg HS lo EE r n v H :=
  sl1_reg HS r v H
    ltac:(cbn [sv_denot]; rewrite (lo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac (SlostNtc.v sn_win). *)
Ltac sl1_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
Ltac sl1_wt :=
  first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
        | right; right; right; right; lia].
(* A closed range 0 <= v < 2 ^ k, decided by computation. *)
Ltac sl1_cz := split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity.

(* The write rights of runs 1 and 2 (the seven regions of ss_sl1; U19 / U18: the bases' values; EFr: the frame's
   address frame_addr ly2 ONANN_CID pos = F). *)
Ltac sl1_awr U19 U18 EFr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFr; change (fs_frame_bytes ONANN_CID / 8) with 128; lia |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFr; change (fs_frame_bytes ONANN_CID) with 1024; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; apply sl1_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; apply sl1_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; apply sl1_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

Section sl1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* 3. The notice n2 and its written range                              *)
(* ------------------------------------------------------------------ *)

(* The notice at n2 = F + 144, as notice's statement reads it (check_state_data_cg.v trans_ntc_at): its 72 bytes are
   WalkNotify.v ntc_state_bytes 0 2 3, session_lost_cg.v slost_ntc Bx 3 at a state S_ONLINE. *)
Lemma sl1_ntc_at : forall ly2 S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bx F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  F = frame_addr ly2 ONANN_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  F + 1024 <= spZ regsC - NOTICE_STK ->
  TW.S_state (slost_w1 Bx) = TS0.DIGINET_S_ONLINE ->
  (forall i, 18 <= i < 27 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 144) (map DSpec.bz (WN.ntc_state_bytes 0 2 3)) ->
  trans_ntc_at B ly2 S2 W memN regsC NOTICE_STK (F + 144) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE).
Proof.
intros ly2 S2 W memN mdN regsC Bx F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Hold ZS HNB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_frames _ _ LAWS ly2 S2 W memN mdN ONANN_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
unfold trans_ntc_at.
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split.
{ right. split.
  - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes ONANN_CID) with 1024.
    unfold NTC_SIZE. lia.
  - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    + apply (TransportGNotice.frame_ra_zero _ F (F + 144) 72 18 27); [lia | exact DFm8 | lia | lia | exact ZS].
    + apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 144) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    + apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia. }
split; [left; unfold NTC_SIZE; lia|].
exists (WN.ntc_state_bytes 0 2 3).
split; [exact HNB|].
unfold slost_ntc. rewrite Hold.
cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
  TI.n_body TI.n_ann length].
assert (Z0 : TW.u_at (WN.ntc_state_bytes 0 2 3) 48 8 = 0) by (vm_compute; reflexivity).
rewrite Z0.
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [vm_compute; reflexivity |].
split; [apply garr8_nil |].
split; [exact (trans_src_ok_null B ly2 S2 W memN) |].
split; [left; lia |].
vm_compute; reflexivity.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT) are apart from n2's bytes (a frame is not image), from its empty
   body, and from TF (onann_apart: they are bytes of onann_wr). *)
Lemma sl1_apart : forall ly2 S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw b Bx F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 -> In (ONANN_CID, pos) (frames S2) ->
  F = frame_addr ly2 ONANN_CID pos ->
  onann_apart TF Bw b ->
  (forall a, notice_wr (slost_w2 Bx) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE) a -> onann_wr Bw b a) ->
  notice_apart W memN (F + 144) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE) TF (slost_w2 Bx).
Proof.
intros ly2 S2 W2 mem2 md2 W memN TF Bw b Bx F pos LAWS HAR Hin EF Hap Hwr x Hx.
pose proof (Hwr x Hx) as Hw.
split; [|split].
- intros Hr.
  pose proof (TransportGNotice.notice_wr_G (slost_w2 Bx) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE) x Hx) as Hg.
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos x HAR Hin);
    [rewrite <- EF; change (fs_frame_bytes ONANN_CID) with 1024; unfold NTC_SIZE in Hr; lia|].
  exact (trans_g_img x Hg).
- intros NB _ _. split.
  + unfold slost_ntc. cbn [TI.n_body length Z.of_nat]. lia.
  + intros Hn. exfalso. apply Hn. reflexivity.
- intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The symbolic states at +0x424 and +0x4e0                         *)
(* ------------------------------------------------------------------ *)

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of the world. *)
Definition sl1_vals (Bx : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8)].
Definition sl1_E (regs : bvmap 5 word) (Bx : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (sl1_vals Bx)).

Lemma sl1_entry0 : forall ly S (W : world segs) regs mem md Bx F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  alloc_ceiling <= sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, F + 144 <= a < F + 160 -> apresent (w_H W) mem a) ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some SL1_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some (SL1_SH + 1) ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (ONANN_S + 96) ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (sl1_E regs Bx)
    (mkSS ONANN_SL1 sr_atoms [SL1_R_sh; SL1_R_n2; SL1_R_slot; SL1_R_gs; SL1_R_dcv; SL1_R_inf; SL1_R_shg] None SL1_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL1)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
intros ly S W regs mem md Bx F sp1 HZC HAR Htw R9 R18 R19 HF0 HF64 HFc HFapp HFG Hce Hsp Hsp32 Hpf Hpsh
  S8 S16 S24 S48.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
set (E := sl1_E regs Bx).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, sl1_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (sl1_vals Bx) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, sl1_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth sl1_vals] in E32, E33.
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 96) 8) as R32.
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 104) 8) as R33.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
assert (ZSH : forall j, j = 0 \/ j = 1 \/ j = 2 \/ j = 9 \/ j = 14 ->
  val_mem segs (mrestrict (w_H W) mem) (SL1_SH + j) 1 0).
{ intros j Hj. apply AE2y.val_mem1_of_aview.
  replace (SL1_SH + j) with (FCells.shadow_addr (ONANN_S + 96 + 8 * j)).
  - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
    + unfold ONANN_S, TA_g_s. destruct Hj as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
    + lia.
    + unfold TW.SZ_g_s. destruct Hj as [-> | [-> | [-> | [-> | ->]]]]; unfold ONANN_S, TA_g_s; lia.
  - unfold FCells.shadow_addr, FCells.ASAN_K, SL1_SH, ONANN_S, TA_g_s.
    destruct Hj as [-> | [-> | [-> | [-> | ->]]]]; reflexivity. }
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SL1_R_sh SL1_R_n2 SL1_R_slot SL1_R_gs
      SL1_R_dcv SL1_R_inf SL1_R_shg base_val]; rewrite ?U9, ?U18, ?U19.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    * apply (chunk_ok_val segs E _ sp1 8 8 (SLit SL1_SH) SL1_SH); [reflexivity | sl1_cz | lia |].
      exact (YCbqM.val_mem_of_rdword segs (w_H W) mem _ _ S8).
    * apply (chunk_ok_val segs E _ sp1 16 8 (SLit (SL1_SH + 1)) (SL1_SH + 1)); [reflexivity | sl1_cz | lia |].
      exact (YCbqM.val_mem_of_rdword segs (w_H W) mem _ _ S16).
    * apply (chunk_ok_val segs E _ sp1 24 8 (SLit (ONANN_S + 96)) (ONANN_S + 96));
        [reflexivity | sl1_cz | lia |].
      exact (YCbqM.val_mem_of_rdword segs (w_H W) mem _ _ S24).
    * apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
        [reflexivity | sl1_cz | lia |].
      exact (YCbqM.val_mem_of_rdword segs (w_H W) mem _ _ S48).
  + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in *. lia.
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 96) 8));
           [apply DEN; [exact E32 | exact R32] | exact R32 | lia |].
         replace (0 + (ONANN_S + 96)) with (TA_g_s + 96) by (unfold ONANN_S; lia).
         exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
           ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 33 0) (TW.u_at Bx (TW.OFF_g_s + 104) 8));
           [apply DEN; [exact E33 | exact R33] | exact R33 | lia |].
         replace (0 + (ONANN_S + 104)) with (TA_g_s + 104) by (unfold ONANN_S; lia).
         exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
           ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
    apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in *. lia.
  + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
    apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in *. lia.
  + split; [unfold SL1_SH; lia|]. split; [unfold SL1_SH; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    * apply (chunk_ok_val segs E _ 0 SL1_SH 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
      rewrite Z.add_0_l. pose proof (ZSH 0 ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
    * apply (chunk_ok_val segs E _ 0 (SL1_SH + 1) 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
      rewrite Z.add_0_l. exact (ZSH 1 ltac:(lia)).
    * apply (chunk_ok_val segs E _ 0 (SL1_SH + 2) 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
      rewrite Z.add_0_l. exact (ZSH 2 ltac:(lia)).
    * apply (chunk_ok_val segs E _ 0 (SL1_SH + 9) 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
      rewrite Z.add_0_l. exact (ZSH 9 ltac:(lia)).
    * apply (chunk_ok_val segs E _ 0 (SL1_SH + 14) 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
      rewrite Z.add_0_l. exact (ZSH 14 ltac:(lia)).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, SL1_R_sh, SL1_R_n2, SL1_R_slot, SL1_R_gs, SL1_R_dcv, SL1_R_inf, SL1_R_shg.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SL1_SH, SHADOW_OFF, ONANN_S, TA_g_s, TW.SZ_g_s in *.
  rewrite HF8. repeat split; first [exact I | lia].
- unfold SL1_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U18, U19.
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
  assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
  { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    apply Z.mod_mul. lia. }
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma sl1_entry : forall ly S (W : world segs) regs mem md Bx F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  alloc_ceiling <= sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, F + 144 <= a < F + 160 -> apresent (w_H W) mem a) ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some SL1_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some (SL1_SH + 1) ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (ONANN_S + 96) ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 25 = w64 (ONANN_S + 104) -> YK11.getr regs 26 = w64 (SL1_SH + 2) ->
  st_ok_pi segs VAL (sl1_E regs Bx) ss_sl1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL1)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md Bx F sp1 HZC HAR Htw R9 R18 R19 HF0 HF64 HFc HFapp HFG Hce Hsp Hsp32 Hpf Hpsh
  S8 S16 S24 S48 R20 R24 R25 R26.
rewrite restrict_mkst_fx.
pose proof (sl1_entry0 ly S W regs mem md Bx F sp1 HZC HAR Htw R9 R18 R19 HF0 HF64 HFc HFapp HFG Hce Hsp Hsp32 Hpf Hpsh
  S8 S16 S24 S48) as H0.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (ONANN_S + 104) H2 R25 eq_refl) as H3.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (SL1_SH + 2) H3 R26 eq_refl) as H4.
exact H4.
Qed.

(* The valuation of run 3: the registers after notice returns, then the 4 bytes of g_s.state in B4. *)
Definition sl1_E3 (regs : bvmap 5 word) (B4 : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at B4 (TW.OFF_g_s + 112) 4)]).

Lemma sl1_entry30 : forall ly S (W : world segs) regs mem md B4 F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B4 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (sl1_E3 regs B4)
    (mkSS SL1_C3 sr_atoms [SL1_R3_sh; SL1_R3_slot; SL1_R3_st; SL1_R3_shg] None SL1_FACTS3)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SL1_C3)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
intros ly S W regs mem md B4 F sp1 HZC HAR Htw R9 R19 HF0 HF64 HFc HFG Hsp Hsp32 Hpsh S48.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
set (E := sl1_E3 regs B4).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, sl1_E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at B4 (TW.OFF_g_s + 112) 4))
  by (unfold E, sl1_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (TWL.u_at_range B4 (TW.OFF_g_s + 112) 4) as R32.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
assert (U32 : bv_unsigned (ew E 32) = TW.u_at B4 (TW.OFF_g_s + 112) 4) by (rewrite E32; apply unsigned_lit_small; lia).
assert (ZSH : val_mem segs (mrestrict (w_H W) mem) (SL1_SH + 2) 1 0).
{ apply AE2y.val_mem1_of_aview.
  replace (SL1_SH + 2) with (FCells.shadow_addr (ONANN_S + 112))
    by (unfold FCells.shadow_addr, FCells.ASAN_K, SL1_SH, ONANN_S, TA_g_s; reflexivity).
  apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
  + unfold ONANN_S, TA_g_s. reflexivity.
  + lia.
  + unfold TW.SZ_g_s. lia. }
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SL1_R3_sh SL1_R3_slot SL1_R3_st
      SL1_R3_shg base_val]; rewrite ?U9, ?U19.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
      [reflexivity | sl1_cz | lia |].
    exact (YCbqM.val_mem_of_rdword segs (w_H W) mem _ _ S48).
  + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at B4 (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    replace (0 + (ONANN_S + 112)) with (TA_g_s + 112) by (unfold ONANN_S; lia).
    exact (tw_read_val segs _ TMAP_A B4 TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + split; [unfold SL1_SH; lia|]. split; [unfold SL1_SH; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 (SL1_SH + 2) 1 (SLit 0) 0); [reflexivity | sl1_cz | lia |].
    rewrite Z.add_0_l. exact ZSH.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, SL1_R3_sh, SL1_R3_slot, SL1_R3_st, SL1_R3_shg.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SL1_SH, SHADOW_OFF, ONANN_S, TA_g_s, TW.SZ_g_s in *.
  rewrite HF8. repeat split; first [exact I | lia].
- unfold SL1_FACTS3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U19, U32.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
  { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    apply Z.mod_mul. lia. }
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma sl1_entry3 : forall ly S (W : world segs) regs mem md B4 F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B4 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  YK11.getr regs 26 = w64 (SL1_SH + 2) ->
  st_ok_pi segs VAL (sl1_E3 regs B4) ss_sl13
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SL1_C3)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md B4 F sp1 HZC HAR Htw R9 R19 HF0 HF64 HFc HFG Hsp Hsp32 Hpsh S48 R26.
rewrite restrict_mkst_fx.
pose proof (sl1_entry30 ly S W regs mem md B4 F sp1 HZC HAR Htw R9 R19 HF0 HF64 HFc HFG Hsp Hsp32 Hpsh S48) as H0.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (SL1_SH + 2) H0 R26 eq_refl) as H1.
exact H1.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma onann_sl1_holds : @onann_sl1_stmt fx rc B MT.
Proof.
unfold onann_sl1_stmt. intros WK. unfold onann_sl1_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F B2
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HSMR & HLEAF & HPFN & HBCMP & HMS & HN & HWKC & HMOC & HF5).
pose proof (onann_cur_ar B MT LAWS HFIX (proj1 HCUR)) as (HARc & HAR2 & ESLO2 & ESHI2 & Efa & _ & Hin & EF2r & HFb &
  HFsh & HFnG & _ & _ & _ & _ & Hceil' & Hlo' & Hhi' & H47' & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 & Hm &
  HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw2 & Hb2 & Hon & Hk1 & Hgf2 &
  Hri2 & HSA & S0).
pose proof HSA as (S8 & S16 & S24 & S48).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R24 & R25 & R26) & R23).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ONANN_FBYTES in HFc, HFapp, HFLw.
set (Bx := TW.set_S_foreign B2 0) in *.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & _). rewrite ?Z.add_0_r in Hsp0a.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _).
clear HJi memS.
assert (HOS : ONANN_STK = 8992) by reflexivity.
assert (HNS : NOTICE_STK = 8240) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HEVn : NOTICE_EV = 0) by reflexivity.
assert (HEV0 : 0 <= ONANN_EV) by (apply Z.leb_le; reflexivity).
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (Hsp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. rewrite HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HACE : alloc_ceiling + 8768 <= sp1) by lia.
assert (Hsp46 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (EF2 : F = frame_addr ly2 ONANN_CID pos) by (symmetry; exact EF2r).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
set (FL := flag_addr lyc ONANN_CID pos) in *.
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL HAR2 Hfrs Hbl
  HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ rewrite DF. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HFG : F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 1024) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  destruct (Z_le_gt_dec F ONANN_S) as [h3|h3].
  - apply (HFnG ONANN_S); [unfold TW.SZ_g_s in *; lia|]. apply sl1_inG. unfold TW.SZ_g_s. lia.
  - apply (HFnG F); [lia|]. apply sl1_inG. lia. }
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
(* the model on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
assert (HLX : length Bx = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
destruct (sl1_k_split TF Bx now Bw' Hk1) as (B4 & HM4 & HK4).
assert (HO1 : TW.S_state (slost_w1 Bx) = TS0.DIGINET_S_ONLINE) by (rewrite (onann_sl_state Bx HLX); exact Hon).
assert (Hne : TW.S_state (slost_w1 Bx) <> TS0.DIGINET_S_IDLE) by (rewrite HO1; apply Z.eqb_neq; reflexivity).
destruct (sn_model TF Bx TS0.DIGINET_R_DESK_OFFLINE B4 HM4 Hne) as (HNT & HNM).
destruct Hb2 as (Hcall2 & d & EB2).
destruct (sl1_x_facts Bw b B2 d Bx HLB EB2 eq_refl) as (HGn & HSt).
assert (HWR : forall a, notice_wr (slost_w2 Bx) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE) a -> onann_wr Bw b a).
{ intros a Ha. apply (onann_wr_slost Bw b Bx TS0.DIGINET_R_DESK_OFFLINE a HLX HLB HGn HSt).
  right; right. split; [exact Hne | right; exact Ha]. }
assert (HGF4 : TW.g_fail_next B4 = TW.g_fail_next Bx) by exact (sn_gfn' TF Bx TS0.DIGINET_R_DESK_OFFLINE B4 HLX HNM).
assert (HRI4 : onann_ri B4).
{ exact (proj1 (proj2 (onann_slost_res TF Bx TS0.DIGINET_R_DESK_OFFLINE B4 HM4 HLX)) Hri2). }
(* +0x424 .. +0x488: run 1 *)
pose proof (sl1_entry ly2 S2 W2 regs2 mem2 md2 Bx F sp1 HZC HAR2 Htw2 R9 R18 R19 HF0 HF64 HFc HFapp HFG
  ltac:(lia) Hsp46 (proj2 Hsp1)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  S8 S16 S24 S48 R20 R24 R25 ltac:(rewrite R26; reflexivity)) as HS.
set (E0 := sl1_E regs2 Bx) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sl1_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, sl1_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E0 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs SL1_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ2 SHOK SL1_B0.
{ sl1_awr U19 U18 EF2r. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
sl1_env HS E0a.
assert (E0alo : forall n, (n < 1024)%nat -> ew E0a n = ew E0 n)
  by (intros n Hn; unfold E0a; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HEIa : img_env VAL A_LIM E0a) by (first [exact HEI | assumption]).
assert (U9a : bv_unsigned (ew E0a 9) = sp1) by (rewrite E0alo by lia; exact U9).
assert (U18a : bv_unsigned (ew E0a 18) = F) by (rewrite E0alo by lia; exact U18).
assert (U19a : bv_unsigned (ew E0a 19) = SHADOW_OFF + F / 8) by (rewrite E0alo by lia; exact U19).
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ sl1_W F a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sl1_W F) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  sl1_win Hiw Hx ltac:(rewrite ?U19a, ?U18a, ?U19, ?U18 in Hx; unfold sl1_W, ONANN_S, TA_g_s; sl1_wt). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
sl1_rnth HS 0%nat RG0.
assert (ZS1 : forall i, 18 <= i < 27 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19a.
  assert (Hi' : i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (SN.sn_chunk0 E0a (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONANN_CID pos HAR1 Hin) as (_ & _ & _ & HFsh1).
rewrite <- EF2, ESH in HFsh1. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh1.
pmkst HS.
sl1_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 160)) Q10 ltac:(cbn [sv_denot]; rewrite U18a; reflexivity).
sl1_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
sl1_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
sl1_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (E0alo 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact R2).
sl1_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27804)) Q1 ltac:(apply codeptr_val; exact HEIa).
sl1_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (E0alo 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
sl1_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (E0alo 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x488: __asan_memset (n2 + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 md1
    (k + 0) (F + 160) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 27804)) HGX G_HARNESS_rw HJ2 Q10 Q11 Q12).
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
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF2r. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + lia.
  - apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
  - apply (TransportGNotice.frame_ra_zero _ F (F + 160) 56 20 27); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 160) 56);
      [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regsM & memM & mdM & -> & HJM & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ sl1_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. unfold sl1_Z in Hn.
  assert (Hn1 : ~ sl1_W F a) by tauto. assert (Hn2 : ~ (F + 160 <= a < F + 216)) by tauto.
  assert (Hn3 : ~ (sp1 - ESTACK <= a < sp1)) by tauto.
  rewrite HeffM; [exact (KW1 a Ha Hn1) | exact Ha | lia | lia]. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
assert (ZMM : forall a, F + 160 <= a < F + 216 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 160) + (a - (F + 160))) by lia. rewrite (HsetM (a - (F + 160)) ltac:(lia)).
  reflexivity. }
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM
  [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 19%nat (SHADOW_OFF + F / 8)); [exact U19a | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in Ha, HSHF. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 18%nat F); [exact U18a | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9a | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply SN.sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in Ha, HFG.
    apply HeffM; [lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - apply SN.sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in Ha, HFG.
    apply HeffM; [lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - apply SN.sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in Ha, HFG.
    apply HeffM; [lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - apply SN.sn_rk_none; [| exact HgrM]. intros a Ha. unfold SL1_SH in Ha.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0a 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0a n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U9b : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; exact U9a).
assert (U18b : bv_unsigned (ew E1 18) = F) by (rewrite E1lo by lia; exact U18a).
assert (U19b : bv_unsigned (ew E1 19) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U19a).
assert (SHOK1 : sh_ok segs SL1_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
clear dependent ms.
(* +0x48c .. +0x4dc: run 2, up to `jalr a2` *)
paj_run_tok RUN HS HJM SHOK1 SL1_B0.
{ sl1_awr U19b U18b EF2r. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
sl1_env HS E2.
assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E1 n)
  by (intros n Hn; unfold E2; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HEIc : img_env VAL A_LIM E2) by (first [exact HEI1 | assumption]).
assert (U9c : bv_unsigned (ew E2 9) = sp1) by (rewrite E2lo by lia; exact U9b).
assert (U18c : bv_unsigned (ew E2 18) = F) by (rewrite E2lo by lia; exact U18b).
assert (U19c : bv_unsigned (ew E2 19) = SHADOW_OFF + F / 8) by (rewrite E2lo by lia; exact U19b).
assert (KWN : forall a, 0 <= a < 2 ^ 64 -> ~ sl1_W F a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sl1_W F) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  sl1_win Hiw Hx ltac:(rewrite ?U19c, ?U18c, ?U19b, ?U18b in Hx; unfold sl1_W, ONANN_S, TA_g_s; sl1_wt). }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ sl1_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (KWN a Ha ltac:(intros Hw; apply Hn; left; exact Hw)). exact (KAM a Ha Hn). }
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
assert (ZMN : forall a, F + 160 <= a < F + 216 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite KWN; [exact (ZMM a Ha) | lia |].
  unfold sl1_W. intros [Hx | [Hx | [Hx | [Hx | Hx]]]]; unfold ONANN_S, TA_g_s, SHADOW_OFF in Hx, HSHF, HFG.
  - destruct HSHF as [Hs | Hs]; lia.
  - lia.
  - destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia.
  - destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia.
  - destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia. }
clear HF HFr HG.
sl1_rnth HS 0%nat RS0. sl1_rnth HS 1%nat RS1. sl1_rnth HS 3%nat RS3. sl1_rnth HS 4%nat RS4. sl1_rnth HS 5%nat RS5.
assert (ZSN : forall i, 18 <= i < 27 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19c.
  assert (Hi' : i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (SN.sn_chunk0 E2 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
pose proof (SN.sn_chunk_val E2 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 144 8 (SLit 2) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (SN.sn_chunk_val E2 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 152 8 (SLit 12884901890) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (SN.sn_chunk_val E2 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158896 4 (SLit 0) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
pose proof (SN.sn_chunk_val E2 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158952 4 (SLit 0) RS4
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VD.
pose proof (SN.sn_chunk_val E2 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158996 4 (SLit 0) RS5
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VI.
cbn [base_val] in VP0, VP8, VG, VD, VI. rewrite U18c in VP0, VP8.
change (N.to_nat 8) with 8%nat in VP0, VP8. change (N.to_nat 4) with 4%nat in VG, VD, VI.
change (bv_unsigned (sv_denot E2 (SLit 2)) mod 2 ^ (8 * Z.of_N 8)) with 2 in VP0.
change (bv_unsigned (sv_denot E2 (SLit 12884901890)) mod 2 ^ (8 * Z.of_N 8)) with 12884901890 in VP8.
change (bv_unsigned (sv_denot E2 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG, VD, VI.
clear RS0 RS1 RS3 RS4 RS5.
pose proof (sl1_split8 _ _ VP8) as (V8a & V8b).
assert (HNB : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (F + 144) (map DSpec.bz (WN.ntc_state_bytes 0 2 3))).
{ replace (F + 144) with (F + 112 + 32) by lia.
  apply SN.sn_nb.
  - replace (F + 112 + 32) with (F + 144) by lia. exact VP0.
  - replace (F + 112 + 40) with (F + 152) by lia. exact V8a.
  - replace (F + 112 + 44) with (F + 152 + 4) by lia. exact V8b.
  - intros a Ha. apply ZMN. lia. }
(* what the call kept, from its entry to the call of notice *)
assert (HSZ : forall a, sl1_Z F sp1 a ->
  (spZ regs - ONANN_STK <= a < spZ regs) \/ dkg_nf ONANN_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a HZ. unfold sl1_Z, sl1_W in HZ. destruct HZ as [[HZ | [HZ | [HZ | [HZ | HZ]]]] | [HZ | HZ]].
  - right; left; right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - right; right. apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in HZ |- *. lia.
  - right; right. apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in HZ |- *. lia.
  - right; right. apply sl1_inG. unfold ONANN_S, TA_g_s, TW.SZ_g_s in HZ |- *. lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - left. lia. }
assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem ms) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 (ms_mem ms)
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b) (sl1_Z F sp1) HGX HARc HAR2 Hfrs Hbl HlyF EF
    eq_refl FFL); [lia | lia | exact HSZ | exact HK | exact KAN | exact GAN]. }
(* the world relation at slost_w2 Bx *)
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (slost_w2 Bx)).
{ apply (sl1_tw_w2 (aview segs (w_H W2) mem2) _ Bx Htw2).
  - intros j Hj. replace (TA_g_s + 212 + j) with (0 + 6158996 + j) by (unfold TA_g_s; lia).
    exact (SH.slh_aview_of_val0 _ _ _ 4 VI j ltac:(lia)).
  - intros j Hj. replace (TA_g_s + 168 + j) with (0 + 6158952 + j) by (unfold TA_g_s; lia).
    exact (SH.slh_aview_of_val0 _ _ _ 4 VD j ltac:(lia)).
  - intros j Hj. replace (TA_g_s + 112 + j) with (0 + 6158896 + j) by (unfold TA_g_s; lia).
    exact (SH.slh_aview_of_val0 _ _ _ 4 VG j ltac:(lia)).
  - intros x Hx H1 H2 H3.
    assert (HxG : inG TG.G_HARNESS x).
    { destruct Hx as (o & b0 & n & Hin3 & Hx). unfold inG. apply Exists_exists. exists (b0, n).
      split; [exact (TMAP_A_in_G o b0 n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_G_HARNESS_hull x HxG) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KAN; [lia|]. unfold sl1_Z, sl1_W. intros HZ.
    destruct HZ as [[HZ | [HZ | [HZ | [HZ | HZ]]]] | [HZ | HZ]].
    + unfold SHADOW_OFF in HZ. lia.
    + exact (HFnG x ltac:(lia) HxG).
    + apply H3. unfold ONANN_S in HZ. lia.
    + apply H2. unfold ONANN_S in HZ. lia.
    + apply H1. unfold ONANN_S in HZ. lia.
    + exact (HFnG x ltac:(lia) HxG).
    + lia. }
(* the registers at `jalr a2` *)
assert (E2lo' : forall n, (n < 1024)%nat -> ew E2 n = ew E0 n)
  by (intros n Hn; rewrite (E2lo n Hn), (E1lo n Hn); exact (E0alo n Hn)).
assert (E32c : ew E2 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite (E2lo' 32%nat ltac:(lia)).
  unfold E0, sl1_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (sl1_vals Bx) 0) as X. cbn [Nat.add nth sl1_vals] in X. rewrite X.
  rewrite <- (sl1_notify Bx HLX), HNT. reflexivity. }
sl1_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32c, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sl1_reg HS (Z_to_bv 5 11) (w64 (F + 144)) T11 ltac:(cbn [sv_denot]; rewrite U18c; reflexivity).
sl1_kreg HS E2lo' EE (Z_to_bv 5 2) 2%nat (YK11.getr regs2 (Z_to_bv 5 2)) T2.
sl1_kreg HS E2lo' EE (Z_to_bv 5 3) 3%nat (YK11.getr regs2 (Z_to_bv 5 3)) T3.
sl1_kreg HS E2lo' EE (Z_to_bv 5 4) 4%nat (YK11.getr regs2 (Z_to_bv 5 4)) T4.
sl1_kreg HS E2lo' EE (Z_to_bv 5 8) 8%nat (YK11.getr regs2 (Z_to_bv 5 8)) T8.
sl1_kreg HS E2lo' EE (Z_to_bv 5 9) 9%nat (YK11.getr regs2 (Z_to_bv 5 9)) T9.
sl1_kreg HS E2lo' EE (Z_to_bv 5 18) 18%nat (YK11.getr regs2 (Z_to_bv 5 18)) T18.
sl1_kreg HS E2lo' EE (Z_to_bv 5 19) 19%nat (YK11.getr regs2 (Z_to_bv 5 19)) T19.
sl1_kreg HS E2lo' EE (Z_to_bv 5 23) 23%nat (YK11.getr regs2 (Z_to_bv 5 23)) T23.
sl1_reg HS (Z_to_bv 5 20) (w64 ONANN_S) T20 ltac:(reflexivity).
sl1_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
sl1_reg HS (Z_to_bv 5 26) (w64 (SL1_SH + 2)) T26 ltac:(reflexivity).
(* +0x4dc: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E2 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEIc HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (27884 + 4) = 0x87f54) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (27884 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros E; apply Hr; rewrite E; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T2 R2)).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T3 (eq_trans R3 Hgp))).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans T4 (eq_trans R4 Htp))).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 144)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJM) as HARN.
assert (HTFC : trans_tframe_at B ly2 S2 W2 (ms_mem ms) regsC NOTICE_STK TF).
{ exact (onann_tf_call B LAWS HROU HRNE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) md3 pos regs regsC NOTICE_STK TF Bw b
    HARc HARN Hfrs Hperm Efa ESLO2 ESHI2 KCN Htfg ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF). }
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + 0) regsC
    (F + 144) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE) TF (slost_w2 Bx) B4
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJM)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (sl1_ntc_at ly2 S2 W2 (ms_mem ms) md3 regsC Bx F pos LAWS HARN Hin EF2 HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) HO1 ZSN HNB)
    HTFC
    (onann_rom_call B HROU HRNE lyc Sc W memc W2 (ms_mem ms) _ _ _ Hrom KCN)
    PTW HNM
    (sl1_apart ly2 S2 W2 mem2 md2 W2 (ms_mem ms) TF Bw b Bx F pos LAWS HAR2 Hin EF2 Hap HWR)
    ltac:(intros HD; exfalso; unfold slost_ntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
    ltac:(rewrite HEVn; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (rewrite HEVn in He3; lia). subst e3.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _).
pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hin3 : In (ONANN_CID, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 ONANN_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh3. rewrite ESH in HFsh3.
assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) by exact (Permutation_trans Hperm3 Hperm).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm3c) Hbm)).
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onann_wr Bw b)
    (notice_wr (slost_w2 Bx) (slost_ntc Bx TS0.DIGINET_R_DESK_OFFLINE)) (dkg_nf ONANN_CID F FL)).
  - lia.
  - lia.
  - exact Efa.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (HWR a Ha). }
(* the bytes the rest reads: the machine frame above sp1, the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK3 : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite USPC in K31. rewrite K31 by lia. apply KAN; [lia|].
  unfold sl1_Z, sl1_W, ONANN_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL3 : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) mem3 (F + 1024 - 8 + i) = aview segs (w_H W2) mem2 (F + 1024 - 8 + i)).
{ intros i Hi. rewrite (K34 ONANN_CID pos (F + 1024 - 8 + i) Hin).
  - apply KAN; [lia|]. unfold sl1_Z, sl1_W, ONANN_S, TA_g_s, SHADOW_OFF in HSHF, HFG |- *.
    intros [[Hz | [Hz | [Hz | [Hz | Hz]]]] | [Hz | Hz]];
      [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
      | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
      | lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2r. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - intros Hw. exact (HFnG (F + 1024 - 8 + i) ltac:(lia) (onann_wr_G Bw b _ (HWR _ Hw))). }
assert (S48' : rdword (aview segs (w_H W3) mem3) (sp1 + 48) = Some (ONANN_S + 112)).
{ unfold onann_slot in S48. rewrite <- S48. apply rdword_ext. intros i Hi. apply KSTK3. lia. }
assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
  YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
  by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
assert (R3_9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1)
  by exact (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)).
assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (CH 19 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T19 R19)).
assert (R3_26 : YK11.getr regs3 (Z_to_bv 5 26) = w64 (SL1_SH + 2))
  by exact (eq_trans (CH 26 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T26).
(* +0x4e0 .. +0x514: n2's shadow bytes := 0xf8, the checked load of g_s.state, to the wake cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + (27884 + 4))) with (Z_to_bv 64 (BASE + SL1_C3)).
pose proof (sl1_entry3 ly3 S3 W3 regs3 mem3 md4 B4 F sp1 HZC HAR3 Htw3 R3_9 R3_19 HF0 HF64 HFc HFG Hsp46 (proj2 Hsp1)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia)))) S48' R3_26) as HS3.
set (E3 := sl1_E3 regs3 B4) in HS3.
assert (HEId : img_env VAL A_LIM E3) by (unfold E3, sl1_E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3, sl1_E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E3_32 : ew E3 32 = Z_to_bv 64 (TW.u_at B4 (TW.OFF_g_s + 112) 4))
  by (unfold E3, sl1_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U19e : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs SL1_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SL1_B0 ONANN_WK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19e in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
sl1_env HS3 E4.
assert (E4lo : forall n, (n < 1024)%nat -> ew E4 n = ew E3 n)
  by (intros n Hn; unfold E4; rewrite ?ew_ewset_other by lia; reflexivity).
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 18 <= a < SHADOW_OFF + F / 8 + 27) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. sl1_win Hiw Hx ltac:(rewrite ?U19e in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md4 mem3 (ms_mem ms4)
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b)
    (fun x => SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL);
    [lia | lia | | exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right; left; right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. cbv beta in Ha. lia. }
assert (KSTK4 : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). exact (KSTK3 a Ha). }
assert (KFL4 : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 1024 - 8 + i) = aview segs (w_H W2) mem2 (F + 1024 - 8 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in HSHF |- *; destruct HSHF; lia). exact (KFL3 i Hi). }
pmkst HS3.
(* the registers at the wake cut *)
sl1_reg HS3 (Z_to_bv 5 10) (Z_to_bv 64 (TW.S_state B4)) Y10
  ltac:(apply sl1_sext; rewrite E4lo by lia; exact E3_32).
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 2) 2%nat (YK11.getr regs3 (Z_to_bv 5 2)) Y2.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 3) 3%nat (YK11.getr regs3 (Z_to_bv 5 3)) Y3.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 4) 4%nat (YK11.getr regs3 (Z_to_bv 5 4)) Y4.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 8) 8%nat (YK11.getr regs3 (Z_to_bv 5 8)) Y8.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 9) 9%nat (YK11.getr regs3 (Z_to_bv 5 9)) Y9.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 18) 18%nat (YK11.getr regs3 (Z_to_bv 5 18)) Y18.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 19) 19%nat (YK11.getr regs3 (Z_to_bv 5 19)) Y19.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 20) 20%nat (YK11.getr regs3 (Z_to_bv 5 20)) Y20.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 23) 23%nat (YK11.getr regs3 (Z_to_bv 5 23)) Y23.
sl1_kreg HS3 E4lo EE3 (Z_to_bv 5 24) 24%nat (YK11.getr regs3 (Z_to_bv 5 24)) Y24.
assert (Z2 : YK11.getr (ms_regs ms4) (Z_to_bv 5 2) = w64 sp1)
  by exact (eq_trans Y2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T2 R2))).
assert (Z3 : YK11.getr (ms_regs ms4) (Z_to_bv 5 3) = YK11.getr regs 3)
  by exact (eq_trans Y3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 R3))).
assert (Z4 : YK11.getr (ms_regs ms4) (Z_to_bv 5 4) = YK11.getr regs 4)
  by exact (eq_trans Y4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 R4))).
assert (Z8 : YK11.getr (ms_regs ms4) (Z_to_bv 5 8) = w64 (spZ regs))
  by exact (eq_trans Y8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8))).
assert (Z9 : YK11.getr (ms_regs ms4) (Z_to_bv 5 9) = w64 sp1)
  by exact (eq_trans Y9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9))).
assert (Z18 : YK11.getr (ms_regs ms4) (Z_to_bv 5 18) = w64 F)
  by exact (eq_trans Y18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T18 R18))).
assert (Z19 : YK11.getr (ms_regs ms4) (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans Y19 (eq_trans (CH 19 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T19 R19))).
assert (Z20 : YK11.getr (ms_regs ms4) (Z_to_bv 5 20) = w64 ONANN_S)
  by exact (eq_trans Y20 (eq_trans (CH 20 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T20)).
assert (Z23 : YK11.getr (ms_regs ms4) (Z_to_bv 5 23) = w64 F)
  by exact (eq_trans Y23 (eq_trans (CH 23 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T23 R23))).
assert (Z24 : YK11.getr (ms_regs ms4) (Z_to_bv 5 24) = w64 SHADOW_OFF)
  by exact (eq_trans Y24 (eq_trans (CH 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T24)).
assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_WK)) mm rom) mdx) Q) end.
apply (WK LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B4 ly3 S3 W3 (ms_mem ms4) md5 (ms_regs ms4) HFIX).
- unfold onann_wk_cur.
  refine (conj _ (conj _ (conj HK4 (conj _ (conj HRI4 _))))).
  + unfold onann_cur.
    refine (conj _ (conj _ (conj Hfrs3 (conj Hperm3c (conj ELF3c (conj _ (conj KC4 (conj _ _)))))))).
    * replace (k + 0) with (k + 0 + 0) by lia. exact HJ3.
    * lia.
    * exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. pose proof (HSo o Ho) as Hob.
      rewrite <- (Hsaved o Ho). apply rdword_ext. intros i Hi. apply KSTK4. lia.
    * unfold ONANN_FBYTES. try change (flag_addr lyc ONANN_CID pos) with FL.
      rewrite <- HFLw. apply rdword_ext. intros i Hi. exact (KFL4 i Hi).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite HGF4. exact Hgf2.
  + unfold onann_slot in S0 |- *. rewrite <- S0. apply rdword_ext. intros i Hi. apply KSTK4. lia.
- unfold onann_regs_wk, onann_regs_rel, onann_regs_base.
  refine (conj (conj (conj Z2 (conj Z3 (conj Z4 (conj Z8 (conj Z9 (conj Z18 Z19)))))) Z23) (conj Y10 (conj Z20 Z24))).
Qed.
End sl1.

(* The sl1 piece of the walk of on_announce (OnannCut.v onann_sl1_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_sl1 : forall fx rc B MT, @onann_sl1_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onann_sl1_holds fx rc B MT). Qed.

Print Assumptions onann_piece_sl1.
