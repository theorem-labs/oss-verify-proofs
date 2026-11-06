(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 580 of its 687 lines of code are new or changed and 1103 lines of the source are left out. *)
(* on_announce_seg_fnb: the facts the foreign-notice piece of on_announce's image-B walk (on_announce_seg_fn.v, which
   proves onann_fn_stmt of lib/B/Prog/OnannCutB.v) uses, at code +0x4e4 .. +0x5b0 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x881ac .. 0x88278). Nothing here runs an instruction.
   - The symbolic states: ss_ofn at the foreign cut (+0x4e4; a0 = s + 136, a1 = its shadow byte, s10 = s + 96 and
     s11 = s + 104 pinned as literals; regions: fn's shadow bytes 28 .. 36 at s2, fn's first 32 bytes at s3, g_s's
     bytes s + 96 .. s + 140 with the code pointer of notice, the context and the state, the spill slots sp1 + 0 ..
     sp1 + 48 at s1, the shadow bytes of s + 96 .. s + 136; the alias fact s2 = (s3 >> 3) + s8, so the check of the
     store at fn + 24 (+0x548 .. +0x554) reads fn's shadow byte 31, which the run itself zeroes) and ss_ofn3 after
     notice's return (+0x594: the two spill slots sp1 + 32 / sp1 + 40, the shadow byte of s + 112, the state);
     ofn_entry / ofn_entry3 / ofn_entry0: they hold of the machine states there.
   - ofn_ntc_at: the 72 bytes at fn = F + 224 (the stores of 6, the state, 8 zero bytes, fp and a; the memset's 40
     zeros) as notice's trans_ntc_at of onann_fntc (the announce at a = F + 32 as diginet_announce_parse left it,
     placed by the frame clause with a's zero shadow bytes 4 .. 8); ofn_apart: notice_cg.v notice_apart for it
     (notice's store GOT.foreign is a byte of G, so not a byte of the frame; the TF part from onann_apart).
   - ofn_cur_step: the cut's facts (OnannCutB.v onann_cur) at a later memory of the same state, when the bytes that
     changed are in the call's stack window below sp1, in the own frame or in G, and miss the frame's last word.
   - The model and the branch: ofn_model (the foreign notice's call_notify, its test and notice_m), ofn_a0 (a0 after
     `lw` / `addiw a0, a0, -1`), ofn_bltu (`bltu a1, a0` with a1 = 1: taken exactly when the state is neither
     S_WAKING nor S_ONLINE). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of s + 96 (s + 104, s + 112, ..., s + 136 have the next five). *)
Definition OFN_SH96 : Z := 2148220628.
Lemma ofn_sh_eq : OFN_SH96 = SHADOW_OFF + (ONANN_S + 96) / 8 /\ OFN_SH96 + 1 = SHADOW_OFF + (ONANN_S + 104) / 8 /\
  OFN_SH96 + 2 = SHADOW_OFF + (ONANN_S + 112) / 8 /\ OFN_SH96 + 5 = SHADOW_OFF + (ONANN_S + 136) / 8.
Proof. repeat split; reflexivity. Qed.

(* notice's return address (+0x594) and the `bltu` (+0x5b0). *)
Definition ONFN_AFT : Z := AF_on_announce + 0x594.
Definition ONFN_BR : Z := AF_on_announce + 0x5b0.

(* At the foreign cut: fn's shadow bytes 28 .. 36 (s2, atom 18, written); fn's bytes F + 224 .. F + 256 (s3, atom
   19, written; the memset writes the 40 after them); g_s's bytes s + 96 .. s + 140 (notify: notice's code pointer;
   ctx: atom 34; state: atom 32; foreign written); the spill slots sp1 + 0 .. sp1 + 48 (s1, atom 9: the shadow
   bytes' addresses of s + 104, s + 96, s + 112, a = F + 32, s + 112); the six shadow bytes of s + 96 .. s + 136. *)
Definition ofn_R_sh : YP09.region := YP09.mkRegion (Some 18%nat) 28 37 28 37 [].
Definition ofn_R_fn : YP09.region := YP09.mkRegion (Some 19%nat) 224 256 224 256 [].
Definition ofn_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 140) (ONANN_S + 136) (ONANN_S + 140)
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff A_TEXT AF_notice));
     YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 34 0));
     YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition ofn_R_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 48 0 0
    [YP09.mkChunk 0 (YP09.CVal 8 (SLit (OFN_SH96 + 1))); YP09.mkChunk 8 (YP09.CVal 8 (SLit OFN_SH96));
     YP09.mkChunk 16 (YP09.CVal 8 (SOff 19 32)); YP09.mkChunk 32 (YP09.CVal 8 (SLit (OFN_SH96 + 2)));
     YP09.mkChunk 40 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition ofn_R_shg : YP09.region :=
  YP09.mkRegion None OFN_SH96 (OFN_SH96 + 6) 0 0
    [YP09.mkChunk OFN_SH96 (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OFN_SH96 + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (OFN_SH96 + 2) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OFN_SH96 + 3) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (OFN_SH96 + 4) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OFN_SH96 + 5) (YP09.CVal 1 (SLit 0))].
Definition ofn_regions : smem := [ofn_R_sh; ofn_R_fn; ofn_R_gs; ofn_R_sl; ofn_R_shg].
Definition ofn_facts : facts :=
  mkFacts [(18%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (19%nat, mkAF 4096 (2 ^ 47) 6);
           (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [shadow_decl 19 24 18].
Definition ofn_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit (ONANN_S + 136))) (Z_to_bv 5 11) (SLit (OFN_SH96 + 5)))
    (Z_to_bv 5 26) (SLit (ONANN_S + 96))) (Z_to_bv 5 27) (SLit (ONANN_S + 104)).
Definition ss_ofn : sstate := mkSS ONANN_FN ofn_regs ofn_regions None ofn_facts.
Definition OFN_Bx : sv := SLit 0.
Definition OFN_B0 : Z * Z := (0, 0).

(* After notice: the spill slots sp1 + 32 / sp1 + 40 (atom 9), the shadow byte of s + 112, the state (atom 32). *)
Definition ofn3_R_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 48 0 0
    [YP09.mkChunk 32 (YP09.CVal 8 (SLit (OFN_SH96 + 2))); YP09.mkChunk 40 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition ofn3_R_shs : YP09.region :=
  YP09.mkRegion None (OFN_SH96 + 2) (OFN_SH96 + 3) 0 0 [YP09.mkChunk (OFN_SH96 + 2) (YP09.CVal 1 (SLit 0))].
Definition ofn3_R_st : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition ofn3_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_ofn3 : sstate := mkSS ONFN_AFT sr_atoms [ofn3_R_sl; ofn3_R_shs; ofn3_R_st] None ofn3_facts.

(* ------------------------------------------------------------------ *)
(* 2. Bytes, the notice's bytes, the model                             *)
(* ------------------------------------------------------------------ *)

Lemma ofn_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma ofn_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
  (forall a, lo <= a < hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion None lo hi wlo whi cs).
Proof.
  intros E H m m2 lo hi wlo whi cs Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - apply (mbyte_of_aview tfibsegs). apply Hav. lia.
  - apply writable_kept. apply Hp.
Qed.

Lemma ofn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). rewrite Z.add_0_r in Hb2. cbn [YP09.c_off] in Hb2.
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1. injection Hb1 as <-.
  unfold aview. rewrite Hb2. reflexivity.
Qed.

Lemma ofn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma ofn_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma ofn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) ->
  val_mem tfibsegs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* The 72 bytes of the foreign notice at fn: the stores of 6 (N_FOREIGN), the state, 8 zero bytes (old_state,
   reason), fp and the announce pointer ap; the memset's 40 zeros (personality, mac_offset, padding, body, body_len,
   counter, retry, padding). *)
Definition ofn_nb_bytes (st fpz ap : Z) : list byte :=
  TW.put 4 6 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpz ++ TW.put 8 ap ++ repeat (DSpec.b8 0) 40.

Lemma ofn_nb_len : forall st fpz ap, length (ofn_nb_bytes st fpz ap) = 72%nat.
Proof. intros st fpz ap. unfold ofn_nb_bytes. rewrite ?length_app, ?TWL.length_put, ?repeat_length. reflexivity. Qed.
Lemma ofn_nb_24 : forall st fpz ap, 0 <= ap < 2 ^ 64 -> TW.u_at (ofn_nb_bytes st fpz ap) 24 8 = ap.
Proof.
  intros st fpz ap Hap. unfold ofn_nb_bytes. WN.ntc_field.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Z.mod_small. exact Hap.
Qed.
Lemma ofn_nb_48 : forall st fpz ap, TW.u_at (ofn_nb_bytes st fpz ap) 48 8 = 0.
Proof. intros st fpz ap. unfold ofn_nb_bytes. WN.ntc_field. Qed.

Lemma ofn_nb : forall (H : word -> bool) (m : word -> option byte) F st fpz ap,
  val_mem tfibsegs (mrestrict H m) (F + 224) 4 6 ->
  val_mem tfibsegs (mrestrict H m) (F + 228) 4 st ->
  val_mem tfibsegs (mrestrict H m) (F + 232) 8 0 ->
  val_mem tfibsegs (mrestrict H m) (F + 240) 8 fpz ->
  val_mem tfibsegs (mrestrict H m) (F + 248) 8 ap ->
  (forall a, F + 256 <= a < F + 296 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) (F + 224) (map DSpec.bz (ofn_nb_bytes st fpz ap)).
Proof.
  intros H m F st fpz ap V0 V4 V8 V16 V24 Z0.
  unfold ofn_nb_bytes. rewrite !map_app.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 4 6 V0)|].
  rewrite length_map, TWL.length_put. replace (F + 224 + Z.of_nat 4) with (F + 228) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 4 st V4)|].
  rewrite length_map, TWL.length_put. replace (F + 228 + Z.of_nat 4) with (F + 232) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 0 V8)|].
  rewrite length_map, TWL.length_put. replace (F + 232 + Z.of_nat 8) with (F + 240) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 fpz V16)|].
  rewrite length_map, TWL.length_put. replace (F + 240 + Z.of_nat 8) with (F + 248) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 ap V24)|].
  rewrite length_map, TWL.length_put. replace (F + 248 + Z.of_nat 8) with (F + 256) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* Two lists of bytes at the same address of one memory are the same list. *)
Lemma ofn_garr8_det : forall (H : word -> bool) (m : word -> option byte) a (l1 l2 : list Z),
  garr8 tfibsegs (mrestrict H m) a l1 -> garr8 tfibsegs (mrestrict H m) a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros H m a l1 l2 H1 H2 HL. apply (nth_ext l1 l2 0 0 HL). intros j Hj.
  destruct (H1 j Hj) as (V1 & R1). destruct (H2 j ltac:(lia)) as (V2 & R2).
  pose proof (aview_of_val_mem1 H m _ _ V1 R1) as A1. pose proof (aview_of_val_mem1 H m _ _ V2 R2) as A2.
  rewrite A1 in A2. injection A2 as A2. exact A2.
Qed.

Lemma ofn_map_bz_inj : forall l1 l2 : list byte, map DSpec.bz l1 = map DSpec.bz l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hl].
Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state; a0 after `addiw a0, a0, -1`. *)
Lemma ofn_sext32 : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state X).
Proof.
  intros E X H. pose proof (TWL.u_at_range X (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ofn_a0 : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit (-1))) =
  Z_to_bv 64 (zalu32 ALU_ADD (TW.S_state X) (-1)).
Proof.
  intros E X H.
  change (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit (-1)))) with
    (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SExt true 32 (SOff 32 0)))) (low32 (Z_to_bv 64 (-1))))).
  rewrite (ofn_sext32 E X H). apply zalu32_sound.
Qed.

(* `bltu a1, a0` with a1 = 1 and a0 = the state - 1 (32-bit): taken exactly when the state is neither 1 (S_WAKING)
   nor 2 (S_ONLINE). *)
Lemma ofn_bltu : forall st, - 2 ^ 31 <= st < 2 ^ 31 ->
  branch_taken BC_LTU (Z_to_bv 64 1) (Z_to_bv 64 (zalu32 ALU_ADD st (-1))) = negb ((st =? 1) || (st =? 2)).
Proof.
  intros st Hst. cbn [branch_taken]. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small 1) by lia.
  unfold zalu32, zalu_raw, zcanon, zu32, M64, M32, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change ((-1) mod 2 ^ 32) with 4294967295.
  destruct (Z.eqb_spec st 1) as [E1|E1]; destruct (Z.eqb_spec st 2) as [E2|E2]; cbn [orb negb];
    first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* A byte of a row of G is a byte of G; g_s's payload bytes are bytes of G. *)
Lemma ofn_inG : forall b0 n0 a, In (b0, n0) TG.G_HARNESS_B -> b0 <= a < b0 + n0 -> inG TG.G_HARNESS_B a.
Proof.
  intros b0 n0 a Hin Ha. unfold inG. apply Exists_exists. exists (b0, n0).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma ofn_inG_gs : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (ofn_inG _ _ a (TMAP_B_in_G _ _ _ TMAP_B_g_s)). unfold ONANN_S in Ha. lia. Qed.

(* The foreign notice's model step: call_notify's test, notice_m's answer, then the rest of :219-220. *)
Lemma ofn_model : forall (TF : option TI.tframe) Bf b Bw',
  onann_k_fn timg_B TF Bf b = Some (Bw', tt) ->
  exists B3, TSS.call_notify timg_B TF Bf (onann_fntc Bf b) = Some (B3, tt) /\
    TW.S_notify Bf = TI.ti_notice timg_B /\
    TC.notice_m timg_B TF Bf (onann_fntc Bf b) = Some (B3, tt) /\
    onann_k_fs timg_B TF B3 = Some (Bw', tt).
Proof.
  intros TF Bf b Bw' H. unfold onann_k_fn in H.
  destruct (TSS.call_notify timg_B TF Bf (onann_fntc Bf b)) as [[B3 []]|] eqn:HC; cbv beta iota in H;
    [|discriminate H].
  exists B3. pose proof HC as HC'. unfold TSS.call_notify in HC'.
  destruct (Z.eqb_spec (TW.S_notify Bf) (TI.ti_notice timg_B)) as [E|E]; [|discriminate HC'].
  exact (conj eq_refl (conj E (conj HC' H))).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The entry states                                                 *)
(* ------------------------------------------------------------------ *)

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuations: the 32 registers, then the state (atom 32) and the notify context (atom 34) of a world. *)
Definition ofn_vals (Bx : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4); Z_to_bv 64 0; Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8)].
Definition ofn_E (regs : bvmap 5 word) (Bx : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (ofn_vals Bx)).
Definition ofn_E3 (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4)]).
Definition ofn_Eb (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma ofn_ew : forall regs Bx n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ofn_E regs Bx) n = YK11.getr regs r.
Proof. intros regs Bx n r Hn. unfold ofn_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ofn_ew32 : forall regs Bx, ew (ofn_E regs Bx) 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4).
Proof. intros regs Bx. unfold ofn_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma ofn_ew34 : forall regs Bx, ew (ofn_E regs Bx) 34 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8).
Proof. intros regs Bx. unfold ofn_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). Qed.
Lemma ofn_ew3 : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ofn_E3 regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold ofn_E3. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ofn_ew3_32 : forall regs X, ew (ofn_E3 regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros regs X. unfold ofn_E3. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma ofn_ewb : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ofn_Eb regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold ofn_Eb. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

(* The symbolic state at the foreign cut holds of the machine state there, before the four registers are pinned. *)
Lemma ofn_entry0 : forall ly S (W : world segs) regs mem md Bx F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx -> TW.S_notify Bx = TI.ti_notice timg_B ->
  YK11.getr regs 18 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 19 = w64 F ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 -> in_app F 512 ->
  (F + 512 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 48 <= 2 ^ 47 -> sp1 mod 32 = 0 -> F + 512 <= sp1 ->
  (forall a, F + 224 <= a < F + 256 -> apresent (w_H W) mem a) ->
  (forall i, 28 <= i < 37 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  onann_slots_ntf W mem sp1 -> onann_slots_arm W mem sp1 -> onann_slot W mem sp1 16 (F + ONANN_A) ->
  st_ok_pi segs VAL (ofn_E regs Bx) (mkSS ONANN_FN sr_atoms ofn_regions None ofn_facts)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_FN)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bx F sp1 HSC HAR Htw HNT R18 R19 R9 R24 HF0 HF64 HFc HFapp HFG Hs46 Hs47 Hs32 HFsp Hpf Hpsh
    (Hsl8 & Hsl0) (Hsl32 & Hsl40) Hsl16.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  set (E := ofn_E regs Bx).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, ofn_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; exact (ofn_ew regs Bx n r Hn)).
  assert (W18 : ew E 18 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity).
  assert (W19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl), R19; reflexivity).
  assert (W24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 24%nat 24%bv eq_refl), R24; reflexivity).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + F / 8)
    by (rewrite W18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite W19; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)) by exact (ofn_ew32 regs Bx).
  assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8)) by exact (ofn_ew34 regs Bx).
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R32.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 104) 8) as R34.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> ONANN_S <= T -> T + 8 <= ONANN_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T HT Hlo Hhi. apply ofn_vm0.
    exact (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) T HAR HT Hlo Hhi HSC). }
  assert (EUN : TW.u_at Bx (TW.OFF_g_s + 96) 8 = BASE + AF_notice).
  { change (TW.S_notify Bx = BASE + AF_notice). rewrite HNT. reflexivity. }
  assert (EBN : BASE + AF_notice = 0x8341c) by reflexivity.
  assert (CS : ONANN_S = 6157888) by reflexivity.
  assert (SL : forall o v, onann_slot W mem sp1 o v -> val_mem segs (mrestrict (w_H W) mem) (sp1 + o) 8 v)
    by (intros o v Hv; exact (val_mem_of_rdword segs (w_H W) mem (sp1 + o) v Hv)).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ofn_regions.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ofn_R_sh ofn_R_fn ofn_R_gs
        ofn_R_sl ofn_R_shg base_val]; rewrite ?U18, ?U19, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
        apply ofn_inG_gs. unfold TW.SZ_g_s. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff A_TEXT AF_notice) (BASE + AF_notice));
             [apply codeptr_val; exact HEI | rewrite EBN; lia | lia |].
           replace (0 + (ONANN_S + 96)) with (TB_g_s + 96) by (unfold ONANN_S; lia).
           rewrite <- EUN.
           exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 96 8 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 34 0) (TW.u_at Bx (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
           replace (0 + (ONANN_S + 104)) with (TB_g_s + 104) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 104 8 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
             [apply DEN; [exact E32 | lia] | exact R32 | lia |].
           replace (0 + (ONANN_S + 112)) with (TB_g_s + 112) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
        [|apply Forall_nil]]]]].
      * apply (chunk_ok_val segs E _ sp1 0 8 (SLit (OFN_SH96 + 1)) (OFN_SH96 + 1));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFN_SH96; lia | lia |].
        apply SL. rewrite (proj1 (proj2 ofn_sh_eq)). exact Hsl0.
      * apply (chunk_ok_val segs E _ sp1 8 8 (SLit OFN_SH96) OFN_SH96);
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFN_SH96; lia | lia |].
        apply SL. rewrite (proj1 ofn_sh_eq). exact Hsl8.
      * apply (chunk_ok_val segs E _ sp1 16 8 (SOff 19 32) (F + 32));
          [cbn [sv_denot]; rewrite U19; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (SL _ _ Hsl16).
      * apply (chunk_ok_val segs E _ sp1 32 8 (SLit (OFN_SH96 + 2)) (OFN_SH96 + 2));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFN_SH96; lia | lia |].
        apply SL. rewrite (proj1 (proj2 (proj2 ofn_sh_eq))). exact Hsl32.
      * apply (chunk_ok_val segs E _ sp1 40 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite CS; lia | lia | exact (SL _ _ Hsl40)].
    + split; [unfold OFN_SH96; lia|]. split; [unfold OFN_SH96; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 OFN_SH96 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace OFN_SH96 with (FCells.shadow_addr (ONANN_S + 96)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (OFN_SH96 + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (OFN_SH96 + 1) with (FCells.shadow_addr (ONANN_S + 104)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (OFN_SH96 + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (OFN_SH96 + 2) with (FCells.shadow_addr (ONANN_S + 112)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (OFN_SH96 + 3) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (OFN_SH96 + 3) with (FCells.shadow_addr (ONANN_S + 120)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (OFN_SH96 + 4) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (OFN_SH96 + 4) with (FCells.shadow_addr (ONANN_S + 128)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (OFN_SH96 + 5) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (OFN_SH96 + 5) with (FCells.shadow_addr (ONANN_S + 136)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
  - apply pairwise_disjoint_of_extents.
    unfold ofn_regions, extent_of_region, ofn_R_sh, ofn_R_fn, ofn_R_gs, ofn_R_sl, ofn_R_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, OFN_SH96, SHADOW_OFF, ONANN_S, TB_g_s, TW.SZ_g_s in *.
    rewrite HF8. destruct HFapp as (HA0 & [HAL | (HAH1 & HAH2)]); destruct HFG as [HG1 | HG1];
      repeat split; first [exact I | lia].
  - unfold ofn_facts, facts_ok, shadow_decl. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U19, U9.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64. change (2 ^ 5) with 32.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    split; [|split; [exact I | split; [|exact I]]].
    + unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + exact (shadow_decl_ok E 19 24 18 F SHADOW_OFF W19 ltac:(lia) W24 W18).
Qed.

Lemma ofn_entry : forall ly S (W : world segs) regs mem md Bx F sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx -> TW.S_notify Bx = TI.ti_notice timg_B ->
  YK11.getr regs 18 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 19 = w64 F ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 10 = w64 (ONANN_S + 136) -> YK11.getr regs 11 = w64 (SHADOW_OFF + (ONANN_S + 136) / 8) ->
  YK11.getr regs 26 = w64 (ONANN_S + 96) -> YK11.getr regs 27 = w64 (ONANN_S + 104) ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 -> in_app F 512 ->
  (F + 512 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 48 <= 2 ^ 47 -> sp1 mod 32 = 0 -> F + 512 <= sp1 ->
  (forall a, F + 224 <= a < F + 256 -> apresent (w_H W) mem a) ->
  (forall i, 28 <= i < 37 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  onann_slots_ntf W mem sp1 -> onann_slots_arm W mem sp1 -> onann_slot W mem sp1 16 (F + ONANN_A) ->
  st_ok_pi segs VAL (ofn_E regs Bx) ss_ofn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_FN)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bx F sp1 HSC HAR Htw HNT R18 R19 R9 R24 R10 R11 R26 R27 HF0 HF64 HFc HFapp HFG Hs46 Hs47
    Hs32 HFsp Hpf Hpsh Hntf Harm Hsl16.
  rewrite restrict_mkst_fx.
  pose proof (ofn_entry0 ly S W regs mem md Bx F sp1 HSC HAR Htw HNT R18 R19 R9 R24 HF0 HF64 HFc HFapp HFG Hs46
    Hs47 Hs32 HFsp Hpf Hpsh Hntf Harm Hsl16) as H0.
  assert (R10' : YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 (ONANN_S + 136)) by exact R10.
  assert (R11' : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 (OFN_SH96 + 5)) by (rewrite (proj2 (proj2 (proj2 ofn_sh_eq))); exact R11).
  assert (R26' : YK11.getr regs (Z_to_bv 5 26) = Z_to_bv 64 (ONANN_S + 96)) by exact R26.
  assert (R27' : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 (ONANN_S + 104)) by exact R27.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) (ONANN_S + 136) H0 R10' eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 11) (OFN_SH96 + 5) H1 R11' eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (ONANN_S + 96) H2 R26' eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) (ONANN_S + 104) H3 R27' eq_refl) as H4.
  exact H4.
Qed.

(* The symbolic state at notice's return (+0x594) holds of the machine state there. *)
Lemma ofn_entry3 : forall ly S (W : world segs) regs mem md X sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 48 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  onann_slots_arm W mem sp1 ->
  st_ok_pi segs VAL (ofn_E3 regs X) ss_ofn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONFN_AFT)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md X sp1 HSC HAR Htw R9 Hs46 Hs47 Hs32 (Hsl32 & Hsl40).
  assert (CS : ONANN_S = 6157888) by reflexivity.
  assert (U9 : bv_unsigned (ew (ofn_E3 regs X) 9) = sp1)
    by (rewrite (ofn_ew3 regs X 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (R32 : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
  assert (U32 : bv_unsigned (ew (ofn_E3 regs X) 32) = TW.u_at X (TW.OFF_g_s + 112) 4)
    by (rewrite ofn_ew3_32; apply unsigned_lit_small; lia).
  assert (Hs : aview segs (w_H W) mem (OFN_SH96 + 2) = Some 0).
  { pose proof (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (ONANN_S + 112) HAR
      ltac:(rewrite CS; reflexivity) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HSC) as H.
    replace (OFN_SH96 + 2) with (FCells.shadow_addr (ONANN_S + 112)) by reflexivity. exact H. }
  assert (SL : forall o v, onann_slot W mem sp1 o v -> val_mem segs (mrestrict (w_H W) mem) (sp1 + o) 8 v)
    by (intros o v Hv; exact (val_mem_of_rdword segs (w_H W) mem (sp1 + o) v Hv)).
  rewrite restrict_mkst_fx. unfold ss_ofn3.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ofn3_R_sl ofn3_R_shs ofn3_R_st
        base_val]; rewrite ?U9.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs _ _ sp1 32 8 (SLit (OFN_SH96 + 2)) (OFN_SH96 + 2));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFN_SH96; lia | lia |].
        apply SL. rewrite (proj1 (proj2 (proj2 ofn_sh_eq))). exact Hsl32.
      * apply (chunk_ok_val segs _ _ sp1 40 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
          [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite CS; lia | lia | exact (SL _ _ Hsl40)].
    + split; [unfold OFN_SH96; lia|]. split; [unfold OFN_SH96; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ 0 (OFN_SH96 + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (ofn_vm0 _ _ _ Hs).
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
      replace (0 + (ONANN_S + 112)) with (TB_g_s + 112) by reflexivity.
      exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, ofn3_R_sl, ofn3_R_shs, ofn3_R_st. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold OFN_SH96. rewrite CS. repeat split; first [exact I | lia].
  - unfold ofn3_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U32. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* A state with no region at any pc of the listing (the `bltu` at +0x5b0 is split from it). *)
Lemma ofn_entry0b : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (ofn_Eb regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The notice, its apart clause                                     *)
(* ------------------------------------------------------------------ *)

(* The foreign notice at fn = F + 224, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma ofn_ntc_at : forall ly2 S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bf b st fpz F pos,
  AR_laws segs B -> @AR rc segs B ly2 S2 W memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  frame_addr ly2 ONANN_CID pos = F -> 4096 <= F -> F mod 64 = 0 -> F + 512 <= alloc_ceiling -> in_app F 512 ->
  F + 512 <= spZ regsC - NOTICE_STK ->
  (forall i, 28 <= i < 37 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  (forall i, 4 <= i < 9 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  st = TW.S_state Bf ->
  garr8 segs (mrestrict (w_H W) memN) (F + 224) (map DSpec.bz (ofn_nb_bytes st fpz (F + 32))) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A) (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b)))) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A + 10)
    (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b)))) ->
  trans_ntc_at B ly2 S2 W memN regsC NOTICE_STK (F + 224) (onann_fntc Bf b).
Proof.
  intros ly2 S2 W memN mdN regsC Bf b st fpz F pos LAWS HAR Hin EFA HF0 HF64 HFc HFapp Hwin ZS ZA Est HNB HV HN.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS ly2 S2 W memN mdN ONANN_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite EFA in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 512 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 64 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Hst : - 2 ^ 31 <= st < 2 ^ 31) by (rewrite Est, onann_rd_state; apply TWL.s32_range).
  assert (HF47 : F + 512 <= 2 ^ 47) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 512.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (TGNA.frame_ra_zero _ F (F + 224) 72 28 37); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (TGNA.frame_hull_vis _ F 512 (F + 224) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (ofn_nb_bytes st fpz (F + 32)).
  split; [exact HNB|].
  rewrite (ofn_nb_48 st fpz (F + 32)), (ofn_nb_24 st fpz (F + 32)) by lia.
  unfold onann_fntc.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann TI.ta_version TI.ta_name onann_ann length].
  rewrite <- Est.
  split; [exact (ofn_nb_len st fpz (F + 32))|].
  unfold ofn_nb_bytes, TW.s32_at.
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hst |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B ly2 S2 W memN) |].
  split; [left; lia |].
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split; [exact HV|]. split; [exact HN|].
  split.
  - right. split.
    + left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 512.
      unfold ANN_SIZE. lia.
    + unfold decode_rd_ok, ANN_SIZE. split; [|split; [|split; [|split; [|split]]]].
      * intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      * apply (TGNA.frame_ra_zero _ F (F + 32) 20 4 9); [lia | exact DFm8 | lia | lia | exact ZA].
      * apply (TGNA.frame_hull_vis _ F 512 (F + 32) 20); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      * apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
      * lia.
      * lia.
  - left. unfold ANN_SIZE. lia.
Qed.

(* notice's store (an N_FOREIGN notice: GOT.foreign, a byte of G) is apart from the notice's bytes and from the
   announce's 20 bytes (frame bytes, not image), from its empty body, and from TF (onann_apart). *)
Lemma ofn_apart : forall ly2 S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw b Bf
    st fpz F pos,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  In (ONANN_CID, pos) (frames S2) -> frame_addr ly2 ONANN_CID pos = F -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  onann_apart TF Bw b ->
  garr8 segs (mrestrict (w_H W) memN) (F + 224) (map DSpec.bz (ofn_nb_bytes st fpz (F + 32))) ->
  notice_apart W memN (F + 224) (onann_fntc Bf b) TF Bf.
Proof.
  intros ly2 S2 W2 mem2 md2 W memN TF Bw b Bf st fpz F pos LAWS HGX HAR Hin EFA HF0 HF47 Hap HNB x Hx.
  pose proof (notice_wr_G _ _ _ Hx) as HxG. destruct (HGX x HxG) as [Hix _].
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos x HAR Hin);
      [rewrite EFA; change (fs_frame_bytes ONANN_CID) with 512; unfold NTC_SIZE in Hr; lia | exact Hix].
  - intros NB HG8 HL. split.
    + unfold onann_fntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros _.
      assert (EN : NB = ofn_nb_bytes st fpz (F + 32)).
      { apply ofn_map_bz_inj. apply (ofn_garr8_det (w_H W) memN (F + 224)); [exact HG8 | exact HNB |].
        rewrite !length_map, HL, ofn_nb_len. reflexivity. }
      rewrite EN, (ofn_nb_24 st fpz (F + 32)) by lia. unfold ANN_SIZE. intros Hr.
      apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos x HAR Hin);
        [rewrite EFA; change (fs_frame_bytes ONANN_CID) with 512; lia | exact Hix].
  - intros fr Hfr. exact (onann_apart_ntc TF Bw b (notice_wr Bf (onann_fntc Bf b)) Hap
      (fun x0 Hx0 => onann_wr_fntc Bf Bf Bw b x0 Hx0) x Hx fr Hfr).
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 5. The cut's facts at a later memory                                *)
(* ------------------------------------------------------------------ *)

Section cs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* onann_cur at a later memory mem3 (and model md3) of the cut state, when every byte that changed is in the call's
   stack window below sp1, in the own frame (its bytes, its shadow bytes, its flag byte: TransportGCg.v dkg_nf) or
   in G, and misses the frame's last word. What the call kept: TransportGFrame.v dk_kept_step_gw with the own frame's
   separation facts (dkg_nf_sep_gw). *)
Lemma ofn_cur_step : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z)
         (Zs : Z -> Prop),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc YE2k.tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, Zs a -> (spZ regs - ONANN_STK <= a < spZ regs - 192) \/
     dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos) a \/ inG TG.G_HARNESS_B a) ->
  (forall a, Zs a -> ~ (F + 504 <= a < F + 512)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
  intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2
    W2 mem2 mem3 md2 md3 e Zs HFIX HCUR HJ3 HZ HZF KD GA.
  pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & EF & _).
  pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
  pose proof (onann_cur_ar B MT LAWS HFIX HCUR) as (HARc & HAR2 & Elo & Ehi & Efa & Efl & Hin2 & EFA2 & HFb & HFsh &
    HFnG & HF4096 & HF64 & HFce & HFapp & Hceil & Hlo2 & Hhi2 & H47 & HFLp & HFLo & HFLr & HFLs1 & HFLs2 & Hsp1 &
    Hsp132 & Hsp146).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
  destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
    (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
  - apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) Zs HARc HK KD GA).
    + intros a Hz Hc. destruct (HZ a Hz) as [Hw | [Hn | Hg]]; [lia | pose proof (N4 a Hn); lia |].
      pose proof (inG_low segs B transportb_segs_low _ a HGX Hg). unfold kLowMemEnd in *. lia.
    + intros b0 m i Hb Hi Ha. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HARc Hb) as (_ & H4096 & Hbc & _).
      destruct (HZ _ Ha) as [Hw | [Hn | Hg]]; [lia | exact (N1 b0 m i Hb Hi Hn) |].
      destruct (HGX _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b0 m (b0 + i) HARc Hb ltac:(lia) Hi').
    + intros a Ha Hi HnG _ _. exfalso. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
      destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [lia | exact (N2 a Hn Hi) | exact (HnG Hg)].
    + intros cid pos' a Hin Hr Ha. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HARc Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct (HZ a Ha) as [Hw | [Hn | Hg]].
      * destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
      * exact (N3 cid pos' a Hin Hr Hn).
      * destruct (HGX _ Hg) as [Hi _]. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
        destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
        -- exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr Hi).
        -- pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(lia) ltac:(lia)).
           unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros Hz.
    assert (HSTK : ONANN_STK = 208 + WAKE_STK) by reflexivity.
    assert (HWE : 4096 <= WAKE_STK) by (vm_compute; discriminate).
    destruct (HZ _ Hz) as [Hw | [Hn | Hg]]; [lia | pose proof (N4 _ Hn); lia |].
    pose proof (inG_low segs B transportb_segs_low _ _ HGX Hg). unfold kLowMemEnd in *. lia.
  - rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KD; [unfold ONANN_FBYTES; lia|]. intros Hz.
    exact (HZF _ Hz ltac:(unfold ONANN_FBYTES; lia)).
Qed.
End cs.
