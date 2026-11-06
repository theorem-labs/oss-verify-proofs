(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module paths and module names changed; 196 of its 235 lines of code are new or changed and 335 lines of the source are left out. *)
(* TickBKit: the shared kit of the pieces of the image-B walk of diginet_session_tick (lib/B/Prog/TickCutB.v): the
   lemmas of image A's kit that name image A (its segments, G, trans_src_ok or world table), read at image B's names.
   rule 24: proves no function (lemmas for the pieces of a walk; the walk is composed at TickCutB.v tick_holds_of).
   Each lemma has the statement of its image-A original at image B's segments (lib/B/YB1v.v tfibsegs), G
   (lib/B/TransportGB.v G_HARNESS_B), call kit (lib/B/Prog/DgnTransportBCg.v trans_src_ok, decode_in_fake,
   decode_rd_ok), trans_tframe_at (lib/B/Prog/check_state_data_cg.v), world table (lib/B/Prog/TWorldB.v TMAP_B) and
   statement (lib/B/Prog/diginet_session_tick_cg.v tick_wr, slost_w1, TICK_S); the proofs are the originals'.
   - trans_src_ok_fake, trans_tframe_at_top (lib/A/Prog/TickSrcKit.v): trans_src_ok of a range of a frame of the
     state with readable bytes (its fake-frame case); trans_tframe_at of the current heap frame TF carried from the
     entry to a later state of the same G journal with the caller's own frame on top, by
     lib/B/Prog/TransportGNoticeB.v trans_tframe_at_kept_gx. This file and DgnTransportBCg.v are the only ones the
     pieces use to build trans_src_ok.
   - tick_wr_G, tick_wr_lo (lib/A/Prog/TickAckl_kit.v ta_wr_G / ta_wr_lo): every byte of tick_wr is a byte of
     G_HARNESS_B, so below the shadow band (trans_tframe_at_top's premise on the written range); tkb_iosend_G
     (ta_iosend_G): io_send's stores for a frame of at most 1514 bytes are bytes of G_HARNESS_B.
   - slh_inGB, slh_tw_w1B (lib/A/Prog/SlostHead.v slh_inG / slh_tw_w1): g_s's payload bytes are bytes of
     G_HARNESS_B; the world relation at slost_w1 Bw after the stores of 0 at s + 212 and s + 168 (TWorldG.v tw_write
     twice, at TMAP_B).
   - sn_rk_noneB, sn_chunk0B, sn_chunk_valB, sn_vm_wB and the Ltacs sn_winB, sn_regB (lib/A/Prog/SlostNtc.v sn_rk_none,
     sn_chunk0, sn_chunk_val, sn_vm_w, sn_win, sn_reg): readings of the position-abstract engine's regions and
     registers at image B's segments (sn_regB resolves DgnTransportBPaLib.v st_ok_pi_restrict_reg). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess.
From Stdlib Require Znumtheory.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. trans_src_ok and trans_tframe_at (TickSrcKit.v)                  *)
(* ------------------------------------------------------------------ *)

Section k. Context {rc : YM05.RunCeil}.
Variable B : asyms.

(* trans_src_ok of a range inside a frame of the state whose bytes are readable: its fake-frame case. *)
Lemma trans_src_ok_fake : forall lyc Sc (W : world tfibsegs) memc q n,
  decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> trans_src_ok B lyc Sc W memc q n.
Proof. intros lyc Sc W memc q n Hf Hrd. right. split; [left; exact Hf | exact Hrd]. Qed.

(* trans_tframe_at of the current heap frame TF, from the caller's entry (window STKc) to a later state of the same G
   journal with the caller's own frame on top, for a callee window K inside the entry's (header). *)
Lemma trans_tframe_at_top : AR_laws tfibsegs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world tfibsegs) memc mdc S2 memN mdN (regs regsN : bvmap 5 word) (TF : option TI.tframe)
    (E : Z -> Prop) STKc K cid pos,
  @AR rc tfibsegs B lyc Sc W memc mdc -> @AR rc tfibsegs B lyc S2 W memN mdN ->
  frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g tfibsegs B TG.G_HARNESS_B lyc Sc W memc W memN (spZ regs - STKc) (spZ regs) E ->
  gx_kept_ex tfibsegs TG.G_HARNESS_B E W memc W memN ->
  (forall x, E x -> forall fr, TF = Some fr ->
     ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)))) ->
  (forall a, E a -> a < SHADOW_OFF) ->
  spZ regs - STKc <= spZ regsN - K -> spZ regsN <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs STKc TF ->
  trans_tframe_at B lyc S2 W memN regsN K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc S2 memN mdN regs regsN TF E STKc K cid pos HARc HAR2 Hfr Hbl Hstk
    HK HGK Hap HElo Hw1 Hw2 HT.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W memN mdN E regs regsN STKc K TF
    HARc HAR2).
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - intros f Hf. rewrite Hfr. right. exact Hf.
  - intros c p. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hstk.
  - exact HK.
  - exact HGK.
  - intros fr Hfr0 a Ha Ea. exact (Hap a Ea fr Hfr0 Ha).
  - intros a Ha Ea. pose proof (HElo a Ea) as Hl. unfold SHADOW_OFF in Hl. lia.
  - exact Hw1.
  - exact Hw2.
  - exact HT.
Qed.

End k.

(* ------------------------------------------------------------------ *)
(* 2. The written range tick_wr (TickAckl_kit.v)                       *)
(* ------------------------------------------------------------------ *)

Lemma tkb_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
  intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The offsets of the fields are closed numerals under the modules' aliases of TWorld: computed, then lia. *)
Ltac tkb_num := unfold twb_fld in *; cbv -[Z.add Z.sub Z.mul Z.le Z.lt Z.min] in *; lia.

(* io_send's stores for a frame of n <= 1514 bytes are bytes of G. *)
Lemma tkb_iosend_G : forall n a, n <= TC.SPEC_MAX_FRAME -> iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof.
  intros n a Hn H. unfold iosend_wr in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]]]]].
  - apply (tkb_row _ _ _ _ TMAP_B_g_fail_next). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_GOT). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_GOT). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_GOT). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_g_last_counter). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_M). tkb_num.
  - destruct H as (s & Hs & H). apply (tkb_row _ _ _ _ TMAP_B_g_cmd). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_g_q). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_g_nq). tkb_num.
Qed.

(* Every byte of tick_wr is a byte of G. *)
Lemma tick_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw a H. unfold tick_wr in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]]]]]].
  1-13: apply (tkb_row _ _ _ _ TMAP_B_g_s); tkb_num.
  - exact (notice_wr_G _ _ a H).
  - exact (notice_wr_G _ _ a H).
  - exact (notice_wr_G _ _ a H).
  - exact (tkb_iosend_G TC.SPEC_MAX_FRAME a ltac:(lia) H).
  - destruct H as (q & Hq & H). apply (tkb_row _ _ _ _ TMAP_B_g_s). tkb_num.
  - apply (tkb_row _ _ _ _ TMAP_B_g_s). tkb_num.
  - unfold senddata_wr in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
    1-9: apply (tkb_row _ _ _ _ TMAP_B_g_s); tkb_num.
    exact (tkb_iosend_G SENDDATA_CAP a ltac:(cbv; congruence) H).
Qed.

(* Every byte of tick_wr lies below the shadow band (it is a byte of G): trans_tframe_at_top's premise on its written
   range. *)
Lemma tick_wr_lo : forall Bw a, tick_wr Bw a -> a < SHADOW_OFF.
Proof.
  intros Bw a H. pose proof (inG_G_HARNESS_hull a (tick_wr_G Bw a H)) as Hl.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI, SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. g_s in G, and the world after the two lost-arm stores (SlostHead.v) *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma slh_inGB : forall a, TICK_S <= a < TICK_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
  intros a Ha. apply (tkb_row _ _ _ _ TMAP_B_g_s). unfold TICK_S in Ha. exact Ha.
Qed.

Lemma tkb_w1_eq : forall Bw,
  slost_w1 Bw = TW.upd (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0).
Proof. intros Bw. reflexivity. Qed.

(* The world relation after the stores of 0 at s + 212 and s + 168. *)
Lemma slh_tw_w1B : forall (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_B rd Bw ->
  (forall j, 0 <= j < 4 -> rd' (TICK_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (TICK_S + 168 + j) = Some 0) ->
  (forall x, tw_in TMAP_B x -> ~ (TICK_S + 212 <= x < TICK_S + 216) -> ~ (TICK_S + 168 <= x < TICK_S + 172) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (slost_w1 Bw).
Proof.
intros rd rd' Bw Hat HI HD HO.
assert (CS : TICK_S = TB_g_s) by reflexivity.
set (rdm := fun x => if ((TICK_S + 168 <=? x) && (x <? TICK_S + 172))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_B rdm (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (tw_write TMAP_B rd rdm Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0 TMAP_B_ok Hat TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm. rewrite <- CS.
    assert (Hb : ((TICK_S + 168 <=? TICK_S + 212 + Z.of_nat j) && (TICK_S + 212 + Z.of_nat j <? TICK_S + 172))%bool
      = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite Hb, (HI (Z.of_nat j) ltac:(lia)).
    destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((TICK_S + 168 <=? x) && (x <? TICK_S + 172))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite tkb_w1_eq.
apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 168 4 0 TMAP_B_ok H1 TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HD (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((TICK_S + 168 <=? x) && (x <? TICK_S + 172))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Readings of the engine's regions and registers (SlostNtc.v)      *)
(* ------------------------------------------------------------------ *)

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma sn_rk_noneB : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
  (forall a, lo <= a < hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion None lo hi wlo whi cs).
Proof.
  intros E H m m2 lo hi wlo whi cs Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - apply (mbyte_of_aview tfibsegs). apply Hav. lia.
  - apply writable_kept. apply Hp.
Qed.

(* A one-byte chunk of the literal 0 reads 0. *)
Lemma sn_chunk0B : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  exact (chunks_zero_aview E H m (base_val E bopt) cs off Hcs Hin).
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma sn_chunk_valB : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma sn_vm_wB : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
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

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac sn_winB Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac sn_regB HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sn_regB: no match for" T; fail
  end.
