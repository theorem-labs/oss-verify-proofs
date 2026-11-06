(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_ntc.v, with its module names and numbers changed; 773 of its 1107 lines of code are new or changed and 792 lines of the source are left out. *)
(* on_ack_seg_ntc: Lemma onack_ntc_piece : onack_ntc_stmt (lib/A/Prog/on_ack_segs.v), the notice piece of on_ack,
   offsets +0x180 .. +0x248 of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x885ac .. 0x88674),
   then the after-notice cut +0x24c, which the onack_aft_at it is given closes.

   What the code does. +0x180 `lb a1, 0(a3)` / `bnez a1`: the check of the store at s + 212 (a3 = its shadow byte, 0:
   g_s's payload lies in the record's zero shadow, on_ack_cg.v trans_onack_cells, read by DgnTransportCg.v
   decode_zshadow_rd); s5 = p = F + 32; the store of 0 at s + 212 (:229, the world is then onack_w1 Bw); the notice's
   shadow bytes 4 .. 12 := 0; the store of 4 at p; s6 = s + 112, s11 = its shadow address, the checked load of
   S_state; the stores at p + 8 (8 zero bytes), p + 4 (the state) and p + 16 (fp); a0 = p + 24, a1 = 0, a2 = 40 and
   `jal __asan_memset` (+0x1ec); the store of s10 at p + 64 (its low 32 bits, fr_ack b); the checked 2-byte load at
   s + 1748 and the stores at p + 68 (its low 16 bits) and p + 70; the checked 8-byte loads of s + 96 (notify) and
   s + 104 (ctx); a1 = p; `jalr a2` (+0x248).

   Two runs of the token engine over the caller's G journal (lib/A/Prog/TransportGRunA.v), from a symbolic state with
   s3 = s, s9 = the shadow base and a3 = the shadow address of s + 212 pinned as literals, so every check reads a
   literal shadow address: run 1 (+0x180 .. +0x1ec) stops at the memset's call, which TransportGCg.v gx_intrin_at
   takes; run 2 (+0x1f0 .. +0x248) goes through `jalr a2`, whose register holds the code pointer the 8 bytes at s + 96
   hold (a region chunk SOff A_TEXT AF_notice: the model's call_notify answers, so S_notify (onack_w1 Bw) is
   TI.ti_notice timg_A = BASE + AF_notice), and stops at notice's entry (paj_run_to_x). notice's contract
   (notice_cg.v transport_notice_cg) is applied there; its post is notice's world B2 with the bytes notice_wr names
   changed, and from it the after-notice cut onack_aft_cur is built: the call's acall_kept_g folds notice's
   (TransportGCg.v dk_kept_trans_nf_g), and the current heap frame TF is carried from the call's entry by the clauses
   of acall_kept_g, the cut's trans_tf_off_g TF ruling out a TF inside G (ont_tframe). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame on_ack_segs on_ack_seg_wld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From Stdlib Require Znumtheory.
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
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x180                                     *)
(* ------------------------------------------------------------------ *)

(* The shadow bytes the checks read: of s + 96 (s + 104 and s + 112 have the next two), of s + 212, of s + 1748. *)
Definition ONT_SH96 : Z := 2148220740.
Definition ONT_SH212 : Z := 2148220754.
Definition ONT_SH1748 : Z := 2148220946.
Lemma ont_sh_eq : ONT_SH96 = SHADOW_OFF + (ONACK_S + 96) / 8 /\ ONT_SH212 = SHADOW_OFF + (ONACK_S + 212) / 8 /\
  ONT_SH1748 = SHADOW_OFF + (ONACK_S + 1748) / 8 /\ ONT_SH96 + 2 = SHADOW_OFF + (ONACK_S + 112) / 8.
Proof. repeat split; reflexivity. Qed.

(* The regions: the notice's shadow bytes 4 .. 12 (s7, atom 23); the notice's bytes p + 0 .. p + 24 and p + 64 ..
   p + 72 (s8, atom 24; the memset writes the bytes between); g_s's bytes s + 96 .. s + 216 (notify: the code pointer
   of notice; ctx: atom 34; state: atom 32; inflight written) and s + 1748 .. s + 1752 (retries: atom 33); the five
   shadow bytes of g_s the checks read. *)
Definition ont_R_sh : YP09.region := YP09.mkRegion (Some 23%nat) 4 13 4 13 [].
Definition ont_R_p1 : YP09.region := YP09.mkRegion (Some 24%nat) 32 56 32 56 [].
Definition ont_R_p2 : YP09.region := YP09.mkRegion (Some 24%nat) 96 104 96 104 [].
Definition ont_R_gs : YP09.region :=
  YP09.mkRegion None (ONACK_S + 96) (ONACK_S + 216) (ONACK_S + 212) (ONACK_S + 216)
    [YP09.mkChunk (ONACK_S + 96) (YP09.CVal 8 (SOff A_TEXT AF_notice));
     YP09.mkChunk (ONACK_S + 104) (YP09.CVal 8 (SOff 34 0));
     YP09.mkChunk (ONACK_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition ont_R_gr : YP09.region :=
  YP09.mkRegion None (ONACK_S + 1748) (ONACK_S + 1752) 0 0 [YP09.mkChunk (ONACK_S + 1748) (YP09.CVal 4 (SOff 33 0))].
Definition ont_R_shg : YP09.region :=
  YP09.mkRegion None ONT_SH96 (ONT_SH96 + 3) 0 0
    [YP09.mkChunk ONT_SH96 (YP09.CVal 1 (SLit 0)); YP09.mkChunk (ONT_SH96 + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (ONT_SH96 + 2) (YP09.CVal 1 (SLit 0))].
Definition ont_R_shi : YP09.region :=
  YP09.mkRegion None ONT_SH212 (ONT_SH212 + 1) 0 0 [YP09.mkChunk ONT_SH212 (YP09.CVal 1 (SLit 0))].
Definition ont_R_shr : YP09.region :=
  YP09.mkRegion None ONT_SH1748 (ONT_SH1748 + 1) 0 0 [YP09.mkChunk ONT_SH1748 (YP09.CVal 1 (SLit 0))].
Definition ont_regions : smem := [ont_R_sh; ont_R_p1; ont_R_p2; ont_R_gs; ont_R_gr; ont_R_shg; ont_R_shi; ont_R_shr].
Definition ont_facts : facts :=
  mkFacts [(23%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (24%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
(* s3 = s, s9 = the shadow base, a3 = the shadow address of s + 212, as literals. *)
Definition ont_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SLit ONACK_S)) (Z_to_bv 5 25) (SLit SHADOW_OFF))
    (Z_to_bv 5 13) (SLit ONT_SH212).
Definition ss_ont : sstate := mkSS ONACK_NTC ont_regs ont_regions None ont_facts.
Definition ONT_Bx : sv := SLit 0.
Definition ONT_B0 : Z * Z := (0, 0).

(* ------------------------------------------------------------------ *)
(* 2. Facts about bytes, registers and the model                       *)
(* ------------------------------------------------------------------ *)

(* A byte of the view read as 0 is a stored 0. *)
Lemma ont_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma ont_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
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
Lemma ont_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
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

(* A chunk of w bytes of the value e reads the w low little-endian bytes of e. *)
Lemma ont_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case closed
   by tac. *)
Ltac ont_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The shadow hull of a range of a 64-aligned frame of fs bytes (a multiple of 64) lies in the frame's fs / 8
   shadow bytes; the range may be empty. *)
Lemma ont_hull_in : forall (rd : Z -> option Z) Fc fs q n,
  0 <= Fc -> Fc mod 64 = 0 -> fs mod 64 = 0 -> 64 <= fs -> Fc <= q -> 0 <= n -> q + n <= Fc + fs ->
  (forall i, 0 <= i < fs / 8 -> rd (SHADOW_OFF + Fc / 8 + i) <> None) ->
  shadow_hull_vis rd q n.
Proof.
  intros rd Fc fs q n HF0 HF64 Hfs64 Hfs Hq Hn Hqn HV s Hs.
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_mod Fc 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  pose proof (Z.div_mod fs 64 ltac:(lia)) as DS. rewrite Hfs64, Z.add_0_r in DS.
  set (g := Fc / 64) in *. set (h := fs / 64) in *.
  assert (EF8 : Fc / 8 = 8 * g) by (rewrite DF; replace (64 * g) with ((8 * g) * 8) by ring; apply Z.div_mul; lia).
  assert (ES8 : fs / 8 = 8 * h) by (rewrite DS; replace (64 * h) with ((8 * h) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 0 <= g) by lia. assert (Hh : 1 <= h) by lia.
  assert (L1 : 8 * g <= q / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (q + n - 1) / 8 < 8 * g + 8 * h) by (apply Z.div_lt_upper_bound; lia).
  assert (A1 : 268431360 + g <= (2147450880 + q / 8) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (A2 : (2147450880 + (q + n - 1) / 8) / 8 < 268431360 + g + h) by (apply Z.div_lt_upper_bound; lia).
  replace s with (SHADOW_OFF + Fc / 8 + (s - (SHADOW_OFF + Fc / 8))) by ring.
  apply HV. rewrite ES8. unfold SHADOW_OFF. rewrite EF8. lia.
Qed.

(* The 72 bytes of the notice at p = F + 32, as WalkNotify.v ntc_acked_bytes reads them: the stores of 4, the state,
   8 zero bytes and fp, the memset's 40 zeros, the counter, the retry and 2 zero bytes. *)
Lemma ont_nb : forall (H : word -> bool) (m : word -> option byte) F st fpz cnt rt,
  val_mem tfibsegs (mrestrict H m) (F + 32) 4 4 ->
  val_mem tfibsegs (mrestrict H m) (F + 36) 4 st ->
  val_mem tfibsegs (mrestrict H m) (F + 40) 8 0 ->
  val_mem tfibsegs (mrestrict H m) (F + 48) 8 fpz ->
  (forall a, F + 56 <= a < F + 96 -> aview tfibsegs H m a = Some 0) ->
  val_mem tfibsegs (mrestrict H m) (F + 96) 4 cnt ->
  val_mem tfibsegs (mrestrict H m) (F + 100) 2 rt ->
  val_mem tfibsegs (mrestrict H m) (F + 102) 2 0 ->
  garr8 tfibsegs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_acked_bytes st fpz cnt rt)).
Proof.
  intros H m F st fpz cnt rt V0 V4 V8 V16 Z0 V64 V68 V70.
  unfold WN.ntc_acked_bytes. rewrite !map_app.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 4 4 V0)|].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 4) with (F + 36) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 4 st V4)|].
  rewrite length_map, TWL.length_put. replace (F + 36 + Z.of_nat 4) with (F + 40) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 8 0 V8)|].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 8) with (F + 48) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 8 fpz V16)|].
  rewrite length_map, TWL.length_put. replace (F + 48 + Z.of_nat 8) with (F + 56) by lia.
  apply garr8_app. split.
  { rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
    apply garr8_zeros. intros a Ha.
    pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
    destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
    cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity. }
  rewrite length_map, repeat_length. replace (F + 56 + Z.of_nat 40) with (F + 96) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 4 cnt V64)|].
  rewrite length_map, TWL.length_put. replace (F + 96 + Z.of_nat 4) with (F + 100) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put _ _ _ 2 rt V68)|].
  rewrite length_map, TWL.length_put. replace (F + 100 + Z.of_nat 2) with (F + 102) by lia.
  exact (TransportGNotice.garr8_of_put _ _ _ 2 0 V70).
Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma ont_sext32 : forall E Bw, ew E 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state Bw).
Proof.
  intros E Bw H. pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The low 16 bits of the sign-extended 2-byte load. *)
Lemma ont_sext16_low : forall u, 0 <= u < 2 ^ 64 ->
  bv_unsigned (sext 64 (bv_extract 0 16 (Z_to_bv 64 u))) mod 2 ^ 16 = u mod 2 ^ 16.
Proof.
  intros u Hu. rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite (unsigned_lit_small u) by lia. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 16) with (2 ^ 16).
  change (bv_half_modulus 16) with (2 ^ 15).
  Z.div_mod_to_equations. lia.
Qed.

(* The low 32 bits of the sign-extended counter are the counter. *)
Lemma ont_swrap_low : forall x, 0 <= x < 2 ^ 32 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) mod 2 ^ 32 = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
  change (bv_half_modulus 32) with (2 ^ 31).
  Z.div_mod_to_equations. lia.
Qed.

(* The store of :229 at its numeral offset. *)
Lemma ont_w1_eq : forall Bw, onack_w1 Bw = TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0).
Proof. intros Bw. reflexivity. Qed.

(* A byte of a row of G is a byte of G. *)
Lemma ont_inG : forall b0 n0 a, In (b0, n0) TG.G_HARNESS -> b0 <= a < b0 + n0 -> inG TG.G_HARNESS a.
Proof.
  intros b0 n0 a Hin Ha. unfold inG. apply Exists_exists. exists (b0, n0).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma ont_inG_gs : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (ont_inG _ _ a (TMAP_A_in_G _ _ _ TMAP_A_g_s)). unfold ONACK_S in Ha. lia. Qed.

(* The notice of this call is an N_ACKED notice: notice's stores are GOT.acked. *)
Lemma ont_nwr_acked : forall Bx Bw b a, notice_wr Bx (onack_ntc Bw b) a -> twa_fld TW.OFF_GOT TA_GOT TW.A_GOT_acked 4 a.
Proof.
  intros Bx Bw b a H. unfold notice_wr in H.
  destruct H as [(E & _) | [(_ & H) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]]; [| exact H | | | |];
    unfold onack_ntc in E; cbn [TI.n_kind] in E;
    unfold TS0.DIGINET_N_ACKED, TC.N_STATE, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E.
Qed.

(* An N_STATE notice writes GOT.t[GOT.n] (0 <= GOT.n < 16) and GOT.n: bytes of [GOT, GOT + 196). *)
Lemma ont_nwr_state : forall Bx (n : TI.ntc) a, TI.n_kind n = TC.N_STATE -> notice_wr Bx n a ->
  TA_GOT <= a < TA_GOT + 196.
Proof.
  intros Bx n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(_ & [(Hg & Hf) | Hf]) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  - unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.OFF_GOT in *. lia.
  - unfold twa_fld, TW.A_GOT_n, TW.OFF_GOT in Hf. lia.
Qed.

(* Every byte the call may store is a byte of G. *)
Lemma ont_wr_G : forall Bw b a, onack_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
  intros Bw b a H.
  pose proof (TMAP_A_in_G _ _ _ TMAP_A_g_s) as Gs. pose proof (TMAP_A_in_G _ _ _ TMAP_A_GOT) as Gg.
  unfold onack_wr in H.
  destruct H as [H | [H | [H | [H | H]]]].
  - apply (ont_inG _ _ _ Gs). unfold twa_fld, TW.A_S_stats_rx_ignored, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - apply (ont_inG _ _ _ Gs). unfold twa_fld, TW.A_S_inflight, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - apply (ont_inG _ _ _ Gg). pose proof (ont_nwr_acked _ _ _ _ H) as Ht.
    unfold twa_fld, TW.A_GOT_acked, TW.OFF_GOT, TW.SZ_GOT in *. lia.
  - apply (ont_inG _ _ _ Gs). unfold twa_fld, TW.A_S_wake_acked, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - destruct H as (_ & [H | (_ & [H | H])]).
    + apply (ont_inG _ _ _ Gs). unfold twa_fld, TW.A_S_next_keepalive_us, TW.OFF_g_s, TW.SZ_g_s in *. lia.
    + apply (ont_inG _ _ _ Gs). unfold twa_fld, TW.A_S_state, TW.OFF_g_s, TW.SZ_g_s in *. lia.
    + apply (ont_inG _ _ _ Gg). pose proof (fun K => ont_nwr_state _ _ _ K H) as Ht. specialize (Ht eq_refl).
      unfold TW.SZ_GOT. lia.
Qed.

(* On the notice path, call_notify's test holds and notice answers. *)
Lemma ont_model : forall (TF : option TI.tframe) Bw b Bw',
  TSS.on_ack_m timg_A TF Bw b = Some (Bw', tt) -> onack_ign Bw b = false ->
  exists B2, TW.S_notify (onack_w1 Bw) = TI.ti_notice timg_A /\
    TC.notice_m timg_A TF (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt) /\
    TSS.call_notify timg_A TF (onack_w1 Bw) (onack_ntc Bw b) = Some (B2, tt).
Proof.
  intros TF Bw b Bw' Hm Hi.
  destruct (onack_model_ntc timg_A TF Bw b Bw' Hi Hm) as (B2 & HC & _).
  exists B2. pose proof HC as HC'. unfold TSS.call_notify in HC'.
  destruct (Z.eqb_spec (TW.S_notify (onack_w1 Bw)) (TI.ti_notice timg_A)) as [E|E]; [|discriminate HC'].
  exact (conj E (conj HC' HC)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section ont. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of the two runs: the registers at the cut, then the world's state, retries and notify context. *)
Definition ont_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1748) 4);
   Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 104) 8)].
Definition ont_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (ont_vals Bw)).

(* The symbolic state at +0x180 holds of the machine state there, before the three registers are pinned. *)
Lemma ont_entry0 : forall ly S (W : world segs) regs mem md Bw F,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> TW.S_notify Bw = TI.ti_notice timg_A ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= ONACK_S \/ ONACK_S + TW.SZ_g_s <= F) ->
  (forall a, (F + 32 <= a < F + 56 \/ F + 96 <= a < F + 104) -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (ont_E regs Bw) (mkSS ONACK_NTC sr_atoms ont_regions None ont_facts)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw F HSC HAR Htw HNT R23 R24 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := ont_E regs Bw).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, ont_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, ont_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = F)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (ont_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ont_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth ont_vals] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 112) 4) as R32.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1748) 4) as R33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 104) 8) as R34.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32, R33. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall T, T mod 8 = 0 -> ONACK_S <= T -> T + 8 <= ONACK_S + TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr T) 1 0).
  { intros T HT Hlo Hhi. apply ont_vm0.
    exact (decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) T HAR HT Hlo Hhi HSC). }
  assert (EUN : TW.u_at Bw (TW.OFF_g_s + 96) 8 = BASE + AF_notice).
  { change (TW.S_notify Bw = BASE + AF_notice). rewrite HNT. reflexivity. }
  assert (EBN : BASE + AF_notice = 0x83578) by reflexivity.
  assert (CS : ONACK_S = 6158784) by reflexivity.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ont_regions.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ont_R_sh ont_R_p1 ont_R_p2 ont_R_gs
        ont_R_gr ont_R_shg ont_R_shi ont_R_shr base_val]; rewrite ?U23, ?U24.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. left. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. right. lia.
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        apply ont_inG_gs. unfold TW.SZ_g_s. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val segs E _ 0 (ONACK_S + 96) 8 (SOff A_TEXT AF_notice) (BASE + AF_notice));
             [apply codeptr_val; exact HEI | rewrite EBN; lia | lia |].
           replace (0 + (ONACK_S + 96)) with (TA_g_s + 96) by (unfold ONACK_S; lia).
           rewrite <- EUN.
           exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONACK_S + 104) 8 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
           replace (0 + (ONACK_S + 104)) with (TA_g_s + 104) by (unfold ONACK_S; lia).
           exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONACK_S + 112) 4 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 112) 4));
             [apply DEN; [exact E32 | lia] | exact R32 | lia |].
           replace (0 + (ONACK_S + 112)) with (TA_g_s + 112) by (unfold ONACK_S; lia).
           exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (ONACK_S + 1748) 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 1748) 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      replace (0 + (ONACK_S + 1748)) with (TA_g_s + 1748) by (unfold ONACK_S; lia).
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 1748 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold ONT_SH96; lia|]. split; [unfold ONT_SH96; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 ONT_SH96 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace ONT_SH96 with (FCells.shadow_addr (ONACK_S + 96)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (ONT_SH96 + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (ONT_SH96 + 1) with (FCells.shadow_addr (ONACK_S + 104)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (ONT_SH96 + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. replace (ONT_SH96 + 2) with (FCells.shadow_addr (ONACK_S + 112)) by (vm_compute; reflexivity).
        apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
    + split; [unfold ONT_SH212; lia|]. split; [unfold ONT_SH212; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 ONT_SH212 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. replace ONT_SH212 with (FCells.shadow_addr (ONACK_S + 208)) by (vm_compute; reflexivity).
      apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
    + split; [unfold ONT_SH1748; lia|]. split; [unfold ONT_SH1748; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 ONT_SH1748 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. replace ONT_SH1748 with (FCells.shadow_addr (ONACK_S + 1744)) by (vm_compute; reflexivity).
      apply ZSH; [rewrite CS; reflexivity | lia | unfold TW.SZ_g_s; lia].
  - apply pairwise_disjoint_of_extents.
    unfold ont_regions, extent_of_region, ont_R_sh, ont_R_p1, ont_R_p2, ont_R_gs, ont_R_gr, ont_R_shg, ont_R_shi,
      ont_R_shr.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, ONT_SH96, ONT_SH212, ONT_SH1748, SHADOW_OFF, ONACK_S,
      TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. destruct HFapp as (HA0 & [HAL | (HAH1 & HAH2)]); destruct HFG as [HG1 | HG1];
      repeat split; first [exact I | lia].
  - unfold ont_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U24.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma ont_entry : forall ly S (W : world segs) regs mem md Bw F,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> TW.S_notify Bw = TI.ti_notice timg_A ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  YK11.getr regs 13 = w64 (SHADOW_OFF + (ONACK_S + 212) / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= ONACK_S \/ ONACK_S + TW.SZ_g_s <= F) ->
  (forall a, (F + 32 <= a < F + 56 \/ F + 96 <= a < F + 104) -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (ont_E regs Bw) ss_ont
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw F HSC HAR Htw HNT R23 R24 R19 R25 R13 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  rewrite restrict_mkst_fx.
  pose proof (ont_entry0 ly S W regs mem md Bw F HSC HAR Htw HNT R23 R24 HF0 HF64 HFc HFapp HFG Hpf Hpsh) as H0.
  assert (R13' : YK11.getr regs (Z_to_bv 5 13) = Z_to_bv 64 ONT_SH212) by exact R13.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) ONACK_S H0 R19 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) SHADOW_OFF H1 R25 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 13) ONT_SH212 H2 R13' eq_refl) as H3.
  exact H3.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ont_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ont_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with the eight regions of ss_ont (U23 / U24: the bases' values; EF: the
   frame's address F = frame_addr lyc ONACK_CID pos). *)
Ltac ont_awr U23 U24 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONACK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U23 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes ONACK_CID / 8) with 32; lia |];
  eapply awr_ok_x_cons_own with (cid := ONACK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes ONACK_CID) with 256; lia |];
  eapply awr_ok_x_cons_own with (cid := ONACK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes ONACK_CID) with 256; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply ont_inG_gs; unfold ONACK_S, TA_g_s, TW.SZ_g_s in *; lia |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, g_s.inflight, and the stack window of __asan_memset below sp1. *)
Definition ont_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (ONACK_S + 212 <= x < ONACK_S + 216) \/ (sp1 - ESTACK <= x < sp1).

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma ont_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem segs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) -> val_mem segs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma ont_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw b fpz F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (ONACK_CID, pos) (frames S2) ->
  F = frame_addr lyc ONACK_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  F + 256 <= spZ regsC - NOTICE_STK ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32)
    (map DSpec.bz (WN.ntc_acked_bytes (TW.S_state (onack_w1 Bw)) fpz (DSpec.fr_ack b)
       (DSpec.u16 (TW.S_inflight_retries (onack_w1 Bw))))) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 32) (onack_ntc Bw b).
Proof.
  intros lyc S2 W memN mdN regsC Bw b fpz F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN ONACK_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes ONACK_CID) with 256 in HFb.
  change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (st := TW.S_state (onack_w1 Bw)) in *.
  set (rt := DSpec.u16 (TW.S_inflight_retries (onack_w1 Bw))) in *.
  assert (Hst : - 2 ^ 31 <= st < 2 ^ 31) by (unfold st, TW.S_state; apply TWL.s32_range).
  assert (Hrt : 0 <= rt < 2 ^ 16).
  { unfold rt, DSpec.u16. pose proof (Z.mod_pos_bound (TW.S_inflight_retries (onack_w1 Bw)) 65536 ltac:(lia)). lia. }
  assert (Hcnt : 0 <= DSpec.fr_ack b < 2 ^ 32) by (unfold DSpec.fr_ack; apply DSpec.be32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists ONACK_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes ONACK_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (TransportGNotice.frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (ont_hull_in _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_acked_bytes st fpz (DSpec.fr_ack b) rt).
  split; [exact HNB|].
  unfold onack_ntc. fold st rt.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_acked_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 4 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpz ++ repeat (DSpec.b8 0) 40 ++
                        TW.put 4 (DSpec.fr_ack b) ++ TW.put 2 rt ++ TW.put 2 0) 48 8 = 0) by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hst |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply Z.mod_small; exact Hcnt |].
  split; [WN.ntc_field; apply Z.mod_small; cbn; lia |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B lyc S2 W memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_ACKED notice: GOT.acked, bytes of G) are apart from the notice's own bytes (a frame is not
   image), from its empty body, and from TF (onack_apart: they are bytes of onack_wr). *)
Lemma ont_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw b F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (ONACK_CID, pos) (frames S2) ->
  F = frame_addr lyc ONACK_CID pos -> onack_apart TF Bw b ->
  notice_apart W memN (F + 32) (onack_ntc Bw b) TF (onack_w1 Bw).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw b F pos LAWS HAR Hin EF Hap x Hx.
  assert (Hw : onack_wr Bw b x) by (right; right; left; exact Hx).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 ONACK_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes ONACK_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (ont_wr_G Bw b x Hw)).
  - intros NB _ _. split.
    + unfold onack_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* The current heap frame, as trans_tframe_at states it at on_ack's entry, at a later state (ly2, S2, W2, mem2)
   whose frames are the own frame on top of the entry's and whose blocks contain the entry's: what the call kept
   (acall_kept_g over onack_wr) keeps TF's bytes, by the clause of TF's placement (a block or a frame of the entry:
   onack_apart keeps TF out of onack_wr; the machine stack: at or above alloc_ceiling, outside on_ack's window; a
   TRANS_RO_RD byte: an image byte outside G, the owned statics and errno); a TF inside G is ruled out by
   trans_tf_off_g TF. *)
Lemma ont_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 (regs regsN : bvmap 5 word) (K : Z)
    (TF : option TI.tframe) (Bw b : list byte) cid pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (cid, pos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc -> ly_stk_lo lyc < ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) ->
  onack_apart TF Bw b -> trans_tf_off_g TF ->
  spZ regs - ONACK_STK <= spZ regsN - K -> spZ regsN <= spZ regs ->
  trans_tframe_at B lyc Sc W memc regs ONACK_STK TF ->
  trans_tframe_at B ly2 S2 W2 mem2 regsN K TF.
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs regsN K TF Bw b cid pos HARc HAR2 Hfr Hbl Hfa
    Elo Ehi Hstk (K1 & K2 & K3 & K4 & K5 & K6) Hap HoffG Hw1 Hw2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (HnE : forall a, q <= a < q + n -> ~ onack_wr Bw b a) by (intros a Ha Hx; exact (Hap a Hx fr eq_refl Ha)).
  assert (HnG : forall a, q <= a < q + n -> ~ inG TG.G_HARNESS a) by (intros a Ha; exact (HoffG fr eq_refl a Ha)).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
  (* the bytes of TF's range are the entry's *)
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
      pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) HinA ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (HnG a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HARc) as [T1 T2].
        apply K1; [lia | unfold decode_off_win in Hoff; lia].
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TG.G_HARNESS_LO in Gh. lia. }
  (* the entry's frames' shadow bytes are the entry's: onack_wr lies in G, below the shadow *)
  assert (KS : forall c p s, In (c, p) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
    pose proof (inG_G_HARNESS_hull s (ont_wr_G Bw b s Hw)) as Hl.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HARc Hin) as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF, TG.G_HARNESS_HI in *. lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs). apply KV. exact Ha. }
  split.
  2: { unfold decode_off_win in *. lia. }
  destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ HinA) | lia].
  - right. split.
    + destruct HL as [(c & p & Hin & F1 & F2) | [HG | [(S1 & S3) | HR]]].
      * left. exists c, p. rewrite !Hfa. split; [exact (Hfin _ Hin) | lia].
      * right; left; exact HG.
      * right; right; left. rewrite Elo, Ehi. lia.
      * right; right; right; exact HR.
    + destruct (Z_lt_le_dec 0 n) as [Hn | Hn].
      * destruct HL as [HF | [(HG & _) | [(S1 & S3) | (_ & Hsh)]]].
        -- exact (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HARc HF Hrd Hn KV KS).
        -- exfalso. exact (HnG q ltac:(lia) (HG q ltac:(lia))).
        -- destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
             as [Ha Hh].
           exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
        -- destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      * assert (En : n = 0) by lia.
        apply (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV); [intros x Hx; lia|].
        destruct HL as [(c & p & Hin & F1 & F2) | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
        -- assert (Hin2 : In (c, p) (frames S2)) by exact (Hfin _ Hin).
           destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (_ & _ & _ & HFsh).
           destruct (TransportGCg.dkg_frame_al64 segs B ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (A1 & A2 & A3).
           destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin2) as (G1 & G2 & _).
           rewrite (Hfa c p) in HFsh. rewrite (Hfa c p) in A1. rewrite (Hfa c p) in G1. rewrite (Hfa c p) in G2.
           apply (ont_hull_in _ (frame_addr lyc c p) (fs_frame_bytes c) q n); try lia.
           intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
        -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
        -- destruct (Z_lt_le_dec q (ly_stk_hi lyc)) as [Hq | Hq].
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
                ltac:(rewrite Ehi; lia)) as [_ Hh].
              exact (trans_hull_sub _ q 1 q n Hh ltac:(lia) ltac:(lia)).
           ++ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 (q - 1) 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
                ltac:(rewrite Ehi; lia)) as [_ Hh].
              exact (trans_hull_sub _ (q - 1) 1 q n Hh ltac:(lia) ltac:(lia)).
        -- exact (proj2 (Hsh ly2 S2 W2 mem2 md2 HAR2)).
Qed.

(* The TRANS_RO_RD bytes at a later state whose memory the call's acall_kept_g relates to the entry's: they are
   image bytes outside G (below G_HARNESS_LO), the owned statics and errno. *)
Lemma ont_rom : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Eo : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi Eo ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi Eo (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

Lemma ont_holds : @onack_ntc_stmt fx rc B MT.
Proof.
unfold onack_ntc_stmt. intros AFT. unfold onack_ntc_at.
intros LAWS0 HMS HN HMO STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2
  mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & HDF & Htw0 & Hgf & Hm & HTF & Hrom &
  Hapart & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hbl & HGK & Htw1 & HTF2 & HTFG &
  Hrom2 & Hign).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R25) & R13 & R20 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ONACK_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HOS : 144 + ESTACK <= ONACK_STK /\ 144 + NOTICE_STK <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a (Z.max ?c ?d) /\ _ =>
    pose proof (Z.le_max_l a (Z.max c d)); pose proof (Z.le_max_r a (Z.max c d)); pose proof (Z.le_max_l c d);
    assert (Ha : a = 4096) by reflexivity; assert (Hc : c = NOTICE_STK) by reflexivity end.
  lia. }
destruct HOS as (HOS1 & HOS2).
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONACK_FRAME.
  pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 128) / 32) in *. set (r := (spZ regs - 128) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 ONACK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh.
change (fs_frame_bytes ONACK_CID) with 256 in HFb. change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh.
set (FL := flag_addr lyc ONACK_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 256 <= ONACK_S \/ ONACK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) ONACK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONACK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ ONACK_S <= x < ONACK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONACK_S) as [h3|h3]; [exists ONACK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 ONACK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes ONACK_CID) with 256; lia|].
  exact (trans_g_img x (ont_inG_gs x Hx2)). }
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HFSG : F + 256 <= ONT_SH96 \/ ONT_SH1748 + 1 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [left | right]; unfold ONT_SH96, ONT_SH1748; lia. }
(* the model's facts on this path *)
assert (HL0 : Z.of_nat (length Bw) = TW.W_LEN) by exact (onack_wlen _ _ Htw0).
destruct (onack_w1_facts Bw HL0) as (EW1s & EW1r & EW1n & _ & _ & EW1g & EW1l).
destruct (ont_model TF Bw b Bw' Hm Hign) as (B2 & HNT & HNM & HCN).
assert (HNTB : TW.S_notify Bw = TI.ti_notice timg_A) by (rewrite <- EW1n; exact HNT).
(* +0x180 .. +0x1ec: run 1, up to `jal __asan_memset` *)
pose proof (ont_entry lyc S2 W regs2 mem2 md2 Bw F HOC HAR2 Htw1 HNTB R23 R24 R19 R25 R13 HF0 HF64 ltac:(lia)
  HFapp HFG
  ltac:(intros a Ha; destruct Ha as [Ha | Ha]; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
set (E0 := ont_E regs2 Bw) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ont_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ont_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U23 : bv_unsigned (ew E0 23) = SHADOW_OFF + F / 8)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E0 24) = F)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs ONT_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ1 SHOK ONT_B0.
{ ont_awr U23 U24 EF. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ont_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ont_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ont_win Hiw Hx ltac:(rewrite ?U23, ?U24 in Hx; unfold ont_Z, ONACK_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ont_chunk0 E0 (w_H W) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms) md1 ONACK_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite <- EF, ESH in HFsh1. change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh1.
pmkst HS.
ont_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 56)) Q10 ltac:(cbn [sv_denot]; rewrite U24; reflexivity).
ont_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ont_reg HS (Z_to_bv 5 12) (Z_to_bv 64 40) Q12 ltac:(reflexivity).
ont_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ont_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 29624)) Q1 ltac:(apply codeptr_val; exact HEI).
ont_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ont_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x1ec: __asan_memset (p + 24, 0, 40), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) lyc S2 md1
    (k + 0) (F + 56) 0 40 (sp1 - sp0) (Z_to_bv 64 (BASE + 29624)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
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
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONACK_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes ONACK_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (TransportGNotice.frame_ra_zero _ F (F + 56) 40 7 12); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (ont_hull_in _ F 256 (F + 56) 40); [lia | exact HF64 | reflexivity | lia | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ ont_Z F sp1 a ->
  aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 23%nat (SHADOW_OFF + F / 8)); [exact U23 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 24%nat F); [exact U24 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply (region_kept_aview _ _ _ _ 24%nat F); [exact U24 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply ont_rk_none; [| exact HgrM]. intros a Ha. unfold ONACK_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONACK_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply ont_rk_none; [| exact HgrM]. intros a Ha. unfold ONACK_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONACK_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply ont_rk_none; [| exact HgrM]. intros a Ha. unfold ONT_SH96, ONT_SH1748 in *.
    apply HeffM; [lia | destruct HFSG; lia | lia].
  - apply ont_rk_none; [| exact HgrM]. intros a Ha. unfold ONT_SH96, ONT_SH212, ONT_SH1748 in *.
    apply HeffM; [lia | destruct HFSG; lia | lia].
  - apply ont_rk_none; [| exact HgrM]. intros a Ha. unfold ONT_SH96, ONT_SH1748 in *.
    apply HeffM; [lia | destruct HFSG; lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U23b : bv_unsigned (ew E1 23) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U23).
assert (U24b : bv_unsigned (ew E1 24) = F) by (rewrite E1lo by lia; exact U24).
assert (SHOK1 : sh_ok segs ONT_Bx (@nil shent) E1 (mrestrict (w_H W) memM)) by constructor.
assert (ZMM : forall a, F + 56 <= a < F + 96 -> aview segs (w_H W) memM a = Some 0).
{ intros a Ha. replace a with ((F + 56) + (a - (F + 56))) by lia. rewrite (HsetM (a - (F + 56)) ltac:(lia)). reflexivity. }
clear dependent ms.
(* +0x1f0 .. +0x248: run 2, through `jalr a2` to notice's entry *)
paj_run_to_tok RUNTO HS HJ2 SHOK1 ONT_B0 AF_notice.
{ ont_awr U23b U24b EF. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ ont_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ont_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ont_win Hiw Hx ltac:(rewrite ?U23b, ?U24b in Hx; unfold ont_Z, ONACK_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (ZMN : forall a, F + 56 <= a < F + 96 -> aview segs (w_H W) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 56) \/ (F + 96 <= x < F + 104) \/
    (ONACK_S + 212 <= x < ONACK_S + 216) \/ (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13)) HFr); [| lia |].
  - intros b0 wlo whi x Hiw Hx. cbv beta.
    ont_win Hiw Hx ltac:(rewrite ?U23b, ?U24b in Hx; unfold ONACK_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]).
  - cbv beta. unfold ONACK_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | [Hx | Hx]]]; [lia | lia | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ ont_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS3.
cbn [ms_mem restrict] in RS0, RS1, RS2, RS3.
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ont_chunk0 E1 (w_H W) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
(* the notice's bytes at the call *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4)).
{ rewrite E1lo by lia. unfold E0, ont_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs2 (ont_vals Bw) 0). }
assert (E33 : ew E1 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1748) 4)).
{ rewrite E1lo by lia. unfold E0, ont_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs2 (ont_vals Bw) 1). }
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 1748) 4) as R33. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33.
assert (D26 : sv_denot E1 (SOff 26 0) = Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b))).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact R26. }
assert (D68 : bv_unsigned (sv_denot E1 (SExt true 16 (SOff 33 0))) mod 2 ^ 16
  = DSpec.u16 (TW.S_inflight_retries (onack_w1 Bw))).
{ cbn [sv_denot]. rewrite E33. rewrite (unsigned_lit_small (TW.u_at Bw (TW.OFF_g_s + 1748) 4)) by lia.
  rewrite Z.add_0_r. rewrite ont_sext16_low by lia. rewrite EW1r. reflexivity. }
assert (Hcnt0 : 0 <= DSpec.fr_ack b < 2 ^ 32) by (unfold DSpec.fr_ack; apply DSpec.be32_range).
set (fpz := bv_unsigned (sv_denot E1 (SOff 20 0)) mod 2 ^ (8 * Z.of_N 8)).
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 32 4 (SLit 4) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 36 4 (SExt true 32 (SOff 32 0)) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP4.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 40 8 (SLit 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 48 8 (SOff 20 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP16.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 96 4 (SOff 26 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP64.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 100 2 (SExt true 16 (SOff 33 0)) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP68.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 102 2 (SLit 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP70.
pose proof (ont_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158996 4 (SLit 0) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP4, VP8, VP16, VP64, VP68, VP70, VG.
rewrite U24b in VP0, VP4, VP8, VP16, VP64, VP68, VP70.
rewrite (ont_sext32 E1 Bw E32) in VP4. rewrite D26 in VP64.
change (N.to_nat 8) with 8%nat in VP8, VP16. change (N.to_nat 4) with 4%nat in VP0, VP4, VP64, VG.
change (N.to_nat 2) with 2%nat in VP68, VP70.
change (bv_unsigned (sv_denot E1 (SLit 4)) mod 2 ^ (8 * Z.of_N 4)) with 4 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in VP8.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 2)) with 0 in VP70.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG.
change (8 * Z.of_N 4) with 32 in VP64. rewrite (ont_swrap_low _ Hcnt0) in VP64.
change (8 * Z.of_N 2) with 16 in VP68. rewrite D68 in VP68.
apply (ont_vm_w _ _ 4 (TW.S_state Bw) ltac:(lia)) in VP4.
change (N.to_nat 4) with 4%nat in VP4. rewrite <- EW1s in VP4.
pose proof (ont_nb (w_H W) (ms_mem ms) F (TW.S_state (onack_w1 Bw)) fpz (DSpec.fr_ack b)
  (DSpec.u16 (TW.S_inflight_retries (onack_w1 Bw))) VP0 VP4 VP8 VP16 ZMN VP64 VP68 VP70) as HNB.
(* what the call kept, from its entry to the call of notice *)
destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 ONACK_CID pos F FL HAR2 Hfrs Hbl EF eq_refl FFL)
  as (N1 & N2 & N3 & N4).
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (ONACK_S + 212 <= x < ONACK_S + 216) -> ~ ont_Z F sp1 x).
{ intros x Hx Hn Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes ONACK_CID) with 256; lia | exact (trans_g_img x Hx)].
  - exact (Hn Hz).
  - lia. }
assert (HSZ : forall a, ont_Z F sp1 a ->
  (spZ regs - ONACK_STK <= a < spZ regs) \/ dkg_nf ONACK_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [Hz | [Hz | [Hz | Hz]]].
  - right; left; right; left. change (fs_frame_bytes ONACK_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes ONACK_CID) with 256. lia.
  - right; right. apply ont_inG_gs. unfold TW.SZ_g_s. lia.
  - left; lia. }
pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
  (ms_mem ms) (spZ regs - ONACK_STK) (spZ regs) ONACK_CID pos F FL (onack_wr Bw b) (ont_Z F sp1) HGX HARc HAR2 Hfrs
  (fun bm Hb => eq_ind_r (fun l => In bm l) Hb Hbl) eq_refl EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN)
  as KCN.
(* the registers at notice's entry *)
ont_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 29716)) T1 ltac:(apply codeptr_val; exact HEI1).
ont_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U24b; reflexivity).
ont_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ont_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
ont_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
ont_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ont_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ont_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ont_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ont_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ont_reg HS (Z_to_bv 5 19) (w64 ONACK_S) T19 ltac:(cbn [sv_denot]; unfold w64; vm_compute; reflexivity).
ont_reg HS (Z_to_bv 5 25) (w64 SHADOW_OFF) T25 ltac:(cbn [sv_denot]; unfold w64; vm_compute; reflexivity).
ont_reg HS (Z_to_bv 5 22) (w64 (ONACK_S + 112)) T22 ltac:(cbn [sv_denot]; unfold w64; vm_compute; reflexivity).
ont_reg HS (Z_to_bv 5 27) (w64 (SHADOW_OFF + (ONACK_S + 112) / 8)) T27
  ltac:(cbn [sv_denot]; unfold w64; vm_compute; reflexivity).
pmkst HS.
set (regsC := ms_regs ms) in *. set (memN := ms_mem ms) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite T2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBR : BASE + 29716 = 0x88678) by reflexivity.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC memN md3) Qx) end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (Hblin : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B lyc S2)) by (intros bm Hbm; rewrite Hbl; exact Hbm).
(* the world relation at the call: the store of :229, every other byte of G kept *)
assert (PTW : tw_at TMAP_A (aview segs (w_H W) memN) (onack_w1 Bw)).
{ rewrite ont_w1_eq.
  apply (tw_write TMAP_A (aview segs (w_H W) mem2) _ Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 212 4 0 TMAP_A_ok Htw1
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. assert (L0 : YO0f.le_byte 0 4 j = 0)
      by (unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia; reflexivity).
    rewrite L0. unfold aview. replace (TA_g_s + 212 + Z.of_nat j) with (0 + 6158996 + Z.of_nat j)
      by (unfold TA_g_s; lia).
    rewrite (VG j Hj), L0. reflexivity.
  - intros x Hx Hn. destruct Hx as (o & b0 & n0 & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x) by exact (ont_inG b0 n0 x (TMAP_A_in_G o b0 n0 Hin3) Hx).
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact HxG | unfold ONACK_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
(* +0x248: notice, at TI.ti_notice timg_A, with ra = +0x24c *)
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONACK_CID, pos) :: own) lyc S2 W memN md3 (k + 0) regsC
    (F + 32) (onack_ntc Bw b) TF (onack_w1 Bw) B2
    HJ2
    ltac:(rewrite T1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite T1, EBR; rewrite unsigned_lit_small by lia; lia)
    T3 T4 T11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ont_ntc_at lyc S2 W memN md3 regsC Bw b fpz F pos LAWS HARN Hin EF HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) ZSN HNB)
    (ont_tframe LAWS HRU HRE lyc Sc W memc mdc lyc S2 W memN md3 regs regsC NOTICE_STK TF Bw b ONACK_CID pos
       HARc HARN Hfrs Hblin (fun _ _ => eq_refl) eq_refl eq_refl HSTKLT KCN Hapart HTFG
       ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    (ont_rom HRU HRE lyc Sc W memc W memN _ _ _ KCN Hrom)
    PTW HNM
    (ont_apart lyc S2 W mem2 md2 W memN TF Bw b F pos LAWS HAR2 Hin EF Hapart)
    ltac:(intros HD; exfalso; unfold onack_ntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_ACKED, TC.N_DATA in HD; discriminate HD)
    ltac:(unfold ONACK_EV, MAYBEON_EV in Hev; unfold NOTICE_EV in *; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & ESLO3 & ESHI3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (ONACK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W memN W3 mem3
    (spZ regs - ONACK_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onack_wr Bw b)
    (notice_wr (onack_w1 Bw) (onack_ntc Bw b)) (dkg_nf ONACK_CID F FL)).
  - lia.
  - lia.
  - intros c p. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hblin.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. right. right. left. exact Ha. }
pose proof HK3 as (K31 & _ & _ & K34 & _).
(* the bytes the after-notice code reads: the saved words above sp1 and the frame's last word *)
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite USPC in K31. rewrite K31 by lia.
  apply KAN; [lia|]. unfold ont_Z, ONACK_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) mem3 (F + 248 + i) = aview segs (w_H W) mem2 (F + 248 + i)).
{ intros i Hi. rewrite (K34 ONACK_CID pos (F + 248 + i) Hin).
  - apply KAN; [lia|]. unfold ont_Z, ONACK_S, TA_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | Hz]]]; [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes ONACK_CID) with 256. lia.
  - intros Hw. assert (Hw' : onack_wr Bw b (F + 248 + i)) by (right; right; left; exact Hw).
    apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes ONACK_CID) with 256; lia|].
    exact (trans_g_img _ (ont_wr_G Bw b _ Hw')). }
assert (HSo : forall o, In o ONACK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold ONACK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* the model's facts after notice *)
assert (Hgf2 : TW.g_fail_next B2 <= 1).
{ destruct (onack_B2_eq timg_A TF Bw b B2 HCN) as (a & EB2). rewrite EB2.
  destruct (onack_B2_facts (onack_w1 Bw) a EW1l) as (_ & _ & _ & _ & _ & _ & EG2 & _).
  rewrite EG2, EW1g. exact Hgf. }
(* the after-notice cut *)
assert (CUR3 : onack_aft_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b TF Bw B2 pos F ly3 S3 W3
  mem3 md4 0).
{ split; [|split; [|split; [|split; [|split; [|split]]]]].
  - split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
    split; [unfold ONACK_EV, MAYBEON_EV, NOTICE_EV; lia|].
    split; [exact Hfrs3|].
    split; [rewrite <- Hbl; exact Hperm3|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC3|].
    split.
    + rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    + unfold ONACK_FBYTES. change (flag_addr lyc ONACK_CID pos) with FL. rewrite <- HFLw.
      replace (F + 256 - 8) with (F + 248) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  - exact Htw3.
  - exact (ont_tframe LAWS HRU HRE lyc Sc W memc mdc ly3 S3 W3 mem3 md4 regs regs ONACK_STK TF Bw b ONACK_CID pos
      HARc HAR3 Hfrs3 Hbl3 EFA3 ltac:(rewrite ESLO3, ESLO; reflexivity) ltac:(rewrite ESHI3, ESHI; reflexivity)
      HSTKLT KC3 Hapart HTFG ltac:(lia) ltac:(lia) HTF).
  - exact (ont_rom HRU HRE lyc Sc W memc W3 mem3 _ _ _ KC3 Hrom).
  - exact Hign.
  - exact HCN.
  - exact Hgf2. }
(* the registers the after-notice code reads, kept by notice *)
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (REGS3 : onack_regs_aft regs regs3 sp1 F).
{ unfold onack_regs_aft, onack_regs_ign, onack_regs_rel.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) (conj _ _)) (conj _ _)).
  - exact (eq_trans (CH 2 ltac:(hnf; lia)) T2).
  - exact (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans T3 (eq_sym Hgp))).
  - exact (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans T4 (eq_sym Htp))).
  - exact (eq_trans (CH 8 ltac:(hnf; lia)) (eq_trans T8 R8)).
  - exact (eq_trans (CH 9 ltac:(hnf; lia)) (eq_trans T9 R9)).
  - exact (eq_trans (CH 18 ltac:(hnf; lia)) (eq_trans T18 R18)).
  - exact (eq_trans (CH 23 ltac:(hnf; lia)) (eq_trans T23 R23)).
  - exact (eq_trans (CH 24 ltac:(hnf; lia)) (eq_trans T24 R24)).
  - exact (eq_trans (CH 19 ltac:(hnf; lia)) T19).
  - exact (eq_trans (CH 25 ltac:(hnf; lia)) T25).
  - exact (eq_trans (CH 22 ltac:(hnf; lia)) T22).
  - exact (eq_trans (CH 27 ltac:(hnf; lia)) T27). }
rewrite T1.
change (Z_to_bv 64 (BASE + 29716)) with (Z_to_bv 64 (BASE + ONACK_AFT)).
exact (AFT LAWS0 HMO STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' B2 pos sp1 F
  ly3 S3 W3 mem3 md4 0 regs3 HFIX CUR3 REGS3).
Qed.

End ont.

(* The notice piece of the walk of on_ack (on_ack_segs.v onack_ntc_stmt), at every machine, run ceiling, record and
   meter. *)
Lemma onack_ntc_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onack_ntc_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ont_holds fx rc B MT). Qed.
