(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 886 of its 1024 lines of code are new or changed and 1072 lines of the source are left out. *)
(* set_state_seg_ntc (image B): Lemma sstb_ntc : sstb_ntc_stmt (lib/B/Prog/set_state_segs.v), the notice piece of the
   image-B walk of set_state, code 0x87420 .. 0x874dc (+0x154 .. +0x210); image B's twin of lib/A/Prog/SlostNtc.v
   (the frame in s9, its shadow address in s8, the notice at p = F + 32 in s7, the state and why in s3 and s2, the
   frame word kept across the call of notice at s1 + 24).
   Run 1 (PaRun token engine) stores the frame word F at s1 + 24, sets s7 = p, unpoisons the notice's shadow bytes
   4 .. 12 and sets up __asan_memset (p + 16, 0, 56), taken through lib/A/Prog/TransportGCg.v gx_intrin_at; run 2
   stores the notice's first 16 bytes (kind 2, st, the old state, why), the checked st at s + 112 (the world
   sstate_w Bw st) and loads g_s.notify and g_s.notify_ctx; `jalr a2` at 0x874b0 calls notice through the premise
   transport_notice_cg (the same G journal; the call's kept facts fold with dk_kept_trans_nf_g); run 3 re-poisons the
   shadow bytes 4 .. 12, loads a0 = F back from s1 + 24 and the proof ends at the release cut sstb_rel_at.
   The notice's 72 bytes are WalkNotify.v ntc_state_bytes st (S_state Bw) why, read as trans_ntc_at reads
   set_state_cg.v sstate_ntc Bw st why; their range is a range of the walk's own side-stack frame (its fake-frame
   case of trans_src_ok, ssn_src_ok_fake below). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg set_state_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TGNB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportGNoticeB.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* On the notice path (the state the code loaded is not st), call_notify's test holds and notice gives Bw'. *)
Lemma ssn_model : forall (TF : option TI.tframe) Bw st why Bw',
  TSS.set_state_m timg_B TF Bw st why = Some (Bw', tt) -> TW.S_state Bw <> st ->
  TW.S_notify (sstate_w Bw st) = TI.ti_notice timg_B /\
  TC.notice_m timg_B TF (sstate_w Bw st) (sstate_ntc Bw st why) = Some (Bw', tt).
Proof.
  intros TF Bw st why Bw' Hm Hne. rewrite sstate_model in Hm.
  rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hm. unfold TSS.call_notify in Hm.
  destruct (Z.eqb_spec (TW.S_notify (sstate_w Bw st)) (TI.ti_notice timg_B)) as [E|E]; [|discriminate Hm].
  split; [exact E | exact Hm].
Qed.

(* sstate_w at the numeral offset of g_s.state (s + 112). *)
Lemma ssn_w_eq : forall Bw st, sstate_w Bw st = TW.upd Bw (TW.OFF_g_s + 112) (TW.put 4 st).
Proof. intros Bw st. reflexivity. Qed.

Lemma ssn_len : forall Bw st, length Bw = Z.to_nat TW.W_LEN -> length (sstate_w Bw st) = Z.to_nat TW.W_LEN.
Proof. intros Bw st L. rewrite ssn_w_eq. wlen. Qed.

(* g_s.notify is not the field the call stores. *)
Lemma ssn_notify : forall Bw st, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_notify (sstate_w Bw st) = TW.u_at Bw (TW.OFF_g_s + 96) 8.
Proof.
  intros Bw st L. rewrite ssn_w_eq. unfold TW.S_notify, TW.A_S_notify.
  rewrite rd_upd_W by wside. reflexivity.
Qed.

(* g_fail_next is not the stored field either, nor one of notice's (an N_STATE notice writes GOT only). *)
Lemma ssn_gfn : forall Bw st, length Bw = Z.to_nat TW.W_LEN -> TW.g_fail_next (sstate_w Bw st) = TW.g_fail_next Bw.
Proof.
  intros Bw st L. rewrite ssn_w_eq. unfold TW.g_fail_next.
  rewrite rd_upd_W by wside. reflexivity.
Qed.

Lemma ssn_gfn' : forall (TF : option TI.tframe) Bw st why Bw', length Bw = Z.to_nat TW.W_LEN ->
  TC.notice_m timg_B TF (sstate_w Bw st) (sstate_ntc Bw st why) = Some (Bw', tt) ->
  TW.g_fail_next Bw' = TW.g_fail_next Bw.
Proof.
  intros TF Bw st why Bw' L H.
  rewrite (notice_state_acked_fail_next timg_B TF (sstate_w Bw st) (sstate_ntc Bw st why) Bw' (or_introl eq_refl)
    (ssn_len Bw st L) H).
  exact (ssn_gfn Bw st L).
Qed.

(* The bytes of sstate_wr are bytes of G (g_s's state field, and notice's stores: TransportGNoticeB.v notice_wr_G). *)
Lemma ssn_wr_G : forall Bw st why a, sstate_wr Bw st why a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw st why a (_ & [H | H]).
  - unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
    split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s)|].
    unfold in_zr, twb_fld, TW.A_S_state, TW.OFF_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
  - exact (TGNB.notice_wr_G _ _ a H).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition SSN_SH : Z := 2148220628.
Lemma SSN_SH_eq : SSN_SH = SHADOW_OFF + (SSTATE_S + 96) / 8.
Proof. reflexivity. Qed.
Definition SSN_R_sh : YP09.region := YP09.mkRegion (Some 24%nat) 4 13 4 13 [].
Definition SSN_R_p : YP09.region := YP09.mkRegion (Some 25%nat) 32 48 32 48 [].
Definition SSN_R_slot : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition SSN_R_gs : YP09.region :=
  YP09.mkRegion None (SSTATE_S + 96) (SSTATE_S + 116) (SSTATE_S + 112) (SSTATE_S + 116)
    [YP09.mkChunk (SSTATE_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (SSTATE_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition SSN_R_shg : YP09.region :=
  YP09.mkRegion None SSN_SH (SSN_SH + 3) 0 0
    [YP09.mkChunk SSN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SSN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SSN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition SSN_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (25%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition SSN_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit SSTATE_S)) (Z_to_bv 5 26) (SLit SHADOW_OFF))
    (Z_to_bv 5 27) (SLit (SSN_SH + 2)).
Definition ss_ssn : sstate :=
  mkSS SSTB_NTC SSN_REGS [SSN_R_sh; SSN_R_p; SSN_R_slot; SSN_R_gs; SSN_R_shg] None SSN_FACTS.
Definition SSN_Bx : sv := SLit 0.
Definition SSN_B0 : Z * Z := (0, 0).
(* run 3, from +0x1e8: the notice's shadow bytes (written) and the frame word at s1 + 24 (read: F, which s9 holds). *)
Definition SSN_R_sh3 : YP09.region := YP09.mkRegion (Some 24%nat) 4 13 4 13 [].
Definition SSN_R_slot3 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SOff 25 0))].
Definition ss_ssn3 : sstate := mkSS (SSTB_NTC + 0x94) sr_atoms [SSN_R_sh3; SSN_R_slot3] None SSN_FACTS.

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma ssn_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
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
Lemma ssn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  exact (TGNB.chunks_zero_aview E H m (base_val E bopt) cs off Hcs Hin).
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma ssn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ssn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Section ssn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* Kit gap: trans_src_ok of a range inside a frame of the state whose bytes are readable, the fake-frame case of
   DgnTransportBCg.v trans_src_ok. DgnTransportBCg.v trans_src_ok_G_range gives its G case (its proof is this one at
   the G disjunct); no lemma of DgnTransportBCg.v, DgnTransportBCgX.v or TransportGNoticeB.v gives the fake-frame
   case. This is the only place this file builds trans_src_ok. *)
Lemma ssn_src_ok_fake : forall lyc Sc (W : world segs) memc q n,
  decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> trans_src_ok B lyc Sc W memc q n.
Proof. intros lyc Sc W memc q n Hf Hrd. right. split; [|exact Hrd]. left. exact Hf. Qed.

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of the world. *)
Definition ssn_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 104) 8)].
Definition ssn_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (ssn_vals Bw)).

Lemma ssn_entry0 : forall ly S (W : world segs) regs mem md Bw F spv,
  trans_sstate_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 25 = w64 F ->
  2 ^ 46 <= spv <= 2 ^ 47 - 64 -> spv mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= spv -> in_app F 256 ->
  (F + 256 <= SSTATE_S \/ SSTATE_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, spv + 24 <= a < spv + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ssn_E regs Bw)
    (mkSS SSTB_NTC sr_atoms [SSN_R_sh; SSN_R_p; SSN_R_slot; SSN_R_gs; SSN_R_shg] None SSN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SSTB_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw F spv HSC HAR Htw R9 R24 R25 Hsp Hsp32 HF0 HF64 HFsp HFapp HFG Hpf Hpsh Hpsl.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := ssn_E regs Bw).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, ssn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = spv)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U25 : bv_unsigned (ew E 25) = F)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (ssn_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ssn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth ssn_vals] in E32, E33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (SSN_SH + Z.of_nat j) 1 0).
  { intros j Hj. apply YE2y.val_mem1_of_aview.
    replace (SSN_SH + Z.of_nat j) with (FCells.shadow_addr (SSTATE_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md SSTATE_S (SSTATE_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold SSTATE_S, TB_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, SSN_SH, SSTATE_S, TB_g_s.
      replace (6157888 + 96 + 8 * Z.of_nat j) with ((769748 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SSN_R_sh SSN_R_p SSN_R_slot SSN_R_gs
        SSN_R_shg base_val]; rewrite ?U9, ?U24, ?U25.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
    + split; [unfold SSTATE_S, TB_g_s; lia|]. split; [unfold SSTATE_S, TB_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
        unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
        split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SSTATE_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (SSTATE_S + 96) 8 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold SSTATE_S, TB_g_s; lia |].
           replace (0 + (SSTATE_S + 96)) with (TB_g_s + 96) by (unfold SSTATE_S; lia).
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 96 8 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (SSTATE_S + 104) 8 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold SSTATE_S, TB_g_s; lia |].
           replace (0 + (SSTATE_S + 104)) with (TB_g_s + 104) by (unfold SSTATE_S; lia).
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 104 8 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s; lia|].
      split; [unfold SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 SSN_SH 1 (SLit 0) 0); [reflexivity | lia | unfold SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s; lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (SSN_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (SSN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, SSN_R_sh, SSN_R_p, SSN_R_slot, SSN_R_gs, SSN_R_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SSN_SH, SHADOW_OFF, SSTATE_S, TB_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold SSN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U24, U25.
    change (2 ^ 3) with 8. change (2 ^ 5) with 32. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma ssn_entry : forall ly S (W : world segs) regs mem md Bw F spv,
  trans_sstate_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 25 = w64 F ->
  YK11.getr regs 20 = w64 SSTATE_S -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 27 = w64 (SHADOW_OFF + (SSTATE_S + 112) / 8) ->
  2 ^ 46 <= spv <= 2 ^ 47 - 64 -> spv mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= spv -> in_app F 256 ->
  (F + 256 <= SSTATE_S \/ SSTATE_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, spv + 24 <= a < spv + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ssn_E regs Bw) ss_ssn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SSTB_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw F spv HSC HAR Htw R9 R24 R25 R20 R26 R27 Hsp Hsp32 HF0 HF64 HFsp HFapp HFG Hpf Hpsh
    Hpsl.
  rewrite restrict_mkst_fx.
  pose proof (ssn_entry0 ly S W regs mem md Bw F spv HSC HAR Htw R9 R24 R25 Hsp Hsp32 HF0 HF64 HFsp HFapp HFG Hpf Hpsh
    Hpsl) as H0.
  assert (R27' : YK11.getr regs (Z_to_bv 5 27) = Z_to_bv 64 (SSN_SH + 2)) by exact R27.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) SSTATE_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) SHADOW_OFF H1 R26 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) (SSN_SH + 2) H2 R27' eq_refl) as H3.
  exact H3.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ssn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ssn_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with the five regions of ss_ssn (U24 / U25 / U9: the bases' values; EF:
   the frame's address F = frame_addr lyc SSTATE_CID pos). *)
Ltac ssn_awr U9 U24 U25 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply TransportGFrame.awr_ok_x_cons_own with (cid := SSTATE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes SSTATE_CID / 8) with 32;
    lia |];
  eapply TransportGFrame.awr_ok_x_cons_own with (cid := SSTATE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes SSTATE_CID) with 256; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    unfold inG; apply Exists_exists; exists (TB_g_s, TW.SZ_g_s);
    split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, g_s.state, the frame word at sp1 + 24, and the stack window of __asan_memset below sp1. *)
Definition ssn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (SSTATE_S + 112 <= x < SSTATE_S + 116) \/ (sp1 + 24 <= x < sp1 + 32) \/ (sp1 - ESTACK <= x < sp1).

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma ssn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
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

(* A region cell of n bytes holding v, read byte by byte through the view. *)
Lemma ssn_aview_of_val : forall H (m : word -> option byte) a (n : nat) v j,
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v j HV Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The 72 bytes of the notice at p = F + 32: the stores of 2, st, the old state and why (4 bytes each), and the
   memset's 56 zeros, read as WalkNotify.v ntc_state_bytes. *)
Lemma ssn_nb : forall (H : word -> bool) (m : word -> option byte) F st old why,
  val_mem segs (mrestrict H m) (F + 32) 4 2 ->
  val_mem segs (mrestrict H m) (F + 36) 4 st ->
  val_mem segs (mrestrict H m) (F + 40) 4 old ->
  val_mem segs (mrestrict H m) (F + 44) 4 why ->
  (forall a, F + 48 <= a < F + 104 -> aview segs H m a = Some 0) ->
  garr8 segs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_state_bytes st old why)).
Proof.
  intros H m F st old why V0 V4 V8 V12 Z0.
  unfold WN.ntc_state_bytes.
  rewrite !map_app. apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 2 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 4) with (F + 36) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 st V4) |].
  rewrite length_map, TWL.length_put. replace (F + 36 + Z.of_nat 4) with (F + 40) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 old V8) |].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 4) with (F + 44) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put segs _ _ 4 why V12) |].
  rewrite length_map, TWL.length_put. replace (F + 44 + Z.of_nat 4) with (F + 48) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma ssn_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw st why F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (SSTATE_CID, pos) (frames S2) ->
  F = frame_addr lyc SSTATE_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  F + 256 <= spZ regsC - NOTICE_STK -> 0 <= st < 2 ^ 31 -> 0 <= why < 2 ^ 31 ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32) (map DSpec.bz (WN.ntc_state_bytes st (TW.S_state Bw) why)) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 32) (sstate_ntc Bw st why).
Proof.
  intros lyc S2 W memN mdN regsC Bw st why F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Hst Hwhy ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN SSTATE_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes SSTATE_CID) with 256 in HFb.
  change (fs_frame_bytes SSTATE_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (old := TW.S_state Bw) in *.
  assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { apply ssn_src_ok_fake.
    - exists SSTATE_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes SSTATE_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (TGNA.frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (TGNA.frame_hull_vis _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes st old why).
  split; [exact HNB|].
  unfold sstate_ntc. fold old.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 st ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
    by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; lia |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
  split; [WN.ntc_field; apply WN.swrap32_mod; lia |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B lyc S2 W memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT) are apart from the notice's own bytes (a frame is not image),
   from its empty body, and from TF (sstate_apart: they are bytes of sstate_wr). *)
Lemma ssn_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw st why
    F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (SSTATE_CID, pos) (frames S2) ->
  F = frame_addr lyc SSTATE_CID pos ->
  sstate_apart TF Bw st why -> TW.S_state Bw <> st ->
  notice_apart W memN (F + 32) (sstate_ntc Bw st why) TF (sstate_w Bw st).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw st why F pos LAWS HAR Hin EF Hap Hst x Hx.
  assert (Hw : sstate_wr Bw st why x) by (split; [exact Hst | right; exact Hx]).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 SSTATE_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes SSTATE_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (ssn_wr_G Bw st why x Hw)).
  - intros NB _ _. split.
    + unfold sstate_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* The symbolic state at +0x1e8 (after notice returns): the registers as atoms, the notice's shadow bytes 4 .. 12 and
   the frame word at sp1 + 24. *)
Lemma ssn_entry3 : forall (W : world segs) regs mem F spv,
  YK11.getr regs 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 9 = w64 spv -> YK11.getr regs 25 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> 2 ^ 46 <= spv <= 2 ^ 47 - 64 -> spv mod 32 = 0 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  val_mem segs (mrestrict (w_H W) mem) (spv + 24) 8 F ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_ssn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SSTB_NTC + 0x94))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R24 R9 R25 HF0 HF64 HFc Hsp Hsp32 Hpsh VSL.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
  assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  assert (U9 : bv_unsigned (ew E 9) = spv)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = w64 F) by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = F) by (rewrite E25; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_ssn3.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SSN_R_sh3 SSN_R_slot3 base_val];
      rewrite ?U24, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ spv 24 8 (SOff 25 0) F);
        [cbn [sv_denot]; rewrite E25, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact VSL.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, SSN_R_sh3, SSN_R_slot3. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U24, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; first [exact I | lia].
  - unfold SSN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U9, U25. change (2 ^ 3) with 8.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma sstb_ntc_holds : @sstb_ntc_stmt fx rc B MT.
Proof.
unfold sstb_ntc_stmt. intros REL. unfold sstb_ntc_at.
intros LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Htw0 & Hgf & Hm & Hst & Hwhy &
  HTF & Hrom & Hapart & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hbl & HGK & Htw1 & Hne).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R10 & R24 & R25) & R18 & R19 & R20 & R21 & R22 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SSTB_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HPW : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a).
{ pose proof HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
pose proof sstb_stk_bounds as (HSS & HSF & HSA & HNS & EST & HSSV).
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold SSTATE_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (r := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
destruct Hsp1 as (Hsp1r & Hs32).
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (SSTATE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 SSTATE_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh.
change (fs_frame_bytes SSTATE_CID) with 256 in HFb. change (fs_frame_bytes SSTATE_CID / 8) with 32 in HFsh.
destruct (FFL lyc S2 W mem2 md2 SSTATE_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr lyc SSTATE_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 256 <= SSTATE_S \/ SSTATE_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) SSTATE_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (SSTATE_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ SSTATE_S <= x < SSTATE_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F SSTATE_S) as [h3|h3]; [exists SSTATE_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 SSTATE_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes SSTATE_CID) with 256; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SSTATE_S in *; cbn [fst snd]; lia]. }
(* the model's facts on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (ssn_model TF Bw st why Bw' Hm Hne) as (HNT & HNM).
(* +0x154 .. +0x188: the frame word at s1 + 24, s7 = p, shadow bytes 4 .. 12 := 0, the memset's arguments,
   `jal __asan_memset` *)
pose proof (ssn_entry lyc S2 W regs2 mem2 md2 Bw F sp1 HSC HAR2 Htw1 R9 R24 R25 R20 R26 R27 ltac:(lia) Hs32 HF0 HF64
  ltac:(lia) HFapp HFG
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  ltac:(intros a Ha; apply HPW; lia)) as HS.
set (E0 := ssn_E regs2 Bw) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ssn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ssn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = SHADOW_OFF + F / 8)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E0 25) = F)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs SSN_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ1 SHOK SSN_B0.
{ ssn_awr U9 U24 U25 EF. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ssn_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ssn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  ssn_win Hiw Hx ltac:(rewrite ?U24, ?U25, ?U9 in Hx; unfold ssn_Z, SSTATE_S, TB_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U24.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ssn_chunk0 E0 (w_H W) (ms_mem ms) (Some 24%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms) md1 SSTATE_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite <- EF, ESH in HFsh1. change (fs_frame_bytes SSTATE_CID / 8) with 32 in HFsh1.
pmkst HS.
ssn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10 ltac:(cbn [sv_denot]; rewrite U25; reflexivity).
ssn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ssn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
ssn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ssn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 25020)) Q1 ltac:(apply codeptr_val; exact HEI).
ssn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ssn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x18c: __asan_memset (p + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (HMS fx) TG.G_HARNESS_B W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0
    md0 ((SSTATE_CID, pos) :: own) lyc S2 md1 (k + 0) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 25020))
    HGX G_HARNESS_B_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hs32, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists SSTATE_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes SSTATE_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (TGNA.frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TGNA.frame_hull_vis _ F 256 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8). apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ ssn_Z F sp1 a ->
  aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 24%nat (SHADOW_OFF + F / 8)); [exact U24 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 25%nat F); [exact U25 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply ssn_rk_none; [| exact HgrM]. intros a Ha. unfold SSTATE_S, TB_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold SSTATE_S, TB_g_s, TW.SZ_g_s in *; lia | lia].
  - apply ssn_rk_none; [| exact HgrM]. intros a Ha. unfold SSN_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U9b : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; exact U9).
assert (U24b : bv_unsigned (ew E1 24) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U24).
assert (U25b : bv_unsigned (ew E1 25) = F) by (rewrite E1lo by lia; exact U25).
assert (SHOK1 : sh_ok segs SSN_Bx (@nil shent) E1 (mrestrict (w_H W) memM)) by constructor.
assert (ZMM : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W) memM a = Some 0).
{ intros a Ha. replace a with ((F + 48) + (a - (F + 48))) by lia. rewrite (HsetM (a - (F + 48)) ltac:(lia)). reflexivity. }
clear dependent ms.
(* +0x190 .. +0x1e0: the notice's first 16 bytes, the checked store of st at s + 112, the checked loads at s + 96 and
   s + 104, up to `jalr a2` *)
paj_run_tok RUN HS HJ2 SHOK1 SSN_B0.
{ ssn_awr U9b U24b U25b EF. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ ssn_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ssn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  ssn_win Hiw Hx ltac:(rewrite ?U24b, ?U25b, ?U9b in Hx; unfold ssn_Z, SSTATE_S, TB_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia]). }
assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (SSTATE_S + 112 <= x < SSTATE_S + 116) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (sp1 + 24 <= x < sp1 + 32)) HFr); [| lia |].
  - intros b wlo whi x Hiw Hx. cbv beta.
    ssn_win Hiw Hx ltac:(rewrite ?U24b, ?U25b, ?U9b in Hx; unfold SSTATE_S, TB_g_s;
      first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]).
  - cbv beta. unfold SSTATE_S, TB_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | [Hx | Hx]]]; [lia | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia | lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ ssn_Z F sp1 a ->
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
{ intros i Hi. rewrite <- U24b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ssn_chunk0 E1 (w_H W) (ms_mem ms) (Some 24%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
set (old := TW.S_state Bw) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
assert (D19 : sv_denot E1 (SOff 19 0) = Z_to_bv 64 st).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 19%nat 19%bv eq_refl), R19. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D21 : sv_denot E1 (SOff 21 0) = Z_to_bv 64 old).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D18 : sv_denot E1 (SOff 18 0) = Z_to_bv 64 why).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 18%nat 18%bv eq_refl), R18. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 F).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 10%nat 10%bv eq_refl), R10. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 32 4 (SLit 2) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 36 4 (SOff 19 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP4.
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 40 4 (SOff 21 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 44 4 (SOff 18 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP12.
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 10 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VSL.
pose proof (ssn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158000 4 (SOff 19 0) RS3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP4, VP8, VP12, VSL, VG. rewrite U25b in VP0, VP4, VP8, VP12. rewrite U9b in VSL.
rewrite D19 in VP4, VG. rewrite D21 in VP8. rewrite D18 in VP12. rewrite D10 in VSL.
change (bv_unsigned (sv_denot E1 (SLit 2)) mod 2 ^ (8 * Z.of_N 4)) with 2 in VP0.
change (N.to_nat 4) with 4%nat in VP0.
apply (ssn_vm_w _ _ 4 st ltac:(lia)) in VP4. apply (ssn_vm_w _ _ 4 old ltac:(lia)) in VP8.
apply (ssn_vm_w _ _ 4 why ltac:(lia)) in VP12. apply (ssn_vm_w _ _ 4 st ltac:(lia)) in VG.
apply (ssn_vm_w _ _ 8 F ltac:(lia)) in VSL.
change (N.to_nat 4) with 4%nat in VP4, VP8, VP12, VG. change (N.to_nat 8) with 8%nat in VSL.
pose proof (ssn_nb (w_H W) (ms_mem ms) F st old why VP0 VP4 VP8 VP12 ZMN) as HNB.
(* what the call kept, from its entry to the call of notice *)
destruct (dkg_nf_sep segs B LAWS transportb_segs_low lyc Sc S2 W mem2 md2 SSTATE_CID pos F FL HAR2 Hfrs Hbl EF eq_refl
  FFL) as (N1 & N2 & N3 & N4).
assert (NZG : forall x, inG TG.G_HARNESS_B x -> ~ (SSTATE_S + 112 <= x < SSTATE_S + 116) -> ~ ssn_Z F sp1 x).
{ intros x Hx Hn Hz. pose proof (inG_low segs B transportb_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes SSTATE_CID) with 256; lia | exact (trans_g_img x Hx)].
  - exact (Hn Hz).
  - lia.
  - lia. }
assert (HSZ : forall a, ssn_Z F sp1 a ->
  (spZ regs - SSTATE_STK <= a < spZ regs) \/ dkg_nf SSTATE_CID F FL a \/ inG TG.G_HARNESS_B a).
{ intros a [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - right; left; right; left. change (fs_frame_bytes SSTATE_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes SSTATE_CID) with 256. lia.
  - right; right. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
    split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SSTATE_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
  - left; lia.
  - left; lia. }
pose proof (TransportGFrame.dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc lyc S2 W memc mdc W
  mem2 md2 mem2 (ms_mem ms) (spZ regs - SSTATE_STK) (spZ regs) SSTATE_CID pos F FL (sstate_wr Bw st why)
  (ssn_Z F sp1) HGX HARc HAR2 Hfrs ltac:(intros bm Hb; rewrite Hbl; exact Hb) eq_refl EF eq_refl FFL ltac:(lia)
  ltac:(lia) HSZ HK KAN GAN) as KCN.
assert (GKN : gx_kept_ex segs TG.G_HARNESS_B (sstate_wr Bw st why) W memc W (ms_mem ms)).
{ apply (gx_kept_ex_trans segs TG.G_HARNESS_B (sstate_wr Bw st why) W memc W mem2 W (ms_mem ms) HGK).
  intros a Ha Hn. apply KAN; [pose proof (inG_low segs B transportb_segs_low _ a HGX Ha); unfold kLowMemEnd in *; lia|].
  intros Hz. apply Hn. pose proof (inG_low segs B transportb_segs_low _ a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - exfalso. unfold SHADOW_OFF in Hz. lia.
  - exfalso. apply (N2 a); [left; change (fs_frame_bytes SSTATE_CID) with 256; lia | exact (trans_g_img a Ha)].
  - split; [exact Hne | left]. unfold twb_fld, TW.A_S_state, SSTATE_S in *. lia.
  - exfalso. lia.
  - exfalso. lia. }
(* the registers at `jalr a2` *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_B)).
{ rewrite E1lo by lia. unfold E0, ssn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (ssn_vals Bw) 0) as X. cbn [Nat.add nth ssn_vals] in X. rewrite X.
  rewrite <- (ssn_notify Bw st HLB), HNT. reflexivity. }
ssn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_B)) T12
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U25b; reflexivity).
ssn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ssn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
ssn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
ssn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ssn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ssn_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ssn_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) T25
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* +0x1e4: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_B < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_B mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W E1 _ _ _ _ 0x600e7 (1%bv : bv 5)
  (12%bv : bv 5) (TI.ti_notice timg_B) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_B) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + 25108 = 0x874b4) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + 25108))
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
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (PTW : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (sstate_w Bw st)).
{ rewrite ssn_w_eq.
  apply (tw_write TMAP_B (aview segs (w_H W) mem2) _ Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 st TMAP_B_ok Htw1
    TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. replace (TB_g_s + 112 + Z.of_nat j) with (0 + 6158000 + Z.of_nat j) by (unfold TB_g_s; lia).
    exact (ssn_aview_of_val (w_H W) (ms_mem ms) _ 4 st j VG Hj).
  - intros x Hx Hn. destruct Hx as (o & b & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS_B x).
    { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_B_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transportb_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact HxG | unfold SSTATE_S, TB_g_s in *; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((SSTATE_CID, pos) :: own) lyc S2 W (ms_mem ms) mdC (k + 0) regsC
    (F + 32) (sstate_ntc Bw st why) TF (sstate_w Bw st) Bw'
    ltac:(apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite Hs32, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ssn_ntc_at lyc S2 W (ms_mem ms) md3 regsC Bw st why F pos LAWS HARN Hin EF HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) Hst Hwhy ZSN HNB)
    (TGNB.trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W (ms_mem ms) md3 (sstate_wr Bw st why)
       regs regsC SSTATE_STK NOTICE_STK TF HARc HARN ltac:(intros bm Hb; rewrite Hbl; exact Hb)
       ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) (fun _ _ => eq_refl) eq_refl eq_refl HSTKLT KCN GKN
       ltac:(intros fr Efr a Ha Hw; exact (Hapart a Hw fr Efr Ha))
       ltac:(intros a Ha Hw; pose proof (inG_low segs B transportb_segs_low _ a HGX (ssn_wr_G Bw st why a Hw)); lia)
       ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_B_LO in Gh; lia)
    PTW HNM
    (ssn_apart lyc S2 W mem2 md2 W (ms_mem ms) TF Bw st why F pos LAWS HAR2 Hin EF Hapart Hne)
    ltac:(intros HD; exfalso; unfold sstate_ntc in HD; cbn [TI.n_kind] in HD; cbv in HD; discriminate HD)
    ltac:(unfold SSTATE_EV in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 SSTATE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hin3 : In (SSTATE_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 SSTATE_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes SSTATE_CID / 8) with 32 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (SSTATE_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
  YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
  by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
assert (R3_24 : YK11.getr regs3 (Z_to_bv 5 24) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (CH 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T24 R24)).
assert (R3_9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1)
  by exact (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)).
assert (R3_25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 F)
  by exact (eq_trans (CH 25 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T25 R25)).
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - SSTATE_STK) (spZ regs)
  (sstate_wr Bw st why)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc lyc S2 W memc W (ms_mem ms) W3 mem3
    (spZ regs - SSTATE_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (sstate_wr Bw st why)
    (notice_wr (sstate_w Bw st) (sstate_ntc Bw st why)) (dkg_nf SSTATE_CID F FL)).
  - lia.
  - lia.
  - intros c p. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. split; [exact Hne | right; exact Ha]. }
(* the frame word at sp1 + 24, kept by notice (it lies above notice's window) *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
rewrite USPC in K31.
assert (VSL3 : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 24) 8 F).
{ apply (val_mem_kept segs (w_H W) (w_H W3) (ms_mem ms) mem3 (sp1 + 24) 8 F); [|exact VSL].
  intros k0 Hk0. apply K31; lia. }
(* +0x1e8 .. +0x210: shadow bytes 4 .. 12 := 0xf8, a0 = F from sp1 + 24, to the release cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + 25108)) with (Z_to_bv 64 (BASE + (SSTB_NTC + 0x94))).
pose proof (ssn_entry3 W3 regs3 mem3 F sp1 R3_24 R3_9 R3_25 HF0 HF64 ltac:(lia) ltac:(lia) Hs32
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia)))) VSL3) as HS3.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U24c : bv_unsigned (ew E3 24) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), R3_24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs SSN_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SSN_B0 SSTB_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply TransportGFrame.awr_ok_x_cons_own with (cid := SSTATE_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes SSTATE_CID / 8) with 32. lia.
  - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. ssn_win Hiw Hx ltac:(rewrite ?U24c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms4) (spZ regs - SSTATE_STK) (spZ regs)
  (sstate_wr Bw st why)).
{ apply (TransportGFrame.dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly3 S3 W memc mdc W3
    mem3 md4 mem3 (ms_mem ms4) (spZ regs - SSTATE_STK) (spZ regs) SSTATE_CID pos F FL (sstate_wr Bw st why)
    (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL
    ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. right. left. change (fs_frame_bytes SSTATE_CID / 8) with 32. cbv beta in Ha. lia. }
pmkst HS3.
(* the registers the release reads *)
ssn_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) F24
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 25) (YK11.getr regs3 (Z_to_bv 5 25)) F25
  ltac:(cbn [sv_denot]; rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ssn_reg HS3 (Z_to_bv 5 10) (w64 F) F10
  ltac:(cbn [sv_denot]; rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), R3_25; unfold w64;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words below the entry sp and the frame's last word *)
assert (KSTK : forall a, spZ regs - 104 <= a < spZ regs ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite K31 by lia.
  apply KAN; [lia|]. unfold ssn_Z, SSTATE_S, TB_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 248 + i) = aview segs (w_H W) mem2 (F + 248 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 SSTATE_CID pos (F + 248 + i) Hin).
  - apply KAN; [lia|]. unfold ssn_Z, SSTATE_S, TB_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | [Hz | Hz]]]]; [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg;
      lia | lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes SSTATE_CID) with 256. lia.
  - intros Hw. apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes SSTATE_CID) with 256; lia|].
    exact (trans_g_img _ (TGNB.notice_wr_G _ _ _ Hw)). }
assert (HSo : forall o, In o SSTB_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold SSTB_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem ms4) md5 0 (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
    split; [unfold SSTATE_EV, NOTICE_EV; lia|].
    split; [exact Hfrs3|].
    split; [rewrite <- Hbl; exact Hperm3|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold SSTB_FBYTES. change (flag_addr lyc SSTATE_CID pos) with FL. rewrite <- HFLw.
      replace (F + 256 - 8) with (F + 248) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite (ssn_gfn' TF Bw st why Bw' HLB HNM). exact Hgf.
- assert (CK : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
  split; [exact (eq_trans F2 (eq_trans (CK 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2))|].
  split; [exact (eq_trans F3 (eq_trans (CK 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 (eq_sym Hgp))))|].
  split; [exact (eq_trans F4 (eq_trans (CK 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 (eq_sym Htp))))|].
  split; [exact (eq_trans F8 (eq_trans (CK 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8)))|].
  split; [exact (eq_trans F9 (eq_trans (CK 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)))|].
  split; [exact F10|].
  split; [exact (eq_trans F24 (eq_trans (CK 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T24 R24)))|].
  exact (eq_trans F25 (eq_trans (CK 25 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T25 R25))).
Qed.

End ssn.

(* The notice piece of the image-B walk of set_state (set_state_segs.v sstb_ntc_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem sstb_ntc : forall fx rc B MT, @sstb_ntc_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@sstb_ntc_holds fx rc B MT). Qed.
