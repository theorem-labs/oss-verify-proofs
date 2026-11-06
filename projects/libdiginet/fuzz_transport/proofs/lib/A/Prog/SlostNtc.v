(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths and module names changed; 799 of its 889 lines of code are new or changed and 988 lines of the source are left out. *)
(* SlostNtc: the notice piece of session_lost's image-A G-form walk, slost_ntc : slost_ntc_stmt (SlostCut.v), code
   0x89084 .. 0x89134. Run 1 (PaRun token engine) unpoisons the notice's shadow bytes 4 .. 12 and sets up
   __asan_memset (p + 16, 0, 56), taken through TransportGCg.v gx_intrin_at; run 2 stores the notice's first 16 bytes,
   the checked 0 at s + 112 (slost_w2) and loads g_s.notify and g_s.notify_ctx; `jalr a2` at 0x8910c calls notice
   through the premise transport_notice_cg (the same G journal; the call's kept facts fold with
   dk_kept_trans_nf_g); run 3 re-poisons shadow bytes 4 .. 12 and the proof ends at the release cut slost_rel_at. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
session_lost_cg SlostCut TransportGNotice SlostNtcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.

(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition SN_SH : Z := 2148220740.
Lemma SN_SH_eq : SN_SH = SHADOW_OFF + (SLOST_S + 96) / 8.
Proof. reflexivity. Qed.
Definition SN_R_sh : YP09.region := YP09.mkRegion (Some 23%nat) 4 13 4 13 [].
Definition SN_R_p : YP09.region := YP09.mkRegion (Some 24%nat) 32 48 32 48 [].
Definition SN_R_gs : YP09.region :=
  YP09.mkRegion None (SLOST_S + 96) (SLOST_S + 116) (SLOST_S + 112) (SLOST_S + 116)
    [YP09.mkChunk (SLOST_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (SLOST_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition SN_R_shg : YP09.region :=
  YP09.mkRegion None SN_SH (SN_SH + 3) 0 0
    [YP09.mkChunk SN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (SN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (SN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition SN_FACTS : facts :=
  mkFacts [(23%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (24%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition SN_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SLit SLOST_S)) (Z_to_bv 5 25) (SLit SHADOW_OFF))
    (Z_to_bv 5 26) (SLit (SN_SH + 2)).
Definition ss_sn : sstate := mkSS SLOST_NTC SN_REGS [SN_R_sh; SN_R_p; SN_R_gs; SN_R_shg] None SN_FACTS.
Definition SN_Bx : sv := SLit 0.
Definition SN_B0 : Z * Z := (0, 0).
Definition ss_sn3 : sstate := mkSS (SLOST_NTC + 0x8c) sr_atoms [SN_R_sh] None
  (mkFacts [(23%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma sn_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
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
Lemma sn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  exact (chunks_zero_aview E H m (base_val E bopt) cs off Hcs Hin).
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma sn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
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
Ltac sn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Section sn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of the world. *)
Definition sn_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 104) 8)].
Definition sn_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (sn_vals Bw)).

Lemma sn_entry0 : forall ly S (W : world segs) regs mem md Bw F,
  trans_slost_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) (slost_w1 Bw) ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= SLOST_S \/ SLOST_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (sn_E regs Bw) (mkSS SLOST_NTC sr_atoms [SN_R_sh; SN_R_p; SN_R_gs; SN_R_shg] None SN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLOST_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw F HSC HAR Htw R23 R24 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := sn_E regs Bw).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, sn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = F)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (sn_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, sn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth sn_vals] in E32, E33.
  pose proof (TWL.u_at_range (slost_w1 Bw) (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range (slost_w1 Bw) (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (SN_SH + Z.of_nat j) 1 0).
  { intros j Hj. apply AE2y.val_mem1_of_aview.
    replace (SN_SH + Z.of_nat j) with (FCells.shadow_addr (SLOST_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md SLOST_S (SLOST_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold SLOST_S, TA_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, SN_SH, SLOST_S, TA_g_s.
      replace (6158784 + 96 + 8 * Z.of_nat j) with ((769860 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SN_R_sh SN_R_p SN_R_gs SN_R_shg
        base_val]; rewrite ?U23, ?U24.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). replace (SHADOW_OFF + F / 8 + o) with (SHADOW_OFF + F / 8 + o) by lia.
      apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold SLOST_S, TA_g_s; lia|]. split; [unfold SLOST_S, TA_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, SLOST_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (SLOST_S + 96) 8 (SOff 32 0) (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold SLOST_S, TA_g_s; lia |].
           replace (0 + (SLOST_S + 96)) with (TA_g_s + 96) by (unfold SLOST_S; lia).
           exact (tw_read_val segs _ TMAP_A (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (SLOST_S + 104) 8 (SOff 33 0) (TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold SLOST_S, TA_g_s; lia |].
           replace (0 + (SLOST_S + 104)) with (TA_g_s + 104) by (unfold SLOST_S; lia).
           exact (tw_read_val segs _ TMAP_A (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold SN_SH, SHADOW_OFF, SLOST_S, TA_g_s; lia|]. split; [unfold SN_SH, SHADOW_OFF, SLOST_S, TA_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 SN_SH 1 (SLit 0) 0); [reflexivity | lia | unfold SN_SH, SHADOW_OFF, SLOST_S, TA_g_s; lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (SN_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold SN_SH, SHADOW_OFF, SLOST_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (SN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold SN_SH, SHADOW_OFF, SLOST_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, SN_R_sh, SN_R_p, SN_R_gs, SN_R_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SN_SH, SHADOW_OFF, SLOST_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold SN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U24.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma sn_entry : forall ly S (W : world segs) regs mem md Bw F,
  trans_slost_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) (slost_w1 Bw) ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F ->
  YK11.getr regs 19 = w64 SLOST_S -> YK11.getr regs 25 = w64 SHADOW_OFF -> YK11.getr regs 26 = w64 (SN_SH + 2) ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= SLOST_S \/ SLOST_S + TW.SZ_g_s <= F) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (sn_E regs Bw) ss_sn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLOST_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw F HSC HAR Htw R23 R24 R19 R25 R26 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  rewrite restrict_mkst_fx.
  pose proof (sn_entry0 ly S W regs mem md Bw F HSC HAR Htw R23 R24 HF0 HF64 HFc HFapp HFG Hpf Hpsh) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) SLOST_S H0 R19 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) SHADOW_OFF H1 R25 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (SN_SH + 2) H2 R26 eq_refl) as H3.
  exact H3.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
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

(* The write rights of a run from a state with the four regions of ss_sn (U23 / U24: the bases' values; EF: the
   frame's address F = frame_addr lyc SLOST_CID pos). *)
Ltac sn_awr U23 U24 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := SLOST_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U23 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes SLOST_CID / 8) with 32; lia |];
  eapply awr_ok_x_cons_own with (cid := SLOST_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes SLOST_CID) with 256; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    unfold inG; apply Exists_exists; exists (TA_g_s, TW.SZ_g_s);
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, g_s.state, and the stack window of __asan_memset below sp1. *)
Definition sn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (SLOST_S + 112 <= x < SLOST_S + 116) \/ (sp1 - ESTACK <= x < sp1).

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma sn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
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

(* The 72 bytes of the notice at p = F + 32: the stores of 2 (8 bytes), old and why (4 bytes each), and the memset's
   56 zeros, read as WalkNotify.v ntc_state_bytes. *)
Lemma sn_nb : forall (H : word -> bool) (m : word -> option byte) F old why,
  val_mem segs (mrestrict H m) (F + 32) 8 2 ->
  val_mem segs (mrestrict H m) (F + 40) 4 old ->
  val_mem segs (mrestrict H m) (F + 44) 4 why ->
  (forall a, F + 48 <= a < F + 104 -> aview segs H m a = Some 0) ->
  garr8 segs (mrestrict H m) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 0 old why)).
Proof.
  intros H m F old why V0 V8 V12 Z0.
  unfold WN.ntc_state_bytes.
  change (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56)
    with (TW.put 8 2 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56).
  rewrite !map_app. apply garr8_app. split; [exact (garr8_of_put segs _ _ 8 2 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 8) with (F + 40) by lia.
  apply garr8_app. split; [exact (garr8_of_put segs _ _ 4 old V8) |].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 4) with (F + 44) by lia.
  apply garr8_app. split; [exact (garr8_of_put segs _ _ 4 why V12) |].
  rewrite length_map, TWL.length_put. replace (F + 44 + Z.of_nat 4) with (F + 48) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* The notice at p = F + 32, as notice's statement reads it (check_state_data_cg.v trans_ntc_at). *)
Lemma sn_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw why F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (SLOST_CID, pos) (frames S2) ->
  F = frame_addr lyc SLOST_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  F + 256 <= spZ regsC - NOTICE_STK -> 0 <= why < 2 ^ 31 ->
  (forall i, 4 <= i < 13 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 32) (map DSpec.bz (WN.ntc_state_bytes 0 (TW.S_state (slost_w1 Bw)) why)) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 32) (slost_ntc Bw why).
Proof.
  intros lyc S2 W memN mdN regsC Bw why F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Hwhy ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN SLOST_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes SLOST_CID) with 256 in HFb.
  change (fs_frame_bytes SLOST_CID / 8) with 32 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  set (old := TW.S_state (slost_w1 Bw)) in *.
  assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists SLOST_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes SLOST_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (frame_hull_vis _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes 0 old why).
  split; [exact HNB|].
  unfold slost_ntc. fold old.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
    by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
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
   from its empty body, and from TF (slost_apart: they are bytes of slost_wr). *)
Lemma sn_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw why F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (SLOST_CID, pos) (frames S2) ->
  F = frame_addr lyc SLOST_CID pos ->
  slost_apart TF Bw why -> TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE ->
  notice_apart W memN (F + 32) (slost_ntc Bw why) TF (slost_w2 Bw).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw why F pos LAWS HAR Hin EF Hap Hst x Hx.
  assert (Hw : slost_wr Bw why x) by (right; right; split; [exact Hst | right; exact Hx]).
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 SLOST_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes SLOST_CID) with 256; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x (sn_wr_G Bw why x Hw)).
  - intros NB _ _. split.
    + unfold slost_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* The symbolic state at +0x208 (after notice returns): the registers as atoms, the notice's shadow bytes 4 .. 12. *)
Lemma sn_entry3 : forall (W : world segs) regs mem F,
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_sn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SLOST_NTC + 0x8c))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R23 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [])).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_sn3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks SN_R_sh base_val]. rewrite U23.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma slost_ntc : @slost_ntc_stmt fx rc B MT.
Proof.
unfold slost_ntc_stmt. intros REL. unfold slost_ntc_at.
intros LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Htw0 & Hgf & Hm & Hwhy & HTF & Hrom &
  Hapart & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hbl & HGK & Htw1 & Hst).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R20 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SLOST_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HSS : SLOST_STK = 144 + NOTICE_STK) by reflexivity.
assert (HNS : NOTICE_STK = 48 + 2 * ESTACK) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold SLOST_FRAME.
  pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 128) / 32) in *. set (r := (spZ regs - 128) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (SLOST_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 SLOST_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh.
change (fs_frame_bytes SLOST_CID) with 256 in HFb. change (fs_frame_bytes SLOST_CID / 8) with 32 in HFsh.
destruct (FFL lyc S2 W mem2 md2 SLOST_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr lyc SLOST_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 256 <= SLOST_S \/ SLOST_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) SLOST_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (SLOST_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ SLOST_S <= x < SLOST_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F SLOST_S) as [h3|h3]; [exists SLOST_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 SLOST_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes SLOST_CID) with 256; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, SLOST_S in *; cbn [fst snd]; lia]. }
(* the model's facts on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (sn_model TF Bw why Bw' Hm Hst) as (HNT & HNM).
(* +0x17c .. +0x1b0: s6 = p, shadow bytes 4 .. 12 := 0, the memset's arguments, `jal __asan_memset` *)
pose proof (sn_entry lyc S2 W regs2 mem2 md2 Bw F HSC HAR2 Htw1 R23 R24 R19 R25 R26 HF0 HF64 ltac:(lia) HFapp HFG
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
set (E0 := sn_E regs2 Bw) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, sn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (U23 : bv_unsigned (ew E0 23) = SHADOW_OFF + F / 8)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E0 24) = F)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs SN_Bx (@nil shent) E0 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK SN_B0.
{ sn_awr U23 U24 EF. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ sn_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(rewrite ?U23, ?U24 in Hx; unfold sn_Z, SLOST_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E0 (w_H W) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms) md1 SLOST_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite <- EF, ESH in HFsh1. change (fs_frame_bytes SLOST_CID / 8) with 32 in HFsh1.
pmkst HS.
sn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10 ltac:(cbn [sv_denot]; rewrite U24; reflexivity).
sn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
sn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 32344)) Q1 ltac:(apply codeptr_val; exact HEI).
sn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
sn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x1b0: __asan_memset (p + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((SLOST_CID, pos) :: own) lyc S2 md1
    (k + 0) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 32344)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
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
    + unfold awr_byte. right; right; right. unfold in_frames. exists SLOST_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes SLOST_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (frame_hull_vis _ F 256 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ sn_Z F sp1 a ->
  aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 23%nat (SHADOW_OFF + F / 8)); [exact U23 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 24%nat F); [exact U24 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold SLOST_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold SLOST_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold SN_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U23b : bv_unsigned (ew E1 23) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U23).
assert (U24b : bv_unsigned (ew E1 24) = F) by (rewrite E1lo by lia; exact U24).
assert (SHOK1 : sh_ok segs SN_Bx (@nil shent) E1 (mrestrict (w_H W) memM)) by constructor.
assert (ZMM : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W) memM a = Some 0).
{ intros a Ha. replace a with ((F + 48) + (a - (F + 48))) by lia. rewrite (HsetM (a - (F + 48)) ltac:(lia)). reflexivity. }
clear dependent ms.
(* +0x1b4 .. +0x204: the notice's first 16 bytes, the checked store of 0 at s + 112, the checked loads at s + 96 and
   s + 104, up to `jalr a2` *)
paj_run_tok RUN HS HJ2 SHOK1 SN_B0.
{ sn_awr U23b U24b EF. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ sn_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (sn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(rewrite ?U23b, ?U24b in Hx; unfold sn_Z, SLOST_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (SLOST_S + 112 <= x < SLOST_S + 116) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13)) HFr); [| lia |].
  - intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U23b, ?U24b in Hx; unfold SLOST_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; lia]).
  - cbv beta. unfold SLOST_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | Hx]]; [lia | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ sn_Z F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
cbn [ms_mem restrict] in RS0, RS1, RS2.
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E1 (w_H W) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
set (old := TW.S_state (slost_w1 Bw)) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
assert (D27 : sv_denot E1 (SOff 27 0) = Z_to_bv 64 old).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 27%nat 27%bv eq_refl), R27. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D20 : sv_denot E1 (SOff 20 0) = Z_to_bv 64 why).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 20%nat 20%bv eq_refl), R20. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 32 8 (SLit 2) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 40 4 (SOff 27 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 44 4 (SOff 20 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP12.
pose proof (sn_chunk_val E1 (w_H W) (ms_mem ms) _ _ _ _ _ _ 6158896 4 (SLit 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP8, VP12, VG. rewrite U24b in VP0, VP8, VP12. rewrite D27 in VP8. rewrite D20 in VP12.
change (N.to_nat 8) with 8%nat in VP0. change (N.to_nat 4) with 4%nat in VP8, VP12, VG.
change (bv_unsigned (sv_denot E1 (SLit 2)) mod 2 ^ (8 * Z.of_N 8)) with 2 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG.
apply (sn_vm_w _ _ 4 old ltac:(lia)) in VP8. apply (sn_vm_w _ _ 4 why ltac:(lia)) in VP12.
change (N.to_nat 4) with 4%nat in VP8, VP12.
pose proof (sn_nb (w_H W) (ms_mem ms) F old why VP0 VP8 VP12 ZMN) as HNB.
(* what the call kept, from its entry to the call of notice *)
destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 SLOST_CID pos F FL HAR2 Hfrs Hbl EF eq_refl FFL)
  as (N1 & N2 & N3 & N4).
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (SLOST_S + 112 <= x < SLOST_S + 116) -> ~ sn_Z F sp1 x).
{ intros x Hx Hn Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes SLOST_CID) with 256; lia | exact (trans_g_img x Hx)].
  - exact (Hn Hz).
  - lia. }
assert (HSZ : forall a, sn_Z F sp1 a ->
  (spZ regs - SLOST_STK <= a < spZ regs) \/ dkg_nf SLOST_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [Hz | [Hz | [Hz | Hz]]].
  - right; left; right; left. change (fs_frame_bytes SLOST_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes SLOST_CID) with 256. lia.
  - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, SLOST_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
  - left; lia. }
pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
  (ms_mem ms) (spZ regs - SLOST_STK) (spZ regs) SLOST_CID pos F FL (slost_wr Bw why) (sn_Z F sp1) HGX HARc HAR2 Hfrs
  ltac:(intros bm Hb; rewrite Hbl; exact Hb) eq_refl EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN)
  as KCN.
assert (GKN : gx_kept_ex segs TG.G_HARNESS (slost_wr Bw why) W memc W (ms_mem ms)).
{ apply (gx_kept_ex_trans segs TG.G_HARNESS (slost_wr Bw why) W memc W mem2 W (ms_mem ms) HGK).
  intros a Ha Hn. apply KAN; [pose proof (inG_low segs B transport_segs_low _ a HGX Ha); unfold kLowMemEnd in *; lia|].
  intros Hz. apply Hn. pose proof (inG_low segs B transport_segs_low _ a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - exfalso. unfold SHADOW_OFF in Hz. lia.
  - exfalso. apply (N2 a); [left; change (fs_frame_bytes SLOST_CID) with 256; lia | exact (trans_g_img a Ha)].
  - right; right. split; [exact Hst | left]. unfold twa_fld, TW.A_S_state, SLOST_S in *. lia.
  - exfalso. lia. }
(* the registers at `jalr a2` *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite E1lo by lia. unfold E0, sn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (sn_vals Bw) 0) as X. cbn [Nat.add nth sn_vals] in X. rewrite X.
  rewrite <- (sn_notify Bw HLB), HNT. reflexivity. }
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U24b; reflexivity).
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
sn_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
sn_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* +0x204: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W E1 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (32424 + 4) = 0x89110) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (32424 + 4)))
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
assert (PTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (slost_w2 Bw)).
{ rewrite sn_w2_eq.
  apply (tw_write TMAP_A (aview segs (w_H W) mem2) _ (slost_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 0 TMAP_A_ok Htw1
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. assert (L0 : YO0f.le_byte 0 4 j = 0)
      by (unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia; reflexivity).
    rewrite L0. unfold aview. replace (TA_g_s + 112 + Z.of_nat j) with (0 + 6158896 + Z.of_nat j)
      by (unfold TA_g_s; lia).
    rewrite (VG j Hj), L0. reflexivity.
  - intros x Hx Hn. destruct Hx as (o & b & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x).
    { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact HxG | unfold SLOST_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((SLOST_CID, pos) :: own) lyc S2 W (ms_mem ms) mdC (k + 0) regsC
    (F + 32) (slost_ntc Bw why) TF (slost_w2 Bw) Bw'
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (sn_ntc_at lyc S2 W (ms_mem ms) md3 regsC Bw why F pos LAWS HARN Hin EF HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) Hwhy ZSN HNB)
    (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W (ms_mem ms) md3 (slost_wr Bw why) regs regsC
       SLOST_STK NOTICE_STK TF HARc HARN ltac:(intros bm Hb; rewrite Hbl; exact Hb)
       ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) (fun _ _ => eq_refl) eq_refl eq_refl HSTKLT KCN GKN
       ltac:(intros fr Efr a Ha Hw; exact (Hapart a Hw fr Efr Ha))
       ltac:(intros a Ha Hw; pose proof (inG_low segs B transport_segs_low _ a HGX (sn_wr_G Bw why a Hw)); lia)
       ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_LO in Gh; lia)
    PTW HNM
    (sn_apart lyc S2 W mem2 md2 W (ms_mem ms) TF Bw why F pos LAWS HAR2 Hin EF Hapart Hst)
    ltac:(intros HD; exfalso; unfold slost_ntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
    ltac:(unfold SLOST_EV in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 SLOST_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hin3 : In (SLOST_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 SLOST_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes SLOST_CID / 8) with 32 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (SLOST_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
assert (R3_23 : YK11.getr regs3 (Z_to_bv 5 23) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP3 23 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T23. exact R23. }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - SLOST_STK) (spZ regs) (slost_wr Bw why)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms) W3 mem3
    (spZ regs - SLOST_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (slost_wr Bw why)
    (notice_wr (slost_w2 Bw) (slost_ntc Bw why)) (dkg_nf SLOST_CID F FL)).
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
  - intros a Ha. left. right. right. split; [exact Hst | right; exact Ha]. }
(* +0x208 .. +0x22c: shadow bytes 4 .. 12 := 0xf8, to the release cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + (32424 + 4))) with (Z_to_bv 64 (BASE + (SLOST_NTC + 0x8c))).
pose proof (sn_entry3 W3 regs3 mem3 F R3_23 HF0 HF64 ltac:(lia)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U23c : bv_unsigned (ew E3 23) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 23%nat (Z_to_bv 5 23) eq_refl), R3_23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs SN_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 SN_B0 SLOST_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := SLOST_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes SLOST_CID / 8) with 32. lia.
  - apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U23c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - SLOST_STK) (spZ regs)
  (slost_wr Bw why)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md4 mem3
    (ms_mem ms4) (spZ regs - SLOST_STK) (spZ regs) SLOST_CID pos F FL (slost_wr Bw why)
    (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL
    ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. right. left. change (fs_frame_bytes SLOST_CID / 8) with 32. cbv beta in Ha. lia. }
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
sn_reg HS3 (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) F23
  ltac:(cbn [sv_denot]; rewrite (EE3 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS3 (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) F24
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words above sp1 and the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite USPC in K31. rewrite K31 by lia.
  apply KAN; [lia|]. unfold sn_Z, SLOST_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 248 + i) = aview segs (w_H W) mem2 (F + 248 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 SLOST_CID pos (F + 248 + i) Hin).
  - apply KAN; [lia|]. unfold sn_Z, SLOST_S, TA_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | Hz]]]; [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes SLOST_CID) with 256. lia.
  - intros Hw. apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes SLOST_CID) with 256; lia|].
    exact (trans_g_img _ (notice_wr_G _ _ _ Hw)). }
assert (HSo : forall o, In o SLOST_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold SLOST_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F ly3 S3 W3 (ms_mem ms4)
  md5 0 (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
    split; [unfold SLOST_EV, NOTICE_EV; lia|].
    split; [exact Hfrs3|].
    split; [rewrite <- Hbl; exact Hperm3|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold SLOST_FBYTES. change (flag_addr lyc SLOST_CID pos) with FL. rewrite <- HFLw.
      replace (F + 256 - 8) with (F + 248) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite (sn_gfn' TF Bw why Bw' HLB HNM). exact Hgf.
- assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
  split; [exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2))|].
  split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 (eq_sym Hgp))))|].
  split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 (eq_sym Htp))))|].
  split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8)))|].
  split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)))|].
  split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T18 R18)))|].
  split; [exact (eq_trans F23 (eq_trans (CH 23 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T23 R23)))|].
  exact (eq_trans F24 (eq_trans (CH 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T24 R24))).
Qed.

End sn.

Print Assumptions slost_ntc.
