(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/MemNormTr.v; 103 of its 120 lines of code are new or changed and 212 lines of the source are left out. *)
(* lib/A/Prog/C_reac_ctrl_parsePP.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the first glue step of the cgif-form
   glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), route (C).

     rcpPP_to_E1   the entry of reac_ctrl_parse (0x83578) -> the first slot of __asan_stack_malloc_1 (0x3d72c, ra =
                   0x835ec): reac_ctrl_parseF_pre.PreFOn.pre_call_F run on MemNorm.normalize memc (its post
                   reac_ctrl_parseF_bnd.BndFOn.PreCall), lifted at the real memory memc by
                   C_reac_ctrl_parseK.rcpK_lift_norm; the journal at the real end memory across the window writes
                   [S - 8800, S) by C_reac_ctrl_parseK.rcpK_journal_win.  The continuation receives PreCall's facts
                   over the normalized end memory m1n and the register file C_reac_ctrl_parseK.rcpK_regsE.

   Ported from a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parsePf.v @ 258208c7d59, image A addresses: B's rcpB_to_E1 (its
   C_reac_ctrl_parseLib.rcpB_pre_F, GlueLift.rrB_lift and GlueLift.rrB_journal_win are A's PreFOn.pre_call_F,
   rcpK_lift_norm and rcpK_journal_win; B's four bytes_at premises of the GOT cells are A's asan_cells; A's run also
   takes the side-stack premise fpx, moved to normalize memc by the local rcpPP_fpx_normalize).
   A lemmas cited: reac_ctrl_parseF_pre.PreFOn.pre_call_F, C_reac_ctrl_parseK.rcpK_lift_norm / rcpK_journal_win,
   MemNormTr.stk_normalize_ro / asan_cells_normalize / asan_tls_cells_transport / ms_rel_MS,
   MemNorm.mem_inv_normalize / bytes_at_normalize, ProgBridge.rng_of_visible / img_vis_W, the core's
   Reusable.YG0q.AR_laws_ok and CtrlImg.ctrl_segs_low.
   rcpPP_fpx_transport / rcpPP_fpx_normalize are MemNormTr.fp_transport / fp_normalize for RcAsanFP.fpx (the same
   conjuncts as fp; the last one, fp_dj D (fp_wx cs FS X), does not read memory), with the proofs copied.
   Route (C): no ctlrt_of_AR / shadow_rw_of_AR / rt_of_core / RT_used_of_AR / VIS0 / OWNED_RO.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT MemNorm MemNormTr ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c reac_ctrl_parseF reac_ctrl_parseF_bnd reac_ctrl_parseF_pre C_reac_ctrl_parseK CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YCbq YG0q.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module PBn := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_bnd.
Module PPr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_pre.
Module K := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseK.
Module CI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Local Notation rsegs := AI0.rsegs (only parsing).

(* ---- fpx on normalize m: MemNormTr.fp_transport / fp_normalize for RcAsanFP.fpx, proofs copied (fp_FS_above_img
   inlined: fs_place's ASAN_GT <= FS, ASAN_GT = 0x5fe000 = ImgBounds.IMG_HI). ---- *)
Lemma rcpPP_fpx_transport : forall (m m' : word -> option byte) cs TP FS lo hi W D X,
  (forall a bs, LM.bytes_at rsegs m a bs -> LM.bytes_at rsegs m' a bs) ->
  (forall lo' hi', IB.IMG_HI <= lo' -> LF.stk rsegs m lo' hi' -> LF.stk rsegs m' lo' hi') ->
  FP.fpx cs m TP FS lo hi W D X -> FP.fpx cs m' TP FS lo hi W D X.
Proof.
  intros m m' cs TP FS lo hi W D X EB ES H.
  destruct H as (DT & TS & C & T & DB & k & TL & HTP & (P1 & P2 & P3 & P4 & PS) & H88 & H96 & HC & HLO & HAPP & DJW &
                 DJD).
  assert (HG : IB.IMG_HI <= FS) by (unfold SMC.ASAN_GT in P3; unfold IB.IMG_HI; lia).
  exists DT, TS, C, T, DB, k.
  split; [exact (MNT.asan_tls_cells_transport m m' TP DT TS C T DB k EB TL)|].
  split; [exact (EB _ _ HTP)|].
  split; [split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4|]; exact (ES _ _ HG PS)|].
  split; [exact (EB _ _ H88)|]. split; [exact (EB _ _ H96)|].
  split; [|split; [exact HLO|]; split; [exact HAPP|]; split; [exact DJW | exact DJD]].
  eapply Forall_impl; [|exact HC]. intros c (Hc & h & flags & Hh & Hf & Hl & Hb).
  split; [exact Hc|]. exists h, flags. split; [exact (EB _ _ Hh)|]. split; [exact (EB _ _ Hf)|].
  split; [exact Hl | exact Hb].
Qed.

Lemma rcpPP_fpx_normalize : forall cs m TP FS lo hi W D X, MN.ro_agree rsegs m -> FP.fpx cs m TP FS lo hi W D X ->
  FP.fpx cs (MN.normalize rsegs m) TP FS lo hi W D X.
Proof.
  intros cs m TP FS lo hi W D X RO. apply rcpPP_fpx_transport.
  - intros a bs H. exact (MN.bytes_at_normalize rsegs m a bs RO H).
  - intros lo' hi' Hlo H. exact (MNT.stk_normalize_ro m lo' hi' RO Hlo H).
Qed.

Section PP.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
(* AR_laws of the bundle: the core's own proof (lib/Reusable/YG0q.v AR_laws_ok), no premise. *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

(* ---- S-A + J1: the entry 0x83578 to the first slot of __asan_stack_malloc_1, lifted, with the journal at the real
   memory m1 there.  The continuation also receives the normalized end memory m1n with PreCall's facts over it. ---- *)
Lemma rcpPP_to_E1 : RK04.wx_segs_nowrap rsegs ->
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc (W : RA0n.world rsegs) memc mdc k
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (f n o S FS : Z) (fr : list byte) (X : list (nat * Z))
    (Q : RA0n.world rsegs -> config -> Prop),
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 8800 -> S <= sp0 ->
  0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> 8800 <= S < 2^64 -> S mod 16 = 0 ->
  ART.HIGHMEM_BEG <= S - 8800 -> S <= ART.APPMEM_END -> length fr = 50%nat ->
  MN.ro_agree rsegs memc -> LF.stk rsegs memc (S - 8800) S -> ART.asan_cells memc ->
  FP.fpx [1%nat] memc (bv_unsigned tp) FS (S - 8800) S (PC.reac_ctrl_parse_W o S) (PC.reac_ctrl_parse_D f n o) X ->
  PB.range_visible (RA0n.w_H W) (S - 8800) 8800 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 m1n : word -> option byte) mdc1,
     LF.munch [(S - 8800, S)] (MN.normalize rsegs memc) m1n ->
     LF.wmono rsegs (MN.normalize rsegs memc) m1n -> PF.rd_mono (MN.normalize rsegs memc) m1n ->
     LM.mem_inv rsegs m1n ->
     LS.rw_cells rsegs m1n (S - 96) (PF.ParseFOn.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
     LF.stk rsegs m1n (S - 8800) (PF.ParseFOn.A S) ->
     MN.mem_rel rsegs m1 m1n -> MN.ro_same rsegs memc m1 ->
     (forall x : word, RA0n.w_H W x = true -> m1 x = memc x) ->
     RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
     RA0n.SRr rsegs W (mkCfg (LMS.MS (K.rcpK_regsE gp tp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2 s3 s7 s8 s10 s11
                                       t3' t4' t5' t6' f n o S)
                                F (Z_to_bv 64 SMC.ASAN_STACK_MALLOC_1) fc None m1 (LP.seg_rom rsegs)) mdc1) Q) ->
  RA0n.SRr rsegs W (mkCfg (LMS.MS (LF.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n)
                      (Z_to_bv 64 o) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 PC.REAC_CTRL_PARSE) fc None memc (LP.seg_rom rsegs)) mdc) Q.
Proof.
  intros Hwx STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f n o S FS fr X Q
    HJ Hlo Hhi Rf Rn Ro RS S16 HHM HAE Lfr RO ST AC FP0 VW K0.
  assert (HIMG : IB.IMG_HI <= S - 8800) by (unfold IB.IMG_HI; unfold ART.HIGHMEM_BEG in HHM; lia).
  pose proof (MNT.stk_normalize_ro memc (S - 8800) S RO HIMG ST) as STn.
  eapply (K.rcpK_lift_norm Hwx W mdc); [exact RO | | ].
  - pose proof (PB.rng_of_visible _ _ _ (PB.img_vis_W W)) as RIMG.
    unfold IB.IMG_LO, IB.IMG_HI in RIMG.
    exact (PPr.PreFOn.pre_call_F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MN.normalize rsegs memc)
             f n o S FS fr (PB.RNG_W (RA0n.w_H W)) Rf Rn Ro RS S16 STn (MN.mem_inv_normalize rsegs memc) Lfr
             (MNT.asan_cells_normalize memc RO AC) HHM HAE X (rcpPP_fpx_normalize _ _ _ _ _ _ _ _ _ RO FP0)
             RIMG (PB.rng_of_visible _ _ _ VW) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ eq_refl).
  - intros ms' md' _ (s' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n &
                            Es' & MU & WM & RM & MI & SV & STA) & HREL & HROS) Hhid Hsame.
    rewrite Es' in HREL. destruct (MNT.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
    rewrite Ems.
    apply (K0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (ms_mem ms') m1n md'
             MU WM RM MI SV STA HMR HROS Hhid).
    apply (K.rcpK_journal_win B LAWS CI.ctrl_segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W
             memc mdc k (ms_mem ms') m1n md' (S - 8800) S HJ);
      [lia | lia | exact HIMG | lia | exact MU | | exact HMR | exact HROS | exact Hhid | exact Hsame].
    intros a Ha. destruct STn as (_ & _ & Hs). destruct (Hs a Ha) as [_ Hb]. exact (RM _ Hb).
Qed.

End PP.
