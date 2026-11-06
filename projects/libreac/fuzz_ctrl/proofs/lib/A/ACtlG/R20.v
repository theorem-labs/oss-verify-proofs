(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths, module names, addresses and numbers changed; 382 of its 398 lines of code are new or changed and 543 lines of the source are left out. *)
(* lib/A/ACtlG/R20.v -- GLUE for stage seg_R20 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:704) (an earlier version, blob a3c6b7b35017, not in this delivery), on a glue base from a working branch 29ddfc3ea99).  Written by a Theorem Labs lane (block of a Theorem Labs lane 03:48Z); single
   writer.  rule 24: no function proved (stage glue of a walk; proves no function, kind: segment lemma).
   Pattern: glue-pattern.md sections 3, 4, 9 (a working note, not in this delivery); pilot lib/A/ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_R20 : forall POST (b : nat),
       CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A818e8_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R20.  Segment R20 (Seg/R20.v:1-17) is 0x818e8 -> 0x81924: `beqz a0,818f0` taken (a0 = 0), `li a0,-8`, six
   1-byte stores of 0xf8 into the frame's own shadow bytes S(fr) + 316, + 317, + 320 .. + 323, `j 8191c`, then
   `mv a0,s8 ; jal __wrap_free` (0x8191c / 0x81920), and the free returns to 0x81924.  It is an ALLOCATOR segment
   (glue-pattern.md section 9 (a working note, not in this delivery)): the walk is carried to the free's entry 0x53378 with ra = 0x81924, a0 = phi, and the
   free site 0x81920 (shared with R13 / R15 / R16) is a Theorem Labs lane's ONE lemma A.ACtlG.Free81920.glue_free_81920
   (a working branch 10fb2f0a627, merged), CITED by name at this file's Section arguments.

   THE PROOF
   G1  the entry cut at index [Z.of_nat b]: ix_cut's index equation, then C_A818e8_at's conjuncts (ACtlCutP.v:1667).
   G2  the run's premises.  a0 = 0 (a0v), s3 = S(fr) (FRAC's register 19).  The window [S(fr) + 316, S(fr) + 324):
       present and writable (stk) from the cut's ctl_rt_C (route (C), A.ACtlRtC): its shadow_rw_on (cut_shadow B ly3
       S3), region (F) of the owned class-6 frame (6, c_fpos cx) in frames S3, [S(fr), S(fr) + 512), and in_shadow
       since the frame is application memory (frames_bounds' in_app on the journal's AR, the frame law, layout_le's
       ly_F); VISIBLE (the rng premise, by ProgBridge.rng_of_visible) from the core's AR_frames_law on the same AR
       (every shadow byte of an owned frame is apresent, hence not hidden).  No runtime fact is cited: the exit's
       ctl_rt_C is glue_free_81920's business (the free's glue states its own exit).
   G3  the walk moved from the cut's map regs3 to the run's canonical start mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the run Seg/R20F.r20_evt_F (a Theorem Labs lane's re-run, Required) at RNG := RNG_W (w_H W3), lifted with
       YA0nR.SRr_fevt_hid (the run writes memory, so the journal needs the hidden bytes it keeps).
   G5  at 0x8191c the walk is moved to mkR_of R (R the run's end map) and the register-only run
       Seg/R15F.rfree_evt_F (0x8191c -> 0x53378, ra := 0x81924, a0 := s8) is lifted with YA0nR.SRr_fevt.  At the
       free's entry the configuration is cfg_at segs 0x53378 R2 m' md'' (ProgBridge.cfg_at_MS read backwards) and
       glue_free_81920 applies at the entry context: the journal crosses both runs by YCbq.ajournal_exec, first with
       the write set
       [S(fr) + 316, S(fr) + 324) (awr_byte's in_frames case: the bytes are the owned class-6 frame's shadow), then
       with the empty set; frames, frame law and k <= 2b + 1 are the entry's; the Permutation is the entry body's;
       C_A81924_at's body at (R2, m') with bl := the entry blocks is rebuilt conjunct by conjunct: registers through
       the runs' K, every memory conjunct kept because its bytes (or, for an addressable range, its shadow bytes)
       lie outside the window -- frame bytes are application memory, the spill base A and the saved registers lie
       above HIGHMEM_BEG (A > c_sp - 4096 >= alloc_ceiling + LLVMF_STK - 4096, journal astk_ok), the input block is a
       live block (al_blocks' in_app, AR_sep_law's separation from the frame); FRAC's 392 frame shadow bytes are
       re-read at m' (present: kept outside the window, stk inside it); FRAC's last conjunct, the fake-frame trailer
       word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) (Batch3, ACtlCutP.v:997), is kept because
       [fr + 4088, fr + 4096) are frame bytes (NWfr); RB at turn (S b) is RB at b (b = 0, B3Rtm.a_RS_012).

   SECTION HYPOTHESES (exact text below)
   - LAWS, TFIB_SYMS, AFREE4, MT_FREE, CHAIN_OF_CUT: ACtl.v's (:237, :252, :276, :279, :598 on a working branch +
     10fb2f0a627), the Section of A.ACtlG.Free81920 with its MOK_FREE given by (fun S => MT_FREE S _), as ACtl.v:277-278
     and R15.v / R16.v (same lane) do.  LAWS / TFIB_SYMS / AFREE4 / MT_FREE are ACtl.v's text; CHAIN_OF_CUT is
     Free81920.v's text, which is ACtl.v's with its notations CB / ctlcx / c_mem / c_md written out.
   - (none from the kit: lib/A/ACtlG/Kit.v is on the glue base, so kit_wx / kit_segs_low are Required and cited as
     A.ACtlG.Kit.kit_wx / A.ACtlG.Kit.kit_segs_low.)
   - No VIS0 / OWNED_RO (none was ever needed here; glue_free_81920 has none since 10fb2f0a627).  The former
     HFREE (glue_free_81920's statement as a hypothesis) is replaced by the citation.
   Required, not assumed: Seg/R20F.v r20_evt_F and Seg/R15F.v rfree_evt_F (a Theorem Labs lane's re-runs) and the kit's
   kit_wx / kit_segs_low.  Proof-internal citations from the _F files' closure, Qed-closed and stated over lib/Lib
   memory predicates only: Seg/R20.v r20_bytes_of_present, Seg/R15.v r15_RS_len, Seg/B3Rtm.v a_RS_012, SlotModel
   OUR_length.

   CLOSURE: every project Require is qualified (no Import / Export of a project module); the six twin modules
   (YI04 YI16 YK11 YK1b YM05 YO09) are named by full path or by a Module alias of the full path; no statement names
   a frame-route identifier.  The blob list of the frame-route files in the closure is in the commit message.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are YK11 / YG0d-qualified (or lib/Lib's, through LPE, where a
   lib/Lib run's own state names them).

   BUILD STATE: see the commit message. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ACtlG.Kit A.AF0m A.ACtlG.Free81920.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Frame Mem PropExec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R20 R20F R15 R15F B3Rtm.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases (the six twin modules and every lib/Lib module this file names). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module SMA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SR20 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R20.
Module SR20F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R20F.
Module SR15 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R15.
Module SR15F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R15F.
Module SB3R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Rtm.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueR20.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:257, :261-262, the two cut records :291-292), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A818e8_at := (ACtlCutP.C_A818e8_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* ACtl.v's Section hypotheses of these names and texts (Free81920.v's Section, with its MOK_FREE given by
   MT_FREE); sources in the header. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k
    (regsT : bvmap 5 word) (pc0 ra : Z),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  CK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  CK11.getr regsT 1 = Z_to_bv 64 ra ->
  LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 27) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 26) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 25) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 24) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 23) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 22) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 21) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 20) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 19) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 18) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 9) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 8) ++
     LMem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R20 : forall POST (b : nat), CF POST (ix_cut C_A81924_at [Z.of_nat b]) -> CF POST (ix_cut C_A818e8_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A818e8_at, ACtlCutP.v:1667). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A818e8_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & (Hn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR) & Hb0 & HRFb & Ha0 & S128 &
    HPRO & S104 & S96 & S64 & R21 & S112 & S144 & S192 & HRWid & HRWjk & S280 & S240 & HRWjy & HRWsc & S152 &
    HAid & HRXS).
  cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A818e8_at ACtlCutP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  (* G2: the frame, from the journal's AR (frames_bounds, AR_frames_law), the frame law and layout_le's ly_F. *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hstklo & Hstksp & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & Hfapp).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & _ & Hfsh).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Efs : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efr3 in Hf4096. rewrite Efr3, Efs in Hfapp. rewrite Efr3, Efs in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
  pose proof (proj1 (@Reusable.YG0f.ASAN_CEIL_range rc)) as HCEIL. unfold Reusable.YG0f.ASAN_CEIL in HCEIL, Hfapp.
  pose proof (proj1 Reusable.YCbq.asan_consts) as Hceil.
  unfold A.ACfn.LLVMF_STK in Hstksp.
  (* FRAC's registers, spill base and frame facts (ACtlCutP.v:982-997); its last two conjuncts are the saved
     registers' bytes_at (Hsaved) and Batch3's fake-frame trailer word at fr + 4088 (Htr) *)
  pose proof HFRAC as (Af & sp & Hr2 & Hspm & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & HAm & HAsp &
    HspA & HfrA & HA416 & Hsp4096 & HspEnd & Hq304 & Hq24 & Hq16 & Hhdr1 & Hhdr2 & (sh & Hsh & Hshl) & Hsaved & Htr).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HspEnd.
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (ESfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (HSfr : 0x7fff8000 + 512 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 324 <= 0x10007fff8000 - 4096).
  { rewrite ESfr. revert Hf4096 Hfapp HCEIL. Z.div_mod_to_equations. lia. }
  (* the write window W = [S(fr) + 316, S(fr) + 324) lies strictly between LOWMEM_END and HIGHMEM_BEG *)
  assert (NW : forall x, (x < 0x7fff8000 \/ 0x10007fff8000 <= x) ->
            ~ (ACtlCutP.Sfr fr + 316 <= x < ACtlCutP.Sfr fr + 324)) by (intros x Hx; lia).
  assert (NWfr : forall x, fr <= x < fr + 4096 -> ~ (ACtlCutP.Sfr fr + 316 <= x < ACtlCutP.Sfr fr + 324)).
  { intros x Hx. apply NW. lia. }
  (* the shadow byte of frame byte fr + j is S(fr) + j / 8 *)
  assert (SHfr : forall j, 0 <= j < 4096 -> (j < 2528 \/ 2592 <= j) ->
            ~ (ACtlCutP.Sfr fr + 316 <= A.AsanRT.shadow_addr (fr + j) < ACtlCutP.Sfr fr + 324)).
  { intros j Hj Hj2. rewrite ESfr. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    revert Hfr8 Hj Hj2. Z.div_mod_to_equations. lia. }
  (* the spill base and the saved registers lie above HIGHMEM_BEG (batch 4 B5.4: FRAC's top is c_sp cx <= APPMEM_END) *)
  assert (HAhi : 0x10007fff8000 <= Af - 4096 /\ Af + 416 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= 2 ^ 47) by lia.
  (* the input block: empty, or a live block of the entry heap, hence of the cut's (HP) *)
  pose proof HB as ((_ & _ & _ & _ & Hinp & Hlen & _) & _).
  assert (INB : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
            ~ (ACtlCutP.Sfr fr + 316 <= x < ACtlCutP.Sfr fr + 324)).
  { intros x Hx. destruct Hinp as [(Hn0 & _) | (Hnpos & Hinb)]; [lia|].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinb. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & _ & _ & Hpapp & _).
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    assert (Ereq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
    { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
    rewrite Ereq in Hpapp. apply NW. lia. }
  assert (SHB : 0 < ACtlCut.c_n cx -> forall i, 0 <= i < ACtlCut.c_n cx ->
            ~ (ACtlCutP.Sfr fr + 316 <= A.AsanRT.shadow_addr (ACtlCut.c_p cx + i) < ACtlCutP.Sfr fr + 324)).
  { intros Hnpos0 i Hi. destruct Hinp as [(Hn0 & _) | (Hnpos & Hinb)]; [lia|].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinb. }
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin)
      as Hdis.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & Hp4096 & _).
    assert (Ereq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
    { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
    unfold Reusable.YG0f.zdisjoint in Hdis. cbn [fst snd] in Hdis. rewrite Efr3, Efs, Ereq in Hdis.
    rewrite ESfr. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    revert Hfr8 Hi Hdis Hp4096. Z.div_mod_to_equations. lia. }
  (* the run's two memory premises: the window is present and writable (stk), and visible (rng).  Route (C) (L3
     recipe 2(c)): the cut carries ctl_rt_C; the window [S(fr) + 316, S(fr) + 324) is the owned class-6 frame's shadow,
     cut_shadow's (F) region at (6, c_fpos cx) in frames S3 *)
  destruct Hrt as (Hcells & Hcut & Himg & Hroag).
  assert (HSTK : LFR.stk A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 316) (ACtlCutP.Sfr fr + 324)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (HF6 : A.ACtlRtC.cut_shadow B ly3 S3 a).
    { left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|].
      rewrite Efr3, Efs. change (4096 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESfr in Ha. lia. }
    apply (Hcut a HF6).
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG.
    rewrite ESfr in Ha. revert Ha Hf4096 Hfapp HCEIL. Z.div_mod_to_equations. lia. }
  assert (HRNG : LEF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 316) 8).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfsh (a - Reusable.YG0f.shadow_addr fr)) as ((Hh & _) & _).
    { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESfr in Ha. lia. }
    replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hh by lia.
    exact Hh. }
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A818e8_at [Z.of_nat b])) with 0x818e8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x818e8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  unfold LR6.mkR_of.
  (* G4: the run 0x818e8 -> 0x8191c (Seg/R20F.v:50-66) at RNG_W (w_H W3), lifted with SRr_fevt_hid. *)
  pose proof (SR20F.r20_evt_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 (ACtlCutP.Sfr fr) Ha0 Hr19 ltac:(lia) ltac:(lia) HSTK HRNG) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
           HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & MU & WM & STK').
  subst ms'.
  (* G5: the free call, 0x8191c -> 0x53378 (Seg/R15F.v:44-54), register-only, from the run's end map R. *)
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of R) R); [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv R))].
  unfold LR6.mkR_of.
  pose proof (SR15F.rfree_evt_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get R 5) (reg_get R 6) (reg_get R 7)
    (reg_get R 8) (reg_get R 9) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14)
    (reg_get R 15) (reg_get R 16) (reg_get R 17) (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21)
    (reg_get R 22) (reg_get R 23) (reg_get R 24) (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get R 28)
    (reg_get R 29) (reg_get R 30) (reg_get R 31) CK11.fp_regs CK11.fp_csr m') as HRUN2.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN2) as HFS2.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS2.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md' (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS2).
  { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
  intros ms'' md'' HQ1 Hsbm2.
  destruct HQ1 as (a0' & Ems2 & Ea0). subst ms'' a0'.
  match goal with |- context [LMS.MS ?RR _ (Z_to_bv 64 0x53378) _ _ _ _] => set (R2 := RR) end.
  (* ProgBridge.cfg_at_MS read backwards (eq_refl), at the free's entry *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 R2 m' md'') (POST cx)).
  (* the registers of the call map R2 that the exit body reads *)
  assert (E2 : CK11.getr R2 2 = CK11.getr regs3 2) by exact K2.
  assert (E3 : CK11.getr R2 3 = CK11.getr regs3 3) by exact K3.
  assert (E4 : CK11.getr R2 4 = CK11.getr regs3 4) by exact K4.
  assert (E8 : CK11.getr R2 8 = CK11.getr regs3 8) by exact K8.
  assert (E9 : CK11.getr R2 9 = CK11.getr regs3 9) by exact K9.
  assert (E19 : CK11.getr R2 19 = CK11.getr regs3 19) by exact K19.
  assert (E21 : CK11.getr R2 21 = CK11.getr regs3 21) by exact K21.
  assert (E22 : CK11.getr R2 22 = CK11.getr regs3 22) by exact K22.
  assert (E23 : CK11.getr R2 23 = CK11.getr regs3 23) by exact K23.
  assert (E25 : CK11.getr R2 25 = CK11.getr regs3 25) by exact K25.
  assert (E26 : CK11.getr R2 26 = CK11.getr regs3 26) by exact K26.
  (* memory across the six stores: unchanged outside the window (munch), present inside it (stk) *)
  assert (KMRD : forall a, 0 <= a < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 316 <= a < ACtlCutP.Sfr fr + 324) ->
            LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha Hna. unfold LMem.mrd. rewrite (MU (LMem.wa a)); [reflexivity|].
    cbn [LFR.outside]. rewrite LMem.wa_unsigned by lia. split; [exact Hna | exact I]. }
  assert (KB : forall a bs, (forall x, a <= x < a + Z.of_nat (length bs) ->
                   ~ (ACtlCutP.Sfr fr + 316 <= x < ACtlCutP.Sfr fr + 324)) ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs Hx (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    rewrite <- (H3 i Hi). exact (KMRD (a + Z.of_nat i) ltac:(lia) (Hx (a + Z.of_nat i) ltac:(lia))). }
  assert (KADDR : forall p n, (forall i, 0 <= i < n ->
                     ~ (ACtlCutP.Sfr fr + 316 <= A.AsanRT.shadow_addr (p + i) < ACtlCutP.Sfr fr + 324)) ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n).
  { intros p n Hx (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. destruct (H4 i Hi) as (Happ & bb & Hbb & Hok). split; [exact Happ|]. exists bb.
    split; [|exact Hok]. rewrite KMRD; [exact Hbb | | exact (Hx i Hi)].
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Happ.
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. revert Happ. Z.div_mod_to_equations. lia. }
  assert (KSP : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R2 m' off v).
  { intros off v Hoff (A0 & HA0 & HQ). exists A0. split; [exact (eq_trans E9 HA0)|].
    pose proof (LMem.bytes_at_bound _ _ _ _ HQ) as HQb. rewrite LMem.length_le8 in HQb.
    assert (EA : A0 = Af).
    { unfold ACtlCut.rgv in HA0, Hr9. rewrite HA0 in Hr9. apply (f_equal (@bv_unsigned 64)) in Hr9.
      rewrite !Z_to_bv_unsigned in Hr9. unfold bv_wrap, bv_modulus in Hr9. cbn [Z.of_N] in Hr9.
      revert Hr9 HQb HAhi HAm. Z.div_mod_to_equations. lia. }
    subst A0. unfold ACtlCutP.q64 in *. apply KB; [|exact HQ]. intros x Hx. apply NW. right. lia. }
  assert (KRW : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + 4096 ->
            LST.rw_cells segs mem3 a [LCE.CB n bs] -> LST.rw_cells segs m' a [LCE.CB n bs]).
  { intros a n bs Ha1 Ha2 ((Hwf & Hb) & Hw).
    assert (Hl : length bs = n) by (cbn [LCE.cells_wf LCE.cell_wf] in Hwf; tauto).
    split; [split; [exact Hwf|]|].
    - apply KB; [|exact Hb]. intros x Hx. apply NWfr. cbn [LCE.cells_bytes LCE.cbytes] in Hx.
      rewrite app_nil_r, Hl in Hx. lia.
    - destruct Hw as (Hw0 & Hw1 & Hw2). split; [exact Hw0|]. split; [exact Hw1|].
      intros i Hi. exact (WM _ (Hw2 i Hi)). }
  (* FRAC at the call map R2 and the new memory m' *)
  assert (HFRAC' : ACtlCutP.FRAC B cx fr fr R2 m').
  { exists Af, sp.
    (* FRAC's register reader and this file's CK11.getr have the same body; each register step goes through
       conversion (eq_trans), never a rewrite, so it holds whichever YK11 copy ACtlCutP's name resolves to (on glue base
       eb89fed7fac it was the unit copy, lib/A/Reusable/YK11) *)
    split; [exact (eq_trans E2 Hr2)|].
    split; [exact Hspm|].
    split; [transitivity (Reusable.YG0d.spZ regs3); [unfold Reusable.YG0d.spZ; f_equal; exact E2 | exact Hspz]|].
    split; [exact (eq_trans E4 Hr4)|].
    split; [exact (eq_trans E8 Hr8)|].
    split; [exact (eq_trans E9 Hr9)|].
    split; [exact (eq_trans E3 Hr3)|].
    split; [exact (eq_trans E19 Hr19)|].
    split; [exact (eq_trans E26 Hr26)|].
    split; [exact Hfrm|]. split; [exact HAm|]. split; [exact HAsp|]. split; [exact HspA|].
    split; [unfold ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact Hsp4096|].
    split; [unfold A.AsanRT.APPMEM_END; exact HspEnd|].
    split; [unfold ACtlCutP.q64 in *; apply KB; [|exact Hq304]; intros x Hx; apply NW; right; lia|].
    split; [unfold ACtlCutP.q64 in *; apply KB; [|exact Hq24]; intros x Hx; apply NW; right; lia|].
    split; [unfold ACtlCutP.q64 in *; apply KB; [|exact Hq16]; intros x Hx; apply NW; right; lia|].
    split; [unfold ACtlCutP.q64 in *; apply KB; [|exact Hhdr1]; rewrite LMem.length_le8;
            intros x Hx; apply NWfr; lia|].
    split; [unfold ACtlCutP.q64 in *; apply KB; [|exact Hhdr2]; rewrite LMem.length_le8;
            intros x Hx; apply NWfr; lia|].
    split.
    - (* the 392 frame shadow bytes, re-read at m' *)
      assert (EFS : Z.to_nat ACtlCutP.FRAME_SHADOW = 392%nat) by reflexivity.
      rewrite EFS in Hshl |- *.
      pose proof (LMem.bytes_at_bound _ _ _ _ Hsh) as Hshb. rewrite Hshl in Hshb.
      destruct (SR20.r20_bytes_of_present 392 m' (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh' & Hsh' & Hsh'l).
      { intros kk Hkk.
        destruct (Z_lt_le_dec (ACtlCutP.Sfr fr + Z.of_nat kk) (ACtlCutP.Sfr fr + 316)) as [Hlo|Hlo];
          [|destruct (Z_lt_le_dec (ACtlCutP.Sfr fr + Z.of_nat kk) (ACtlCutP.Sfr fr + 324)) as [Hhi|Hhi]].
        - destruct (nth_error sh kk) as [b0|] eqn:En; [|apply nth_error_None in En; lia].
          exists b0. rewrite KMRD by lia. pose proof (proj2 (proj2 Hsh) kk ltac:(lia)) as Hk'.
          rewrite En in Hk'. exact Hk'.
        - destruct STK' as (_ & _ & Hst). destruct (Hst (ACtlCutP.Sfr fr + Z.of_nat kk) ltac:(lia)) as (_ & bb & Hbb).
          exists bb. exact Hbb.
        - destruct (nth_error sh kk) as [b0|] eqn:En; [|apply nth_error_None in En; lia].
          exists b0. rewrite KMRD by lia. pose proof (proj2 (proj2 Hsh) kk ltac:(lia)) as Hk'.
          rewrite En in Hk'. exact Hk'. }
      exists sh'. split; [exact Hsh' | exact Hsh'l].
    - split.
      + (* the saved caller registers at [c_sp - 104, c_sp): above HIGHMEM_BEG *)
        apply KB; [|exact Hsaved]; intros x Hx; apply NW; right; lia.
      + (* the fake-frame trailer word at fr + 4088 (Batch3): [fr + 4088, fr + 4096) are frame bytes, outside the
           shadow window [S(fr) + 316, S(fr) + 324) the run writes *)
        unfold ACtlCutP.q64 in *; apply KB; [|exact Htr]; rewrite LMem.length_le8; intros x Hx; apply NWfr; lia. }
  (* the frame records, RB at turn (S b) (= turn b: b = 0, B3Rtm.a_RS_012) *)
  assert (Hb2 : (b <= 2)%nat) by lia.
  destruct (SB3R.a_RS_012 (ACtlCut.c_in cx) b Hb2) as (EID & EFG).
  destruct (SR15.r15_RS_len (ACtlCut.c_in cx) b) as (LID & LFG).
  pose proof (SMA.OUR_length (ACtlCut.c_in cx)) as LOUR.
  assert (KOUR : ACtlCutP.OURb cx fr mem3 -> ACtlCutP.OURb cx fr m').
  { unfold ACtlCutP.OURb. intros H. apply KB; [|exact H]. rewrite LOUR. intros x Hx. apply NWfr. lia. }
  destruct HRFb as ((Rb6 & HCURb & Rour & Rr23 & Ridb & Rfgb) & Hrnb & Hr24 & Hphi).
  assert (HRB' : ACtlCutP.RB cx fr b (SMA.RID (ACtlCut.c_in cx) (S b)) (SMA.RFG (ACtlCut.c_in cx) (S b)) R2 m').
  { rewrite EID, EFG.
    split; [exact Rb6|].
    split.
    { destruct HCURb as (Rc0 & Rc22 & Rc25). split; [exact Rc0|].
      split; [exact (eq_trans E22 Rc22) | exact (eq_trans E25 Rc25)]. }
    split; [exact (KOUR Rour)|].
    split; [exact (eq_trans E23 Rr23)|].
    split.
    { unfold ACtlCutP.IDBr in *. apply KB; [|exact Ridb]. rewrite LID. intros x Hx. apply NWfr. lia. }
    { unfold ACtlCutP.FGBr in *. apply KB; [|exact Rfgb]. rewrite LFG. intros x Hx. apply NWfr. lia. } }
  (* PRO (ACtlCutP.v:468): the spills, our[]'s 6 bytes (shadow S(fr) + 328), the input block *)
  assert (HPRO' : ACtlCutP.PRO cx fr R2 m').
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
      P184 & P256 & P264 & P272 & P32).
    split; [eapply KSP; [lia | exact P40]|]. split; [eapply KSP; [lia | exact P120]|].
    split; [eapply KSP; [lia | exact P136]|]. split; [eapply KSP; [lia | exact P160]|].
    split; [eapply KSP; [lia | exact P168]|]. split; [eapply KSP; [lia | exact P176]|].
    split; [eapply KSP; [lia | exact P208]|]. split; [eapply KSP; [lia | exact P248]|].
    split.
    { apply KADDR; [|exact Pad]. intros i Hi. replace (fr + 2624 + i) with (fr + (2624 + i)) by lia.
      apply SHfr; lia. }
    split; [apply KB; [exact INB | exact Pin]|].
    split; [intros Hnpos; apply KADDR; [exact (SHB Hnpos) | exact (Pg Hnpos)]|].
    split; [eapply KSP; [lia | exact P184]|]. split; [eapply KSP; [lia | exact P256]|].
    split; [eapply KSP; [lia | exact P264]|]. split; [eapply KSP; [lia | exact P272]|].
    eapply KSP; [lia | exact P32]. }
  (* RXS (ACtlCutP.v:520): the spills and the fragment record's 72 addressable bytes (S(fr) + 282 .. + 290) *)
  assert (HRXS' : ACtlCutP.RXS cx fr R2 m').
  { destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
    split; [eapply KSP; [lia | exact X48]|]. split; [eapply KSP; [lia | exact X56]|].
    split; [eapply KSP; [lia | exact X88]|]. split; [eapply KSP; [lia | exact X80]|].
    split; [eapply KSP; [lia | exact X72]|]. split; [eapply KSP; [lia | exact X8]|].
    split; [eapply KSP; [lia | exact X0]|]. split; [eapply KSP; [lia | exact X200]|].
    split; [eapply KSP; [lia | exact X216]|].
    apply KADDR; [|exact Xad]. intros i Hi. replace (fr + 2256 + i) with (fr + (2256 + i)) by lia.
    apply SHfr; lia. }
  (* the journal across both runs (ajournal_exec, YCbq.v:636-643) *)
  assert (HJ1 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => ACtlCutP.Sfr fr + 316 <= a < ACtlCutP.Sfr fr + 324).
    - exact HJ.
    - (* outside the window the memory is the entry's *)
      intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [LFR.outside]. split; [exact Hx | exact I].
    - (* no visible byte disappears: outside the window by munch, inside it by stk and the empty rom there *)
      intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr. cbn [Z.of_N] in Hxr.
      destruct (Z_lt_le_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 316)) as [Hlo|Hlo];
        [rewrite (MU x) by (cbn [LFR.outside]; split; [lia | exact I]); exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 324)) as [Hhi|Hhi];
        [|rewrite (MU x) by (cbn [LFR.outside]; split; [lia | exact I]); exact Hx].
      destruct STK' as (_ & _ & Hst). destruct (Hst (bv_unsigned x) (conj Hlo Hhi)) as (_ & bb & Hbb).
      unfold LMem.wa in Hbb. rewrite LMS.Z_to_bv_bv_unsigned in Hbb.
      revert Hbb. unfold LMem.mrd. destruct (m' x) as [b'|]; intros Hbb; [discriminate|].
      exfalso. unfold LPE.seg_rom, memory_read in Hbb. cbn [Z.of_N] in Hbb.
      rewrite (Reusable.YK04.find_segment1_none_above segs 0x5fe000 (bv_unsigned x)) in Hbb;
        [discriminate Hbb | vm_compute; reflexivity | lia].
    - exact Hhid.
    - exact Hsbm.
    - (* every written byte is a shadow byte of the owned class-6 frame (awr_byte's in_frames case) *)
      intros a Ha. right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Efs.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESfr in Ha. lia. }
  assert (HJ2 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md'' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ1 | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm2 | intros a Ha; destruct Ha]. }
  (* glue_free_81920 (a Theorem Labs lane) at the free's entry *)
  apply (A.ACtlG.Free81920.glue_free_81920 B MT XM_LIB RLO RHI LAWS TFIB_SYMS AFREE4 (fun S => MT_FREE S _)
           CHAIN_OF_CUT POST b cx fr k ly3 S3 W3 R2 m' md'' phi HX HB HJ2 HF HL Hk HP).
  - (* C_A81924_at's body (ACtlCutP.v:1696) at R2, m', with bl := the entry blocks *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at ACtlCutP.ixn ACtlCutP.ixz nth].
    rewrite Nat2Z.id.
    split; [apply Permutation_refl|].
    split; [exact HFRAC'|].
    split; [exact Hn|]. split; [exact Hb6|].
    split; [exact (eq_trans E23 R23)|].
    split; [exact (KOUR HOUR)|].
    split.
    { unfold ACtlCutP.OUTA in *. apply KADDR; [|exact HOUTA]. intros i Hi.
      replace (fr + 544 + i) with (fr + (544 + i)) by lia. apply SHfr; lia. }
    split; [exact HRB'|].
    split; [eapply KSP; [lia | exact S128]|].
    split; [exact HPRO'|].
    split; [eapply KSP; [lia | exact S104]|]. split; [eapply KSP; [lia | exact S96]|].
    split; [eapply KSP; [lia | exact S64]|].
    split; [exact (eq_trans E21 R21)|].
    split; [eapply KSP; [lia | exact S112]|]. split; [eapply KSP; [lia | exact S144]|].
    split; [eapply KSP; [lia | exact S192]|].
    split; [destruct HRWid as (idb & HW); exists idb; eapply KRW; [lia | lia | exact HW]|].
    split; [destruct HRWjk as (junk & HW); exists junk; eapply KRW; [lia | lia | exact HW]|].
    split; [eapply KSP; [lia | exact S280]|]. split; [eapply KSP; [lia | exact S240]|].
    split; [destruct HRWjy as (jy & HW); exists jy; eapply KRW; [lia | lia | exact HW]|].
    split; [destruct HRWsc as (junk & HW); exists junk; eapply KRW; [lia | lia | exact HW]|].
    split; [eapply KSP; [lia | exact S152]|].
    split.
    { apply KADDR; [|exact HAid]. intros i Hi. replace (fr + 2176 + i) with (fr + (2176 + i)) by lia.
      apply SHfr; lia. }
    exact HRXS'.
  - (* ra = 0x81924 *)
    reflexivity.
  - (* a0 = s8 = phi (RFb's register 24) *)
    transitivity (CK11.getr regs3 24); [exact K24 | exact Hr24].
Qed.

End GlueR20.
