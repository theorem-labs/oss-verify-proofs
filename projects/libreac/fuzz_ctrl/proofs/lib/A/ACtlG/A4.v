(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 289 of its 312 lines of code are new or changed and 822 lines of the source are left out. *)
(* lib/A/ACtlG/A4.v -- GLUE for stage seg_A4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:655,
   `Hypothesis seg_A4 : forall POST, CF POST (ix_cut C_A81400_at [0]) -> CF POST C_Jrel -> CF POST C_A810e4`).
   Written by a Theorem Labs lane's glue lane (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A2.v.
   rule 24: no function proved (segment lemma).

   WHAT IT PROVES
     glue_seg_A4 : forall POST, CF POST (ix_cut C_A81400_at [0]) -> CF POST C_Jrel -> CF POST C_A810e4
   with ACtl.v's own CF / ix_cut notations (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_A4.  Segment A4 is 0x810e4 -> 0x813fc (198 instructions): the 137 tail shadow stores of the
   class-6 frame [S(fr) + 255, S(fr) + 392), the n test `srli a1,s8,26` / `beqz a1`, and on the fall-through the
   spill block [A + 16, A + 288) of the prologue save area; exit 0x81400 at turn t = 0.  The C_Jrel hypothesis
   (the early edge 0x81314 -> 0x82b80, taken when 2^26 <= n) is NOT used: ctl_base's lib pre
   (A.ACfn.tfib_lib_pre_x, ACfn.v:38) gives n = 0 or 0 < n < 2^26, so that arm of the run's post is refuted.

   RULE 24 (released proofs first): as lib/A/ACtlG/A2.v (proof-index LLVMFuzzerTestOneInput, index v5; the
   released ASan donor cgif/cgif_file_fuzzer lifts no outside-proved run), so this glue has no donor counterpart.

   THE RUN.  a Theorem Labs lane's mechanical v1.9 re-run A.Prog.Seg.A4F.a4_evt_F (Seg/A4F.v:144-167), Required, not
   assumed: the footprint twin of ctrl's a4_evt (Seg/A4.v:168).  Its start map is the explicit `mkR ra0 .. t6`,
   instantiated with `Sem.reg_get regs3 1` .. `Sem.reg_get regs3 31` (= Regs6ss.mkR_of regs3 by delta); its F / fc
   are the core's CK11.fp_regs / CK11.fp_csr; its post's getr / seg_rom (ctrl's lib/A/Reusable/YK11) are rewritten
   to the core's with `change` (same bodies).  Its two rng premises: the frame-shadow tail by
   KitMem.kitmem_rng_frame_sh, the spill block by KitMem.kitmem_rng_win.

   THE PROOF, step by step (glue-pattern.md section 3 (a working note, not in this delivery))
   G1  unfold the entry cut C_A810e4 (ACtlCutP.v:1228-1239): live list, FRAHC (header 0x41b58ab3), n <= ANMAX,
       s2 = -8, s4 = -14, s5 = sel, s6 = fr, s7 = p, s8 = n, s9 = S(fr) + 68, the input bytes and their
       addressability.  FRAHC's arithmetic prefix is destructed by position (stable under a Theorem Labs lane's announced
       `<` -> `<=` change), its memory tail BY SHAPE (so the announced trailer conjunct is carried unnamed).
   G2  the run's premises: KitMem.kitmem_own6 (4096 <= fr, fr + 4096 <= alloc_ceiling <= c_sp - LLVMF_STK, frame_addr
       at ly3), YCbq.frames_bounds (the frame's application band), YCbq.asan_consts (the ceiling's range); from
       them 8 * S(fr) = fr + 8 * ASAN_K, S(fr) + 392 <= A, A + 288 <= 2^64; the two rw_cells blocks from lib/Lib
       stk windows (KitMem.kitmem_stk_of_journal for [A + 16, A + 288), KitMem.kitmem_stk_of_present with the AR
       frames law's shadow presence for [S(fr) + 255, S(fr) + 392)) through ctrl's Seg/A4.v lib_rw_stk; the
       run's own `stk lo hi` premise at the empty window lo = hi = 0 (its post is not used).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to mkR_of regs3.
   G4  KitMem.kitmem_lift at RNG_W (w_H W3) (fp_avoids by ProgBridge.fp_avoids_RNG_W); the continuation receives
       the run's fsteps.
   G5  the exit cut ix_cut C_A81400_at [0] (ACtlCutP.v:1136-1158, 34 conjuncts) at the run's end map R and memory
       m', the same cx, fr, k, ly3, S3, W3 and the materialized model md':
         journal  ProgWorld.ajournal_of_fsteps with WR = [(S(fr) + 255, S(fr) + 392); (A + 16, A + 288)]; awr_byte
                  by KitMem.kitmem_not_outside, then kitmem_awr_frame (the owned frame's shadow) or
                  kitmem_awr_win (the LLVMF stack window);
         frames, frame law, k bound   unchanged (own6 and kmax 0 on both cuts);
         body     FRAC built BY SHAPE at (regs3, m') from FRAHC (words off WR by kitmem_q64_munch /
                  kitmem_bytes_munch, the frame shadow by kitmem_bytes_grow over ProgWorld.pws_fsteps_mem's
                  mem_grows) plus the run's spills [A + 24] = sel, [A + 16] = fr, then moved to R by
                  Kit.kit_frac_move; registers and spills from the run's a4_exit (ctrl's port, Seg/A4.v:1017-1085);
                  PRO's our[] bytes addressable by ctrl's a4_our_addr; the input bytes by kitmem_bytes_munch and
                  their addressability by kitmem_addressable_mrd (KitMem.kitmem_input_apart: the block is below
                  alloc_ceiling and apart from the frame, so neither it nor its shadow is in WR); the frame records
                  and our[] junk from the frame's presence (AR frames law, lib/Lib Frame.stk_transport across WR);
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR (same ly3 S3, memory m'), with the
                  entry's arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal, RELRO_IMG) and made
                  arodata_okP by ProgWorld.arodata_okP_of_S.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe (internal path)
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  This stage reads none of its
   facts at the entry (the run has no runtime premise; the frame shadow comes from FRAHC's bytes and mem_grows) and
   supplies it at the exit from AR.

   SECTION HYPOTHESES (each is ACtl.v's Section hypothesis of the same name and text; the top supplies it)
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a -- for the exit's arodata_okS.
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record, which kitmem_own6, frames_bounds, al_frames,
     kitmem_rng_frame_sh, kitmem_input_apart, ajournal_of_fsteps and ctl_rt_C_of_AR take.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the core's symbol record, which ctl_rt_C_of_AR takes.
   kitmem_input_apart's premise IMG_HI <= frame_addr ly3 6 pos is a Theorem Labs lane's PROVED, premise-free
     A.ProgWorld_Fs.ctl_frame_above_img (statement ProgWorld.ctl_frame_above_img_stmt, every class; files taken by
     path from a working branch 1d23ced37fd, a Theorem Labs lane 07:4xZ), cited by name (a4g_frame6_above_img).

   STAND-IN VALUES: reads no stand-in value (no ts_gp, pc_wrap_*, pc_stack_malloc, zero-shadow or 0x9fe18 / 0xa2878
   row is read by the run or used by this proof); ctl_rt_C_of_AR reads CtrlTSyms B, a Section hypothesis.

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier (ctrl's Seg/A4.v lib_rw_stk,
   bytes_at_nil, a4_our_addr and a4_exit are used inside the proof only).  The twin modules are loaded by absolute
   Require lines and written through CK11 / CK1b / CM05 / CO09 (the core's) and AK11 (ctrl's YK11); lib/Lib through
   LMem / LRegs / LFrame / LStep / LCells / LExecF.  Frame-route files of record in the closure (through Seg/A4F.v),
   blobs at the glue worktree HEAD e35bbb668b3: Seg/A4F.v 33af12fe190, Seg/A4.v d4483123111, SlotInv.v
   4cf85db229a, Seg/Tac_slot.v de02ff45188, Seg/Tac_fs.v 8bd492a660d, SlotModel.v 04dc7903221, AsanRT.v
   b67d26f8ec7 (mcs 30), AsanRTInv.v 2a8602e8526, Contract.v fa6fd478d9a, FrameAPI.v f6ffefa9bb4, MemNorm.v
   cb518fc0304.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (through CK11 / AK11) or Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/A4.v   -- hits only inside this header comment.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_A4: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.Img0 A.AsanRT A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP.
(* route (C): the cut's runtime conjunct, its producer from AR, the symbol record it takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorld_Fs A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.A4 A.Prog.Seg.A4F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module KM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.
Module SA4 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.A4.
Module SA4F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.A4F.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueA4.

(* ACtl.v's Section shape, restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A810e4 := (ACtlCutP.C_A810e4 B).
Local Notation C_A81400_at := (ACtlCutP.C_A81400_at B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).

(* ACtl.v's Section hypotheses this stage reads, same names and texts: the read-only span is image bytes
   (RELRO_IMG, for the exit's arodata_okS), the core's AR laws (LAWS) and symbol record (TFIB_SYMS, for
   ctl_rt_C_of_AR). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* The owned class-6 frame lies above the loaded image (the premise of KitMem.kitmem_input_apart): a Theorem Labs lane's
   proved ProgWorld_Fs.ctl_frame_above_img at class 6. *)
Lemma a4g_frame6_above_img : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  A.Prog.ImgBounds.IMG_HI <= Reusable.YG0f.frame_addr ly 6 pos.
Proof. intros ly S W mem md pos HAR Hin. exact (A.ProgWorld_Fs.ctl_frame_above_img B ly S W mem md 6 pos HAR Hin). Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_A4 : forall POST, CF POST (ix_cut C_A81400_at [0]) -> CF POST C_Jrel -> CF POST C_A810e4.
Proof.
  intros POST HX _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A810e4 (ACtlCutP.v:1121-1132); FRAHC's arithmetic prefix by position, its memory tail
     (the spill [A+304], the frame header words, the frame shadow, the saved registers and any later trailer) by
     shape. *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A810e4] in Hbody.
  destruct Hbody as (HP & HFRAH & Hnmax & R18 & R20 & R21 & R22 & R23 & R24 & R25 & Hinb & Hina).
  destruct HFRAH as (Asp & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA416 & HS4096 & HSapp & HFT).
  repeat match type of HFT with _ /\ _ => let H1 := fresh "HT" in destruct HFT as [H1 HFT] end.
  unfold ART.APPMEM_END in HSapp.
  (* G2: the owned class-6 frame, the entry's input, and the numeric facts of the run's premises. *)
  pose proof HJ as (HAR & _).
  destruct (KM.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & _ & Hfrceil & Hceilsp).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  rewrite Hfb6 in Hfrceil. unfold A.ACfn.LLVMF_STK in Hceilsp.
  pose proof Reusable.YCbq.asan_consts as (Hceil & _).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Happ6).
  rewrite Efr3, Hfb6 in Happ6.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ6.
  assert (Hfr8 : fr mod 8 = 0).
  { pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite Hfr32 in X.
    replace fr with ((4 * (fr / 32)) * 8) by lia. apply Z_mod_mult. }
  (* the frame's shadow base, linearly: 8 * Sfr fr = fr + 8 * ASAN_K (fr mod 8 = 0) *)
  assert (HSfrq : 8 * ACtlCutP.Sfr fr = fr + 8 * 2147450880).
  { unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K.
    pose proof (Z.mod_eq fr 8 ltac:(lia)) as X. rewrite Hfr8 in X. lia. }
  assert (HSlow : 2147450880 <= ACtlCutP.Sfr fr) by lia.
  assert (HShi : ACtlCutP.Sfr fr + 392 <= 0x10007fff8000) by lia.
  assert (HSpos : 0 <= ACtlCutP.Sfr fr) by lia.
  assert (HfrA' : fr + 4096 <= Asp) by lia.
  assert (HSA : ACtlCutP.Sfr fr + 392 <= Asp) by lia.
  assert (HA288 : Asp + 288 <= 2 ^ 64) by lia.
  assert (Hband : fr + 4096 <= ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 392 <= fr) by lia.
  assert (Happfr : forall a, fr <= a < fr + 4096 -> ART.app_mem a).
  { intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia. }
  (* the entry's input (ctl_base's lib pre and KitMem.kitmem_input_apart) *)
  pose proof HB as (Hpre & _).
  pose proof Hpre as (_ & _ & _ & _ & Hcase & _).
  assert (Hn : 0 <= ACtlCut.c_n cx < 2 ^ 26) by (destruct Hcase as [(E & _) | (H & _)]; lia).
  destruct (KM.kitmem_input_apart (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI cx [] ly3 S3 W3 mem3 md3 k
              LAWS HB HJ HF HP (a4g_frame6_above_img ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) HAR Hin6))
    as (Hlin & Hp0 & Hpceil & Hpfr & Hpband).
  rewrite Efr3, Hfb6 in Hpfr.
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpband.
  (* the run's register premises: the cut's rgv facts on the run's canonical map *)
  assert (E9 : Sem.reg_get regs3 9 = Z_to_bv 64 Asp) by exact Hr9.
  assert (E18 : Sem.reg_get regs3 18 = Z_to_bv 64 (-8)) by exact R18.
  assert (E19 : Sem.reg_get regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact Hr19.
  assert (E20 : Sem.reg_get regs3 20 = Z_to_bv 64 (-14)) by exact R20.
  assert (E21 : Sem.reg_get regs3 21 = Z_to_bv 64 fr) by exact R21.
  assert (E22 : Sem.reg_get regs3 22 = Z_to_bv 64 fr) by exact R22.
  assert (E23 : Sem.reg_get regs3 23 = Z_to_bv 64 (ACtlCut.c_p cx)) by exact R23.
  assert (E24 : Sem.reg_get regs3 24 = Z_to_bv 64 (ACtlCut.c_n cx)) by exact R24.
  assert (E25 : Sem.reg_get regs3 25 = Z_to_bv 64 (ACtlCutP.Sfr fr + 68)) by exact R25.
  (* the spill block [A + 16, A + 288): the LLVMF stack window, present by the journal *)
  assert (STsp : LFrame.stk A.Img0.rsegs mem3 (Asp + 16) (Asp + 288)).
  { eapply KM.kitmem_stk_of_journal; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  destruct (SA4.lib_rw_stk mem3 (Asp + 16) 272
              ltac:(change (Z.of_nat 272) with 272; replace (Asp + 16 + 272) with (Asp + 288) by lia; exact STsp))
    as (jsp & RWsp).
  (* the frame's shadow tail [S(fr) + 255, S(fr) + 392): present by the AR frames law *)
  assert (STsh : LFrame.stk A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 255) (ACtlCutP.Sfr fr + 392)).
  { apply (KM.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha.
    destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
      as (_ & _ & _ & Hsh).
    rewrite Efr3 in Hsh.
    assert (Hi : 0 <= a - ACtlCutP.Sfr fr < Reusable.YG00.fs_frame_bytes 6 / 8)
      by (rewrite Hfb6; change (4096 / 8) with 512; lia).
    destruct (Hsh _ Hi) as (Hpr & _).
    replace (Reusable.YG0f.shadow_addr fr + (a - ACtlCutP.Sfr fr)) with a in Hpr
      by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K;
          lia).
    exact Hpr. }
  destruct (SA4.lib_rw_stk mem3 (ACtlCutP.Sfr fr + 255) 137
              ltac:(change (Z.of_nat 137) with 137;
                    replace (ACtlCutP.Sfr fr + 255 + 137) with (ACtlCutP.Sfr fr + 392) by lia; exact STsh))
    as (jsh & RWsh).
  (* the run's other window: empty (its post is not used) *)
  assert (STnil : LFrame.stk A.Img0.rsegs mem3 0 0).
  { split; [lia|]. split; [lia|]. intros a Ha. lia. }
  (* the footprint ranges *)
  assert (Hrsh : LExecF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 255) 137).
  { apply (KM.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ _ HAR Hin6);
      rewrite Efr3; [unfold ACtlCutP.Sfr; lia | rewrite Hfb6; change (4096 / 8) with 512; unfold ACtlCutP.Sfr in *; lia]. }
  assert (Hrsp : LExecF.rng (PB.RNG_W (Reusable.YA0n.w_H W3)) (Asp + 16) 272).
  { eapply KM.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A810e4) with 0x810e4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x810e4) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  unfold LRegs.mkR_of.
  (* G4: the run at the cut's map, and the lift with the run's fsteps. *)
  pose proof (SA4F.a4_evt_F (PB.RNG_W (Reusable.YA0n.w_H W3))
    (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
    (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8)
    (Sem.reg_get regs3 9) (Sem.reg_get regs3 10) (Sem.reg_get regs3 11) (Sem.reg_get regs3 12)
    (Sem.reg_get regs3 13) (Sem.reg_get regs3 14) (Sem.reg_get regs3 15) (Sem.reg_get regs3 16)
    (Sem.reg_get regs3 17) (Sem.reg_get regs3 18) (Sem.reg_get regs3 19) (Sem.reg_get regs3 20)
    (Sem.reg_get regs3 21) (Sem.reg_get regs3 22) (Sem.reg_get regs3 23) (Sem.reg_get regs3 24)
    (Sem.reg_get regs3 25) (Sem.reg_get regs3 26) (Sem.reg_get regs3 27) (Sem.reg_get regs3 28)
    (Sem.reg_get regs3 29) (Sem.reg_get regs3 30) (Sem.reg_get regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 Asp (ACtlCutP.Sfr fr) (ACtlCut.c_n cx) fr fr 0 0 jsh jsp
    E9 E18 E19 E20 E21 E22 E24 E25 ltac:(lia) HSpos HSA HA288
    ltac:(destruct RWsh as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | exact Hb] | exact Hw])
    ltac:(destruct RWsp as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | exact Hb] | exact Hw])
    STnil STsh Hrsh Hrsp) as HRUN.
  change (@AK11.getr) with (@CK11.getr) in HRUN.
  change (@AK11.seg_rom) with (@CK11.seg_rom) in HRUN.
  apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HRUN
           (PB.fp_avoids_RNG_W _)).
  (* G5: the continuation, at the run's end state. *)
  intros ms' md' Hrun HQ Hsbm.
  destruct HQ as (R & pc' & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K26 & MU & WM & _ & _ & _ & Hbr).
  destruct Hbr as [(Hlt & Hpc & HX4) | (Hge & _ & _)]; [| exfalso; lia].
  unfold SA4.a4_exit in HX4. change (@AK11.getr) with (@CK11.getr) in HX4.
  destruct HX4 as (X1 & X7 & X11 & X12 & X13 & X14 & X18 & X21 & X23 & X24 & X27 & X28 & X29 & X30 & X31 &
    Xsh & Xfr16 & Xsel24 & X144 & X152 & X168 & Xdecl200 & Xfrag192 & X216 & X240 & X280 &
    X40 & X120 & X136 & X160 & X176 & X448 & X248 & X184 & X256 & X264 & X272 & Xfirst32).
  subst pc'.
  assert (Emem : ms_mem ms' = m') by (rewrite Ems; reflexivity).
  destruct (PW.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) _ _ _ Hrun (PB.fp_avoids_RNG_W _)) as (Hgrow0 & _).
  assert (Hgrow : CK1b.mem_grows mem3 m') by (rewrite <- Emem; exact Hgrow0).
  (* the write set WR = [S(fr) + 255, S(fr) + 392) u [A + 16, A + 288) *)
  assert (HOUT : forall x, (x < ACtlCutP.Sfr fr + 255 \/ ACtlCutP.Sfr fr + 392 <= x) ->
            (x < Asp + 16 \/ Asp + 288 <= x) ->
            LFrame.outside [(ACtlCutP.Sfr fr + 255, ACtlCutP.Sfr fr + 392); (Asp + 16, Asp + 288)] x).
  { intros x H1 H2. cbn [LFrame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (HIN : forall x,
            ~ LFrame.outside [(ACtlCutP.Sfr fr + 255, ACtlCutP.Sfr fr + 392); (Asp + 16, Asp + 288)] x ->
            (ACtlCutP.Sfr fr + 255 <= x < ACtlCutP.Sfr fr + 392) \/ (Asp + 16 <= x < Asp + 288)).
  { intros x Hx. destruct (KM.kitmem_not_outside _ x Hx) as (lo & hi & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [E | [E | []]]; injection E as <- <-; [left | right]; exact Hr. }
  (* the journal across the run (ProgWorld.ajournal_of_fsteps): the frame-shadow bytes are the owned class-6
     frame's shadow, the spill bytes lie in the LLVMF stack window *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                  (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx)
                  (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { rewrite <- Emem.
    eapply (PW.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx).
    2:{ exact Hrun. }
    { exact HJ. }
    { exact (PB.fp_avoids_RNG_W _). }
    { rewrite Emem. exact MU. }
    { exact Hsbm. }
    { intros a Ha Ho. destruct (HIN a Ho) as [Hr | Hr].
      - apply (KM.kitmem_awr_frame _ _ _ _ _ _ _ 6 (ACtlCut.c_fpos cx) fr a (eq_sym Efr3)).
        + left. reflexivity.
        + right. rewrite Hfb6. change (4096 / 8) with 512. unfold ACtlCutP.Sfr in Hr. lia.
      - apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia. } }
  (* ctl_rt_C at the exit (same ly3 S3, memory m'): ctl_rt_C_of_AR at the exit journal's AR, with the entry's
     arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal) *)
  assert (Hrt' : A.ACtlRtC.ctl_rt_C B ly3 S3 m').
  { pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
    pose proof HJ' as (HAR' & _).
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m' md' HAR'
             (PW.arodata_okP_of_S B RLO RHI RLO RHI _
                (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' HROS)
                (Z.le_refl _) (Z.le_refl _))). }
  (* the frame's bytes: present at the cut (AR frames law), not written by the run *)
  assert (Hfstk3 : LFrame.stk A.Img0.rsegs mem3 fr (fr + 4096)).
  { apply (KM.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha.
    destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
      as (_ & _ & Hfb & _).
    rewrite Efr3, Hfb6 in Hfb. exact (proj1 (Hfb a Ha)). }
  assert (Hfstk : LFrame.stk A.Img0.rsegs m' fr (fr + 4096)).
  { apply (LFrame.stk_transport _ _ mem3 m' fr (fr + 4096) Hfstk3 MU WM).
    intros x Hx. left. apply HOUT; lia. }
  assert (Hrec : forall o len, 0 <= o -> 0 <= len -> o + len <= 4096 ->
            exists bs, LStep.rw_cells A.Img0.rsegs m' (fr + o) [LCells.CB (Z.to_nat len) bs]).
  { intros o len H1 H2 H3. apply SA4.lib_rw_stk. rewrite Z2Nat.id by lia.
    destruct (LFrame.stk_split _ m' fr (fr + o) (fr + 4096) Hfstk ltac:(lia)) as (_ & X).
    destruct (LFrame.stk_split _ m' (fr + o) (fr + o + len) (fr + 4096) X ltac:(lia)) as (Y & _).
    exact Y. }
  (* the spills of the run, through register 9 = A *)
  assert (HR9' : ACtlCut.rgv R 9 Asp).
  { unfold ACtlCut.rgv. transitivity (Sem.reg_get regs3 9); [exact K9 | exact E9]. }
  assert (Hsp : forall off v, ACtlCutP.q64 m' (Asp + off) v -> ACtlCutP.spill R m' off v)
    by (intros off v Hq; exists Asp; split; [exact HR9' | exact Hq]).
  (* the input block: below alloc_ceiling and apart from the frame, so neither its bytes nor its shadow bytes are
     written *)
  assert (Hinb' : LMem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { apply (KM.kitmem_bytes_munch _ mem3 m' _ _ Hinb MU). intros x Hx. rewrite Hlin in Hx. apply HOUT; lia. }
  assert (Hina' : 0 < ACtlCut.c_n cx -> ART.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Hn0. apply (KM.kitmem_addressable_mrd mem3 m' _ _ (Hina Hn0)). intros i Hi.
    apply (KM.kitmem_mrd_munch _ mem3 m' _ MU).
    - unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia.
    - apply HOUT; unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia. }
  (* FRAC at the run's end memory and the cut's map, BY SHAPE: FRAHC's conjuncts (registers, arithmetic,
     memory words off WR moved by munch, the frame shadow rebuilt by growth, any later trailer word by munch)
     plus the two spills the run writes, [A + 24] = sel and [A + 16] = fr; then to the run's map by
     Kit.kit_frac_move (the run keeps registers 2 3 4 8 9 19 26). *)
  assert (HFRAC3 : ACtlCutP.FRAC B cx fr fr regs3 m').
  { pose proof (KM.kitmem_saved_len cx) as Hslen.
    assert (Q24 : ACtlCutP.q64 m' (Asp + 24) fr) by exact Xsel24.
    assert (Q16 : ACtlCutP.q64 m' (Asp + 16) fr) by exact Xfr16.
    unfold ACtlCutP.FRAC. exists Asp, sp.
    repeat (match goal with |- _ /\ _ => split end);
    first
      [ match goal with H : ?G |- ?G => exact H end
      | lazymatch goal with
        | |- ACtlCutP.q64 m' ?a ?v =>
            match goal with Hq : ACtlCutP.q64 mem3 a v |- _ =>
              apply (KM.kitmem_q64_munch _ mem3 m' a v Hq MU); intros ? ?; apply HOUT; lia end
        | |- LMem.bytes_at _ m' ?a ?bs =>
            match goal with Hb : LMem.bytes_at _ mem3 a bs |- _ =>
              apply (KM.kitmem_bytes_munch _ mem3 m' a bs Hb MU); intros ? ?; apply HOUT; lia end
        | |- exists sh, LMem.bytes_at _ m' ?lo sh /\ length sh = ?n =>
            match goal with Hx : exists sh, LMem.bytes_at _ mem3 lo sh /\ length sh = n |- _ =>
              let sh := fresh "sh" in let Hb := fresh "Hb" in let Hl := fresh "Hl" in
              let bs := fresh "bs" in let Hl2 := fresh "Hl" in let Hb2 := fresh "Hb" in
              let HNI := fresh "HNI" in
              destruct Hx as (sh & Hb & Hl);
              assert (HNI : forall x, lo <= x < lo + Z.of_nat (length sh) -> ~ Reusable.YG0d.in_img segs x)
                by (intros ? ?; apply KM.kitmem_not_img_hi; unfold A.Prog.ImgBounds.IMG_HI; lia);
              destruct (KM.kitmem_bytes_grow mem3 m' lo sh Hgrow Hb HNI) as (bs & Hl2 & Hb2);
              exists bs; split; [exact Hb2 | rewrite Hl2; exact Hl]
            end
        end ]. }
  assert (HFRAC : ACtlCutP.FRAC B cx fr fr R m').
  { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m' HFRAC3);
      match goal with |- CK11.getr R ?r = CK11.getr regs3 ?r =>
        transitivity (Sem.reg_get regs3 r); [assumption | reflexivity] end. }
  (* the exit cut ix_cut C_A81400_at [0] (ACtlCutP.v:1136-1158) at the run's end map R and memory m' *)
  rewrite Ems.
  refine (HX cx [0] fr k ly3 S3 W3 R m' md' HB HJ' HF HL Hk _ Hrt').
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81400_at ACtlCutP.ixz nth].
  split; [reflexivity|].
  split; [exact HP|].
  split; [exact HFRAC|].
  split; [lia|].
  split; [lia|].
  split; [unfold ACtlCut.rgv; rewrite Z.min_l by lia; rewrite Z.add_0_r, X23; exact E23|].
  split; [unfold ACtlCut.rgv; rewrite Z.min_l by lia; rewrite Z.sub_0_r, X24; exact E24|].
  split; [exact (SA4.bytes_at_nil m' (fr + 2624) ltac:(lia))|].
  split; [exact X21|]. split; [exact X28|].
  split; [exact (Hsp 152 (ACtlCutP.Sfr fr + 68) X152)|].
  split; [exact X18|].
  split.
  { (* PRO: the thirteen spills, our[]'s six bytes addressable by the shadow byte 6, the input facts *)
    unfold ACtlCutP.PRO.
    split; [exact (Hsp 40 (fr + 32) X40)|]. split; [exact (Hsp 120 (fr + 160) X120)|].
    split; [exact (Hsp 136 (fr + 128) X136)|]. split; [exact (Hsp 160 (fr + 528) X160)|].
    split; [exact (Hsp 168 (fr + 2624) X168)|]. split; [exact (Hsp 176 (fr + 64) X176)|].
    split; [exact (Hsp 208 (fr + 448) X448)|]. split; [exact (Hsp 248 (fr + 176) X248)|].
    split; [exact (SA4.a4_our_addr m' fr ltac:(lia) Hfr8 ltac:(unfold ART.APPMEM_END; lia)
                     (fun a Ha => Happfr a ltac:(lia)) Xsh)|].
    split; [exact Hinb'|].
    split; [exact Hina'|].
    split; [exact (Hsp 184 (fr + 336) X184)|]. split; [exact (Hsp 256 (fr + 256) X256)|].
    split; [exact (Hsp 264 (fr + 304) X264)|]. split; [exact (Hsp 272 (fr + 272) X272)|].
    exact (Hsp 32 (fr + 2880) Xfirst32). }
  split; [exact X7|]. split; [exact X1|]. split; [exact X11|]. split; [exact X12|]. split; [exact X13|].
  split; [exact X14|]. split; [exact X29|]. split; [exact X30|]. split; [exact X31|].
  split; [exact Xsh|]. split; [exact X27|].
  split; [exact (Hsp 144 (fr + 2688) X144)|]. split; [exact (Hsp 192 (fr + 2768) Xfrag192)|].
  split; [exact (Hrec 2688 38 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (Hrec 2768 72 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (Hsp 280 (fr + 3040) X280)|]. split; [exact (Hsp 240 (fr + 3056) X240)|].
  split; [exact (Hrec 3040 1 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (Hrec 3056 32 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (Hsp 200 (ACtlCutP.decl_slot fr) Xdecl200)|].
  split; [exact (Hsp 216 (fr + 2528) X216)|].
  (* our[]'s six frame bytes: present (frame bytes the run does not write) *)
  destruct (LFrame.stk_split _ m' fr (fr + 2624) (fr + 4096) Hfstk ltac:(lia)) as (_ & X).
  destruct (LFrame.stk_split _ m' (fr + 2624) (fr + 2630) (fr + 4096) X ltac:(lia)) as (Y & _).
  destruct (LFrame.stk_bytes _ m' (fr + 2624) (fr + 2630) Y ltac:(lia)) as (junk & Hjl & Hjb).
  exists junk. split; [rewrite Hjl; f_equal; lia | exact Hjb].
Qed.

End GlueA4.
