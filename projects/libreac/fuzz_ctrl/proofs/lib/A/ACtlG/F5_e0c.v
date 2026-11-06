(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module paths and module names changed; 197 of its 212 lines of code are new or changed and 544 lines of the source are left out. *)
(* lib/A/ACtlG/F5_e0c.v -- GLUE for stage seg_F5_e0c of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:755).  Written by a Theorem Labs lane; single writer.
   rule 24: no function proved (kind: segment lemma -- one glue stage of the entry walk).

   WHAT IT PROVES
     glue_seg_F5_e0c : forall POST (j : nat),
       CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F5_e0c (ACtl.v:572).  Segment F5_e0c is 0x81ea4 -> 0x81ea8, ONE instruction
     0x81ea4  sd zero,240(s1)
   on the long arm of the frame loop (the record is 50 bytes or more), which writes the 8-byte spill cell
   [s1 + 240] with 0; the cut's own flag for that cell is b2z (t_8819 j) and the entry cut carries
   t_8819 j = false, so the written word IS the exit cut's b5_sp 240 value and its b5_W240 witness.

   THE SHAPE OF THE STAGE (two steps, as the plain proof Seg/F5.v:1111-1230 is shaped)
   S1  the exit cut 0x81ea8 is reached from the stage's own premise, the loop head 0x81ec0, through the
       NEIGHBOUR stage seg_F5_e10 (ACtl.v:574): glue_seg_F5_e10 POST j HX : CF POST (ix_cut C_A81ea8_at [j]).
       (Seg/F5.v:1115 does exactly this with its seg_F5_e10.)
   S2  the 0x81ea4 run is lifted onto that, G1-G5 of the glue pattern
       (glue-pattern.md sections 2-4 and 6 (a working note, not in this delivery); worked example
       lib/A/ACtlG/A5.v):
     G1  unfold the entry cut: ix_cut's index equation, then C_A81ea4_at (ACtlCutP.v:2050-2060) = FRAC plus
         b5_body (:1042) plus the nine-conjunct exit predicate; `ixn 0 [Z.of_nat j]` becomes j by Nat2Z.id.
     G2  the run's premises FROM VISIBLE STATE, never from a hypothesis:
         - the spill base A (register 9) and 0 <= A < 2 ^ 64: A.ACtlG.F5_df0.f5g_frac_base of FRAC;
         - every numeric bound the keeps need (HIGHMEM_BEG <= A, A + 416 <= APPMEM_END, 0 <= fr,
           fr + FRAME_BYTES <= A, phi + a_size (flen j) <= A, c_p + |c_in| <= A, c_sp - LLVMF_STK <= A,
           A + 416 <= c_sp): A.ACtlG.F5_df0.f5g_bounds, from ctl_base, the journal, LAWS, FRAC and the
           live-block Permutation of b5_body;
         - `stk rsegs mem3 (A + 240) (A + 288)` and `rng (RNG_W (w_H W3)) (A + 240) 8`: the journal's stack
           window is apresent (YCbq.ajournal's 14th conjunct) over [c_sp - LLVMF_STK, c_sp), which contains
           [A + 240, A + 288) by the two bounds above; apresent gives BOTH the visibility (w_H W3 .. = false,
           hence A.ProgBridge.rng_of_visible) and the byte (hence wview / mrd, hence stk).
     G3  ProgBridge.cfg_at_MS puts the cut's configuration in the run's state form; the cut's map regs3 and the
         run's canonical mkR_of regs3 are only Regs6ss.xregs_eqv, so the WALK is moved by
         Reusable.YA0nR.SRr_xregs_eqv.
     G4  lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid (THE lift
         for a run that writes memory: its continuation also receives the hidden-byte equation that
         YCbq.ajournal_exec takes) at RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3), fp_avoids by
         A.ProgBridge.fp_avoids_RNG_W.
     G5  the continuation at MS R .. 0x81ea8 .. mem' with mem' = write_to_mem mem3 (wa (A + 240)) (le8 0):
         the write set is W := [(A + 240, A + 248)] (munch_write / wmono_write / all_app by Seg/F5.f5_app_ivl),
         and the exit cut C_A81ea8_at (ACtlCutP.v:2064-2074) is rebuilt conjunct by conjunct:
           journal   A.ACtlG.F5_df0.f5g_journal (ajournal_exec with Wr := ~ outside W); every written byte is
                     in the stack window because [A + 240, A + 248) is;
           ctl_rt_C  A.ACtlG.F5_df0.f5g_ctl_rt_C_keep at the entry cut's own ly3 S3 (the write is at or above
                     HIGHMEM_BEG <= A, so it misses the asan cells, every shadow byte and every read-only byte);
           frames / frame law / k   unchanged (own6 and the same kmax on both cuts);
           FRAC      A.ACtlG.F5_df0.f5g_frac_keep (its frame premise from A.ACtlG.F5_df0.f5g_frame_below);
           HB / FLSI / LK / b5_C / IDj   A.ACtlG.F5_e10.f5g_keep;
           b5_PF     A.ACtlG.F5_e10.f5g_pf_keep (its cells lie below A + 240);
           rgv 22 0 / 24 t_k / 25 (phi + 18)   kept registers, A.ACtlG.F5_e10.f5g_rgv;
           b5_sp 240 (b2z (t_8819 j))   t_8819 j = false, so the value is 0: the new cell, Mem.bytes_at_write_same;
           u32 (fr + 176) (t_k j)       Seg/F5.f5_u32_keep (fr + 180 < A + 240 by fr + FRAME_BYTES <= A);
           b5_F17    Seg/F5.f5_q64_keep at [A + 200] (its own spill base is FRAC's, by Seg/F5.f5_id);
           b5_W240   the new cell with w240 = 0 and t_8819 j = false.

   SECTION HYPOTHESES (exact text below; source of each)
   - LAWS: the core's AR law record (YCbq.v:207, Section a0's hypothesis), as ACtl.v:183 states it; f5g_bounds
     and f5g_journal take it.  ACtl.v discharges it in its section 9.
   - The other ACtl.v Section Ctl entries (RELRO_IMG, TFIB_SYMS, TFIB_LIB, XN_LIB, the two REAC_* variables)
     are copied verbatim from ACtl.v:167-194 and vanish at End Section (unused here).
   NO OTHER SECTION HYPOTHESIS: the file has no TEMP hypothesis left.
   CITED BY NAME, NOT HYPOTHESES: the neighbour stage A.ACtlG.F5_e10.glue_seg_F5_e10 (ACtl.v:574, Qed at
   F5_e10.v blob c3cee14887c, commit e970e657ceb); the shared lemmas A.ACtlG.F5_e10.f5g_keep / f5g_pf_keep /
   f5g_rgv and A.ACtlG.F5_df0.f5g_frac_base / f5g_bounds / f5g_frac_keep / f5g_ctl_rt_C_keep / f5g_journal
   (F5_df0.v blob ebef2f09a2a, commit dfda47419cd); the run A.Prog.Seg.F5F.seg_F5_e0c_run_F (F5F.v:218, blob
   336a376f81d on the base), instantiated at ctrl's FPState A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs
   lib.Reusable.YK11.fp_csr (glue-pattern.md section 6); the model facts A.Prog.Seg.F5.f5_id / f5_app_ivl /
   f5_q64_keep / f5_u32_keep; Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt_hid; A.ProgBridge.cfg_at_MS /
   fevt_of_evtF / tfibsegs_rsegs / RNG_W / fp_avoids_RNG_W / rng_of_visible;
   lib.Reusable.YK1b.write_to_mem_grows;
   lib/Lib's Frame / Mem write lemmas; A.ACtlG.Kit.kit_wx.

   THE TWO YK11 COPIES (a Theorem Labs lane's measured rule, 2026-10-29 04:2xZ): in a file that Requires A.ACtlCutP the
   unprefixed spelling of the core's YK11 resolves to CTRL's copy lib/A/Reusable/YK11.v, so the core's twins are written
   `lib.Reusable.X` (X in YI04 YI16 YK11 YK1b YM05 YO09) and ctrl's `A.Reusable.X` everywhere, and the core's
   copies are Required through `From ...lib.Reusable Require X.` (porter amendment 04:33Z).  The cut layer mixes
   the two (FRAC's registers 2 3 4 are ctrl's getr, ACtlCut.rgv is the core's): they are convertible, so this
   file moves facts between them with `exact` / `change`, never with `rewrite`.

   CLOSURE (the glue closure rule, a Theorem Labs lane 23:32Z): every project Require below is qualified (no Import / Export
   of a project module); no STATEMENT here names a frame-route identifier (Seg/F5.v, Seg/F5F.v are cited inside
   proofs only, and they are in the closure of Seg/F5F.v, which this file Requires).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / A.Reusable.YK11 / Reusable.YG0d-
   qualified everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F5_e0c.v   -- hits only inside comments.

   ROUTE (C) L3 (a Theorem Labs lane, 2026-10-29; recipe L3-recipe.md (a working note, not in this delivery)):
   ctl_from hands the stage Hrt : A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch's shell).  The stage never opens Hrt
   (no destruct, no use of a shadow part): its one use is the exit, which keeps the state (the exit cut is applied
   at the same ly3 S3), so ctl_rt_C B ly3 S3 mem' is kept across the one write by A.ACtlG.F5_df0.f5g_ctl_rt_C_keep
   (both shadow parts by A.ShadowRwOnK.fl_shadow_rw_on).  No VIS0 / OWNED_RO / AR_VIS0 / AR_OWNED_RO hypothesis
   and no stage-level ctlrt_of_AR.  The run's contract takes no mem_inv premise.

   BUILD STATE: type-check with cb build --fresh (BASE 23b918fe0c2e) on a working branch 1899bed1aee merged with
   a working branch; the lane report names the build log, the .vo mtime and Print Assumptions of
   glue_seg_F5_e0c (Rocq primitives and functional_extensionality_dep only).  No Axiom, no Parameter, no Admitted,
   no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACfn A.ACtlK A.AF0m A.ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F5 A.Prog.Seg.F5F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.F5_e10 A.ACtlG.F5_df0.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF5e0c.

(* ACtl.v's Section Ctl shape (ACtl.v:170-194), verbatim; the unused entries vanish at End Section. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* ACtl.v's notation block (ACtl.v:213, :217-218 and the C_* lines :269-271), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ea4_at := (ACtlCutP.C_A81ea4_at B).
Local Notation C_A81ea8_at := (ACtlCutP.C_A81ea8_at B).
Local Notation C_A81ec0_at := (ACtlCutP.C_A81ec0_at B).

(* The neighbour stage 0x81ea8 -> 0x81ec0 is A.ACtlG.F5_e10.glue_seg_F5_e10 (ACtl.v:574), Qed at
   lib/A/ACtlG/F5_e10.v blob c3cee14887c (commit e970e657ceb); it is cited by name in the proof below. *)

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F5_e0c : forall POST (j : nat), CF POST (ix_cut C_A81ec0_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ea4_at [Z.of_nat j]).
Proof.
  intros POST j HX.
  (* S1: the exit cut 0x81ea8, from the stage's own premise through the neighbour stage *)
  pose proof (A.ACtlG.F5_e10.glue_seg_F5_e10 B MT XM_LIB RLO RHI LAWS POST j HX) as Hea8.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A81ea4_at, ACtlCutP.v:2050-2060) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ea4_at ACtlCutP.b5_body ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & HPerm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & Hlen50 & R22 & R24 & R25 &
    H8819 & Hu32 & HID & HF17 & HPF).
  (* the numeric constants the bounds are read with *)
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HKh : A.AsanRT.HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKa : A.AsanRT.APPMEM_END = 140737488355328) by reflexivity.
  assert (HFB : ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  (* G2: the spill base and every numeric bound, from visible state *)
  destruct (A.ACtlG.F5_df0.f5g_frac_base B cx fr fr regs3 mem3 HFRAC) as (Asp & R9 & HAr).
  destruct (A.ACtlG.F5_df0.f5g_bounds B MT XM_LIB RLO RHI cx _ ly3 S3 W3 mem3 md3 k fr fr Asp phi j regs3
              LAWS Hbase HJ HFRAC R9 HAr HPerm)
    as (HAhi & HAapp & Hfr0 & HfrA & HphiA & HpA & HspA & HAsp416).
  (* the whole class-6 frame lies below the spill base (f5g_frac_keep's frame premise): the journal's frame, the
     frame law, astk_ok and FRAC, through A.ACtlG.F5_df0.f5g_frame_below *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr6 : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  pose proof (A.ACtlG.F5_df0.f5g_frame_below B cx _ ly3 S3 W3 mem3 md3 k fr fr Asp regs3 LAWS HJ Hin6 Efr6 HFRAC
                R9 HAr) as Hfr6.
  (* the journal's stack window is apresent in mem3 (YCbq.ajournal's 14th conjunct) *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (HSTK : lib.Lib.Frame.stk A.Img0.rsegs mem3 (Asp + 240) (Asp + 288)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as (Hvis & b & Hbb).
    split.
    - unfold wview, lib.Lib.Mem.wa. rewrite Hbb. cbn. discriminate.
    - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  assert (HRNG : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Asp + 240) 8).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81ea4_at [Z.of_nat j])) with 0x81ea4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81ea4) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3
           (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run (F5F.v:218) at ctrl's FPState instance, then the lift for a run that writes memory *)
  pose proof (@A.Prog.Seg.F5F.seg_F5_e0c_run_F
                (A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr)
                regs3 mem3 Asp (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) R9 HSTK HRNG) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
           (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
  (* G5: the continuation at the run's end state *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K23 & K18 & K24 &
    K25 & K22 & Hmem).
  subst ms' pc'.
  (* the run's register facts, read in the CORE's getr (they are ctrl's; the two copies are convertible) *)
  assert (C2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact K2.
  assert (C3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact K3.
  assert (C4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact K4.
  assert (C8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact K8.
  assert (C9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
  assert (C19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact K19.
  assert (C21 : lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) by exact K21.
  assert (C26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact K26.
  assert (C23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by exact K23.
  assert (C18 : lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18) by exact K18.
  assert (C24 : lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24) by exact K24.
  assert (C25 : lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) by exact K25.
  assert (C22 : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by exact K22.
  (* the write set of this run: the one spill cell [A + 240, A + 248) *)
  assert (HWout1 : forall x, x < Asp + 240 -> lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HWout2 : forall x, Asp + 248 <= x < Asp + 280 -> lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HWout3 : forall x, Asp + 288 <= x -> lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
  assert (HWlow : forall x, x < A.AsanRT.HIGHMEM_BEG -> lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x)
    by (intros x Hx; apply HWout1; lia).
  assert (MU : lib.Lib.Frame.munch [(Asp + 240, Asp + 248)] mem3 mem').
  { rewrite Hmem.
    apply (lib.Lib.Frame.munch_write [(Asp + 240, Asp + 248)] mem3 mem3 (Asp + 240)
             (lib.Lib.Mem.le8 (Z_to_bv 64 0)));
      [ apply lib.Lib.Frame.munch_refl | lia
      | rewrite lib.Lib.Mem.length_le8; lia
      | rewrite lib.Lib.Mem.length_le8; cbn [lib.Lib.Frame.inside]; left; lia ]. }
  assert (WM : lib.Lib.Frame.wmono A.Img0.rsegs mem3 mem').
  { rewrite Hmem. apply lib.Lib.Frame.wmono_write. apply lib.Lib.Frame.wmono_refl. }
  assert (HAW : A.AsanRTFacts.all_app [(Asp + 240, Asp + 248)]).
  { cbn [A.AsanRTFacts.all_app]. split; [apply A.Prog.Seg.F5.f5_app_ivl; lia | exact I]. }
  assert (Hq240 : ACtlCutP.q64 mem' (Asp + 240) 0).
  { rewrite Hmem. unfold ACtlCutP.q64.
    apply lib.Lib.Mem.bytes_at_write_same; [lia | rewrite lib.Lib.Mem.length_le8; lia]. }
  (* the carried bundles across the write *)
  destruct (A.ACtlG.F5_e10.f5g_keep cx j phi fr Asp regs3 R mem3 mem' [(Asp + 240, Asp + 248)]
              HHB HFLSI HLK HC HID R9 HAhi HAapp HfrA HphiA HpA MU WM HAW HWout1 HWout2 C2 C9 C18 C21 C23)
    as (HHB' & HFLSI' & HLK' & HC' & HID').
  pose proof (A.ACtlG.F5_e10.f5g_pf_keep cx j phi fr Asp regs3 R mem3 mem' [(Asp + 240, Asp + 248)]
                HPF R9 HAhi HAapp Hfr0 HfrA HphiA MU HAW HWout1 C9) as HPF'.
  (* b5_F17's own spill base is FRAC's: both name register 9 and both are below 2 ^ 64 *)
  pose proof HF17 as (A7 & H97 & HA7 & Hq7).
  assert (EA7 : A7 = Asp).
  { apply A.Prog.Seg.F5.f5_id; [exact HA7 | lia |].
    transitivity (lib.Reusable.YK11.getr regs3 9); [symmetry; exact H97 | exact R9]. }
  subst A7.
  (* Seg/F5.v's keeps are stated over its own copy of the frame vocabulary (lib/A/Tk/UL/Frame.v, the same
     text as lib/Lib/Frame.v): the write set is given explicitly so the two copies meet by conversion. *)
  assert (Hout200 : forall x, Asp + 200 <= x < Asp + 200 + 8 ->
            lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x) by (intros x Hx; apply HWout1; lia).
  pose proof (A.Prog.Seg.F5.f5_q64_keep [(Asp + 240, Asp + 248)] mem3 mem' (Asp + 200) (phi + 18)
                Hq7 MU Hout200) as Hq200.
  assert (Hout176 : forall x, fr + 176 <= x < fr + 176 + 4 ->
            lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] x) by (intros x Hx; apply HWout1; lia).
  pose proof (A.Prog.Seg.F5.f5_u32_keep [(Asp + 240, Asp + 248)] mem3 mem' (fr + 176)
                (A.Prog.SlotModel.t_k (ACtlCut.c_in cx) j) Hu32 MU Hout176) as Hu32'.
  (* the long arm took the 0x81ea4 edge, so the model flag of [A + 240] is false *)
  assert (E240 : A.Prog.SlotModel.b2z (A.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j) = 0)
    by (rewrite H8819; reflexivity).
  (* every byte this run writes lies in the journal's stack window *)
  assert (HJW : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside [(Asp + 240, Asp + 248)] a ->
                  ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < ACtlCut.c_sp cx).
  { intros a Ha Hin.
    destruct (Z_le_gt_dec (Asp + 240) a) as [L1|L1];
      [| exfalso; apply Hin; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]].
    destruct (Z_lt_le_dec a (Asp + 248)) as [L2|L2];
      [| exfalso; apply Hin; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]].
    lia. }
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81ea8_at [Z.of_nat j])) R mem' md')
            (POST cx)).
  apply (Hea8 cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' Hbase).
  - (* the journal across the write (ajournal_exec with Wr := ~ outside W) *)
    eapply A.ACtlG.F5_df0.f5g_journal.
    + exact LAWS.
    + exact HJ.
    + exact MU.
    + rewrite Hmem. apply lib.Reusable.YK1b.write_to_mem_grows.
    + exact Hhid.
    + exact Hsbm.
    + exact HJW.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax on both cuts *)
    exact Hk.
  - (* the exit body, C_A81ea8_at (ACtlCutP.v:2064-2074), at the same turn j *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81ea8_at ACtlCutP.b5_body
      ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    split.
    { exact (A.ACtlG.F5_df0.f5g_frac_keep B cx fr fr Asp regs3 R mem3 mem' [(Asp + 240, Asp + 248)]
               HFRAC R9 HAhi Hfr6 MU HWout1 HWout3 C2 C3 C4 C8 C9 C19 C26). }
    exists phi.
    split; [exact HPerm|].
    split; [exact Hcn|].
    split; [exact Hj255|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C22 R22)|].
    split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C24 R24)|].
    split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C25 R25)|].
    rewrite E240.
    (* b5_sp 240: the cell the 0x81ea4 store wrote, with t_8819 j = false *)
    split.
    { exists Asp. split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C9 R9)|].
      split; [exact HAr | exact Hq240]. }
    split; [exact Hu32'|].
    split; [exact HID'|].
    (* b5_F17: F4's [A + 200] word, missed by the 0x81ea4 store *)
    split.
    { exists Asp. split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C9 R9)|].
      split; [exact HAr | exact Hq200]. }
    (* b5_W240: that store's 0, with t_8819 j = false *)
    split.
    { exists Asp. split; [exact (A.ACtlG.F5_e10.f5g_rgv regs3 R _ _ C9 R9)|].
      split; [exact HAr|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819 in E; discriminate | intros _; reflexivity]. }
    exact HPF'.
  - (* ctl_rt_C at the same ly3 S3: the write is at or above HIGHMEM_BEG <= A *)
    exact (A.ACtlG.F5_df0.f5g_ctl_rt_C_keep B ly3 S3 mem3 mem' [(Asp + 240, Asp + 248)] Hrt MU WM HWlow).
Qed.

End GlueF5e0c.
