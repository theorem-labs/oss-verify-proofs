(* lib/A/ACtlG/A5.v -- GLUE for stage seg_A5 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:657):
   the pilot of the glue pattern (brief glue-pilot.md (a working note, not in this delivery); the pattern
   for the other 93 lanes is glue-pattern.md (a working note, not in this delivery)).  Written by
   a Theorem Labs lane; single writer.  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_A5 : forall POST (t : Z), CF POST C_A81414 -> CF POST (ix_cut C_A81400_at [t])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_A5.  Segment A5 is 0x81400 -> 0x81414, five register-only instructions (Seg/A5.v:2-7 at e8259d2f41e):
     0x81400 mv s6,s7   0x81404 add a4,a4,a1   0x81408 addi a1,a1,1   0x8140c mv a0,a4   0x81410 mv s9,s8.

   RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28 20:16:23Z
   from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM: the released ASan
   donor is cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e; its walk lifts no outside-proved run (all its
   runs are symbolic), so this glue has no donor counterpart.  Its pieces are the donor's: SRr (YA0n), the journal
   lemma ajournal_exec (YCbq.v:636 in the planning core), frames_bounds (YCbq.v:450), and a Theorem Labs lane's kit and
   bridge (Reusable/YA0nR.v SRr_xregs_eqv / SRr_fevt at a working branch 5f2500c036a; A/ProgBridge.v
   fevt_of_evtF, tfibsegs_rsegs, cfg_at_MS, same blob at 94d4995b31f and 5f2500c036a; type-checked there on the
   planning core).

   THE PROOF, step by step (glue-pattern.md section 3 repeats it as the template)
   G1  unfold the entry cut: ix_cut's index equation, then C_A81400_at's 34 conjuncts (ACtlCutP.v:1137-1155).
   G2  the run's premises from the body: a1 = t (R11), a4 = fr + 2624 (R14), 0 <= t (Ht); the two numeric bounds
       from VISIBLE state, never from a hypothesis: 4096 <= fr from the journal's frame (frames_bounds on the AR of
       the journal, the shell's frame law fr = frame_addr (c_ly cx) 6 (c_fpos cx), and layout_le's ly_F equation),
       and fr + 2630 < 2 ^ 64 from FRAC (fr + FRAME_BYTES <= A <= c_sp cx < APPMEM_END).
   G3  register maps: one rewrite with ProgBridge.cfg_at_MS turns the cut's cfg_at into
       MS regs3 fp_regs 0x81400 fp_csr None mem3 (seg_rom segs); the _F run starts at MS (mkR_of regs3) ..., and
       the two maps are only Regs6ss.xregs_eqv, so the WALK is moved to the run's start by
       Reusable.YA0nR.SRr_xregs_eqv (R := mkR_of regs3, R' := regs3, proof xregs_eqv_sym (mkR_of_eqv regs3)).
   G4  lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs (the run is over Img0.rsegs, the cut over the core's
       tfibsegs), then YA0nR.SRr_fevt at the EMPTY footprint (the run reads and writes no memory, so fp_avoids is
       vacuous and no visibility fact is needed).
   G5  the continuation: the end state is MS R fp_regs 0x81414 fp_csr None mem3 (seg_rom segs), R the run's own end
       map; cfg_at_MS read backwards makes it the exit cut's configuration at regs := R; then the exit cut's
       ctl_from at the same cx, fr, k, ly3, S3, W3, mem3, the map R and the materialized model md':
         journal  ajournal_exec with the empty write set (memory is unchanged, but the model is materialized, so
                  the journal still needs this lemma, and with it the core's LAWS and segs_low);
         frames, frame law, k bound   unchanged (exact: own6 and kmax 0 on both cuts);
         body     memory conjuncts unchanged; register conjuncts through the run's K; FRAC through its seven
                  registers (Kit.kit_frac_move); spills through register 9 (s1);
         ctl_rt   unchanged (same memory).

   SECTION HYPOTHESES (exact text below; source of each)
   - seg_A5_run_F: the _F run.  COPIED from lib/A/Prog/Seg/Tac_slotF.v (not in this delivery) (seg_A5_run_F) at
     a working branch df036f892c5: its start state (MS (Regs6ss.mkR_of regs) fp_regs 0x81400
     fp_csr None mem (seg_rom rsegs)), its post shape (exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem'
     (seg_rom rsegs) /\ K), and its conclusion ExecF.evtF rsegs RNG.  ADAPTED, as a mechanical v1.9 re-run is:
     (a) RNG is the FIRST binder (a Theorem Labs lane's re-run convention, a Theorem Labs lane's A2F.v; a Theorem Labs lane a3d847b56c1);
     (b) K is v1.9's: Tac_slotF's K is the v1.8 one (its exit cut was FRA alone, Tac_slot.v:558-561), which keeps
         only registers 2 3 4 8 9 19 26 and so cannot rebuild the v1.9 exit body; the K here is the K that v1.9's
         seg_A5 gives sl_run (Seg/A5.v (not in this delivery) at a working branch e8259d2f41e), written with
         a5_evt's ou (Seg/A5.v (not in this delivery)) where Seg/A5.v (not in this delivery) writes fr + 2624;
     (c) a5_evt's five premises (Seg/A5.v:40: a1 = t, a4 = ou, 0 <= t, 0 <= ou, ou + t + 1 < 2 ^ 64), stated on the
         register map, which the v1.9 K needs (it names t and ou);
     (d) names qualified to this unit's vocabulary: MS -> Lib.MState.MS; getr / fp_regs / fp_csr / seg_rom ->
         Reusable.YK11.* (Tac_slotF's are lib/A/Reusable/YK11's: same bodies, a different FPState class, see
         glue-pattern.md section 6); rsegs -> A.Img0.rsegs; footprint / evtF -> Lib.ExecF.*.
     TRUE AS STATED: it is a5_evt (proved, Seg/A5.v (not in this delivery)) run under StepF plus the evt_mono step of
     Seg/A5.v (not in this delivery).  DISCHARGE when a Theorem Labs lane's v1.9 re-run of a5_evt lands: Lib.ExecF.evtF_mono over
     a5_evt_F at ou := ..., t := ..., with the post step of Seg/A5.v (not in this delivery) (glue-pattern.md section 6 (a working note, not in this delivery)).
   - LAWS: the core's AR law record, the Section hypothesis of the core's YCbq Section a0 (YCbq.v:207) that
     ajournal_exec and frames_bounds take; the donor's walk takes it the same way (A/ACfj.v:99, A/ACf2.v:47).  NOT in
     the brief's list: the journal must cross the run's model materialization and the frame bound comes from the
     AR, and both lemmas are stated under LAWS.  ACtl.v discharges it where it discharges the donor-form laws.
   CITED BY NAME, NOT HYPOTHESES (a Theorem Labs lane 23:4xZ / 00:2xZ: use a Theorem Labs lane's landed names): SRr_fevt and
   SRr_xregs_eqv are Reusable.YA0nR's (YA0nR.v:38 and :119, PROVED at a working branch 5f2500c036a,
   lemmas in 6517e7b00a9, build 20261029T001125Z rc=0); fevt_of_evtF, tfibsegs_rsegs and cfg_at_MS are
   A.ProgBridge's (ProgBridge.v:29-31, :75-76, :80-83).
   NOT USED: rt_of_core (ctl_RT): the run has no runtime premise.

   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied; its header says which helper serves
   which step): Kit.kit_wx and Kit.kit_segs_low (the image facts SRr_fevt and ajournal_exec take),
   Kit.kit_frac_move (FRAC along a map that keeps its seven registers) and Kit.kit_RNG0 (the empty footprint).

   CLOSURE (the glue closure rule, a Theorem Labs lane 23:32Z, FINAL with the porter 23:38Z / 23:40Z): every Require below is
   qualified (no Import / Export of a project module); no statement here names a frame-route identifier; the
   measured transitive closure, with a blob per file, is the last section of glue-pattern.md (a working note, not in this delivery).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 / Reusable.YG0d-qualified everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/A5.v   -- hits only inside comments.

   BUILD STATE (honest): TYPECHECKS on the image-A PLANNING core 5a85b67a5d8 (TYPE-CHECK ONLY, values do not count):
   cb build on the packed fuzz_ctrl base 362baf478bf5 (FACTS ed6b6b7b0ab), with the core's undefined
   port_core_refused_<hex> names replaced by the hex literal in the build workspace only (core errors, reported
   to the porter a Theorem Labs lane).  lib/Reusable/YK04R.v, lib/Reusable/YA0nR.v and lib/A/ProgBridge.v are on this
   branch BY PATH from a working branch 5f2500c036a (a Theorem Labs lane's, unchanged).  One fix at the
   first build: the fp_avoids step named its hypothesis Hn, already taken by G1's destruct.  No Axiom, no
   Parameter, no Admitted, no admit; seg_A5_run_F and LAWS stay Section hypotheses. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YC5d YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 AsanRT ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:155 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueA5.

(* ACtl.v's Section shape (ACtl.v:162-166), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:187, :191-192, :201-202), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81400_at := (ACtlCutP.C_A81400_at B).
Local Notation C_A81414 := (ACtlCutP.C_A81414 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The _F run of segment A5 (Tac_slotF.v:45-52, adapted as the header says). *)
Hypothesis seg_A5_run_F :
  forall (RNG : Lib.ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (ou t : Z),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 t -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 14 = Z_to_bv 64 ou ->
  0 <= t -> 0 <= ou -> ou + t + 1 < 2 ^ 64 ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms => exists R pc' mem',
       ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs pc' OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem'
              (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
       (pc' = Z_to_bv 64 0x81414 /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 1 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 1 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 7 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 7 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 12 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 12 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 13 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 13 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 27 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 27 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 28 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 28 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 29 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 29 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 30 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 30 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 31 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 31 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (ou + t) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 (t + 1) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 14 = Z_to_bv 64 (ou + t)))
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81400) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs)).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_A5 : forall POST (t : Z), CF POST C_A81414 -> CF POST (ix_cut C_A81400_at [t]).
Proof.
  intros POST t HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [t] (ix_cut, ACtlCut.v:215-217; C_A81400_at, ACtlCutP.v:1133-1155). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81400_at ACtlCutP.ixz nth] in Hb.
  destruct Hb as (HP & HFRAC & Hn & Ht & R23 & R24 & HOURt & R21 & R28 & S152 & R18 & HPRO & R7 & R1 & R11 &
    R12 & R13 & R14 & R29 & R30 & R31 & Hsh328 & R27 & S144 & S192 & Hid & Hjk72 & S280 & S240 & Hjy & Hjk32 &
    S200 & S216 & Hour).
  (* G2: the run's numeric premises, from visible state. *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Hfr4096 : 4096 <= fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. exact Hf4096. }
  pose proof HFRAC as (Asp & sp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAS & _ & HfrA & _ & _ & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  assert (Hb64 : fr + 2624 + t + 1 < 2 ^ 64) by lia.
  (* G3: the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl), then the walk moved from
     the cut's register map regs3 to the run's canonical one, mkR_of regs3 (YA0nR.SRr_xregs_eqv). *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81400_at [t])) with 0x81400.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81400) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the lift (the run is over Img0.rsegs, the cut over tfibsegs: ProgBridge.tfibsegs_rsegs). *)
  pose proof (seg_A5_run_F A.ACtlG.Kit.kit_RNG0 regs3 mem3 (fr + 2624) t R11 R14 (proj1 Ht) ltac:(lia) Hb64)
    as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
  { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
  (* G5: the continuation, at the run's end state MS R .. 0x81414 .. mem3: R is the run's own end map, so the exit
     cut is taken at regs := R and every register fact of the run's post is a fact of the cut's map. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K1 & K7 & K12 & K13 &
    K18 & K21 & K27 & K28 & K29 & K30 & K31 & K22 & K25 & K10 & K11 & K14).
  subst ms' pc' mem'.
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81414) R mem3 md') (POST cx)).
  assert (Hsp : forall off v, ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R mem3 off v).
  { intros off v (Ab & HAb & Hq). exists Ab. split; [|exact Hq].
    unfold ACtlCut.rgv in *. rewrite K9. exact HAb. }
  apply (HX cx [] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643, as YCbq.v:2236 calls it) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 0 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81414 (ACtlCutP.v:1159-1181), at the same turn t *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A81414].
    exists t.
    split; [exact HP|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hn|]. split; [exact Ht|].
    split; [unfold ACtlCut.rgv; rewrite K1; exact R1|].
    split; [unfold ACtlCut.rgv; rewrite K7; exact R7|].
    split; [unfold ACtlCut.rgv; exact K10|].
    split; [unfold ACtlCut.rgv; exact K11|].
    split; [unfold ACtlCut.rgv; rewrite K12; exact R12|].
    split; [unfold ACtlCut.rgv; rewrite K13; exact R13|].
    split; [unfold ACtlCut.rgv; exact K14|].
    split; [unfold ACtlCut.rgv; rewrite K18; exact R18|].
    split; [unfold ACtlCut.rgv; rewrite K21; exact R21|].
    split; [unfold ACtlCut.rgv; rewrite K22; exact R23|].
    split; [unfold ACtlCut.rgv; rewrite K25; exact R24|].
    split; [unfold ACtlCut.rgv; rewrite K28; exact R28|].
    split; [unfold ACtlCut.rgv; rewrite K29; exact R29|].
    split; [unfold ACtlCut.rgv; rewrite K30; exact R30|].
    split; [unfold ACtlCut.rgv; rewrite K31; exact R31|].
    split; [exact (Hsp _ _ S152)|].
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
        P184 & P256 & P264 & P272 & P32).
      exact (conj (Hsp _ _ P40) (conj (Hsp _ _ P120) (conj (Hsp _ _ P136) (conj (Hsp _ _ P160)
        (conj (Hsp _ _ P168) (conj (Hsp _ _ P176) (conj (Hsp _ _ P208) (conj (Hsp _ _ P248)
        (conj Pad (conj Pin (conj Pg (conj (Hsp _ _ P184) (conj (Hsp _ _ P256) (conj (Hsp _ _ P264)
        (conj (Hsp _ _ P272) (Hsp _ _ P32)))))))))))))))). }
    split; [exact Hsh328|].
    split; [unfold ACtlCut.rgv; rewrite K27; exact R27|].
    split; [exact (Hsp _ _ S144)|]. split; [exact (Hsp _ _ S192)|].
    split; [exact Hid|]. split; [exact Hjk72|].
    split; [exact (Hsp _ _ S280)|]. split; [exact (Hsp _ _ S240)|].
    split; [exact Hjy|]. split; [exact Hjk32|].
    split; [exact (Hsp _ _ S200)|]. split; [exact (Hsp _ _ S216)|].
    exact Hour.
  - (* ctl_rt: the memory is the entry cut's *)
    exact Hrt.
Qed.

End GlueA5.
