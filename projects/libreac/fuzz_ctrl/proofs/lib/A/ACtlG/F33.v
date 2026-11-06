(* lib/A/ACtlG/F33.v -- GLUE for stage seg_F33 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v (at head lib/A/ACtl.v:845),
   which carries a Theorem Labs lane's Batch3 (from a working branch d36efc6152d, through the glue base from a working branch 8ee48574229); the statement is
   unchanged since 1633437e8f0).  Written by a Theorem Labs lane,
   re-fitted to Batch3 by a Theorem Labs lane; single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (G1-G5), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (stage glue of a walk from an already-proved segment run through the proved bridge).

   WHAT IT PROVES
     glue_seg_F33 : forall POST (j : nat),
       CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat 0]) -> CF POST (ix_cut C_A828bc_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A8285c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): exactly ACtl.v's Section hypothesis
   seg_F33.  ENTRY C_A8285c_at [j] (ACtlCutP.v:2786); EXITS C_A8286c_at [j; 0] (the row loop head at row 0,
   ACtlCutP.v:2803) and C_A828bc_at [j] (the target of both branches; not reached, as in Seg/F33.v:193, because the
   entry body pins a0 = BOX_CATALOGUE <> 0 and the count word 11 <> 0).  Segment F33 is 0x8285c -> 0x8286c:
     0x8285c beqz a0,828bc (not taken)  0x82860 ld s8,0(s8)  0x82864 beqz s8,828bc (not taken)  0x82868 mv s4,a0.

   THE RUN: lib/A/Prog/Seg/F33F.v f33_evt_F (blob 5cb4d3d5dd2 at 1633437e8f0; this worker's mechanical re-run of
   f33_evt of Seg/F33.v 392fed23960 (the blob this tree had at release c5e779efe8c)), Required qualified.  It takes no callee contract and no Section
   hypothesis; its one footprint premise is the count-word load's own access `acc_in RNG (wa c, 8)`.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j]: ix_cut's index equation, then C_A8285c_at's conjuncts (phi, the live list,
       FRAC, c_n, j <= 255, HB, FLSI, LK, FLSX, t_rowsel, a0 = BOX_CATALOGUE, s8 = fr + 32, the count word 11 at
       fr + 32, LT); ixn 0 [Z.of_nat j] is Z.to_nat (Z.of_nat j) = j (Nat2Z.id).
   G2  the run's premises: a0 and s8 from the body's rgv conjuncts; the load's 8 bytes from the body's q64 by
       Lib.Mem.bytes_at_ov_read; the footprint: RNG := ProgBridge.RNG_W (w_H W3), and the access lies in the class-6
       frame [fr, fr + 4096), visible by a Theorem Labs lane's ProgWorldVisFrame.frame_vis (AR_frames_law) at the journal's
       AR, with frame_addr ly3 6 (c_fpos cx) = fr from the shell's frame law and layout_le's ly_F equation (A5's G2).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt at RNG_W (w_H W3): the run reads one frame word and writes no
       memory; fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the run's end state is MS R .. 0x8286c .. mem3 with R the run's explicit map (s4 = s10 = BOX_CATALOGUE,
       s8 = 11, every other register regs3's): the exit cut C_A8286c_at [j; 0] is taken there.  Journal:
       ajournal_exec with the empty write set (memory unchanged, model materialized); frames / frame law / k bound
       unchanged (own6, the same kmax 14 + 2 j + 1 on both cuts); body: memory conjuncts unchanged, FRAC through
       Kit.kit_frac_move, FLSI / LK / FLSX / LT along registers 9 18 21 22 23 25 (the local *_move lemmas below),
       RL at row 0 (s4 = CAT + CAT_ROW * 0, s8 = CAT_N - 0, no earlier row); ctl_rt_C unchanged.

   ROUTE (C) (L3; ACtlCut.v (at head lib/A/ACtlCut.v:243); the walk shell from a working branch 8ce82d7e310): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3).  This stage reads no shadow byte and keeps ly3, S3 and
   the memory, so its exit passes the entry's Hrt as it is; the Section never had VIS0 / OWNED_RO.

   FRAC AND BATCH3'S TRAILER WORD.  This stage PRODUCES FRAC at its exit C_A8286c_at [j; 0], and since Batch3
   (a Theorem Labs lane, d36efc6152d) FRAC's last conjunct is the fake-frame trailer word
   `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))` (ACtlCutP.v (at head lib/A/ACtlCutP.v:1078)).  The run writes no memory and the exit
   memory is the entry's mem3, so the entry body's FRAC, trailer word included, is the exit's at the same memory:
   Kit.kit_frac_move moves it along the register change only (its unfolding rewrites registers and keeps every
   memory conjunct as it is).  No positional destruct of FRAC here.

   SECTION HYPOTHESES: LAWS only (the core's AR law record, ACtl.v:210; ajournal_exec and frame_vis take it).  The
   Section mirrors ACtl.v's Section Ctl (ACtl.v:183-238) restricted to what this stage uses, in its order.

   LOCAL HELPERS (not in the kit; the exact statements are sent to the kit's writer a Theorem Labs lane): f33_flsi_move,
   f33_flsx_move, f33_lk_move, f33_lt_move move the transcribed bundles FLSI / FLSX / LK / LT (ACtlCutP.v:639-808)
   between two register maps that agree on the registers those bundles read.

   CLOSURE (glue closure rule): every project Require below is qualified; no statement here names a frame-route
   identifier.  The closure reaches the frame route only through Seg/F33F.v -> Seg/F33.v (SlotInv, AsanRTInv, ...),
   as closure rule 1 allows.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 / Reusable.YG0d-qualified everywhere, and the six
   modules that exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05
   YO09) are named by their FULL path OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X> (a Theorem Labs lane 03:48Z), as
   are lib/Lib's Mem and MState, which also exist under lib/A/Bz/Lib, lib/B/Bz/Lib and lib/AZ/Lib (not in this delivery); every Require
   names its full directory in the From clause (05:28Z rule).

   BUILD STATE (2026-10-29): TYPE-CHECK ON INTERIM 5da74c9c931, CLOSURE REACHES NO STAND-IN, not acceptance.  The
   glue base a working branch 121bf608343 carries a Theorem Labs lane's stand-in-free 29ddfc3ea99 (a Theorem Labs lane's interim core
   5da74c9c931 + Batch3 + a Theorem Labs lane's ProgWorld files): lib/A/AE2k.v AF0m.v AF0l.v ACej.v ACeh.v hold no port_core_refused
   name, and the build substitutes nothing.  F33.vo compiles from a fresh clone through cb (BASE
   23b918fe0c2e; the lane report names the commit, log and .vo mtime); Print Assumptions glue_seg_F33 = Rocq
   primitives + functional_extensionality_dep (LAWS is its Section-hypothesis argument).  No Axiom, no Parameter, no
   Admitted.  The Batch3 re-fit itself type-checked first on 8ee48574229 with the stand-ins. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG00 YG01 YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F33F.
(* lib/Lib by its own root: the partial `From ..lib Require Lib.Mem` would also match lib/A/Bz/Lib, lib/AZ/Lib and
   lib/B/Bz/Lib (scripted Require scan, 05:2xZ). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The transcribed frame-loop bundles across a register change.  FLSI and LT read register 9 only (their spills),
   LK register 21, FLSX registers 9 18 22 23 25; every other conjunct is about memory or the model. *)
Lemma f33_flsi_move : forall cx j fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m.
Proof.
  intros cx j fr regs regs' m E9 H.
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.spill, ACtlCut.rgv in *.
  rewrite E9. exact H.
Qed.

Lemma f33_flsx_move : forall cx j phi fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25 ->
  ACtlCutP.FLSX cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E9 E18 E22 E23 E25 H.
  unfold ACtlCutP.FLSX, ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.spill,
    ACtlCut.rgv in *.
  rewrite E9, E18, E22, E23, E25. exact H.
Qed.

Lemma f33_lk_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m.
Proof.
  intros cx fr j regs regs' m E21 H. unfold ACtlCutP.LK, ACtlCut.rgv in *. rewrite E21. exact H.
Qed.

Lemma f33_lt_move : forall cx fr j (regs regs' : bvmap 5 word) (m : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m.
Proof.
  intros cx fr j regs regs' m E9 H.
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.spill, ACtlCut.rgv in *.
  rewrite E9. exact H.
Qed.

Section GlueF33.

(* ACtl.v's Section shape (ACtl.v:183-238), restricted to what this stage uses, in ACtl.v's order. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The core's AR laws (ACtl.v:210; YCbq Section a0's hypothesis, YCbq.v:207). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :349-354), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8285c_at := (ACtlCutP.C_A8285c_at B).
Local Notation C_A8286c_at := (ACtlCutP.C_A8286c_at B).
Local Notation C_A828bc_at := (ACtlCutP.C_A828bc_at B).

Lemma glue_seg_F33 : forall POST (j : nat),
  CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat 0]) -> CF POST (ix_cut C_A828bc_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]).
Proof.
  intros POST j HX _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:234-236; C_A8285c_at, ACtlCutP.v:2786-2801). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8285c_at ACtlCutP.ixn nth] in Hb.
  rewrite !Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLSX & Hsel & R10 & R24 & Hcnt & HLT).
  (* G2: the frame word at fr + 32 is visible (AR_frames_law through ProgWorldVisFrame.frame_vis). *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr.
    first [ rewrite EF; reflexivity | rewrite <- EF; reflexivity ]. }
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 32) 8 HAR Hin
              ltac:(lia) ltac:(lia)) as (Hvis & _).
  (* the count word's 8 bytes, from the body's q64 *)
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_ov_read A.Img0.rsegs mem3 (fr + 32) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 11)) 0 8 Hcnt
                ltac:(rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; lia)) as RD.
  cbn [Z.of_nat] in RD.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in RD by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; lia).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8285c_at [Z.of_nat j])) with 0x8285c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8285c) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold Lib.Regs6ss.mkR_of.
  (* G4: the lift at RNG_W (w_H W3) (the run is over Img0.rsegs, the cut over tfibsegs: tfibsegs_rsegs). *)
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { apply A.ProgBridge.fevt_of_evtF.
    apply A.Prog.Seg.F33F.f33_evt_F with (T := A.Prog.reac_box_catalogue_c.BOX_CATALOGUE) (c := fr + 32).
    - exact R10.
    - unfold A.Prog.reac_box_catalogue_c.BOX_CATALOGUE. lia.
    - exact R24.
    - exact RD.
    - exact (Lib.ExecF.rng_acc_lit _ (fr + 32) 8 (fr + 32) 8 (A.ProgBridge.rng_of_visible _ _ _ Hvis)
               ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)). }
  { exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)). }
  (* G5: the end state MS R .. 0x8286c .. mem3, R the run's own map: the exit cut C_A8286c_at [j; 0] there. *)
  intros ms' md' HQ0 Hsbm. cbv beta in HQ0. subst ms'.
  match goal with |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R0 _ _ _ _ _ _] => set (R := R0) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat 0])) R mem3 md')
            (POST cx)).
  assert (E2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E21 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E25 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (E26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (K20 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 20 = Z_to_bv 64 A.Prog.reac_box_catalogue_c.BOX_CATALOGUE) by reflexivity.
  assert (K24 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 24 = Z_to_bv 64 11) by reflexivity.
  apply (HX cx [Z.of_nat j; Z.of_nat 0] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A8286c_at [j; 0] (ACtlCutP.v:2803-2816) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8286c_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite !Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC E2 E3 E4 E8 E9 E19 E26)|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (f33_flsi_move cx j fr regs3 R mem3 E9 HFLSI)|].
    split; [exact (f33_lk_move cx fr j regs3 R mem3 E21 HLK)|].
    split; [lia|].
    split.
    { (* RL at row 0: s4 = the catalogue, s8 = 11 rows left, no row before row 0 *)
      unfold ACtlCutP.RL.
      split; [lia|].
      split.
      { unfold ACtlCut.rgv. rewrite K20.
        first [ reflexivity
              | (f_equal; unfold A.Prog.reac_box_catalogue_c.BOX_CATALOGUE, A.Prog.SlotModel.CAT,
                   A.Prog.SlotModel.CAT_ROW; lia) ]. }
      split.
      { unfold ACtlCut.rgv. rewrite K24.
        first [ reflexivity | (f_equal; unfold A.Prog.SlotModel.CAT_N; lia) ]. }
      split; [intros i' Hi'; lia|].
      split; [exact Hsel|].
      exact (f33_flsx_move cx j phi fr regs3 R mem3 E9 E18 E22 E23 E25 HFLSX). }
    exact (f33_lt_move cx fr j regs3 R mem3 E9 HLT).
  - (* ctl_rt_C B ly3 S3 mem3: ly3, S3 and the memory are the entry cut's *)
    exact Hrt.
Qed.

End GlueF33.

Print Assumptions glue_seg_F33.
