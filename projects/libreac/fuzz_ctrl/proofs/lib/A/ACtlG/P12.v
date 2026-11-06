(* lib/A/ACtlG/P12.v -- GLUE for stage seg_P12 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:735, Hypothesis seg_P12).  Written by a Theorem Labs lane after the pattern of
   lib/A/ACtlG/A5.v (glue-pattern.md (a working note, not in this delivery)); single writer.
   rule 24: no function proved (stage glue of a walk).
   proves no function (kind: segment lemma).
   REUSE SEARCH (FREE-PIECES rule 17; `proof-index glue_seg_P12 seg_P12`, index built 2026-10-29T07:26:27Z, run 07:34Z,
   output reuse-P12.txt): glue_seg_P12: 0 named, 0 by address, 0 related,
   0 released, the delivered package 0; declared only on this branch (a working branch). seg_P12: 0 released; its hits are the stage
   hypothesis (ACtl.v) and source lemma (Seg/P12.v, image B twin) this file builds on.  Written new.
   At ossv/recipes c5e779efe8c (2026-10-31), glue_seg_P12 and seg_P12 are defined only in this unit (glue_seg_P12 in
   this file; seg_P12 at the stage hypotheses lib/A/ACtl.v:735 and lib/B/ACtl.v:510, the source lemmas lib/A/Prog/Seg/P12.v:870 and
   lib/B/Prog/Seg/P12.v:321, and image B's lib/B/ACtlW3b.v:2196).

   WHAT IT PROVES
     glue_seg_P12 : forall POST,
       CF POST (ix_cut C_A81d40_at [Z.of_nat 0]) -> CF POST C_A82b04 -> CF POST C_A81c84
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_P12.  The ENTRY is C_A81c84 (pc 0x81c84, own6, k <= 14, live list = entry blocks); the two
   EXITS are the frame loop's head at turn 0, C_A81d40_at [0] (pc 0x81d40), and the loop exit C_A82b04
   (pc 0x82b04), chosen by `beqz s9` at 0x81ce0 (s9 = n - c0 = t_left 0).

   THE RUNS (lib/A/Prog/Seg/P12F.v, a Theorem Labs lane's _F re-runs of Seg/P12.v, Required qualified; which run covers
   which exit):
     p12_evt_a_F   0x81c84 -> 0x81ce0  the two instrumented checks of the "?" string at QMARK = 0x211e0 and the
                                       eight frame-shadow stores sb s11,K(s3) in [S(fr) + 370, S(fr) + 386);
                                       WRITES those 16 shadow bytes.  Runs on BOTH arms.
     p12_evt_b0_F  0x81ce0 -> 0x82b04  s9 = 0: the loop is not entered.  No access, no write.  EXIT C_A82b04.
     p12_evt_b1_F  0x81ce0 -> 0x81d40  s9 <> 0: j := 0 and the twelve spill stores / four spill loads;
                                       WRITES [A + 48, A + 120) and [A + 128, A + 136).  EXIT C_A81d40_at [0].
   P12F.v has no further run (its three _of_F corollaries pin P12.v's p12_evt_a / p12_evt_b0 / p12_evt_b1).
   Premises TSV rows 594-601 are p12_evt_a_F's five rng regions and p12_evt_b1_F's three.

   THE PROOF, step by step (glue-pattern.md section 3; G4/G5 twice on the b1 arm)
   G1  unfold the entry cut C_A81c84 (ACtlCutP.v:1938-1949, 18 conjuncts; no index: C_A81c84 is not an ix_cut).
   G2  the runs' premises, all from visible state:
       - a0 = QMARK, s10 = ASAN_K, s3 = S(fr) from the body's a0v / FRAC (registers 10, 26, 19);
       - the two shadow-byte reads and the two string bytes from the body's `addressable m QMARK 2`
         (ACtlCutP.v:1946, conjunct 7 of C_A81c84) and `kind_name_strings m` (as Seg/P12.v:920-948 does);
       - the sixteen frame-shadow cells from ctl_rt_C's cut_shadow conjunct over the frame's shadow window (region
         (F) of A.ACtlRtC.cut_shadow: frames S3 holds the owned (6, c_fpos cx); in_shadow by the AR frame law's
         in_app), the three spill-block cells from the journal's window-present conjunct
         (every byte of [c_sp - LLVMF_STK, c_sp) is present, hence writable) and the body's spills;
       - footprints: the image string by A.ProgBridge.img_vis_W; its shadow byte 0x7fffc23c by the record's
         constant-shadow row QMARK_ROW, through AR's am_const (CtrlTSyms' ts_const) and a Theorem Labs lane's
         A.ProgWorldVisFrame.vis_of_aview (lemma p12g_qmark_sh_vis below); the frame shadow by the AR frame
         law; the spill blocks by the journal's window-present conjunct;
       - the numeric bounds: 4096 <= fr and fr + 4096 <= alloc_ceiling from YCbq.frames_bounds with the
         shell's frame law and layout_le's ly_F; the spill base A above alloc_ceiling from FRAC
         (sp <= A, c_sp - 4096 < sp) and the journal's astk_ok (alloc_ceiling <= ly_stk_lo, + LLVMF_STK
         <= c_sp).  No bound is left as a hypothesis.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the runs' canonical map
       Regs6ss.mkR_of regs3 (instantiated at reg_get regs3 1 .. 31).
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid at
       ProgBridge.RNG_W (w_H W3) for the memory-writing runs a and b1 (fp_avoids by fp_avoids_RNG_W), and
       Reusable.YA0nR.SRr_fevt at the empty footprint Kit.kit_RNG0 for the register-only run b0.
   G5  the journal crosses each write by Reusable.YCbq.ajournal_exec: Wr := [S(fr) + 370, S(fr) + 386) for
       run a (awr_byte's in_frames case, the owned class-6 frame's shadow) and Wr := [A + 48, A + 120) U
       [A + 128, A + 136) for run b1 (awr_byte's stack case, [c_sp - LLVMF_STK, c_sp)); the hidden bytes come
       from SRr_fevt_hid, mem_grows from the runs' own post (the written bytes are present after).  frames,
       the frame law and the k bound are unchanged; ctl_rt_C at each exit memory (m1 for C_A82b04, m2 for
       C_A81d40_at [0]) is A.ProgWorldCtlRtC.ctl_rt_C_of_AR at that journal's AR (HJ1 / HJ2), the read-only view
       kept from ctl_base by A.ACtlG.KitMem.kitmem_arodataS_journal (route (C), L3-recipe section 2(d)).
       The exit bodies are rebuilt conjunct by conjunct from the entry body across the two write sets, with
       the b1 run's ten q64 facts for the spills FLC / FSj writes.  FRAC at each new memory (HFRAC2 at m1,
       HFRAC3 at m2) is rebuilt by a GENERIC walk over its conjuncts (Ltac p12g_frac_split, then one case per
       shape: q64 word kept, frame-shadow bytes rebuilt, saved registers kept, memory-free conjunct copied), so
       a q64 conjunct appended to FRAC (the planned trailer `q64 m (fr + 4088) (flag_addr ..)`, inside the
       class-6 frame [fr, fr + 4096), which neither run writes) is proved with no edit.

   SECTION HYPOTHESES.  The Section mirrors ACtl.v's Section Ctl (ACtl.v (at head lib/A/ACtl.v:217-262) (an earlier version, blob 84ef756918c, not in this delivery), less RELRO_KIND_NAME, RELRO_CAT, RELRO_FRAMES and MO_LE) in its
   order, then ONE NEW hypothesis, QMARK_ROW (exact text at its declaration; a Theorem Labs lane 05:52Z / a Theorem Labs lane): the
   bundle's constant-shadow row `z1 (ANum (shadow_addr QMARK)) 2` is in Tfib_const.  TRUE on the record core
   (a Theorem Labs lane's AF0m.v (from a working branch e56483f863b), Tfib_const_shadow :2179), not provable on
   the planning base; ACtl.v discharges it there by vm_compute.  The proof uses RELRO_IMG (kitmem_arodataS_journal at
   the exits), LAWS, TFIB_SYMS and QMARK_ROW, so after the Section the lemma is
   `glue_seg_P12 B MT XM_LIB RLO RHI RELRO_IMG LAWS TFIB_SYMS QMARK_ROW`.

   CITED BY NAME: Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt / SRr_fevt_hid and A.ProgBridge.cfg_at_MS /
   fevt_of_evtF / tfibsegs_rsegs / RNG_W / fp_avoids_RNG_W / rng_of_visible / range_visible_sub / img_vis_W
   (a Theorem Labs lane); A.ProgWorldVisFrame.vis_of_aview (a Theorem Labs lane, PROVED there); the core's Reusable.YCbq
   (ajournal_exec, frames_bounds, asan_consts, sep_block_frame, req_size_pos, seg_rom_none),
   Reusable.YG0d.al_frames / al_blocks and Reusable.YG0n.am_const; A.AsanRTFacts (app_not_shadow,
   in_shadow_range, shadow_of_app); A.AF0m.ts_const; the _F runs A.Prog.Seg.P12F.p12_evt_a_F /
   p12_evt_b0_F / p12_evt_b1_F; route (C): A.ACtlRtC.cut_shadow / ctl_rt_C, A.ProgWorldCtlRtC.ctl_rt_C_of_AR,
   A.ProgWorld.arodata_okP_of_S;
   Seg/P12.v's top-level pure facts p12_id_ok, p12_frag_ok, p12_FI (identity / fragment records at turn 0).
   From the kit (Required, never copied): kit_wx, kit_segs_low, kit_frac_move, kit_RNG0; KitMem's
   kitmem_arodataS_journal.

   LOCAL HELPERS, the p12g_ prefix: the byte / cell / shadow transport this stage needs and the kit lacks; their
   statements go to the kit's single writer (a Theorem Labs lane) through a Theorem Labs lane.  Nothing is copied from Kit.v.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here names
   a frame-route identifier (the _F file's closure reaches the frame route, allowed by closure rule 1).  The six
   modules that exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04, YI16, YK11,
   YK1b, YM05, YO09) are named by their FULL path through the module aliases CK11 / CK1b / CM05 / CO09
   (porter a Theorem Labs lane, FINAL 04:24Z), and lib/Lib's Mem / Frame / Step / Cells / MState / ExecF / Regs6ss
   through LMem / LFrm / LStp / LCel / LMS / LExF / LRgs, because lib/AZ/Lib (not in this delivery) carries same-named files.
   Measured (every `From OSSVerify.Proofs.libreac.fuzz_ctrl.. Require ..` followed from this file over the
   branch tree): 395 files at the glue commit; at the route (C) L3 switch, by fclosure.py
   (conservative over-approximation): 508 files, 499 before the switch on its working-branch
   merge 04a1fa44844, the switch adding A/ACtlCutC, ACtlG/KitMem, ProgWorldCtlRt, ProgWorldCtlRtC,
   ProgWorldOwnedRo, ProgWorldVisHeap, ProgWorldVisWin, ProgWorld_Fs and Reusable/YConstIn; no lib/AZ/AsanW (not in this delivery), no W6,
   no SegCF / *_cfw / Cf* route file (the core's Reusable/R/Cfg.v, reached through YK04, is not one); its lib/AZ
   files are
   AZ/LibA/AcctCore.v (through Lib/ExecF.v) and AZ/Spec/{AsanCtrl,AsanCtrlProps,STree}.v (through Seg/P12.v);
   it reaches A/AE2k, AF0l, AF0m, ACej, ACeh (the workspace stand-in files) and not A/AD2l.  Frame-route files,
   each the blob of record: Seg/P12.v 52985bf47a6, Seg/P12F.v f3f37491416, Seg/Tac_slot.v de02ff45188,
   Seg/Tac_fs.v 8bd492a660d, Seg/Tac_fsfree.v d76d2012bf8, SlotInv.v 4cf85db229a, SlotModel.v 04dc7903221,
   AsanRT.v b67d26f8ec7 (mcs 30), AsanRTInv.v 2a8602e8526, AsanRTFacts.v 1657e654e8c, Contract.v fa6fd478d9a,
   FrameAPI.v f6ffefa9bb4, MemNorm.v cb518fc0304, PContract.v a0c4b1b2aa5, AsanLift.v e92b008d733,
   KindBGlue.v 35e845dad50, Prog/RcAsanFP.v 4ec9fa6fbdb, Prog/RcAsanFPLib.v e1f4a4f0b5a,
   Prog/RcAsanRT.v 706993599b7, Tk/AW/SmLeaf.v f05c2c200c9, Tk/AW/SmLib.v dd0c46281d3.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are CK11.* / Reusable.YG0d.cfg_at only.

   BUILD STATE: type-check rc=0 WITH WORKSPACE STAND-INS (provisional; see the commit message): the core's
   undefined port_core_refused_<hex> names read as 0x<hex> in the build workspace only.  This file uses none of
   them by value (no as_zero_shadow row; the shadow byte comes from QMARK_ROW).  No Axiom, no Parameter, no
   Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six doubled modules are Required through their OWN prefix, never `...lib Require Reusable.X`, which
   matches both copies (porter a Theorem Labs lane, amendment (b), 04:33Z); the same for lib/Lib, which lib/AZ/Lib (not in this delivery)
   doubles. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.ACfn A.ACtlK A.AF0m A.ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.AsanRTFacts A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorld A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcIdentModel Prog.RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P12 A.Prog.Seg.P12F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Step Cells PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The six doubled modules and lib/Lib's files, by their full path (porter a Theorem Labs lane, FINAL 04:24Z). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCel := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LExF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LRgs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.P12F.
Module SP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.P12.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module RKN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcKind.
Module IMB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
(* LPS's register reader (LinuxProcessSemantics.Riscv.Sem.reg_get), which Regs6ss.mkR_of and the _F runs'
   explicit mkR maps are written over; loaded through lib/Lib/Regs6ss. *)
Module RSem := LinuxProcessSemantics.Riscv.Sem.
Local Notation reg_get := RSem.reg_get (only parsing).

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Local helpers (no Section argument): byte, cell and shadow transport. *)

(* A byte list survives a memory change that keeps every byte of its range. *)
Lemma p12g_ba_keep : forall (m m' : word -> option byte) a (bs : list byte),
  LMem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x)) ->
  LMem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (K (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma p12g_q64_keep : forall (m m' : word -> option byte) a v,
  ACtlCutP.q64 m a v ->
  (forall x, a <= x < a + 8 -> LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x)) ->
  ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.q64 in *.
  apply (p12g_ba_keep m m' a _ H). rewrite LMem.length_le8. exact K.
Qed.

(* A spill read through register 9 is the q64 at the known spill base A. *)
Lemma p12g_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v HA HAr Hoff (A' & HA' & Hq).
  assert (E : A' = A).
  { unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
    apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
    change (bv_modulus 64) with (2 ^ 64) in HA'.
    pose proof Hq as Hq'. unfold ACtlCutP.q64 in Hq'.
    apply LMem.bytes_at_bound in Hq'. rewrite LMem.length_le8 in Hq'. cbn [Z.of_nat] in Hq'.
    rewrite (Z.mod_small A) in HA' by lia.
    assert (Hr : - 2 ^ 62 < A' < 2 ^ 64) by lia.
    Z.div_mod_to_equations. nia. }
  subst A'. exact Hq.
Qed.

(* A spill moves to a map that keeps register 9 and a memory that keeps its eight bytes. *)
Lemma p12g_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> ACtlCut.rgv regs' 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.spill regs m off v ->
  (forall x, A + off <= x < A + off + 8 -> LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x)) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v HA HA' HAr Hoff Hs K.
  exists A. split; [exact HA'|].
  exact (p12g_q64_keep m m' (A + off) v (p12g_spill_at regs m A off v HA HAr Hoff Hs) K).
Qed.

(* addressable reads only the shadow bytes of its range. *)
Lemma p12g_addr_keep : forall (m m' : word -> option byte) p n,
  ART.addressable m p n ->
  (forall i, 0 <= i < n ->
     LMem.mrd segs m' (LMem.wa (ART.shadow_addr (p + i))) =
     LMem.mrd segs m (LMem.wa (ART.shadow_addr (p + i)))) ->
  ART.addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) K. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [|exact Hok]. change A.Img0.rsegs with segs. rewrite (K i Hi). exact Hb.
Qed.

(* A shadow byte inside [S(fr) + 370, S(fr) + 386) is the shadow of a frame byte in [fr + 2960, fr + 3088)
   (Seg/P12.v:473-478, restated here over ACtlCutP's Sfr). *)
Lemma p12g_sh_back : forall fr y, fr mod 8 = 0 -> 0 <= y ->
  ACtlCutP.Sfr fr + 370 <= ART.shadow_addr y < ACtlCutP.Sfr fr + 386 -> fr + 2960 <= y < fr + 3088.
Proof.
  intros fr y Hm Hy H. unfold ART.shadow_addr, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in H.
  revert H Hm Hy. Z.div_mod_to_equations. lia.
Qed.

(* A readable + writable window, from a pointwise present-and-writable fact. *)
Lemma p12g_stk_of : forall (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> exists b, m (Z_to_bv 64 a) = Some b) ->
  LFrm.stk segs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (H a Ha) as (b & Hb). unfold LMem.wa, LMem.mrd. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. rewrite Hb. reflexivity.
Qed.

Lemma p12g_stk_sub : forall m lo hi a b,
  LFrm.stk segs m lo hi -> lo <= a -> a <= b -> b <= hi -> LFrm.stk segs m a b.
Proof.
  intros m lo hi a b (H0 & H1 & H) Hlo Hab Hhi.
  split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

(* A range whose bytes all read is a bytes_at of some list of that length. *)
Lemma p12g_bytes_present : forall (m : word -> option byte) (n : nat) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, LMem.mrd segs m (LMem.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, LMem.bytes_at segs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a H0 Hn H.
  - exists []. split; [|reflexivity].
    split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). cbn [Z.of_nat] in Hb. rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; destruct (H (S i) ltac:(lia)) as (b' & Hb');
                      exists b'; replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia; exact Hb'))
      as (bs & Hbs & Hlen).
    exists (b :: bs). split; [|cbn [length]; rewrite Hlen; reflexivity].
    pose proof Hbs as (_ & Hb1 & Hb2).
    split; [lia|]. split; [cbn [length]; rewrite Hlen; cbn [length] in Hb1; rewrite Hlen in Hb1; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb2. cbn [length] in Hi. lia.
Qed.

(* A readable + writable window yields a cell block of junk bytes (Seg/P12.v:223-233, restated). *)
Lemma p12g_cells : forall m lo hi a (n : nat),
  LFrm.stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, LStp.rw_cells segs m a [LCel.CB n junk].
Proof.
  intros m lo hi a n HST Hlo Hhi.
  pose proof HST as (H0 & H1 & HW).
  destruct (p12g_bytes_present m n a ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; destruct (HW (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb);
                    exists b; exact Hb)) as (bs & Hbs & Hlen).
  exists bs. split.
  - split.
    + cbn [LCel.cells_wf LCel.cell_wf]. split; [exact Hlen | exact I].
    + cbn [LCel.cells_bytes LCel.cbytes]. rewrite app_nil_r. exact Hbs.
  - cbn [LCel.cells_size LCel.csize]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (HW (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* One readable + writable spill word as a one-cell block (Seg/P12.v:564-575, restated). *)
Lemma p12g_q64_rw1 : forall m lo hi a v,
  LFrm.stk segs m lo hi -> lo <= a -> a + 8 <= hi -> ACtlCutP.q64 m a v ->
  LStp.rw_cells segs m a [LCel.C8 (Z_to_bv 64 v)].
Proof.
  intros m lo hi a v HST Hlo Hhi Hq. pose proof HST as (H0 & H1 & HW).
  unfold ACtlCutP.q64 in Hq. split.
  - split; [cbn [LCel.cells_wf LCel.cell_wf]; split; exact I|].
    cbn [LCel.cells_bytes LCel.cbytes]. rewrite app_nil_r. exact Hq.
  - cbn [LCel.cells_size LCel.csize]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (HW (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* A window holding f at a, v at a + 16 and o at a + 56 as a five-cell block (Seg/P12.v:531-561, restated). *)
Lemma p12g_q64_rw4 : forall m lo hi a f v o,
  LFrm.stk segs m lo hi -> lo <= a -> a + 64 <= hi ->
  ACtlCutP.q64 m a f -> ACtlCutP.q64 m (a + 16) v -> ACtlCutP.q64 m (a + 56) o ->
  exists junk0 junk, LStp.rw_cells segs m a
    [LCel.C8 (Z_to_bv 64 f); LCel.CB 8 junk0; LCel.C8 (Z_to_bv 64 v); LCel.CB 32 junk;
     LCel.C8 (Z_to_bv 64 o)].
Proof.
  intros m lo hi a f v o HST Hlo Hhi Hq0 Hq16 Hq56.
  destruct (p12g_cells m lo hi (a + 8) 8 HST ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk0 & HR8).
  destruct (p12g_cells m lo hi (a + 24) 32 HST ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk & HR32).
  exists junk0, junk.
  pose proof HST as (H0 & H1 & HW).
  unfold ACtlCutP.q64 in Hq0, Hq16, Hq56.
  destruct HR8 as [[Hwf8 Hb8] _]. cbn [LCel.cells_wf LCel.cell_wf] in Hwf8.
  cbn [LCel.cells_bytes LCel.cbytes] in Hb8. rewrite app_nil_r in Hb8. destruct Hwf8 as (Hl8 & _).
  destruct HR32 as [[Hwf32 Hb32] _]. cbn [LCel.cells_wf LCel.cell_wf] in Hwf32.
  cbn [LCel.cells_bytes LCel.cbytes] in Hb32. rewrite app_nil_r in Hb32. destruct Hwf32 as (Hl32 & _).
  split.
  - split.
    + cbn [LCel.cells_wf LCel.cell_wf]. repeat split; try exact I; try exact Hl8; try exact Hl32.
    + cbn [LCel.cells_bytes LCel.cbytes]. rewrite app_nil_r.
      apply (proj2 (LMem.bytes_at_app segs m a _ _)). split; [exact Hq0|]. rewrite LMem.length_le8.
      replace (a + Z.of_nat 8) with (a + 8) by lia.
      apply (proj2 (LMem.bytes_at_app segs m (a + 8) _ _)). split; [exact Hb8|]. rewrite Hl8.
      replace (a + 8 + Z.of_nat 8) with (a + 16) by lia.
      apply (proj2 (LMem.bytes_at_app segs m (a + 16) _ _)). split; [exact Hq16|]. rewrite LMem.length_le8.
      replace (a + 16 + Z.of_nat 8) with (a + 24) by lia.
      apply (proj2 (LMem.bytes_at_app segs m (a + 24) _ _)). split; [exact Hb32|]. rewrite Hl32.
      replace (a + 24 + Z.of_nat 32) with (a + 56) by lia. exact Hq56.
  - cbn [LCel.cells_size LCel.csize]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (HW (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* The 392 frame-shadow bytes after a write confined to [S0 + 370, S0 + 386) (Seg/P12.v:265-298, restated over
   ACtlCutP's FRAME_SHADOW). *)
Lemma p12g_sh_rebuild : forall (m m' : word -> option byte) S0 sh sh16,
  LMem.bytes_at segs m S0 sh -> length sh = Z.to_nat ACtlCutP.FRAME_SHADOW ->
  (forall x, S0 <= x < S0 + 370 -> LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x)) ->
  (forall x, S0 + 386 <= x < S0 + 392 -> LMem.mrd segs m' (LMem.wa x) = LMem.mrd segs m (LMem.wa x)) ->
  LMem.bytes_at segs m' (S0 + 370) sh16 -> length sh16 = 16%nat ->
  exists sh', LMem.bytes_at segs m' S0 sh' /\ length sh' = Z.to_nat ACtlCutP.FRAME_SHADOW.
Proof.
  intros m m' S0 sh sh16 Hsh Hlen K1 K2 HB16 HL16.
  assert (HFS : Z.to_nat ACtlCutP.FRAME_SHADOW = 392%nat) by reflexivity.
  rewrite HFS in Hlen |- *.
  rewrite <- (firstn_skipn 370 sh) in Hsh.
  apply (proj1 (LMem.bytes_at_app segs m S0 _ _)) in Hsh. destruct Hsh as (Hpre & Hrest).
  assert (Lpre : length (firstn 370 sh) = 370%nat) by (rewrite length_firstn, Hlen; reflexivity).
  assert (Lrest : length (skipn 370 sh) = 22%nat) by (rewrite length_skipn, Hlen; reflexivity).
  rewrite Lpre in Hrest.
  rewrite <- (firstn_skipn 16 (skipn 370 sh)) in Hrest.
  apply (proj1 (LMem.bytes_at_app segs m (S0 + 370) _ _)) in Hrest. destruct Hrest as (_ & Hpost).
  assert (Lmid : length (firstn 16 (skipn 370 sh)) = 16%nat) by (rewrite length_firstn, Lrest; reflexivity).
  assert (Lpost : length (skipn 16 (skipn 370 sh)) = 6%nat) by (rewrite length_skipn, Lrest; reflexivity).
  rewrite Lmid in Hpost.
  assert (Hpre' : LMem.bytes_at segs m' S0 (firstn 370 sh))
    by (apply (p12g_ba_keep m m' S0 _ Hpre); rewrite Lpre; intros x Hx; apply K1; lia).
  assert (Hpost' : LMem.bytes_at segs m' (S0 + 370 + 16) (skipn 16 (skipn 370 sh)))
    by (apply (p12g_ba_keep m m' _ _ Hpost); rewrite Lpost; intros x Hx; apply K2; lia).
  exists (firstn 370 sh ++ sh16 ++ skipn 16 (skipn 370 sh)).
  split.
  - apply (proj2 (LMem.bytes_at_app segs m' S0 _ _)). split; [exact Hpre'|].
    rewrite Lpre. apply (proj2 (LMem.bytes_at_app segs m' (S0 + 370) _ _)). split; [exact HB16|].
    rewrite HL16. replace (S0 + 370 + Z.of_nat 16) with (S0 + 370 + 16) by lia. exact Hpost'.
  - rewrite !length_app, Lpre, HL16, Lpost. reflexivity.
Qed.

(* A single readable byte is a one-byte read (Seg/P12.v:182-192, restated). *)
Lemma p12g_rd1 : forall (m : word -> option byte) a b,
  0 <= a -> a + 1 <= 2 ^ 64 -> LMem.mrd segs m (LMem.wa a) = Some b ->
  ov_read_bytes segs m (LMem.wa a) 1 = Some [b].
Proof.
  intros m a b Ha Hb H.
  assert (HB : LMem.bytes_at segs m a [b]).
  { split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact H. }
  pose proof (LMem.bytes_at_ov_read segs m a [b] 0 1 HB ltac:(cbn [length]; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH.
Qed.

(* FRAC at a new memory, conjunct by conjunct and GENERICALLY: with the goal `FRAC_body m -> FRAC_body m'` (the
   same A / sp on both sides), split both conjunctions in step, leaving one goal `X m -> X m'` per conjunct of
   FRAC, whatever their number.  The caller closes each by its shape (q64 / exists-shadow / bytes_at / memory-free),
   so a conjunct appended to FRAC later (a Theorem Labs lane's trailer `q64 m (fr + 4088) (flag_addr ..)`) is closed by the
   q64 case with no edit here (a Theorem Labs lane 05:53Z). *)
Ltac p12g_frac_split :=
  lazymatch goal with
  | |- (?a /\ ?b) -> (?c /\ ?d) =>
      let Ha := fresh "Ha" in let Hb := fresh "Hb" in
      intros [Ha Hb]; split; [revert Ha; p12g_frac_split | revert Hb; p12g_frac_split]
  | |- _ => idtac
  end.

(* ---------------------------------------------------------------------------------------------------------
   2. The stage. *)
Section GlueP12.

(* ACtl.v's Section Ctl shape (ACtl.v:170-194), in its order. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.
(* THE ONE NEW HYPOTHESIS (two Theorem Labs lanes 05:52Z): the bundle's constant-shadow row of the "?" string, `z1
   (ANum 0x7fffc23c) 0x2` (shadow_addr 0x211e0 = 0x7fffc23c by computation: QMARK is a 2-byte global in a
   partial granule, so its shadow byte holds 2).  TRUE on the record core (a Theorem Labs lane's AF0m.v (from a working branch e56483f863b),
   Tfib_const_shadow, :2179); not provable on the planning
   base this file builds on, whose Tfib_const lacks the row.  ACtl.v discharges it on the record by vm_compute. *)
Hypothesis QMARK_ROW : forall ly,
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum (Reusable.YG0f.shadow_addr KNA.QMARK)) 2) (A.AF0m.Tfib_const ly).

(* The shadow byte of the "?" string is visible in every world the AR holds in: AR's am_const gives the view
   Some 2 there (cell_holds of the row above, which CtrlTSyms puts in as_const), and a byte the view reads is
   not hidden (ProgWorldVisFrame.vis_of_aview: a hidden byte lies off every segment, w_Hoff). *)
Lemma p12g_qmark_sh_vis : forall ly S (W : Reusable.YA0n.world segs) (mem : word -> option byte) md,
  Reusable.YG0n.AR segs B ly S W mem md ->
  Reusable.YA0n.w_H W (Z_to_bv 64 (Reusable.YG0f.shadow_addr KNA.QMARK)) = false.
Proof.
  intros ly S W mem md HAR.
  pose proof (proj1 HAR) as HC. apply Reusable.YG0n.am_const in HC.
  rewrite (A.AF0m.ts_const B TFIB_SYMS ly) in HC.
  pose proof (proj1 (Forall_forall _ _) HC _ (QMARK_ROW ly)) as Hc.
  cbv beta iota zeta delta [Reusable.YG0f.cell_holds Reusable.YG0f.z1 Reusable.YG0f.c1
    Reusable.YG0f.c_at Reusable.YG0f.c_w Reusable.YG0f.c_val Reusable.YG0f.aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)).
  apply (A.ProgWorldVisFrame.vis_of_aview segs W mem).
  rewrite <- (Z.add_0_r (Reusable.YG0f.shadow_addr KNA.QMARK)).
  change 0 with (Z.of_nat 0). rewrite Hc. discriminate.
Qed.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :261-262, :315), verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81c84 := (ACtlCutP.C_A81c84 B).
Local Notation C_A81d40_at := (ACtlCutP.C_A81d40_at B).
Local Notation C_A82b04 := (ACtlCutP.C_A82b04 B).

Lemma glue_seg_P12 : forall POST, CF POST (ix_cut C_A81d40_at [Z.of_nat 0]) -> CF POST C_A82b04 -> CF POST C_A81c84.
Proof.
  intros POST HS HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut C_A81c84 (ACtlCutP.v:1938-1949) ---- *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81c84] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & Ha0 & HSTR & HAD2 & HXC & HCUR & HPRO & S144 & HAD2691 &
    S192 & HADF & HADI & HID & HFG & HAD2880).
  change (k <= 14) in Hk.
  change (Reusable.YG01.frames S3 = [(6, ACtlCut.c_fpos cx)]) in HF.
  change (forall cid pos, In (cid, pos) [(6, ACtlCut.c_fpos cx)] ->
            fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) in HL.
  pose proof HPRO as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & HAD2624 & HBin & HAinG &
    S184 & S256 & S264 & S272 & S32).
  pose proof HCUR as (Hc0 & R22 & R25).
  (* FRAC's register / bound conjuncts by name; its memory conjuncts stay in HFR for the generic walk (a
     conjunct appended after them is absorbed by the final `_`) *)
  pose proof HFRAC as (A & sp & HFR).
  pose proof HFR as (R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA416 & Hsp4096 & HSapp & _).
  assert (Hsvl : Z.of_nat (length (ACtlCutP.saved_bytes cx)) = 104)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !LMem.length_le8; reflexivity).
  pose proof Hrt as (_ & Hcut & _ & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & _ & Hceil & Hstklo & _).
  pose proof Reusable.YCbq.asan_consts as (Hac & _ & _ & _ & _).
  pose proof HB as ((_ & _ & _ & _ & Hpn & Elen & _ & _ & _ & _ & HROS & _) & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp. unfold A.ACfn.LLVMF_STK in Hstklo.
  (* ---- G2: the geometry, from visible state ---- *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp0).
  rewrite Efr3 in Hf4096, Hfceil, Hfapp0. rewrite Hfb6 in Hfceil, Hfapp0.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  rewrite Efr3, Hfb6 in Hfrb, Hfrsh.
  assert (ESh : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (unfold Reusable.YG0f.shadow_addr, ACtlCutP.Sfr, ART.shadow_addr, Reusable.YG0f.SHADOW_OFF,
          ART.ASAN_K; lia).
  rewrite ESh in Hfrsh.
  assert (HSfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (Hfrm8 : fr mod 8 = 0) by (revert Hfr32; Z.div_mod_to_equations; lia).
  (* the spill base A lies in high application memory, above the allocation ceiling *)
  assert (HAhi : 0x7fff7f800000 <= A) by lia.
  assert (HAapp : forall x, A <= x < A + 416 -> ART.app_mem x).
  { intros x Hx. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  (* the frame's bytes are application memory, its 512 shadow bytes are shadow *)
  assert (HfrappM : forall x, fr <= x < fr + 4096 -> ART.app_mem x).
  { intros x Hx.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg,
      Reusable.YG0f.kHighMemBeg in Hfapp0.
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
    destruct Hfapp0 as (_ & [Hlo | (Hhi1 & Hhi2)]); [left; lia | right; lia]. }
  assert (Hshb : forall i, 0 <= i < 512 -> ART.in_shadow (ACtlCutP.Sfr fr + i)).
  { intros i Hi. rewrite HSfr.
    unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg,
      Reusable.YG0f.kHighMemBeg in Hfapp0.
    destruct Hfapp0 as (_ & Hcase). Z.div_mod_to_equations. lia. }
  assert (HShlo : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 0x10007fff8000).
  { pose proof (Hshb 0 ltac:(lia)) as H0. pose proof (Hshb 511 ltac:(lia)) as H1.
    unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in H0, H1.
    lia. }
  (* a shadow byte is never an application byte, so the two write sets never meet the frame or the input *)
  assert (Hnotsh : forall x, ART.app_mem x -> ~ (ACtlCutP.Sfr fr + 370 <= x < ACtlCutP.Sfr fr + 386)).
  { intros x Hx Hc. apply (ARF.app_not_shadow x Hx).
    pose proof (Hshb (x - ACtlCutP.Sfr fr) ltac:(lia)) as Hi.
    replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hi by lia. exact Hi. }
  (* ---- G2: the run's register premises ---- *)
  assert (G10 : reg_get regs3 10 = Z_to_bv 64 KNA.QMARK) by exact Ha0.
  assert (G26 : reg_get regs3 26 = Z_to_bv 64 0x7fff8000) by exact R26.
  assert (G19 : reg_get regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact R19.
  assert (G9 : reg_get regs3 9 = Z_to_bv 64 A) by exact R9.
  assert (G25 : reg_get regs3 25 = Z_to_bv 64 (ACtlCut.c_n cx - SM.c0 (ACtlCut.c_in cx))) by exact R25.
  (* ---- G2: the "?" string and its shadow byte (Seg/P12.v:920-948) ---- *)
  pose proof HAD2 as (HQ1 & HQ2 & HQ3 & HQ4).
  destruct (HQ4 0 ltac:(lia)) as (Hap0 & kb & Hkb & Hok0).
  destruct (HQ4 1 ltac:(lia)) as (Hap1 & kb1 & Hkb1 & Hok1).
  assert (Heqsh : ART.shadow_addr (KNA.QMARK + 1) = ART.shadow_addr (KNA.QMARK + 0))
    by (vm_compute; reflexivity).
  rewrite Heqsh, Hkb in Hkb1. injection Hkb1 as Ekb. subst kb1.
  assert (HKa : ov_read_bytes segs mem3 (LMem.wa (KNA.QMARK / 8 + 0x7fff8000)) 1 = Some [kb]).
  { apply p12g_rd1; [unfold KNA.QMARK; lia | unfold KNA.QMARK; lia |].
    replace (KNA.QMARK / 8 + 0x7fff8000) with (ART.shadow_addr (KNA.QMARK + 0)) by (vm_compute; reflexivity).
    change A.Img0.rsegs with segs in Hkb. exact Hkb. }
  assert (HKb : ov_read_bytes segs mem3 (LMem.wa ((KNA.QMARK + 1) / 8 + 0x7fff8000)) 1 = Some [kb]).
  { apply p12g_rd1; [unfold KNA.QMARK; lia | unfold KNA.QMARK; lia |].
    replace ((KNA.QMARK + 1) / 8 + 0x7fff8000) with (ART.shadow_addr (KNA.QMARK + 0))
      by (vm_compute; reflexivity).
    change A.Img0.rsegs with segs in Hkb. exact Hkb. }
  assert (OKa : bv_signed kb = 0 \/ 0 < bv_signed kb).
  { unfold ART.shadow_ok in Hok0. destruct Hok0 as [H|H]; [left; exact H|].
    right. assert (E0 : (KNA.QMARK + 0) mod 8 = 0) by (vm_compute; reflexivity). lia. }
  assert (OKb : bv_signed kb = 0 \/ 1 < bv_signed kb).
  { unfold ART.shadow_ok in Hok1. destruct Hok1 as [H|H]; [left; exact H|].
    right. assert (E1 : (KNA.QMARK + 1) mod 8 = 1) by (vm_compute; reflexivity). lia. }
  pose proof (HSTR 14 ltac:(lia)) as HQS.
  replace (KNA.kind_name_addr 14) with KNA.QMARK in HQS by (vm_compute; reflexivity).
  replace (RKN.cstr_bytes (RKN.kind_name 14)) with [Z_to_bv 8 63; Z_to_bv 8 0] in HQS
    by (vm_compute; reflexivity).
  change A.Img0.rsegs with segs in HQS.
  assert (HS0 : ov_read_bytes segs mem3 (LMem.wa KNA.QMARK) 1 = Some [Z_to_bv 8 63]).
  { pose proof (LMem.bytes_at_ov_read segs mem3 KNA.QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 0 1 HQS
                  ltac:(cbn [length]; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH. }
  assert (HS1 : ov_read_bytes segs mem3 (LMem.wa (KNA.QMARK + 1)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (LMem.bytes_at_ov_read segs mem3 KNA.QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 1 1 HQS
                  ltac:(cbn [length]; lia)) as HH.
    change (Z.of_nat 1) with 1 in HH. cbn [firstn skipn] in HH. exact HH. }
  (* ---- G2: the sixteen frame-shadow cells run a writes ---- *)
  assert (Hstksh : LFrm.stk segs mem3 (ACtlCutP.Sfr fr + 370) (ACtlCutP.Sfr fr + 386)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    (* route (C): the window lies in the owned class-6 frame's shadow [Sfr fr, Sfr fr + 512), region (F) *)
    assert (HF6 : A.ACtlRtC.cut_shadow B ly3 S3 a).
    { left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite Efr3, ESh, Hfb6. change (4096 / 8) with 512. lia. }
    apply (Hcut a HF6).
    pose proof (Hshb (a - ACtlCutP.Sfr fr) ltac:(lia)) as Hi.
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hi by lia. exact Hi. }
  destruct (p12g_cells mem3 _ _ (ACtlCutP.Sfr fr + 370) 16 Hstksh ltac:(lia) ltac:(cbn [Z.of_nat]; lia))
    as (junk & HCsh).
  (* ---- G2: the footprints ---- *)
  (* the image string at QMARK *)
  assert (HvisQ : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) KNA.QMARK 2).
  { apply (A.ProgBridge.range_visible_sub _ IMB.IMG_LO (IMB.IMG_HI - IMB.IMG_LO));
      [exact (A.ProgBridge.img_vis_W W3) | | |];
      unfold IMB.IMG_LO, IMB.IMG_HI, KNA.QMARK; lia. }
  (* its shadow byte 0x7fffc23c, from the bundle's constant-shadow row of the string (QMARK_ROW, AR's am_const) *)
  assert (HvisQS : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (KNA.QMARK / 8 + 0x7fff8000) 1).
  { pose proof (p12g_qmark_sh_vis ly3 S3 W3 mem3 md3 HAR) as Hv.
    split; [unfold KNA.QMARK; lia|]. split; [unfold KNA.QMARK; lia|].
    intros a Ha.
    replace a with (Reusable.YG0f.shadow_addr KNA.QMARK)
      by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, KNA.QMARK in *; lia).
    exact Hv. }
  (* the frame's shadow window *)
  assert (HvisSH : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (ACtlCutP.Sfr fr + 370) 16).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfrsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as ((Hv & _) & _).
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hv by lia. exact Hv. }
  (* the spill blocks, inside the journal's present window *)
  assert (HvisW : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> 0 <= len -> lo + len <= ACtlCut.c_sp cx ->
                    A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. split; [lia|]. split; [lia|]. intros a Ha.
    unfold A.ACfn.LLVMF_STK in Hwin. destruct (Hwin a ltac:(lia)) as (Hv & _). exact Hv. }
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  (* ---- G3: the cut's configuration, then the runs' canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81c84) with 0x81c84.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRgs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81c84) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRgs.xregs_eqv_sym _ _ (LRgs.mkR_of_eqv regs3))].
  unfold LRgs.mkR_of.
  (* ---- G4: run a (0x81c84 -> 0x81ce0), which writes the sixteen frame-shadow bytes ---- *)
  pose proof (SF.p12_evt_a_F RNG
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5)
    (reg_get regs3 6) (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10)
    (reg_get regs3 11) (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15)
    (reg_get regs3 16) (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20)
    (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25)
    (reg_get regs3 26) (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30)
    (reg_get regs3 31) CK11.fp_regs CK11.fp_csr mem3 (ACtlCutP.Sfr fr) kb junk
    G10 G26 G19 HKa HKb OKa OKb HS0 HS1 HCsh
    (A.ProgBridge.rng_of_visible _ _ _ HvisQS)
    ltac:(replace ((KNA.QMARK + 1) / 8 + 0x7fff8000) with (KNA.QMARK / 8 + 0x7fff8000)
            by (vm_compute; reflexivity);
          exact (A.ProgBridge.rng_of_visible _ _ _ HvisQS))
    (A.ProgBridge.rng_of_visible _ _ _
       (A.ProgBridge.range_visible_sub _ _ _ KNA.QMARK 1 HvisQ ltac:(lia) ltac:(lia) ltac:(lia)))
    (A.ProgBridge.rng_of_visible _ _ _
       (A.ProgBridge.range_visible_sub _ _ _ (KNA.QMARK + 1) 1 HvisQ ltac:(lia) ltac:(lia) ltac:(lia)))
    (A.ProgBridge.rng_of_visible _ _ _ HvisSH)) as HRUNa.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUNa) as HFSa.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFSa.
  refine (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFSa
            (A.ProgBridge.fp_avoids_RNG_W _) _).
  intros ms1 md1 HQ1a Hhid1 Hsbm1.
  destruct HQ1a as (a0' & a1' & a2' & s11' & m1 & sh16 & Ems1 & MU1 & WM1 & HB16 & HL16). subst ms1.
  (* the kept bytes of run a *)
  assert (KR1 : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 370 <= x < ACtlCutP.Sfr fr + 386) ->
                  LMem.mrd segs m1 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
  { intros x Hx Hnx. unfold LMem.mrd. rewrite (MU1 (LMem.wa x)); [reflexivity|].
    rewrite LMem.wa_unsigned by lia. cbn [LFrm.outside]. split; [exact Hnx | exact I]. }
  (* every byte of the shadow window is present after the stores (mem_grows of ajournal_exec) *)
  assert (HpresSH : forall x : word, ACtlCutP.Sfr fr + 370 <= bv_unsigned x < ACtlCutP.Sfr fr + 386 ->
                      m1 x <> None).
  { intros x Hx Hnone. destruct HB16 as (_ & _ & Hbb).
    pose proof (Hbb (Z.to_nat (bv_unsigned x - (ACtlCutP.Sfr fr + 370))) ltac:(rewrite HL16; lia)) as Hb'.
    rewrite Z2Nat.id in Hb' by lia.
    replace (ACtlCutP.Sfr fr + 370 + (bv_unsigned x - (ACtlCutP.Sfr fr + 370))) with (bv_unsigned x)
      in Hb' by lia.
    unfold LMem.mrd, LMem.wa in Hb'. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hnone in Hb'.
    assert (Hxr : 0 <= bv_unsigned x < 2 ^ 64)
      by (pose proof (bv_unsigned_in_range 64 x) as Hr;
          change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
    assert (Hrom : CK11.seg_rom segs (Z_to_bv 64 (bv_unsigned x)) = None).
    { apply Reusable.YCbq.seg_rom_none; [exact Hxr|].
      intros Himg. pose proof (A.ACtlG.Kit.kit_segs_low _ Himg) as Hlo.
      unfold Reusable.YG0f.kLowMemEnd in Hlo. lia. }
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hrom.
    change (LPE.seg_rom segs x = None) in Hrom.
    destruct (nth_error sh16 (Z.to_nat (bv_unsigned x - (ACtlCutP.Sfr fr + 370)))) as [b2|] eqn:En.
    - rewrite Hrom in Hb'. discriminate Hb'.
    - apply nth_error_None in En. rewrite HL16 in En. lia. }
  (* the journal across run a *)
  assert (HJ1 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                  (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                  (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m1 md1 k).
  { eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => ACtlCutP.Sfr fr + 370 <= a < ACtlCutP.Sfr fr + 386).
    - exact HJ.
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU1 x); [reflexivity|].
      cbn [LFrm.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 370) (bv_unsigned x));
        [destruct (Z_lt_ge_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 386))|].
      + apply HpresSH. lia.
      + rewrite (MU1 x); [exact Hx|]. cbn [LFrm.outside]. split; [lia | exact I].
      + rewrite (MU1 x); [exact Hx|]. cbn [LFrm.outside]. split; [lia | exact I].
    - exact Hhid1.
    - exact Hsbm1.
    - intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx).
      split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Hfb6, ESh. lia. }
  (* ctl_rt_C after run a (route (C)): at run a's journal AR, the read-only view kept from ctl_base *)
  assert (Hrt1 : A.ACtlRtC.ctl_rt_C B ly3 S3 m1).
  { pose proof HJ1 as (HAR1 & _).
    pose proof (A.ACtlG.KitMem.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ1 HROS)
      as HROS1.
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m1 md1 HAR1
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS1 (Z.le_refl _) (Z.le_refl _))). }
  (* the end map of run a keeps every register but 10, 11, 12 and 27 *)
  match goal with |- context [LMS.MS ?R _ (Z_to_bv 64 0x81ce0) _ _ _ _] => set (R1 := R) end.
  assert (E1_2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
  assert (E1_3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
  assert (E1_4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
  assert (E1_8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
  assert (E1_9 : CK11.getr R1 9 = CK11.getr regs3 9) by reflexivity.
  assert (E1_19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
  assert (E1_22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
  assert (E1_25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
  assert (E1_26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
  assert (R9_1 : ACtlCut.rgv R1 9 A) by (unfold ACtlCut.rgv in *; rewrite E1_9; exact R9).
  assert (HA63 : 0 <= A < 2 ^ 63) by lia.
  (* the s9 branch at 0x81ce0 *)
  assert (Hs9 : bv_unsigned (reg_get regs3 25) = ACtlCut.c_n cx - SM.c0 (ACtlCut.c_in cx)).
  { rewrite G25. apply LMS.unsigned_lit. unfold SM.c0 in *. lia. }
  destruct (Z.eq_dec (ACtlCut.c_n cx - SM.c0 (ACtlCut.c_in cx)) 0) as [Hz | Hz].
  - (* ======== arm 1: s9 = 0, run b0 to the exit C_A82b04 ======== *)
    eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md1 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (SF.p12_evt_b0_F A.ACtlG.Kit.kit_RNG0
               (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5)
               (reg_get regs3 6) (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) a0' a1' a2'
               (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
               (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20)
               (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24)
               (reg_get regs3 25) (reg_get regs3 26) s11' (reg_get regs3 28) (reg_get regs3 29)
               (reg_get regs3 30) (reg_get regs3 31) CK11.fp_regs CK11.fp_csr m1).
      rewrite Hs9. exact Hz. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    intros ms2 md2 HQb0 Hsbm2. cbv beta in HQb0. subst ms2.
    (* the exit cut C_A82b04 at run b0's map (the entry's, but 10, 11, 12, 27) and the memory m1 *)
    match goal with |- context [LMS.MS ?R _ (Z_to_bv 64 0x82b04) _ _ _ _] => set (Rb0 := R) end.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A82b04) Rb0 m1 md2) (POST cx)).
    assert (E2_2 : CK11.getr Rb0 2 = CK11.getr regs3 2) by reflexivity.
    assert (E2_3 : CK11.getr Rb0 3 = CK11.getr regs3 3) by reflexivity.
    assert (E2_4 : CK11.getr Rb0 4 = CK11.getr regs3 4) by reflexivity.
    assert (E2_8 : CK11.getr Rb0 8 = CK11.getr regs3 8) by reflexivity.
    assert (E2_9 : CK11.getr Rb0 9 = CK11.getr regs3 9) by reflexivity.
    assert (E2_19 : CK11.getr Rb0 19 = CK11.getr regs3 19) by reflexivity.
    assert (E2_26 : CK11.getr Rb0 26 = CK11.getr regs3 26) by reflexivity.
    assert (R9_2 : ACtlCut.rgv Rb0 9 A) by (unfold ACtlCut.rgv in *; rewrite E2_9; exact R9).
    (* the memory facts that cross run a: app-memory ranges and the frame are untouched *)
    assert (KFR : forall x, fr <= x < fr + 4096 ->
                    LMem.mrd segs m1 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx. apply KR1; [unfold ART.APPMEM_END in *; pose proof (HfrappM x Hx);
                               unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in *; lia
                              | exact (Hnotsh x (HfrappM x Hx))]. }
    assert (KA : forall x, A <= x < A + 416 ->
                   LMem.mrd segs m1 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx. apply KR1; [lia | exact (Hnotsh x (HAapp x Hx))]. }
    assert (KSP : forall x, ACtlCut.c_sp cx - 4096 <= x < ACtlCut.c_sp cx ->
                    LMem.mrd segs m1 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx. apply KR1; [lia|].
      apply Hnotsh. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
    (* the shadow bytes of a frame range outside [fr + 2960, fr + 3088) are untouched *)
    assert (KSH : forall y, fr <= y < fr + 4096 -> ~ (fr + 2960 <= y < fr + 3088) ->
                    LMem.mrd segs m1 (LMem.wa (ART.shadow_addr y)) =
                    LMem.mrd segs mem3 (LMem.wa (ART.shadow_addr y))).
    { intros y Hy Hny. apply KR1.
      - pose proof (ARF.in_shadow_range (ART.shadow_addr y)
                      (ARF.shadow_of_app y (HfrappM y Hy))) as Hr. lia.
      - intros Hc. exact (Hny (p12g_sh_back fr y Hfrm8 ltac:(lia) Hc)). }
    apply (HX cx [] fr k ly3 S3 W3 Rb0 m1 md2 HB).
    + (* the journal: run a's, then run b0 writes nothing (only the model materializes) *)
      eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun _ : Z => False);
        [exact HJ1 | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm2 | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + cbv beta iota delta [ACtlCut.cut_kmax ACtlCutP.C_A82b04]. unfold A.ACtlK.EV_LLVMF. lia.
    + (* the exit body (ACtlCutP.v:2972-2979) *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82b04].
      (* FRAC at m1, by the generic walk: q64 words in the spill block or the frame, the 392 frame-shadow bytes
         rebuilt around run a's window, the saved registers in the stack window, the rest memory-free *)
      assert (HFRAC2 : ACtlCutP.FRAC B cx fr fr regs3 m1).
      { exists A, sp. revert HFR. p12g_frac_split.
        all: lazymatch goal with
          | |- ACtlCutP.q64 _ _ _ -> _ =>
              let Hq := fresh "Hq" in intros Hq; apply (p12g_q64_keep _ _ _ _ Hq);
              intros ?x ?Hx; first [apply KA; lia | apply KFR; lia]
          | |- (exists _, _) -> _ =>
              let shold := fresh "shold" in let Hshb0 := fresh "Hshb0" in let Hshl := fresh "Hshl" in
              intros (shold & Hshb0 & Hshl);
              apply (p12g_sh_rebuild mem3 m1 (ACtlCutP.Sfr fr) shold sh16 Hshb0 Hshl);
              [ intros ?x ?Hx; apply KR1; lia | intros ?x ?Hx; apply KR1; lia | exact HB16 | exact HL16 ]
          | |- LMem.bytes_at _ _ _ _ -> _ =>
              let Hb := fresh "Hb" in intros Hb; apply (p12g_ba_keep _ _ _ _ Hb);
              intros ?x ?Hx; apply KSP; lia
          | |- _ => exact (fun h => h)
          end. }
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rb0 m1 HFRAC2 E2_2 E2_3 E2_4 E2_8 E2_9
                       E2_19 E2_26)|].
      split; [exact Hn|].
      split.
      { unfold ACtlCutP.OURb in *. apply (p12g_ba_keep mem3 m1 _ _ HOUR).
        rewrite SM.OUR_length. intros x Hx. apply KFR. lia. }
      split.
      { apply (p12g_spill_keep regs3 Rb0 mem3 m1 A 144 (fr + 2688) R9 R9_2 HA63 ltac:(lia) S144).
        intros x Hx. apply KA. lia. }
      split.
      { (* the 21 identity bytes and the zero byte the exit reads *)
        exists (firstn 21 RIM.ID0).
        split.
        - unfold ACtlCutP.IDBe in HID.
          rewrite <- (firstn_skipn 21 RIM.ID0) in HID.
          apply (proj1 (LMem.bytes_at_app segs mem3 (fr + 2688) _ _)) in HID.
          apply (p12g_ba_keep mem3 m1 _ _ (proj1 HID)).
          rewrite length_firstn. unfold RIM.ID0. rewrite repeat_length. unfold RIM.ID_SIZE.
          intros x Hx. apply KFR. cbn [Nat.min] in Hx. lia.
        - split; [rewrite length_firstn; unfold RIM.ID0; rewrite repeat_length;
                  unfold RIM.ID_SIZE; reflexivity|].
          vm_compute. intros HH. discriminate HH. }
      { apply (p12g_addr_keep mem3 m1 _ _ HAD2691). intros i Hi. apply KSH; lia. }
    + exact Hrt1.
  - (* ======== arm 2: s9 <> 0, run b1 to the exit C_A81d40_at [0] ======== *)
    (* the three spill blocks run b1 uses, built at mem3 and carried to m1 *)
    assert (HpresW : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
                       exists b, mem3 (Z_to_bv 64 a) = Some b).
    { intros a Ha. unfold A.ACfn.LLVMF_STK in Hwin.
      destruct (Hwin a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
    assert (Hstkw1 : LFrm.stk segs m1 (A + 32) (A + 256)).
    { apply p12g_stk_of; [lia | lia|]. intros a Ha.
      destruct (HpresW a ltac:(lia)) as (b & Hb). exists b.
      rewrite (MU1 (Z_to_bv 64 a)); [exact Hb|].
      rewrite LMS.unsigned_lit by lia. cbn [LFrm.outside].
      split; [exact (Hnotsh a (HAapp a ltac:(lia))) | exact I]. }
    destruct (p12g_cells m1 _ _ (A + 48) 88 Hstkw1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk1 & HC1').
    assert (KA1 : forall x, A <= x < A + 416 ->
                   LMem.mrd segs m1 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx. apply KR1; [lia | exact (Hnotsh x (HAapp x Hx))]. }
    assert (Q192 : ACtlCutP.q64 m1 (A + 192) (ACtlCutP.fragb fr)).
    { apply (p12g_q64_keep mem3 m1 _ _
               (p12g_spill_at regs3 mem3 A 192 (ACtlCutP.fragb fr) R9 HA63 ltac:(lia) S192)).
      intros x Hx. apply KA1. lia. }
    assert (Q208 : ACtlCutP.q64 m1 (A + 192 + 16) (fr + 448)).
    { replace (A + 192 + 16) with (A + 208) by lia.
      apply (p12g_q64_keep mem3 m1 _ _ (p12g_spill_at regs3 mem3 A 208 (fr + 448) R9 HA63 ltac:(lia) S208)).
      intros x Hx. apply KA1. lia. }
    assert (Q248 : ACtlCutP.q64 m1 (A + 192 + 56) (fr + 176)).
    { replace (A + 192 + 56) with (A + 248) by lia.
      apply (p12g_q64_keep mem3 m1 _ _ (p12g_spill_at regs3 mem3 A 248 (fr + 176) R9 HA63 ltac:(lia) S248)).
      intros x Hx. apply KA1. lia. }
    destruct (p12g_q64_rw4 m1 (A + 32) (A + 256) (A + 192) (ACtlCutP.fragb fr) (fr + 448) (fr + 176)
                Hstkw1 ltac:(lia) ltac:(lia) Q192 Q208 Q248) as (junk0 & junk2 & HC2').
    assert (HC3' : LStp.rw_cells segs m1 (A + 32) [LCel.C8 (Z_to_bv 64 (fr + 2880))]).
    { apply (p12g_q64_rw1 m1 (A + 32) (A + 256)); [exact Hstkw1 | lia | lia |].
      apply (p12g_q64_keep mem3 m1 _ _ (p12g_spill_at regs3 mem3 A 32 (fr + 2880) R9 HA63 ltac:(lia) S32)).
      intros x Hx. apply KA1. lia. }
    (* ---- G4: run b1 (0x81ce0 -> 0x81d40), which writes the twelve spill words ---- *)
    eapply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md1 RNG _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (SF.p12_evt_b1_F RNG
               (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5)
               (reg_get regs3 6) (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) a0' a1' a2'
               (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
               (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20)
               (reg_get regs3 21) (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24)
               (reg_get regs3 25) (reg_get regs3 26) s11' (reg_get regs3 28) (reg_get regs3 29)
               (reg_get regs3 30) (reg_get regs3 31) CK11.fp_regs CK11.fp_csr m1
               A (ACtlCutP.fragb fr) (fr + 448) (fr + 176) (fr + 2880) junk1 junk0 junk2);
        [ exact G9
        | rewrite Hs9; exact Hz
        | exact HC1' | exact HC2' | exact HC3'
        | apply A.ProgBridge.rng_of_visible; apply HvisW; lia
        | apply A.ProgBridge.rng_of_visible; apply HvisW; lia
        | apply A.ProgBridge.rng_of_visible; apply HvisW; lia ]. }
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms2 md2 HQb1 Hhid2 Hsbm2.
    destruct HQb1 as (a0'' & a1'' & m2 & bs88 & Ems2 & MU2 & WM2 & HB88 & HL88 & Q104 & Q112 & Q128 &
      Q64 & Q72 & Q80 & Q88 & Q96 & Q48 & Q56).
    subst ms2.
    (* the kept bytes of run b1, and of the two runs together *)
    assert (KR2 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 48 <= x < A + 120) -> ~ (A + 128 <= x < A + 136) ->
                    LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs m1 (LMem.wa x)).
    { intros x Hx H1 H2. unfold LMem.mrd. rewrite (MU2 (LMem.wa x)); [reflexivity|].
      rewrite LMem.wa_unsigned by lia. cbn [LFrm.outside].
      split; [exact H1 | split; [exact H2 | exact I]]. }
    assert (KFR : forall x, fr <= x < fr + 4096 ->
                    LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx.
      assert (Hap : ART.app_mem x) by exact (HfrappM x Hx).
      assert (Hx64 : 0 <= x < 2 ^ 64)
        by (unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Hap; lia).
      rewrite (KR2 x Hx64 ltac:(lia) ltac:(lia)). apply KR1; [lia | exact (Hnotsh x Hap)]. }
    assert (KA2 : forall x, A <= x < A + 416 -> ~ (A + 48 <= x < A + 120) -> ~ (A + 128 <= x < A + 136) ->
                    LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx H1 H2. rewrite (KR2 x ltac:(lia) H1 H2). apply KR1; [lia | exact (Hnotsh x (HAapp x Hx))]. }
    assert (KSP : forall x, ACtlCut.c_sp cx - 4096 <= x < ACtlCut.c_sp cx ->
                    ~ (A + 48 <= x < A + 120) -> ~ (A + 128 <= x < A + 136) ->
                    LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx H1 H2. rewrite (KR2 x ltac:(lia) H1 H2). apply KR1; [lia|].
      apply Hnotsh. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
    assert (KSH : forall y, fr <= y < fr + 4096 -> ~ (fr + 2960 <= y < fr + 3088) ->
                    LMem.mrd segs m2 (LMem.wa (ART.shadow_addr y)) =
                    LMem.mrd segs mem3 (LMem.wa (ART.shadow_addr y))).
    { intros y Hy Hny.
      pose proof (ARF.in_shadow_range (ART.shadow_addr y) (ARF.shadow_of_app y (HfrappM y Hy))) as Hr.
      assert (Hsh' : ART.in_shadow (ART.shadow_addr y)) by exact (ARF.shadow_of_app y (HfrappM y Hy)).
      assert (Hns : ~ (A + 48 <= ART.shadow_addr y < A + 136)).
      { intros Hc. apply (ARF.app_not_shadow (ART.shadow_addr y)); [|exact Hsh'].
        apply HAapp. lia. }
      rewrite (KR2 (ART.shadow_addr y) ltac:(lia) ltac:(lia) ltac:(lia)).
      apply KR1; [lia|]. intros Hc. exact (Hny (p12g_sh_back fr y Hfrm8 ltac:(lia) Hc)). }
    (* the written spill bytes are present after the stores *)
    assert (HpresA : forall x : word, A + 48 <= bv_unsigned x < A + 136 -> m2 x <> None).
    { intros x Hx Hnone. destruct HB88 as (_ & _ & Hbb).
      pose proof (Hbb (Z.to_nat (bv_unsigned x - (A + 48))) ltac:(rewrite HL88; lia)) as Hb'.
      rewrite Z2Nat.id in Hb' by lia.
      replace (A + 48 + (bv_unsigned x - (A + 48))) with (bv_unsigned x) in Hb' by lia.
      unfold LMem.mrd, LMem.wa in Hb'. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hnone in Hb'.
      assert (Hxr : 0 <= bv_unsigned x < 2 ^ 64)
        by (pose proof (bv_unsigned_in_range 64 x) as Hr;
            change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
      assert (Hrom : CK11.seg_rom segs (Z_to_bv 64 (bv_unsigned x)) = None).
      { apply Reusable.YCbq.seg_rom_none; [exact Hxr|].
        intros Himg. pose proof (A.ACtlG.Kit.kit_segs_low _ Himg) as Hlo.
        unfold Reusable.YG0f.kLowMemEnd in Hlo. lia. }
      rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hrom.
      change (LPE.seg_rom segs x = None) in Hrom.
      destruct (nth_error bs88 (Z.to_nat (bv_unsigned x - (A + 48)))) as [b2|] eqn:En.
      - assert (Hc : LPE.seg_rom segs x = Some b2) by exact Hb'.
        rewrite Hrom in Hc. discriminate Hc.
      - apply nth_error_None in En. rewrite HL88 in En. lia. }
    (* the journal across run b1: the write set is inside the stack window *)
    assert (HJ2 : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                    (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                    (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m2 md2 k).
    { eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a => (A + 48 <= a < A + 120) \/ (A + 128 <= a < A + 136)).
      - exact HJ1.
      - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU2 x); [reflexivity|].
        cbn [LFrm.outside]. split; [intros Hc; apply Hx; left; exact Hc|].
        split; [intros Hc; apply Hx; right; exact Hc | exact I].
      - intros x Hx. unfold Reusable.YK04.mrestrict in *.
        destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
        destruct (Z_le_gt_dec (A + 48) (bv_unsigned x));
          [destruct (Z_lt_ge_dec (bv_unsigned x) (A + 136))|].
        + apply HpresA. lia.
        + rewrite (MU2 x); [exact Hx|]. cbn [LFrm.outside].
          split; [lia | split; [lia | exact I]].
        + rewrite (MU2 x); [exact Hx|]. cbn [LFrm.outside].
          split; [lia | split; [lia | exact I]].
      - exact Hhid2.
      - exact Hsbm2.
      - intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia. }
    (* ctl_rt_C after run b1 (route (C)): at run b1's journal AR, the read-only view kept from ctl_base *)
    assert (Hrt2 : A.ACtlRtC.ctl_rt_C B ly3 S3 m2).
    { pose proof HJ2 as (HAR2 & _).
      pose proof (A.ACtlG.KitMem.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ2 HROS)
        as HROS2.
      exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m2 md2 HAR2
               (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS2 (Z.le_refl _) (Z.le_refl _))). }
    (* ---- G5: the exit cut C_A81d40_at at turn 0 ---- *)
    match goal with |- context [LMS.MS ?R _ (Z_to_bv 64 0x81d40) _ _ _ _] => set (R2m := R) end.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81d40_at [Z.of_nat 0])) R2m m2 md2)
              (POST cx)).
    assert (E3_2 : CK11.getr R2m 2 = CK11.getr regs3 2) by reflexivity.
    assert (E3_3 : CK11.getr R2m 3 = CK11.getr regs3 3) by reflexivity.
    assert (E3_4 : CK11.getr R2m 4 = CK11.getr regs3 4) by reflexivity.
    assert (E3_8 : CK11.getr R2m 8 = CK11.getr regs3 8) by reflexivity.
    assert (E3_9 : CK11.getr R2m 9 = CK11.getr regs3 9) by reflexivity.
    assert (E3_19 : CK11.getr R2m 19 = CK11.getr regs3 19) by reflexivity.
    assert (E3_21 : CK11.getr R2m 21 = Z_to_bv 64 0) by reflexivity.
    assert (E3_22 : CK11.getr R2m 22 = CK11.getr regs3 22) by reflexivity.
    assert (E3_25 : CK11.getr R2m 25 = CK11.getr regs3 25) by reflexivity.
    assert (E3_26 : CK11.getr R2m 26 = CK11.getr regs3 26) by reflexivity.
    assert (R9_3 : ACtlCut.rgv R2m 9 A) by (unfold ACtlCut.rgv in *; rewrite E3_9; exact R9).
    (* a spill of the entry map that run b1 does not write moves to R2m / m2 *)
    assert (SPK : forall off v, 0 <= off <= 272 ->
                    (off + 8 <= 48 \/ (120 <= off /\ off + 8 <= 128) \/ 136 <= off) ->
                    ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R2m m2 off v).
    { intros off v Hoff Hout Hs.
      apply (p12g_spill_keep regs3 R2m mem3 m2 A off v R9 R9_3 HA63 ltac:(lia) Hs).
      intros x Hx. apply KA2; lia. }
    (* a q64 of run b1's post is a spill of R2m *)
    assert (SPQ : forall off v, ACtlCut.rgv R2m 9 A -> ACtlCutP.q64 m2 (A + off) v ->
                    ACtlCutP.spill R2m m2 off v)
      by (intros off v HR Hq; exists A; split; [exact HR | exact Hq]).
    (* the frame body is readable and writable at the post (the AR of the journal after the write) *)
    pose proof HJ2 as (HAR2 & _).
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 m2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin6)
      as (_ & _ & Hfrb2 & _).
    rewrite Efr3, Hfb6 in Hfrb2.
    assert (Hstkfr : LFrm.stk segs m2 fr (fr + ACtlCutP.FRAME_BYTES)).
    { apply p12g_stk_of; [lia | unfold ACtlCutP.FRAME_BYTES; lia |].
      intros a Ha. destruct (Hfrb2 a ltac:(unfold ACtlCutP.FRAME_BYTES in Ha; lia)) as ((_ & b & Hb) & _).
      exists b. exact Hb. }
    (* the input block: inside the live list (0 < n on this arm), so below the allocation ceiling *)
    assert (Hnpos : 0 < ACtlCut.c_n cx) by (unfold SM.c0 in *; lia).
    assert (HinP : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)))
      by (destruct Hpn as [(H0 & _) | ((_ & _) & Hin)]; [lia | exact Hin]).
    assert (HinP3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP)); exact HinP).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR HinP3)
      as (_ & Hp4096 & Hpceil & Hpapp & Hpby & _ & Hnmax).
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as (_ & Hrs).
    assert (HKIN : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
                     LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg,
        Reusable.YG0f.kHighMemBeg in Hpapp.
      assert (Happ : ART.app_mem x).
      { unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
        destruct Hpapp as (_ & [Hl | (Hh1 & Hh2)]); [left; lia | right; lia]. }
      assert (Hx64 : 0 <= x < 2 ^ 64)
        by (unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Happ; lia).
      rewrite (KR2 x Hx64 ltac:(lia) ltac:(lia)). apply KR1; [lia | exact (Hnotsh x Happ)]. }
    (* the input block and the owned frame are disjoint (AR's separation) *)
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx)
                  HAR HinP3 Hin6) as HdPF.
    unfold Reusable.YG0f.zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Efr3, Hfb6 in HdPF.
    assert (HKINS : forall i, 0 <= i < ACtlCut.c_n cx ->
                      LMem.mrd segs m2 (LMem.wa (ART.shadow_addr (ACtlCut.c_p cx + i))) =
                      LMem.mrd segs mem3 (LMem.wa (ART.shadow_addr (ACtlCut.c_p cx + i)))).
    { intros i Hi.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg,
        Reusable.YG0f.kHighMemBeg in Hpapp.
      assert (Happ : ART.app_mem (ACtlCut.c_p cx + i)).
      { unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
        destruct Hpapp as (_ & [Hl | (Hh1 & Hh2)]); [left; lia | right; lia]. }
      pose proof (ARF.shadow_of_app _ Happ) as Hsh'.
      pose proof (ARF.in_shadow_range _ Hsh') as Hr.
      assert (Hns : ~ (A + 48 <= ART.shadow_addr (ACtlCut.c_p cx + i) < A + 136)).
      { intros Hc. apply (ARF.app_not_shadow (ART.shadow_addr (ACtlCut.c_p cx + i)));
          [apply HAapp; lia | exact Hsh']. }
      rewrite (KR2 (ART.shadow_addr (ACtlCut.c_p cx + i)) ltac:(lia) ltac:(lia) ltac:(lia)).
      apply KR1; [lia|].
      (* a shadow byte of run a's window is the shadow of a frame byte, and the input block misses the frame *)
      intros Hc. pose proof (p12g_sh_back fr (ACtlCut.c_p cx + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
    (* the bundles of the exit body *)
    assert (HPRO2 : ACtlCutP.PRO cx fr R2m m2).
    { unfold ACtlCutP.PRO.
      split; [exact (SPK 40 (fr + 32) ltac:(lia) ltac:(lia) S40)|].
      split; [exact (SPK 120 (fr + 160) ltac:(lia) ltac:(lia) S120)|].
      split; [exact (SPK 136 (fr + 128) ltac:(lia) ltac:(lia) S136)|].
      split; [exact (SPK 160 (fr + 528) ltac:(lia) ltac:(lia) S160)|].
      split; [exact (SPK 168 (fr + 2624) ltac:(lia) ltac:(lia) S168)|].
      split; [exact (SPK 176 (fr + 64) ltac:(lia) ltac:(lia) S176)|].
      split; [exact (SPK 208 (fr + 448) ltac:(lia) ltac:(lia) S208)|].
      split; [exact (SPK 248 (fr + 176) ltac:(lia) ltac:(lia) S248)|].
      split; [apply (p12g_addr_keep mem3 m2 _ _ HAD2624); intros i Hi; apply KSH; lia|].
      split; [apply (p12g_ba_keep mem3 m2 _ _ HBin); intros x Hx; apply HKIN; lia|].
      split; [intros _; apply (p12g_addr_keep mem3 m2 _ _ (HAinG Hnpos)); intros i Hi; apply HKINS; lia|].
      split; [exact (SPK 184 (fr + 336) ltac:(lia) ltac:(lia) S184)|].
      split; [exact (SPK 256 (fr + 256) ltac:(lia) ltac:(lia) S256)|].
      split; [exact (SPK 264 (fr + 304) ltac:(lia) ltac:(lia) S264)|].
      split; [exact (SPK 272 (fr + 272) ltac:(lia) ltac:(lia) S272)|].
      exact (SPK 32 (fr + 2880) ltac:(lia) ltac:(lia) S32). }
    assert (HOUR2 : ACtlCutP.OURb cx fr m2).
    { unfold ACtlCutP.OURb in *. apply (p12g_ba_keep mem3 m2 _ _ HOUR).
      rewrite SM.OUR_length. intros x Hx. apply KFR. lia. }
    assert (S144' : ACtlCutP.spill R2m m2 144 (fr + 2688))
      by exact (SPK 144 (fr + 2688) ltac:(lia) ltac:(lia) S144).
    assert (HAD2691' : ART.addressable m2 (fr + 2691) 17)
      by (apply (p12g_addr_keep mem3 m2 _ _ HAD2691); intros i Hi; apply KSH; lia).
    assert (HFLSH : ACtlCutP.FLSH cx 0 fr R2m m2).
    { unfold ACtlCutP.FLSH.
      split; [exact HPRO2|].
      split; [exact (SPQ 128 (fr + 452) R9_3 ltac:(replace (fr + 452) with (fr + 448 + 4) by lia; exact Q128))|].
      split; [exact Hstkfr|].
      split; [exact S144' | exact HAD2691']. }
    assert (HF1IN : ACtlCutP.f1_IN cx m2).
    { unfold ACtlCutP.f1_IN. split.
      - apply (p12g_addr_keep mem3 m2 _ _ (HAinG Hnpos)). intros i Hi. apply HKINS; lia.
      - apply (p12g_ba_keep mem3 m2 _ _ HBin). intros x Hx. apply HKIN; lia. }
    assert (HFLC : ACtlCutP.FLC fr R2m m2).
    { unfold ACtlCutP.FLC.
      split; [exact (SPK 256 (fr + 256) ltac:(lia) ltac:(lia) S256)|].
      split; [exact (SPK 184 (fr + 336) ltac:(lia) ltac:(lia) S184)|].
      split; [exact (SPK 192 (ACtlCutP.fragb fr) ltac:(lia) ltac:(lia) S192)|].
      split; [exact (SPQ 80 (ACtlCutP.fragb fr + 15) R9_3 Q80)|].
      split; [exact (SPQ 88 (ACtlCutP.fragb fr + 19) R9_3 Q88)|].
      split; [exact (SPQ 96 (ACtlCutP.fragb fr + 8) R9_3 Q96)|].
      split; [exact (SPK 272 (fr + 272) ltac:(lia) ltac:(lia) S272)|].
      split; [exact (SPK 264 (fr + 304) ltac:(lia) ltac:(lia) S264)|].
      split; [apply (p12g_addr_keep mem3 m2 _ _ HADF); intros i Hi; unfold ACtlCutP.fragb; apply KSH; lia|].
      split; [apply (p12g_addr_keep mem3 m2 _ _ HADI); intros i Hi; apply KSH; lia|].
      split; [exact (SPQ 72 (fr + 186) R9_3 ltac:(replace (fr + 186) with (fr + 176 + 10) by lia; exact Q72))|].
      split; [exact (SPQ 64 (fr + 180) R9_3 ltac:(replace (fr + 180) with (fr + 176 + 4) by lia; exact Q64))|].
      split; [exact (SPQ 56 (fr + 2889) R9_3 ltac:(replace (fr + 2889) with (fr + 2880 + 9) by lia; exact Q56))
             | exact (SPQ 48 (fr + 2890) R9_3 ltac:(replace (fr + 2890) with (fr + 2880 + 10) by lia; exact Q48))]. }
    assert (HLI : ACtlCutP.LI cx fr 0 R2m m2).
    { unfold ACtlCutP.LI, ACtlCutP.LK, ACtlCutP.CUR, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb,
        ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FSj, ACtlCutP.FSb.
      split.
      { split; [lia|]. split; [unfold ACtlCut.rgv; rewrite E3_21; reflexivity | exact HOUR2]. }
      split.
      { split; [exact Hc0|].
        split; [unfold ACtlCut.rgv in *; rewrite E3_22; exact R22
               | unfold ACtlCut.rgv in *; rewrite E3_25; exact R25]. }
      split.
      { change (1 <= SM.nlen (ACtlCut.c_in cx) - SM.c0 (ACtlCut.c_in cx)).
        unfold SM.nlen. rewrite <- Elen. lia. }
      split.
      { split.
        - unfold ACtlCutP.IDBe in *. apply (p12g_ba_keep mem3 m2 _ _ HID).
          unfold RIM.ID0. rewrite repeat_length. unfold RIM.ID_SIZE. intros x Hx. apply KFR. lia.
        - exact SP.p12_id_ok. }
      split.
      { split.
        - unfold ACtlCutP.FGBe in *. apply (p12g_ba_keep mem3 m2 _ _ HFG).
          rewrite SM.z72_length. intros x Hx. apply KFR. lia.
        - exact SP.p12_frag_ok. }
      split; [exact (SPQ 104 0 R9_3 Q104)|].
      split; [exact (SPQ 112 0 R9_3 Q112)|].
      split.
      { change (LMem.bytes_at segs m2 (fr + 2880) []).
        split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
      split; [apply (p12g_addr_keep mem3 m2 _ _ HAD2880); intros i Hi; apply KSH; lia | exact SP.p12_FI]. }
    (* the frame-shadow bytes outside run a's window are untouched by both runs *)
    assert (KSHW : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
                     ~ (ACtlCutP.Sfr fr + 370 <= x < ACtlCutP.Sfr fr + 386) ->
                     LMem.mrd segs m2 (LMem.wa x) = LMem.mrd segs mem3 (LMem.wa x)).
    { intros x Hx Hnx.
      assert (Hs' : ART.in_shadow x).
      { pose proof (Hshb (x - ACtlCutP.Sfr fr) ltac:(lia)) as Hi.
        replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hi by lia. exact Hi. }
      rewrite (KR2 x ltac:(pose proof (ARF.in_shadow_range x Hs'); lia)
                 ltac:(intros Hc; apply (ARF.app_not_shadow x); [apply HAapp; lia | exact Hs'])
                 ltac:(intros Hc; apply (ARF.app_not_shadow x); [apply HAapp; lia | exact Hs'])).
      apply KR1; [pose proof (ARF.in_shadow_range x Hs'); lia | exact Hnx]. }
    (* FRAC at m2, by the generic walk (as at m1, with run b1's spill windows left out of the kept bytes) *)
    assert (HFRAC3 : ACtlCutP.FRAC B cx fr fr regs3 m2).
    { exists A, sp. revert HFR. p12g_frac_split.
      all: lazymatch goal with
        | |- ACtlCutP.q64 _ _ _ -> _ =>
            let Hq := fresh "Hq" in intros Hq; apply (p12g_q64_keep _ _ _ _ Hq);
            intros ?x ?Hx; first [apply KA2; lia | apply KFR; lia]
        | |- (exists _, _) -> _ =>
            let shold := fresh "shold" in let Hshb0 := fresh "Hshb0" in let Hshl := fresh "Hshl" in
            intros (shold & Hshb0 & Hshl);
            apply (p12g_sh_rebuild mem3 m2 (ACtlCutP.Sfr fr) shold sh16 Hshb0 Hshl);
            [ intros ?x ?Hx; apply KSHW; lia | intros ?x ?Hx; apply KSHW; lia
            | apply (p12g_ba_keep m1 m2 _ _ HB16); rewrite HL16; intros ?x ?Hx; apply KR2; lia
            | exact HL16 ]
        | |- LMem.bytes_at _ _ _ _ -> _ =>
            let Hb := fresh "Hb" in intros Hb; apply (p12g_ba_keep _ _ _ _ Hb);
            intros ?x ?Hx; apply KSP; lia
        | |- _ => exact (fun h => h)
        end. }
    apply (HS cx [Z.of_nat 0] fr k ly3 S3 W3 R2m m2 md2 HB).
    + exact HJ2.
    + exact HF.
    + exact HL.
    + change (k <= 14 + 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat 0])).
      unfold ACtlCutP.ixn. cbn [nth]. rewrite Znat.Nat2Z.id. lia.
    + split; [reflexivity|].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81d40_at ACtlCutP.ixn nth].
      rewrite Znat.Nat2Z.id.
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R2m m2 HFRAC3 E3_2 E3_3 E3_4 E3_8 E3_9
                       E3_19 E3_26)|].
      split; [exact Hn|].
      split; [exact HLI|].
      split; [exact HFLSH|].
      split; [exact HF1IN|].
      split; [exact (SPK 248 (fr + 176) ltac:(lia) ltac:(lia) S248) | exact HFLC].
    + exact Hrt2.
Qed.

End GlueP12.
