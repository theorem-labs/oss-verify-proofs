(* lib/A/ACtlG/P5.v -- GLUE for stage seg_P5 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:721).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved
   (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_P5 : forall POST, CF POST C_A81bd8 -> CF POST C_A81b90
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_P5.  Segment P5 is 0x81b90 -> 0x81bd8: nine one-byte stores into the frame shadow
   [S(fr) + 370, S(fr) + 386) and the code byte fr + 3040, two spill loads at A + 280 / A + 240, then the call
   `jal __asan_memset` at 0x81bd4 with a0 = fr + 3056, a2 = 32.

   THE PROOF (glue-pattern.md section 3, the memory-writing variant)
   G1  the entry cut C_A81b90 (ACtlCutP.v:1837-1851): 13 named conjuncts and the trailing existential.
   G2  the run's premises from the body, the journal's AR (frames_bounds, astk_ok) and the frame law.  Every
       numeric bound is discharged from VISIBLE state: 4096 <= fr and in_app fr 4096 from the journal's frame,
       the spill base A and sp from FRAC, the stack window from the journal's astk_ok.
   G3  the walk is moved from the cut's register map regs3 to the run's canonical start map mkR_of regs3
       (lib.Reusable.YA0nR.SRr_xregs_eqv), after ProgBridge.cfg_at_MS.
   G4  the lift.  The run is Seg/P5F.p5_evt_F_on (a Theorem Labs lane's route (C) twin of p5_evt_F, a working branch
       e2736e27164), whose callee premise asan_memset_contract_F_on is discharged by the CLOSED theorem
       A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds (never by an SRr_at).  The footprint
       is A.ProgBridge.RNG_W (w_H W3); each of its ten premises is a visibility fact of the walk's state
       (segment-F-premises-A.tsv rows 653-670):
         rng_bytes                        ProgBridge.rng_bytes_RNG_W
         [S + 370, S + 386)               the frame's shadow bytes, AR_frames_law through ProgWorldVisFrame
         [A + 280, A + 288), [A + 240, A + 248), [sp - 2208, sp)
                                          the journal's stack window, ProgWorldVisWin.win_vis
         [Y, Y + 1), [D, D + 32)          frame bytes, ProgWorldVisFrame.frame_vis
         [IMG_LO, IMG_HI)                 ProgBridge.img_vis_W
         sh_word_rng D 32                 ProgWorldVisFrame.frame_vis, second part (the 64-byte hull of
                                          [D, D + 32) lies in the frame because fr mod 32 = 0)
         sh_word_rng (sp - 2208) 2208     ProgWorldVisWin.win_sh_vis (the stack's zero-shadow range)
       The run writes memory, so THE lift is lib.Reusable.YA0nR.SRr_fevt_hid.
   G5  the continuation.  The journal crosses the run by lib.Reusable.YCbq.ajournal_exec with the write set
       Wr = [S(fr) + 370, S(fr) + 386) U [Y, Y + 1) U [D, D + 32) U [sp - 2208, sp): the first three are
       awr_byte's in_frames case (the frame and its shadow), the last its stack case.  Every memory conjunct of
       the exit body C_A81bd8 (ACtlCutP.v:1856-1872) is transported across the single munch Wall by
       Lib.Frame.bytes_at_transport / Seg/P5.p5_addr_keep, except
         - FRAC's 392 frame-shadow bytes, which the run's post restates;
         - XC's `addressable m (fr + 3040) 1`, from the shadow byte S(fr) + 380 = 1 the run writes;
         - the three new conjuncts the exit cut adds for the identity_reply call at 0x81bf4:
             q64 m (A + 232) pa, q64 m (A + 224) pp   the stack window is present after the run (the exit
                                                      journal's own presence conjunct) -> Seg/P5.p5_rd8_le8;
             addressable m (spZ regs - K) K           A.ProgWorldShadow.ctl_stack_shadow_of_AR at [sp - 9072, sp);
             addressable m REAC_CTRL_PARSE_BC 6       p5g_bc_addressable: the record's partial-granule row of
                                                      .str.4 (p5g_bc_row, value 7) through
                                                      A.ProgWorldShadow.ctl_gshadow_of_AR.
       FRAC's last conjunct (a Theorem Labs lane), the fake-frame trailer word
       `q64 m (fr + 4088) (YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))`, is one of the transported words: the run writes
       the frame only in [fr + 3040, fr + 3088), so [fr + 4088, fr + 4096) is outside every window of Wall (DJfrhi).
       ctl_rt_C (route C, a working branch 1899bed1aee) moves with asan_cells_kept, and its two regions (cut_shadow B ly3 S3,
       img_shadow) with A.Prog.Seg.P5.p5_shadow_rw_on across the nine frame-shadow stores and
       A.ShadowRwOnT.shadow_rw_on_kept across the memset (the state ly3 S3 is unchanged), and the run's own ro_agree.
       The cut's shadow facts come from ctl_rt_C's cut_shadow, (F) disjunct (the owned class-6 frame's shadow
       [Sv, Sv + 512)): the 392 frame-shadow bytes of RWsh and the run's region p5_evt_F_shadow_R (fr + 3056).

   SECTION HYPOTHESES: only ACtl.v a3c6b7b35017's own, each the same constant and shape as ACtl.v's (About in this
   file's context); all four are discharged by ACtl.v's top.
     LAWS                       ACtl.v:210.  Same constant, different spelling: ACtl.v writes the partial path
                                Reusable.YG0d.AR_laws, this file the full path lib.Reusable.YG0d.AR_laws of the one
                                copy of YG0d in the tree.
     TFIB_SYMS                  ACtl.v:225, character-identical.
     KREPLY, KPARSE             ACtl.v:237-238, character-identical: the two callee constants of ACtlCutP.v:377-378 at
                                their v1.9.0 values.  C_A81bd8's body asserts `addressable m (spZ regs - K) K` and
                                `addressable m BC 6`, which are FALSE for an arbitrary K / BC.
   CITED, PROVED ON THE GLUE BASE (the first two statements are character-identical to the hypotheses
   CTL_STACK_SHADOW / CTL_GSHADOW this file carried before; the third replaces the temporary copy p5g_frame_GT):
     A.ProgWorldShadow.ctl_stack_shadow_of_AR : A.ProgWorld.ctl_stack_shadow_of_AR_stmt B   (ProgWorld.v:867-872)
     A.ProgWorldShadow.ctl_gshadow_of_AR      : A.ProgWorld.ctl_gshadow_of_AR_stmt B        (ProgWorld.v (at head lib/A/ProgWorld.v:1116-1123),
                                a Theorem Labs lane's CORRECTED text, ctl_gshadow_of_AR_fixed (not in this delivery; written on a working branch 1888d8b45bf), with the image bound
                                kImgLo <= g, g + k <= kImgEnd)
     A.ProgWorld_Fs.ctl_frame_above_img       : A.ProgWorld.ctl_frame_above_img_stmt B      (ProgWorld.v:1243-1247,
                                premise-free: every live fake frame lies at or above 0x5fe000)
   PROVED HERE: p5g_bc_row, ctrl's record row of .str.4.  The base's lib/A/AF0m.v is the record blob 44930bfd861 (the blob this tree had at release c5e779efe8c), so the
   row is a theorem of the base; the proof is bc_row_record's (lib/A/ACtlG/P5RecRow.v at 1169f6edba1).
   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied): Kit.kit_wx (G4) and
   Kit.kit_segs_low (G5).  kit_frac_move is not used: this run moves memory as well as registers, so FRAC is
   rebuilt conjunct by conjunct; kit_RNG0 is not used: this run has a real footprint.
   CITED BY NAME: lib.Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt_hid; A.ProgBridge.fevt_of_evtF /
   tfibsegs_rsegs / cfg_at_MS / RNG_W / rng_of_visible / rng_bytes_RNG_W / img_vis_W;
   A.ProgWorldVisFrame.frame_vis, A.ProgWorldVisWin.win_vis / win_sh_vis; lib.Reusable.YCbq.frames_bounds /
   ajournal_exec; A.Prog.Seg.P5F.p5_evt_F_on; A.Prog.asan_memsetF_on.asan_memset_holds_F_on; A.Prog.memset.memset_holds.

   STATEMENT: glue_seg_P5's type is ACtl.v:582 (blob a3c6b7b35017 on the glue base 29ddfc3ea99) character for
   character, under ACtl.v's own CF / C_A81b90 / C_A81bd8 notations (ACtl.v:261-262, :298-299), so ACtl.v
   discharges seg_P5 with `glue_seg_P5 B MT XM_LIB RLO RHI REAC_CTRL_IDENTITY_REPLY_K REAC_CTRL_PARSE_BC LAWS
   TFIB_SYMS KREPLY KPARSE` (implicit fx / rc inferred; LS is not an argument, the stage does not use it) -- the
   argument order `About` prints for it.

   CLOSURE: every Require is qualified; no statement here names a frame-route identifier (the frame route is
   reached only through Seg/P5.v and Seg/P5F.v, as closure rule 1 allows).  SHADOWED NAMES: getr / mkst /
   seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified throughout; lib/Lib's modules are
   written `lib.Lib.X` (an unqualified `Lib.Frame` resolves to another copy in this closure).  The six modules
   that exist twice or more (YI04 YI16 YK11 YK1b YM05 YO09) are written `lib.Reusable.X.n` (the CORE copy)
   everywhere, per the porter's 04:24Z rule, and Required by their explicit path.

   BUILD STATE: type-check on 5da74c9c931, closure reaches no stand-in (glue base 29ddfc3ea99; scripted
   closure scan in the commit message): built from a `git archive` of the commit in a new `cb`-prepared workspace on
   a build machine, with no substitution of any kind.  Not a compile of record. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every Reusable Require names the CORE copy by its explicit path: the partial form
   `From ...fuzz_ctrl.lib Require Reusable.X` matches four copies of YI04 / YI16 / YK11 / YK1b / YM05 / YO09 /
   YP09 in this tree (lib.Reusable, lib.U.Reusable, lib.A.Reusable, lib.B.Reusable) and the stage gate rejects
   it (gate/F28a/REPORT.md item 6 (a working note, not in this delivery)). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YP09 YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01 YG00 YG0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.AF0m A.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisFrame A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldShadow A.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Step Cells PropExec
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.asan_memset_c A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memset_cF A.Prog.asan_memsetF A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P5 A.Prog.Seg.P5F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on A.Prog.asan_memset_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memset_cF_on A.Prog.asan_memsetF_on.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Two bridges this file needs and no shared kit has.  Both are closed by Qed and name no frame-route
   identifier. *)

(* A byte the journal reports present in the stack window is a writable, readable byte of lib/Lib's memory:
   mrd reads it, and it is not read-only because no image segment reaches 0x5fe000 (Seg/P5.p5_ro_addr_hi). *)
Lemma p5g_stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) ->
  0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  lib.Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi Hp Hlo Hhi.
  split; [lia |]. split; [lia |]. intros a Ha.
  destruct (Hp a Ha) as (_ & b & Hb).
  assert (Hm : lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = Some b).
  { unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  split; [| exists b; exact Hm].
  exact (A.BzBridge.wview_of_mrd m (lib.Lib.Mem.wa a) b Hm
           (A.Prog.Seg.P5.p5_ro_addr_hi a ltac:(lia))).
Qed.

(* The exit cut reads two 8-byte words of the stack window that the entry body does not name; both are present
   after the run, so they hold SOME value (Seg/P5.p5_rd8_le8, as Seg/P5.v:1330-1335 reads them). *)
Lemma p5g_q64_of_present : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  (forall i, 0 <= i < 8 -> lib.Reusable.YG0n.apresent H m (a + i)) ->
  0 <= a -> a + 8 <= 2 ^ 64 ->
  exists v, 0 <= v < 2 ^ 64 /\ lib.Lib.Mem.bytes_at A.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros H m a Hp Ha Hhi.
  assert (Hrd : forall i, 0 <= i < 8 ->
            exists b, lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa (a + i)) = Some b).
  { intros i Hi. destruct (Hp i Hi) as (_ & b & Hb). exists b.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  destruct (A.Prog.Seg.P5.p5_rd8_le8 m a Ha Hhi Hrd) as (w & Hw).
  exists (bv_unsigned w). split; [apply bv_unsigned_in_range |].
  rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. exact Hw.
Qed.

(* ctrl's RECORD row of .str.4 = REAC_CTRL_PARSE_BC = 0x21200 (7 bytes: the 6 0xff bytes the bcmp wrapper compares
   with and the NUL): `z1 (ANum 0x7fffc240) 0x7` in A.AF0m.Tfib_const_shadow (0x7fffc240 = shadow_addr 0x21200; the rows
   on both sides read 0xf9, its redzone).  A fact of the start-up table only, independent of B.  The glue base's
   lib/A/AF0m.v is the record blob 44930bfd861 (the blob this tree had at release c5e779efe8c) (that of a working branch e56483f863b), so the
   row is a theorem here.  Proof taken by path from bc_row_record, lib/A/ACtlG/P5RecRow.v (not in this delivery) at
   a working branch 1169f6edba1. *)
Lemma p5g_bc_row : forall ly,
  In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum (lib.Reusable.YG0f.shadow_addr 0x21200)) 7) (A.AF0m.Tfib_const ly).
Proof.
  intros ly. unfold A.AF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  unfold A.AF0m.Tfib_const_shadow.
  repeat (first [ left; reflexivity | right ]).
Qed.

Section GlueP5.

(* ACtl.v's Section shape (ACtl.v:183-187 and :227-228), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block (ACtl.v:261-262, :298-299), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81b90 := (ACtlCutP.C_A81b90 B).
Local Notation C_A81bd8 := (ACtlCutP.C_A81bd8 B REAC_CTRL_IDENTITY_REPLY_K REAC_CTRL_PARSE_BC).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:210, same constant: ACtl.v spells the one copy
   of YG0d by the partial path Reusable.YG0d). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
(* The core's symbol record for B (ACtl.v:225); a premise of ctl_gshadow_of_AR. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* The two callee constants of ACtlCutP.v:377-378, at their v1.9.0 values (ACtl.v:237-238, character-identical). *)
Hypothesis KREPLY : REAC_CTRL_IDENTITY_REPLY_K = 9072.
Hypothesis KPARSE : REAC_CTRL_PARSE_BC = 0x21200.

(* Kit.v is on the glue base, so its helpers are Required, never restated: this file uses A.ACtlG.Kit.kit_wx (G4)
   and A.ACtlG.Kit.kit_segs_low (G5).  kit_frac_move is not used (FRAC is rebuilt here because the run moves memory as
   well as registers) and kit_RNG0 is not used (this run has a real footprint). *)

(* The ONE step of this file whose truth depends on a start-up table: the 6 bytes of .str.4 are addressable, through
   the record's partial-granule row of the string (p5g_bc_row) and a Theorem Labs lane's corrected partial-granule law
   (A.ProgWorldShadow.ctl_gshadow_of_AR, statement A.ProgWorld.ctl_gshadow_of_AR_stmt). *)
Lemma p5g_bc_addressable : forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
  lib.Reusable.YG0n.AR segs B ly S W m md -> A.AsanRT.addressable m 0x21200 6.
Proof.
  intros ly S W m md HAR.
  (* the image bound of the corrected statement: 0x10000 <= 0x21200 and 0x21200 + 7 <= 0x677000 *)
  apply (A.ProgWorldShadow.ctl_gshadow_of_AR B TFIB_SYMS LAWS ly S W m md 0x21200 7 0x21200 6 HAR (p5g_bc_row ly));
    unfold lib.Reusable.YG0f.kImgLo, lib.Reusable.YG0f.kImgEnd; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P5 : forall POST, CF POST C_A81bd8 -> CF POST C_A81b90.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut's body (ACtlCutP.v:1841-1851) ---- *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81b90] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn26 & HOUR & HCUR & HPRO & HSP144 & HAD17 & HSP192 & HADF & HADI & HIDB &
                     HFGB & A0 & jy & junk & HrA0 & HA0nn & HQ280 & HQ240 & RWy & RWd & HAF).
  destruct Hrt as (HAC & Hcut & Himg & HROa).

  (* ---- G2: the journal, the frame and the spill base ---- *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk3 & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ELO & EHI & _).
  destruct Hstk3 as (_ & HSTKnn & HCEIL & HSLO & HSHI & H47 & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (EFA : lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (EFB : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  rewrite EFA in Hf4096, Hfceil, Hfapp. rewrite EFB in Hfceil, Hfapp.
  assert (HGT : 0x5fe000 <= fr).
  { pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as H.
    rewrite EFA in H. exact H. }
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as (HCR & _).
  unfold lib.Reusable.YG0f.ASAN_CEIL in HCR.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  (* in_app of the frame, with the core's constants unfolded for lia *)
  pose proof Hfapp as Hfapp'.
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
    lib.Reusable.YG0f.ASAN_CEIL in Hfapp'.
  (* the frame bytes are application bytes *)
  assert (Happ : forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a).
  { intros a Ha.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  (* FRAC, with a Theorem Labs lane's trailer word as its last conjunct *)
  pose proof HFRAC as HFR2.
  destruct HFR2 as (A & sp & Hr2 & Hspm & Haspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & HAm & HAS &
                    Hspa & HfrA & HA416 & HS4 & HAPP & Hq304 & Hq24 & Hq16 & Hqhdr & Hqent & Hsh & Hsaved & Htrail).
  unfold A.AsanRT.APPMEM_END in HAPP. unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (HAr : 0 <= A /\ A + 320 <= 2 ^ 64).
  { pose proof Hq304 as Hb0. unfold ACtlCutP.q64 in Hb0.
    pose proof (lib.Lib.Mem.bytes_at_bound segs mem3 (A + 304) (lib.Lib.Mem.le8 (Z_to_bv 64 fr)) Hb0) as Hb.
    rewrite lib.Lib.Mem.length_le8 in Hb. lia. }
  (* the cut's s1 = A0 is FRAC's spill base A *)
  assert (HA0r : 0 <= A0 /\ A0 + 288 <= 2 ^ 64).
  { pose proof HQ280 as Hb0. unfold ACtlCutP.q64 in Hb0.
    pose proof (lib.Lib.Mem.bytes_at_bound segs mem3 (A0 + 280) (lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 3040))) Hb0) as Hb.
    rewrite lib.Lib.Mem.length_le8 in Hb. lia. }
  assert (HA0A : A0 = A).
  { apply (A.Prog.Seg.P5.p5_rg_inj regs3 9 A0 A); [exact HrA0 | exact Hr9 | lia | lia]. }
  subst A0.
  (* every spill of the body is at the same base *)
  assert (HA9 : forall A', ACtlCut.rgv regs3 9 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. apply (A.Prog.Seg.P5.p5_rg_inj regs3 9 A' A); [exact HA' | exact Hr9 | lia | lia]. }
  (* the same, for a spill whose base is bounded only through the spill cell itself (A' + off in range) *)
  assert (HA9' : forall A' off, ACtlCut.rgv regs3 9 A' -> 0 <= off <= 408 -> 0 <= A' + off ->
                   A' + off + 8 <= 2 ^ 64 -> A' = A).
  { intros A' off HrA' Ho Hlo Hhi.
    pose proof Hr9 as Hr9'. unfold ACtlCut.rgv in HrA', Hr9'.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9') HrA')) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by lia.
    clear - E0 Ho Hlo Hhi HAS HAPP HAr. Z.div_mod_to_equations. lia. }
  (* the stack window of the journal, and the three windows inside it *)
  assert (ESTK : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (HspA : sp <= A) by lia.
  assert (Hwin : ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= sp - 2208 /\ sp <= ACtlCut.c_sp cx) by lia.

  (* ---- the three derived addresses of the run ---- *)
  set (Sv := ACtlCutP.Sfr fr) in *.
  assert (ESv : Sv = fr / 8 + 2147450880).
  { subst Sv. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. reflexivity. }
  assert (Hfr8 : fr mod 8 = 0) by (pose proof Hfrm as H; Z.div_mod_to_equations; lia).
  assert (HshIS : forall x, Sv <= x < Sv + 512 -> A.AsanRT.in_shadow x).
  { intros x Hx. rewrite ESv in Hx.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG.
    pose proof Hfapp' as (_ & HH).
    destruct HH as [Hlow | (Hh1 & Hh2)]; Z.div_mod_to_equations; lia. }
  assert (HSvr : 0 <= Sv /\ Sv + 512 <= 2 ^ 64).
  { rewrite ESv. Z.div_mod_to_equations. lia. }
  (* the frame's shadow is apart from the frame (low or high application memory) and far below the stack *)
  assert (HSvfr : Sv + 512 <= fr \/ fr + 4096 <= Sv).
  { rewrite ESv. pose proof Hfapp' as (_ & HH).
    destruct HH as [Hlow | (Hh1 & Hh2)]; [right | left]; Z.div_mod_to_equations; lia. }
  assert (HSvsp : Sv + 512 <= sp - 2208).
  { rewrite ESv. Z.div_mod_to_equations. lia. }
  (* the owned class-6 frame's shadow [Sv, Sv + 512) is ctl_rt_C's cut_shadow, (F) disjunct *)
  assert (HRF : forall a, Sv <= a < Sv + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite EFA, EFB. change (4096 / 8) with 512. rewrite ESv in Ha.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia. }
  (* the 392 frame-shadow bytes as one writable cell *)
  destruct Hsh as (sh & Hshb & Hshl).
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; vm_compute; reflexivity).
  assert (RWsh : lib.Lib.Step.rw_cells A.Img0.rsegs mem3 Sv [lib.Lib.Cells.CB 392 sh]).
  { split; [split |].
    - cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. split; [rewrite Hshl'; reflexivity | exact I].
    - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Hshb.
    - cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add].
      split; [lia |]. split; [lia |]. intros i Hi.
      exact (proj1 (Hcut (Sv + i) (HRF (Sv + i) ltac:(lia)) (HshIS (Sv + i) ltac:(lia)))). }
  (* the two spill cells as read-only cells *)
  pose proof (A.AsanRTFacts.ro_c8 mem3 (A + 280) (Z_to_bv 64 (fr + 3040)) HQ280) as RO280.
  pose proof (A.AsanRTFacts.ro_c8 mem3 (A + 240) (Z_to_bv 64 (fr + 3056)) HQ240) as RO240.
  (* the stack window is a stk *)
  assert (STK3 : lib.Lib.Frame.stk A.Img0.rsegs mem3 (ACtlCut.c_sp cx - A.ACfn.LLVMF_STK) sp).
  { apply (p5g_stk_of_present (lib.Reusable.YA0n.w_H W3)); [| lia | lia].
    intros a Ha. apply Hpres3. lia. }
  (* the memset destination's shadow granule *)
  assert (HD8 : (fr + 3056) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HDS : (fr + 3056) / 8 + A.AsanRT.ASAN_K = Sv + 382).
  { rewrite ESv. unfold A.AsanRT.ASAN_K.
    replace (fr + 3056) with (fr + 382 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HappD : A.AsanRTFacts.app_ivl (fr + 3056) (fr + 3056 + 33)) by (intros a Ha; apply Happ; lia).

  (* ---- the footprint and its ten premises ---- *)
  set (RNG := A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) in *.
  assert (Gby : lib.Lib.RngBytes.rng_bytes RNG) by apply A.ProgBridge.rng_bytes_RNG_W.
  assert (Gimg : lib.Lib.ExecF.rng RNG A.Prog.ImgBounds.IMG_LO
                   (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO))
    by (apply A.ProgBridge.rng_of_visible; apply A.ProgBridge.img_vis_W).
  (* the frame's bytes and its shadow bytes *)
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
              (fr + 3040) 1 HAR Hin6 ltac:(rewrite EFA; lia) ltac:(rewrite EFA, EFB; lia)) as (VY & _).
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
              (fr + 3056) 32 HAR Hin6 ltac:(rewrite EFA; lia) ltac:(rewrite EFA, EFB; lia)) as (VD & VDsh).
  assert (Gy : lib.Lib.ExecF.rng RNG (fr + 3040) 1) by (apply A.ProgBridge.rng_of_visible; exact VY).
  assert (Gd : lib.Lib.ExecF.rng RNG (fr + 3056) 32) by (apply A.ProgBridge.rng_of_visible; exact VD).
  assert (Gshd : A.Prog.rng_asan.sh_word_rng RNG (fr + 3056) 32).
  { destruct (VDsh ltac:(lia) ltac:(rewrite EFA; Z.div_mod_to_equations; lia)
                ltac:(rewrite EFA, EFB; Z.div_mod_to_equations; lia)) as [Hz | Hv];
      [right; exfalso; lia | right; apply A.ProgBridge.rng_of_visible; exact Hv]. }
  (* the frame's shadow window the nine stores write *)
  assert (Gsh : lib.Lib.ExecF.rng RNG (Sv + 370) 16).
  { apply A.ProgBridge.rng_of_visible.
    assert (Hfl : lib.Reusable.YG0d.AR_frames_law segs B) by (destruct LAWS; assumption).
    destruct (Hfl ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as (_ & _ & _ & Hshp).
    split; [lia |]. split; [lia |]. intros a Ha.
    assert (Hi : 0 <= a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx))
                 < lib.Reusable.YG00.fs_frame_bytes 6 / 8).
    { rewrite EFA, EFB. change (4096 / 8) with 512. rewrite ESv in Ha.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia. }
    destruct (Hshp _ Hi) as [[Hv _] _].
    replace (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) +
             (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx))))
      with a in Hv by ring.
    exact Hv. }
  (* the stack windows *)
  assert (Vwin : forall lo len, ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= lo -> lo + len <= ACtlCut.c_sp cx ->
                   A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len Hlo Hhi.
    exact (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
             (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.cut_own C_A81b90 cx) ly3 S3 W3 mem3
             md3 k lo len HJ Hlo Hhi). }
  assert (Ga280 : lib.Lib.ExecF.rng RNG (A + 280) 8)
    by (apply A.ProgBridge.rng_of_visible; apply Vwin; lia).
  assert (Ga240 : lib.Lib.ExecF.rng RNG (A + 240) 8)
    by (apply A.ProgBridge.rng_of_visible; apply Vwin; lia).
  assert (Gstk : lib.Lib.ExecF.rng RNG (sp - A.Prog.asan_memset_c.ASAN_MEMSET_K) A.Prog.asan_memset_c.ASAN_MEMSET_K).
  { apply A.ProgBridge.rng_of_visible. apply Vwin; unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia. }
  assert (Gshs : A.Prog.rng_asan.sh_word_rng RNG (sp - A.Prog.asan_memset_c.ASAN_MEMSET_K)
                   A.Prog.asan_memset_c.ASAN_MEMSET_K).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3
                (sp - A.Prog.asan_memset_c.ASAN_MEMSET_K) A.Prog.asan_memset_c.ASAN_MEMSET_K HAR
                ltac:(rewrite ELO; unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia)
                ltac:(rewrite EHI; unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia)
                ltac:(unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia)) as [Hz | Hv];
      [right; exfalso; unfold A.Prog.asan_memset_c.ASAN_MEMSET_K in Hz; lia
      | right; apply A.ProgBridge.rng_of_visible; exact Hv]. }

  (* ---- G3: the cut's configuration in the run's state form, and the register move ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81b90) with 0x81b90.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81b90) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3
           (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].

  (* ---- G4: the run and its lift ---- *)
  assert (MSET : A.Prog.asan_memset_cF_on.asan_memset_contract_F_on)
    by (apply A.Prog.asan_memsetF_on.asan_memset_holds_F_on; exact A.Prog.memset.memset_holds).
  (* the run's region, the memset destination's shadow words, inside the owned frame's shadow *)
  assert (HSWD : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P5F.p5_evt_F_shadow_R (fr + 3056)) mem3).
  { refine (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 _ Hcut). intros a Ha.
    unfold A.Prog.Seg.P5F.p5_evt_F_shadow_R, A.Prog.Seg.P5F.p5_memset_ro_F_shadow_R,
      A.Prog.asan_memset_c_on.asan_memset_shadow_R, A.Prog.sh_word_on.sh_word_on,
      A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
    rewrite !Z_to_bv_unsigned in Ha. unfold bv_wrap, bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ha.
    rewrite !Z.mod_small in Ha by lia.
    apply HRF. destruct Ha as (_ & Ha1 & Ha2). rewrite ESv.
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha1, Ha2. clear - Ha1 Ha2 Hfr8.
    Z.div_mod_to_equations. lia. }
  assert (HRUN := A.Prog.Seg.P5F.p5_evt_F_on MSET RNG
    (lib.Lib.PropExec.getr regs3 1) (lib.Lib.PropExec.getr regs3 2) (lib.Lib.PropExec.getr regs3 3)
    (lib.Lib.PropExec.getr regs3 4) (lib.Lib.PropExec.getr regs3 5) (lib.Lib.PropExec.getr regs3 6)
    (lib.Lib.PropExec.getr regs3 7) (lib.Lib.PropExec.getr regs3 8) (lib.Lib.PropExec.getr regs3 9)
    (lib.Lib.PropExec.getr regs3 10) (lib.Lib.PropExec.getr regs3 11) (lib.Lib.PropExec.getr regs3 12)
    (lib.Lib.PropExec.getr regs3 13) (lib.Lib.PropExec.getr regs3 14) (lib.Lib.PropExec.getr regs3 15)
    (lib.Lib.PropExec.getr regs3 16) (lib.Lib.PropExec.getr regs3 17) (lib.Lib.PropExec.getr regs3 18)
    (lib.Lib.PropExec.getr regs3 19) (lib.Lib.PropExec.getr regs3 20) (lib.Lib.PropExec.getr regs3 21)
    (lib.Lib.PropExec.getr regs3 22) (lib.Lib.PropExec.getr regs3 23) (lib.Lib.PropExec.getr regs3 24)
    (lib.Lib.PropExec.getr regs3 25) (lib.Lib.PropExec.getr regs3 26) (lib.Lib.PropExec.getr regs3 27)
    (lib.Lib.PropExec.getr regs3 28) (lib.Lib.PropExec.getr regs3 29) (lib.Lib.PropExec.getr regs3 30)
    (lib.Lib.PropExec.getr regs3 31)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
    sp A Sv (fr + 3040) (fr + 3056) (ACtlCut.c_sp cx - A.ACfn.LLVMF_STK) sh jy junk
    Hr2 Hr9 Hr19 ltac:(lia) ltac:(lia) ltac:(lia)
    RO280 RO240 RWsh RWy RWd
    ltac:(Z.div_mod_to_equations; lia) ltac:(lia)
    ltac:(pose proof Hfapp' as (_ & HH); destruct HH as [Hlow | (Hh1 & Hh2)]; [right | left];
            Z.div_mod_to_equations; lia) ltac:(left; lia)
    ltac:(rewrite ESv; unfold A.AsanRT.RT_HI; Z.div_mod_to_equations; lia)
    ltac:(unfold A.AsanRT.RT_HI; lia)
    ltac:(apply Happ; lia)
    ltac:(Z.div_mod_to_equations; lia) ltac:(lia)
    HD8 HDS HappD ltac:(left; unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia)
    STK3 ltac:(unfold A.Prog.asan_memset_c.ASAN_MEMSET_K; lia)
    ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia) ltac:(unfold A.AsanRT.APPMEM_END; lia)
    HAC HSWD HROa
    Gsh Ga280 Ga240 Gy Gby Gimg Gstk Gd Gshd Gshs).
  rewrite A.Prog.Seg.P5.p5_mkR_of.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W3)). }

  (* ---- G5: the continuation ---- *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (R & m1 & mem' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 &
                   MU1 & WM1 & RO1 & HSH1 & H380 & (bY & HYb) & MU2 & WM2 & RO2 & STk & (zs & RWk)).
  subst ms'. cbn [ms_mem] in Hhid.
  (* the run's register facts, in the core's getr (lib/Lib's getr has the same body) *)
  change (lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) in K2.
  change (lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) in K3.
  change (lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) in K4.
  change (lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) in K8.
  change (lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) in K9.
  change (lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) in K19.
  change (lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) in K26.
  change (lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) in K22.
  change (lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) in K25.
  set (MK := A.Prog.asan_memset_c.ASAN_MEMSET_K) in *.
  assert (EMK : MK = 2208) by reflexivity.

  (* the single write window of the whole segment *)
  set (Wall := [(Sv + 370, Sv + 386); (fr + 3040, fr + 3040 + 1); (fr + 3056, fr + 3056 + 32); (sp - MK, sp)])
    in *.
  assert (MUall : lib.Lib.Frame.munch Wall mem3 mem').
  { apply (lib.Lib.Frame.munch_trans Wall mem3 m1 mem').
    - eapply lib.Lib.Frame.munch_weaken; [| exact MU1].
      intros x Hx. subst Wall. cbn [lib.Lib.Frame.outside] in Hx |- *.
      destruct Hx as (H1 & H2 & _ & _ & _). split; [exact H1 |]. split; [exact H2 | exact I].
    - eapply lib.Lib.Frame.munch_weaken; [| exact MU2].
      intros x Hx. subst Wall. cbn [lib.Lib.Frame.outside] in Hx |- *.
      destruct Hx as (_ & _ & H3 & H4 & _). split; [exact H3 |]. split; [exact H4 | exact I]. }
  assert (WMall : lib.Lib.Frame.wmono A.Img0.rsegs mem3 mem')
    by (apply (lib.Lib.Frame.wmono_trans A.Img0.rsegs mem3 m1 mem'); assumption).
  assert (HappS : forall a, sp - MK <= a < sp -> A.AsanRT.app_mem a).
  { intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    right. lia. }
  (* a shadow byte outside the frame's own window is outside every window the segment writes *)
  assert (OSH : forall a, A.AsanRT.in_shadow a -> ~ (Sv + 370 <= a < Sv + 386) ->
                  lib.Lib.Frame.outside Wall a).
  { intros a Hin Hne. subst Wall. cbn [lib.Lib.Frame.outside].
    split; [exact Hne |].
    split; [intro Hc; exact (A.AsanRTFacts.app_not_shadow a (Happ a ltac:(lia)) Hin) |].
    split; [intro Hc; exact (A.AsanRTFacts.app_not_shadow a (Happ a ltac:(lia)) Hin) |].
    split; [intro Hc; exact (A.AsanRTFacts.app_not_shadow a (HappS a ltac:(lia)) Hin) | exact I]. }

  (* ---- the bytes of the exit cut: everything apart from the four windows is the entry's ---- *)
  assert (BT : forall a bs, lib.Lib.Mem.bytes_at segs mem3 a bs ->
                 lib.Lib.Frame.disjoint_from Wall a (Z.of_nat (length bs)) ->
                 lib.Lib.Mem.bytes_at segs mem' a bs).
  { intros a bs Hb Hd. exact (lib.Lib.Frame.bytes_at_transport segs Wall mem3 mem' a bs Hb MUall Hd). }
  assert (DJfr : forall a n, fr <= a -> a + n <= fr + 2960 -> 0 <= n ->
                   lib.Lib.Frame.disjoint_from Wall a n).
  { intros a n H1 H2 H3. subst Wall. cbn [lib.Lib.Frame.disjoint_from].
    split; [Z.div_mod_to_equations; lia |].
    split; [left; lia |]. split; [left; lia |]. split; [left; lia | exact I]. }
  assert (DJsp : forall a n, A <= a -> a + n <= ACtlCut.c_sp cx -> 0 <= n ->
                   lib.Lib.Frame.disjoint_from Wall a n).
  { intros a n H1 H2 H3. subst Wall. cbn [lib.Lib.Frame.disjoint_from].
    split; [Z.div_mod_to_equations; lia |].
    split; [right; lia |]. split; [right; lia |]. split; [right; lia | exact I]. }
  (* the frame bytes above both written frame windows *)
  assert (DJfrhi : forall a n, fr + 3088 <= a -> a + n <= fr + 4096 -> 0 <= n ->
                     lib.Lib.Frame.disjoint_from Wall a n).
  { intros a n H1 H2 H3. subst Wall. cbn [lib.Lib.Frame.disjoint_from].
    split; [Z.div_mod_to_equations; lia |].
    split; [lia |]. split; [lia |]. split; [lia | exact I]. }
  assert (ADK : forall p n, A.AsanRT.addressable mem3 p n ->
                  (forall i, 0 <= i < n -> lib.Lib.Frame.outside Wall (A.AsanRT.shadow_addr (p + i))) ->
                  A.AsanRT.addressable mem' p n).
  { intros p n Had Hsh2. exact (A.Prog.Seg.P5.p5_addr_keep Wall mem3 mem' p n Had MUall Hsh2). }
  assert (ADFR : forall p n, A.AsanRT.addressable mem3 p n -> fr <= p -> p + n <= fr + 2960 -> 0 <= n ->
                   A.AsanRT.addressable mem' p n).
  { intros p n Had H1 H2 H3. apply ADK; [exact Had |]. intros i Hi.
    assert (Hs : Sv <= A.AsanRT.shadow_addr (p + i) < Sv + 370).
    { rewrite ESv. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
    apply OSH; [apply HshIS; lia | lia]. }

  (* ---- the journal across the run ---- *)
  assert (MG : lib.Reusable.YK1b.mem_grows mem3 mem').
  { assert (PR : forall a, 0 <= a < 2 ^ 64 -> mem3 (lib.Lib.Mem.wa a) <> None -> mem' (lib.Lib.Mem.wa a) <> None).
    { intros a Ha Hm.
      assert (CSH : Sv + 370 <= a < Sv + 386 -> mem' (lib.Lib.Mem.wa a) <> None).
      { intros Hc. destruct HSH1 as (sh' & Hsb' & Hsl').
        destruct (A.Prog.Seg.P5.p5_ba_present m1 Sv sh' a Hsb' ltac:(rewrite Hsl'; lia)) as (b & Hb).
        rewrite (MU2 (lib.Lib.Mem.wa a)).
        - rewrite (A.Prog.Seg.P5.p5_mrd_hi m1 a b ltac:(Z.div_mod_to_equations; lia) Hb).
          discriminate.
        - rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside].
          split; [intro Hd; exact (A.AsanRTFacts.app_not_shadow a (Happ a ltac:(lia))
                                     (HshIS a ltac:(lia))) |].
          split; [intro Hd; exact (A.AsanRTFacts.app_not_shadow a (HappS a ltac:(lia))
                                     (HshIS a ltac:(lia))) | exact I]. }
      assert (CY : a = fr + 3040 -> mem' (lib.Lib.Mem.wa a) <> None).
      { intros ->. rewrite (MU2 (lib.Lib.Mem.wa (fr + 3040))).
        - rewrite (A.Prog.Seg.P5.p5_mrd_hi m1 (fr + 3040) bY ltac:(lia) HYb). discriminate.
        - rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside].
          split; [lia |]. split; [lia | exact I]. }
      assert (CD : fr + 3056 <= a < fr + 3088 -> mem' (lib.Lib.Mem.wa a) <> None).
      { intros Hc.
        destruct (A.Prog.Seg.P5.p5_cells_bytes mem' (fr + 3056) [lib.Lib.Cells.CB 32 zs] RWk) as (Hbz & Hlz).
        cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add] in Hlz.
        destruct (A.Prog.Seg.P5.p5_ba_present mem' (fr + 3056) _ a Hbz ltac:(rewrite Hlz; lia)) as (b & Hb).
        rewrite (A.Prog.Seg.P5.p5_mrd_hi mem' a b ltac:(lia) Hb). discriminate. }
      assert (CS : sp - MK <= a < sp -> mem' (lib.Lib.Mem.wa a) <> None).
      { intros Hc. destruct STk as (_ & _ & Hsv). destruct (Hsv a ltac:(lia)) as (_ & b & Hb).
        rewrite (A.Prog.Seg.P5.p5_mrd_hi mem' a b ltac:(lia) Hb). discriminate. }
      destruct (Z_le_gt_dec (Sv + 370) a) as [c1 | c1];
        [destruct (Z_lt_ge_dec a (Sv + 386)) as [c2 | c2]; [exact (CSH ltac:(lia)) |] |];
        (destruct (Z.eq_dec a (fr + 3040)) as [c3 | c3]; [exact (CY c3) |]);
        (destruct (Z_le_gt_dec (fr + 3056) a) as [c4 | c4];
          [destruct (Z_lt_ge_dec a (fr + 3088)) as [c5 | c5]; [exact (CD ltac:(lia)) |] |]);
        (destruct (Z_le_gt_dec (sp - MK) a) as [c6 | c6];
          [destruct (Z_lt_ge_dec a sp) as [c7 | c7]; [exact (CS ltac:(lia)) |] |]);
        (rewrite (MUall (lib.Lib.Mem.wa a)); [exact Hm |]);
        (rewrite lib.Lib.Mem.wa_unsigned by lia); cbn [lib.Lib.Frame.outside];
        (split; [lia |]); (split; [lia |]); (split; [lia |]); (split; [lia | exact I]). }
    intros x Hx. pose proof (PR (bv_unsigned x) (bv_unsigned_in_range 64 x)) as Hp.
    unfold lib.Lib.Mem.wa in Hp. rewrite (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned _ x) in Hp. exact (Hp Hx). }
  assert (HJ' : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                  (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx)
                  (ACtlCut.c_md cx) (ACtlCut.cut_own C_A81b90 cx) ly3 S3 W3 mem' md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (Sv + 370 <= a < Sv + 386) \/ (fr + 3040 <= a < fr + 3040 + 1) \/
                           (fr + 3056 <= a < fr + 3056 + 32) \/ (sp - MK <= a < sp)).
    - exact HJ.
    - intros x HnW. unfold lib.Reusable.YK04.mrestrict.
      destruct (lib.Reusable.YA0n.w_H W3 x) eqn:EH; cbv beta iota; [reflexivity |].
      apply MUall. subst Wall. cbn [lib.Lib.Frame.outside].
      split; [intro Hc; apply HnW; left; exact Hc |].
      split; [intro Hc; apply HnW; right; left; exact Hc |].
      split; [intro Hc; apply HnW; right; right; left; exact Hc |].
      split; [intro Hc; apply HnW; right; right; right; exact Hc | exact I].
    - intros x Hx. unfold lib.Reusable.YK04.mrestrict in Hx |- *.
      destruct (lib.Reusable.YA0n.w_H W3 x); [exfalso; apply Hx; reflexivity | exact (MG x Hx)].
    - exact Hhid.
    - exact Hsbm.
    - intros a HW.
      destruct HW as [Hw | [Hw | [Hw | Hw]]].
      + right. right. right. exists 6, (ACtlCut.c_fpos cx).
        split; [left; reflexivity |]. right.
        rewrite EFA, EFB. change (4096 / 8) with 512. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd].
        unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
        rewrite ESv in Hw. lia.
      + right. right. right. exists 6, (ACtlCut.c_fpos cx).
        split; [left; reflexivity |]. left.
        rewrite EFA, EFB. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. lia.
      + right. right. right. exists 6, (ACtlCut.c_fpos cx).
        split; [left; reflexivity |]. left.
        rewrite EFA, EFB. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. lia.
      + left. lia. }
  pose proof HJ' as (HAR' & _).
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres' & _).

  (* ---- the exit cut ---- *)
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81bd8) R mem' md') (POST cx)).
  apply (HX cx [] fr k ly3 S3 W3 R mem' md' HB HJ' HF HL Hk).
  2: { (* ctl_rt_C B ly3 S3 mem' (route C): the same state; asan_cells as before, the two regions across the nine
          frame-shadow stores (P5.p5_shadow_rw_on) and the memset (ShadowRwOnT.shadow_rw_on_kept) *)
    assert (MKm : A.AsanRTFacts.meta_kept m1 mem').
    { apply (A.AsanRTFacts.munch_meta [(fr + 3056, fr + 3056 + 32); (sp - MK, sp)] m1 mem' MU2).
      cbn [A.AsanRTFacts.all_app]. split; [| split; [| exact I]]; intros a Ha.
      + apply Happ. lia.
      + apply HappS. lia. }
    assert (KP : forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P mem').
    { intros P HPm. destruct HSH1 as (sh' & Hsb' & Hsl').
      apply (A.ShadowRwOnT.shadow_rw_on_kept P m1 mem'); [| exact MKm | exact WM2].
      apply (A.Prog.Seg.P5.p5_shadow_rw_on mem3 m1 Sv (fr + 3040) sh' MU1 WM1 Hsb' Hsl'); [| exact HPm].
      intro Hc. exact (A.AsanRTFacts.app_not_shadow (fr + 3040) (Happ (fr + 3040) ltac:(lia)) Hc). }
    split; [| split; [| split]].
    - unfold A.ACtlK.asan_cells_at.
      apply (A.AsanRTFacts.asan_cells_kept Wall mem3 mem' HAC MUall).
      subst Wall. cbn [lib.Lib.Frame.disjoint_from]. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI.
      split; [Z.div_mod_to_equations; lia |].
      split; [lia |]. split; [lia |]. split; [lia | exact I].
    - exact (KP _ Hcut).
    - exact (KP _ Himg).
    - exact RO2. }
  (* the body of C_A81bd8 (ACtlCutP.v:1860-1872) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81bd8].
  assert (SPM : forall off v, ACtlCutP.spill regs3 mem3 off v -> 0 <= off -> off + 8 <= 416 ->
                  ACtlCutP.spill R mem' off v).
  { intros off v (A' & HrA' & Hq') Ho1 Ho2.
    assert (EA' : A' = A).
    { pose proof Hq' as Hb0. unfold ACtlCutP.q64 in Hb0.
      pose proof (lib.Lib.Mem.bytes_at_bound segs mem3 (A' + off) (lib.Lib.Mem.le8 (Z_to_bv 64 v)) Hb0) as Hb.
      rewrite lib.Lib.Mem.length_le8 in Hb. apply (HA9' A' off HrA'); lia. }
    subst A'. exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact Hr9 |].
    unfold ACtlCutP.q64 in Hq' |- *. apply BT; [exact Hq' |].
    rewrite lib.Lib.Mem.length_le8. apply DJsp; lia. }
  split; [exact HP |].
  split.
  { (* FRAC *)
    exists A, sp.
    split; [rewrite K2; exact Hr2 |]. split; [exact Hspm |].
    split; [unfold lib.Reusable.YG0d.spZ in Haspz |- *; rewrite K2; exact Haspz |].
    split; [rewrite K4; exact Hr4 |].
    split; [unfold ACtlCut.rgv; rewrite K8; exact Hr8 |].
    split; [unfold ACtlCut.rgv; rewrite K9; exact Hr9 |].
    split; [rewrite K3; exact Hr3 |].
    split; [unfold ACtlCut.rgv; rewrite K19; exact Hr19 |].
    split; [unfold ACtlCut.rgv; rewrite K26; exact Hr26 |].
    split; [exact Hfrm |]. split; [exact HAm |]. split; [exact HAS |]. split; [exact Hspa |].
    split; [exact HfrA |]. split; [exact HA416 |]. split; [exact HS4 |]. split; [exact HAPP |].
    split; [unfold ACtlCutP.q64 in Hq304 |- *; apply BT;
            [exact Hq304 | rewrite lib.Lib.Mem.length_le8; apply DJsp; lia] |].
    split; [unfold ACtlCutP.q64 in Hq24 |- *; apply BT;
            [exact Hq24 | rewrite lib.Lib.Mem.length_le8; apply DJsp; lia] |].
    split; [unfold ACtlCutP.q64 in Hq16 |- *; apply BT;
            [exact Hq16 | rewrite lib.Lib.Mem.length_le8; apply DJsp; lia] |].
    split; [unfold ACtlCutP.q64 in Hqhdr |- *; apply BT;
            [exact Hqhdr | rewrite lib.Lib.Mem.length_le8; apply DJfr; lia] |].
    split; [unfold ACtlCutP.q64 in Hqent |- *; apply BT;
            [exact Hqent | rewrite lib.Lib.Mem.length_le8; apply DJfr; lia] |].
    split.
    { destruct HSH1 as (sh' & Hsb' & Hsl'). exists sh'. split; [| rewrite Hsl'; vm_compute; reflexivity].
      apply (lib.Lib.Frame.bytes_at_transport segs [(fr + 3056, fr + 3056 + 32); (sp - MK, sp)]
               m1 mem' Sv sh' Hsb').
      - eapply lib.Lib.Frame.munch_weaken; [| exact MU2]. intros y Hy. exact Hy.
      - rewrite Hsl'. cbn [lib.Lib.Frame.disjoint_from].
        split; [Z.div_mod_to_equations; lia |].
        split; [Z.div_mod_to_equations; lia | exact I]. }
    split.
    { apply BT; [exact Hsaved |].
      unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8.
      apply DJsp; lia. }
    (* FRAC's last conjunct (Batch3), the trailer word: [fr + 4088, fr + 4096) lies above every frame window the run
       writes (the highest ends at fr + 3088), so it is transported like the other frame words *)
    unfold ACtlCutP.q64 in Htrail |- *. apply BT; [exact Htrail |].
    rewrite lib.Lib.Mem.length_le8. apply DJfrhi; lia. }
  split; [exact Hn26 |].
  split.
  { unfold ACtlCutP.OURb in HOUR |- *. apply BT; [exact HOUR |].
    rewrite A.Prog.SlotModel.OUR_length. apply DJfr; lia. }
  split.
  { destruct HCUR as (Hc0 & H22 & H25). split; [exact Hc0 |].
    unfold ACtlCut.rgv in H22, H25 |- *. split; [rewrite K22; exact H22 | rewrite K25; exact H25]. }
  (* the input block is apart from every window the segment writes *)
  assert (DJIN : lib.Lib.Frame.disjoint_from Wall (ACtlCut.c_p cx) (Z.of_nat (length (ACtlCut.c_in cx))) /\
                 (0 < ACtlCut.c_n cx ->
                  forall a, ACtlCut.c_p cx <= a < ACtlCut.c_p cx + ACtlCut.c_n cx ->
                    ~ (fr + 2960 <= a < fr + 3088))).
  { pose proof HB as (HPRE & _).
    destruct HPRE as (_ & _ & _ & _ & Hblk & Hlen & _).
    destruct Hblk as [(Hn0 & Hp0) | (Hnpos & Hin)].
    - split.
      + rewrite <- Hlen, Hn0. cbn [Z.of_nat]. subst Wall. cbn [lib.Lib.Frame.disjoint_from].
        rewrite Hp0. unfold A.ACfn.A_EMPTY.
        split; [Z.div_mod_to_equations; lia |].
        split; [left; lia |]. split; [left; lia |]. split; [left; lia | exact I].
      + intros Hpos. exfalso. lia.
    - assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HP)); exact Hin).
      destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
        as (_ & H4096 & Hceil & Happb & _).
      pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx)
                    (ACtlCut.c_n cx) 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin6) as Hsep.
      unfold lib.Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
      rewrite EFA, EFB in Hsep.
      assert (Ers : lib.Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
        by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia).
      rewrite Ers in Hceil, Happb, Hsep.
      unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg,
        lib.Reusable.YG0f.kHighMemBeg in Happb.
      split.
      + rewrite <- Hlen. subst Wall. cbn [lib.Lib.Frame.disjoint_from].
        split; [rewrite ESv; destruct Happb as (_ & [Hlow | (Hh1 & Hh2)]);
                [left | right]; Z.div_mod_to_equations; lia |].
        split; [lia |]. split; [lia |]. split; [left; lia | exact I].
      + intros Hpos a Ha. lia. }
  destruct DJIN as (DJIN & DJIN2).
  (* PRO *)
  split.
  { unfold ACtlCutP.PRO in HPRO |- *.
    destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pn &
                      P184 & P256 & P264 & P272 & P32).
    split; [exact (SPM 40 (fr + 32) P40 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 120 (fr + 160) P120 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 136 (fr + 128) P136 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 160 (fr + 528) P160 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 168 (fr + 2624) P168 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 176 (fr + 64) P176 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 208 (fr + 448) P208 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 248 (fr + 176) P248 ltac:(lia) ltac:(lia)) |].
    split; [exact (ADFR (fr + 2624) 6 Pad ltac:(lia) ltac:(lia) ltac:(lia)) |].
    split; [apply BT; [exact Pin | exact DJIN] |].
    split.
    { intros Hpos. apply ADK; [exact (Pn Hpos) |]. intros i Hi.
      pose proof (A.AsanRTFacts.addressable_app mem3 (ACtlCut.c_p cx) (ACtlCut.c_n cx) (Pn Hpos)) as Hai.
      assert (Hap : A.AsanRT.app_mem (ACtlCut.c_p cx + i)) by (apply Hai; lia).
      apply OSH; [apply A.AsanRTFacts.shadow_of_app; exact Hap |].
      intro Hc. apply (DJIN2 Hpos (ACtlCut.c_p cx + i) ltac:(lia)).
      rewrite ESv in Hc. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hc.
      Z.div_mod_to_equations. lia. }
    split; [exact (SPM 184 (fr + 336) P184 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 256 (fr + 256) P256 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 264 (fr + 304) P264 ltac:(lia) ltac:(lia)) |].
    split; [exact (SPM 272 (fr + 272) P272 ltac:(lia) ltac:(lia)) |].
    exact (SPM 32 (fr + 2880) P32 ltac:(lia) ltac:(lia)). }
  split; [exact (SPM 144 (fr + 2688) HSP144 ltac:(lia) ltac:(lia)) |].
  split; [exact (ADFR (fr + 2691) 17 HAD17 ltac:(lia) ltac:(lia) ltac:(lia)) |].
  split; [exact (SPM 192 (ACtlCutP.fragb fr) HSP192 ltac:(lia) ltac:(lia)) |].
  split; [unfold ACtlCutP.fragb in HADF |- *;
          exact (ADFR (fr + 2768) 72 HADF ltac:(lia) ltac:(lia) ltac:(lia)) |].
  split; [exact (ADFR (fr + 2688) 38 HADI ltac:(lia) ltac:(lia) ltac:(lia)) |].
  split.
  { unfold ACtlCutP.IDBe in HIDB |- *. apply BT; [exact HIDB |].
    assert (EID : length lib.Prog.RcIdentModel.ID0 = 38%nat) by (vm_compute; reflexivity).
    rewrite EID. apply DJfr; lia. }
  split.
  { unfold ACtlCutP.FGBe in HFGB |- *. apply BT; [exact HFGB |].
    rewrite A.Prog.SlotModel.z72_length. apply DJfr; lia. }
  (* XC *)
  assert (HADY : A.AsanRT.addressable mem' (fr + 3040) 1).
  { assert (ESY : A.AsanRT.shadow_addr (fr + 3040) = Sv + 380).
    { rewrite ESv. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
      replace (fr + 3040) with (fr + 380 * 8) by lia. rewrite Z.div_add by lia. lia. }
    split; [lia |]. split; [lia |].
    split; [unfold A.AsanRT.APPMEM_END; lia |].
    intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
    split; [apply Happ; lia |].
    exists (Z_to_bv 8 1). rewrite ESY. split.
    - unfold lib.Lib.Mem.mrd in H380 |- *. rewrite (MU2 (lib.Lib.Mem.wa (Sv + 380))); [exact H380 |].
      rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside].
      split; [intro Hc; exact (A.AsanRTFacts.app_not_shadow (Sv + 380) (Happ (Sv + 380) ltac:(lia))
                                 (HshIS (Sv + 380) ltac:(lia))) |].
      split; [intro Hc; exact (A.AsanRTFacts.app_not_shadow (Sv + 380) (HappS (Sv + 380) ltac:(lia))
                                 (HshIS (Sv + 380) ltac:(lia))) | exact I].
    - unfold A.AsanRT.shadow_ok.
      assert (E1 : bv_signed (Z_to_bv 8 1) = 1) by (vm_compute; reflexivity).
      rewrite E1. right. split; [Z.div_mod_to_equations; lia | lia]. }
  split.
  { split.
    - intros A' HA' HA'r.
      assert (EA' : A' = A)
        by (apply HA9; [unfold ACtlCut.rgv in HA' |- *; rewrite <- K9; exact HA' | lia]).
      subst A'. unfold ACtlCutP.q64 in HQ280 |- *. apply BT; [exact HQ280 |].
      rewrite lib.Lib.Mem.length_le8. apply DJsp; lia.
    - exact HADY. }
  (* the three facts the identity_reply call at 0x81bf4 needs *)
  assert (HQ232 : exists v, 0 <= v < 2 ^ 64 /\
            lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (A + 232) (lib.Lib.Mem.le8 (Z_to_bv 64 v))).
  { apply (p5g_q64_of_present (lib.Reusable.YA0n.w_H W3)); [| lia | lia].
    intros i Hi. apply Hpres'. lia. }
  assert (HQ224 : exists v, 0 <= v < 2 ^ 64 /\
            lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (A + 224) (lib.Lib.Mem.le8 (Z_to_bv 64 v))).
  { apply (p5g_q64_of_present (lib.Reusable.YA0n.w_H W3)); [| lia | lia].
    intros i Hi. apply Hpres'. lia. }
  destruct HQ232 as (pa & Hpar & Hpab). destruct HQ224 as (pp & Hppr & Hppb).
  exists A, pa, pp, (ACtlCutP.fragb fr).
  split; [unfold ACtlCut.rgv; rewrite K9; exact Hr9 |].
  split; [lia |]. split; [exact Hpar |]. split; [exact Hppr |].
  split; [exact Hpab |]. split; [exact Hppb |].
  split.
  { destruct HSP192 as (A' & HrA' & Hq').
    assert (EA' : A' = A).
    { pose proof Hq' as Hb0. unfold ACtlCutP.q64 in Hb0.
      pose proof (lib.Lib.Mem.bytes_at_bound segs mem3 (A' + 192)
                    (lib.Lib.Mem.le8 (Z_to_bv 64 (ACtlCutP.fragb fr))) Hb0) as Hb.
      rewrite lib.Lib.Mem.length_le8 in Hb. apply (HA9' A' 192 HrA'); lia. }
    subst A'. unfold ACtlCutP.q64 in Hq' |- *. apply BT; [exact Hq' |].
    rewrite lib.Lib.Mem.length_le8. apply DJsp; lia. }
  split.
  { rewrite KREPLY.
    assert (Esp : lib.Reusable.YG0d.spZ R = sp)
      by (unfold lib.Reusable.YG0d.spZ; rewrite K2; exact Haspz).
    rewrite Esp.
    exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS ly3 S3 W3 mem' md' (sp - 9072) 9072 HAR'
             ltac:(rewrite ELO; lia) ltac:(lia) ltac:(rewrite EHI; lia)). }
  split.
  { rewrite KPARSE. exact (p5g_bc_addressable ly3 S3 W3 mem' md' HAR'). }
  exact (ADFR (fr + 2880) 35 HAF ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

End GlueP5.
