(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 540 of its 622 lines of code are new or changed and 2475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F20.v, with its module paths, module names and numbers changed; 322 of its 378 lines of code are new or changed and 566 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/B7Cuts.v; 572 of its 625 lines of code are new or changed and 325 lines of the source are left out. *)
(* lib/A/ACtlG/F23.v -- GLUE for stage seg_F23 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   `Hypothesis seg_F23`).  Written by a Theorem Labs lane; single writer.  The
   pattern is glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F23 : forall POST (j : nat),
       CF POST (ix_cut C_A825c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's seg_F23.  Segment F23
   is 0x825a0 -> 0x825c8 (Seg/F23.v:1-28): the head of the inlined check_ports, the two frame shadow stores
   `sb zero,16(s3)` / `sb a0,17(s3)`, the ports-pointer load `ld s4,136(s1)` and the call of the runtime's checked
   memcpy (0x52028) copying the 12 image bytes at PORTSC = 0x21180 to the frame's ports words [fr + 128, fr + 140).

   THE RUN.  ONE footprint run, lifted whole (no split: a Theorem Labs lane's split rule 04:01Z): a Theorem Labs lane's route (C) twin
   lib/A/Prog/Seg/F23Fs_on.v f23_evt_Fs_on of a Theorem Labs lane's F23Fs.f23_evt_Fs (whose statement stays unchanged and whose proof changed only to name MState by its full path; itself the
   narrowing of a Theorem Labs lane's F23F.f23_evt_F with the copy's stack-window base lo a binder; F23F fixes
   lo = spv - FN_STACK, a 1 MB window the cut cannot give; pinned back to F23F.f23_evt_F by F23Fs.f23_evt_F_of_Fs,
   constr_eq-checked): the same statement with asan_memcpy_contract_F -> asan_memcpy_contract_F_on, `shadow_rw m`
   narrowed to `shadow_rw_on (f23_evt_Fs_shadow_R fr Sf) m` and the post's `shadow_rw m'` replaced by the forall-P
   transport.  Its contract premise is discharged by the PROVED closed theorem
   A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on (a Theorem Labs lane 83ab88c3325, by path), at lo := c_sp cx - 32768 (the
   journal's stack window).

   ROUTE (C) (a working branch 1899bed1aee; recipe L3-recipe.md section 2 (a working note, not in this delivery)): the
   entry carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3, destructed as (Hac & Hcut & Himg & Hro).  The run's shadow region
   f23_evt_Fs_shadow_R fr (Sfr fr) comes from the union of the two regions: the two frame shadow stores
   [Sfr fr + 16, Sfr fr + 18) and the copy's destination words over [fr + 128, fr + 140) lie in the owned class-6
   frame's shadow (cut_shadow's (F) disjunct), the copy's source words over [PORTSC, PORTSC + 12) in the image's
   shadow (img_shadow).  The exit keeps the state (ly3, S3): asan_cells by AsanRTFacts.asan_cells_kept, both regions
   by the run's forall-P post, ro_agree from the post.

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index, C_A825a0_at = FRAC /\ b7_body (.. a0 = s4 = t_want_v).
   G2  the run's premises from the cut: registers (FRAC's 2 / 9 / 19 pins, the body's a0 = s4); the frame bounds
       from the journal's AR (frames_bounds, AR_frames_law, f23g_frame6_above_img) and the frame law; the spill
       [A + 136] = fr + 128 from B7K's B7SPL (B7Cuts.b7_spill_at); the 12 destination bytes as rw_cells carved from
       FLSH's frame stk window; PORTSC's 12 bytes addressable from the RECORD rows (zero shadow of granule 0x21180,
       partial-granule row 0x7fffc231 := 4) through ProgWorldShadow.ctl_global_shadow_of_AR; ctl_rt_C's
       asan_cells / regions / ro_agree; the copy's stack window present from the journal; every footprint range of
       RNG := RNG_W (w_H W3) from visibility (ProgWorldVisWin win_vis / win_sh_vis, ProgWorldVisFrame frame_vis,
       AR_frames_law's frame shadow, ProgBridge img_vis_W; PORTSC's 8-byte shadow word [0x7fffc230, 0x7fffc238) byte by
       byte from the RECORD zero-shadow and const-shadow rows: AR_zshadow_law / AR's am_const, then vis_of_aview).
   G3  cfg_at_MS, then the walk moved to the run's start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  lift: ProgBridge.fevt_of_evtF and YA0nR.SRr_fsteps (the continuation keeps the fsteps run, for the journal).
   G5  the exit cut at the run's end map R and memory m' (writes: the copy's window [sp - 2224, sp), the ports words
       [fr + 128, fr + 140), the frame shadow bytes Sfr fr + 16 / + 17):
         journal  ProgWorld.ajournal_of_fsteps (PROVED, a Theorem Labs lane) with the run's munch list; each written byte is
                  awr_byte: the stack window of the journal, or the owned class-6 frame / its shadow;
         frames, frame law, k bound   unchanged;
         body     FRAC: KitMem.kitmem_frac_keep (by shape, the coming trailer q64 (fr + 4088) included: its premise
                  over [fr + 4088, fr + 4096) is proved here) then Kit.kit_frac_move; HB: B7Cuts.b7_addr_munch; FLSI and B7K: the local
                  f23g_flsi_keep / f23g_b7k_keep; the exit's own conjuncts (s4 = fr + 128, the three words -7, the 12
                  bytes addressable) from the run's post;
         ctl_rt_C asan_cells by AsanRTFacts.asan_cells_kept (the writes miss the runtime cells), the two regions by
                  the run's forall-P post, ro_agree from the run's post.
   INSTRUCTIONS THIS GLUE STEPS ITSELF: none (every instruction is inside f23_evt_Fs_on).

   LOCAL LEMMAS (stage-specific transports over ACtlCutP's bundles, restated from Seg/B7Cuts.v because ACtlCutP's
   transcription is not convertible with SlotInv's; a Theorem Labs lane ruling 04:3xZ):
     f23g_spill_keep  B7Cuts.b7_spill_keep over ACtlCutP.spill (applied by conversion: spill / q64 / rg ARE verbatim)
     f23g_flsi_keep   B7Cuts.b7_flsi_keep over ACtlCutP.FLSI.  DIFFERENCE recorded: ACtlCutP.f1_IN (ACtlCutP.v:658-659)
                      drops SlotInv.f1_IN's `0 < g_n g -> In (g_p g, g_n g) (g_H g)` (SlotInv.v:1826), so the input
                      block's outside-the-writes premises are stated over c_p / c_in / c_n and discharged in the glue
                      from the lib pre (In (c_p, c_n) (ablocks ..)) and the journal's block clause.
     f23g_b7k_keep    B7Cuts.b7_B7K_keep over ACtlCutP.B7K (the register equalities over the core's getr).
     f23g_out3 / f23g_in3   `outside` of the run's three-interval write list, both ways.
     glue_f23_frame_sh  an aligned shadow-word range (sh_word_on) inside the owned class-6 frame is a cut_shadow
                      byte ((F) disjunct, A.ACtlRtC.v:25-36).
     f23g_const_vis   a byte a const row of the bundle names is visible at every AR state (AR's am_const under
                      CtrlTSyms' ts_const, then ProgWorldVisFrame.vis_of_aview; the extraction of a Theorem Labs lane's
                      ctl_gshadow_of_AR).  General: a Kit / KitMem candidate.
   RE-ESTABLISH FRAC AT A NEW MEMORY: only through KitMem.kitmem_frac_keep (G5); no local lemma rebuilds FRAC.

   SECTION HYPOTHESES (exact text below; source of each)
   - LAWS, TFIB_SYMS: the route (C) walk's ACtl.v's own (`Hypothesis LAWS`, `Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B`), same name
     and text: the core's AR laws and the bundle's symbol facts (ts_zsh, ts_const).  VIS0 / OWNED_RO: none.
   - (none for the frame: the first draft's kit_frame6_above_img is now the local Qed lemma f23g_frame6_above_img,
     from a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img at cid = 6.)
   - (none for PORTSC's shadow: TFIB_ZSH_21180, TFIB_ZSH_211A0 and TFIB_CSH_PORTSC, carried by the first draft as
     Section hypotheses, are now local Qed lemmas over the RECORD lib/A/AF0m.v the glue base carries (blob
     44930bfd861 = a working branch e56483f863b): AF0m.v:2956 Tfib_zero_shadow rows
     (0x21180, 0x21188 - 0x21180) and (0x211a0, 0x211e0 - 0x211a0); :2176-2178 Tfib_const_shadow rows
     z1 0x7fffc231 0x4, z1 0x7fffc232 0xf9, z1 0x7fffc233 0xf9; proved by in_cons / in_eq and in_or_app.)
   STAND-IN VALUES: none read (no planning-core zero-shadow row, no Tfib_const_abs / owned_static /
   port_core_refused value; PORTSC's shadow comes only from the three record rows above).
   CITED BY NAME, PROVED: ProgWorld.ajournal_of_fsteps / pws_fsteps_mem; ProgWorldShadow.ctl_global_shadow_of_AR
   (a Theorem Labs lane's corrected lemma, on the glue base as ProgWorldShadow.v 2acf3a713ac under the name of record; its
   statement is a Theorem Labs lane's ctl_global_shadow_of_AR_stmt); ProgWorld_Fs.ctl_frame_above_img (a Theorem Labs lane);
   ProgWorldVisWin.win_vis / win_sh_vis; ProgWorldVisFrame.frame_vis / vis_of_aview; ProgBridge.*;
   YA0nR.SRr_xregs_eqv / SRr_fsteps; YCbq.frames_bounds / sep_block_frame / asan_consts; YG0d.al_frames / al_blocks /
   al_zshadow; asan_memcpyF_on.asan_memcpy_holds_F_on; F23Fs_on.f23_evt_Fs_on; KitMem.kitmem_frac_keep; Kit.kit_wx /
   kit_frac_move; B7Cuts.b7_spill_keep / b7_spill_at / b7_addr_munch / b7_t*_len / b7_fsbody_len;
   RcAsanFPLib.fl_bytes; AsanRTFacts.asan_cells_kept; ShadowRwOn.shadow_rw_on_mono / shadow_rw_on_union.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here names a
   frame-route identifier (the local lemmas name ACtlCutP / lib/Lib / AsanRT vocabulary only; frame-route lemmas are
   used inside proofs, cited qualified).  The six twin modules (YI04 YI16 YK11 YK1b YM05 YO09) and the lib/Lib
   modules are written fully qualified and Required by absolute path.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are qualified everywhere.

   BUILD STATE: type-checked with cb build on a build machine (workspace (internal path)) on a working branch 1899bed1aee;
   the build of record is the lane's cbrec run (report).  Section hypotheses: LAWS and TFIB_SYMS only.  No Axiom, no
   Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan A.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memcpy_c_on A.Prog.sh_word_on A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.RcAsanFPLib A.Prog.SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F23 A.Prog.Seg.F23Fs_on A.Prog.Seg.B7Cuts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ProgWorldShadow.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local lemmas (no Section variable). *)

(* `outside` of the run's three-interval write list, both ways. *)
Lemma f23g_out3 : forall l1 h1 l2 h2 l3 h3 x,
  ~ (l1 <= x < h1) -> ~ (l2 <= x < h2) -> ~ (l3 <= x < h3) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(l1, h1); (l2, h2); (l3, h3)] x.
Proof.
  intros l1 h1 l2 h2 l3 h3 x H1 H2 H3. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact I].
Qed.

Lemma f23g_in3 : forall l1 h1 l2 h2 l3 h3 x,
  ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(l1, h1); (l2, h2); (l3, h3)] x ->
  (l1 <= x < h1) \/ (l2 <= x < h2) \/ (l3 <= x < h3).
Proof.
  intros l1 h1 l2 h2 l3 h3 x H.
  destruct (Z_le_dec l1 x); destruct (Z_lt_dec x h1); try (left; split; assumption).
  all: destruct (Z_le_dec l2 x); destruct (Z_lt_dec x h2); try (right; left; split; assumption).
  all: destruct (Z_le_dec l3 x); destruct (Z_lt_dec x h3); try (right; right; split; assumption).
  all: exfalso; apply H; apply f23g_out3; lia.
Qed.

(* B7Cuts.b7_spill_keep over ACtlCutP.spill (spill / q64 / rg are SlotInv's text verbatim, so it applies by
   conversion). *)
Lemma f23g_spill_keep : forall (regs regs' : bvmap 5 word) (mem mem' : word -> option byte)
    (W : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (A off v : Z),
  A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch W mem mem' ->
  (forall x, A <= x < A + 416 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  0 <= off -> off + 8 <= 416 ->
  A.ACtlCutP.spill regs mem off v -> A.ACtlCutP.spill regs' mem' off v.
Proof.
  intros regs regs' mem mem' W A off v H9 HA0 HA E9 MU HWA Ho0 Ho1 Hs.
  exact (A.Prog.Seg.B7Cuts.b7_spill_keep regs regs' mem mem' W A off v H9 HA0 HA E9 MU HWA Ho0 Ho1 Hs).
Qed.

(* B7Cuts.b7_flsi_keep over ACtlCutP.FLSI (f1_IN without the input block's In fact: see the header). *)
Lemma f23g_flsi_keep : forall (cx : A.ACtlCut.ctlcx) (j : nat) (fr : Z) (regs regs' : bvmap 5 word)
    (mem mem' : word -> option byte) (W : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (A : Z),
  A.ACtlCutP.FLSI cx j fr regs mem -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch W mem mem' ->
  (forall x, A <= x < A + 416 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall i, 0 <= i < 6 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 38 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (fr + 2688 + i))) ->
  (forall i, 0 <= i < 72 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (A.ACtlCutP.fragb fr + i))) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + Z.of_nat (length (A.ACtlCut.c_in cx)) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall i, 0 <= i < A.ACtlCut.c_n cx ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i))) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk segs mem' fr (fr + A.ACtlCutP.FRAME_BYTES) ->
  A.ACtlCutP.FLSI cx j fr regs' mem'.
Proof.
  intros cx j fr regs regs' mem mem' W A
    (((F40 & F120 & F136 & F160 & F168 & F176 & F208 & P248 & Fout6 & Pin & Pin2 & P184 & P256 & P264 & P272 &
       P32) &
      F128 & Fstk & F144 & Fid17) &
     F216 & F224 & F248 & (Fin1 & Fin2) & FC)
    H9 HA0 HA E9 MU HWA HWsh HWsh38 HWsh72 HWin HWinsh Hstk'.
  pose proof (f23g_spill_keep regs regs' mem mem' W A) as Kq.
  assert (HWsh17 : forall i, 0 <= i < 17 ->
            OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (fr + 2691 + i))).
  { intros i Hi. replace (fr + 2691 + i) with (fr + 2688 + (i + 3)) by lia. apply HWsh38. lia. }
  assert (Kin : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem' (A.ACtlCut.c_p cx)
                  (A.ACtlCut.c_in cx))
    by exact (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ Fin2 MU HWin).
  assert (Kad : A.AsanRT.addressable mem' (A.ACtlCut.c_p cx) (A.ACtlCut.c_n cx))
    by exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' _ _ MU HWinsh Fin1).
  destruct FC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & A72 & A38 & C72 & C64 & C56 & C48).
  split; [split|].
  { split; [apply (Kq 40 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F40]|].
    split; [apply (Kq 120 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F120]|].
    split; [apply (Kq 136 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F136]|].
    split; [apply (Kq 160 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F160]|].
    split; [apply (Kq 168 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F168]|].
    split; [apply (Kq 176 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F176]|].
    split; [apply (Kq 208 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F208]|].
    split; [apply (Kq 248 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P248]|].
    split; [exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' (fr + 2624) 6 MU HWsh Fout6)|].
    split; [exact Kin|].
    split; [intros _; exact Kad|].
    split; [apply (Kq 184 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P184]|].
    split; [apply (Kq 256 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P256]|].
    split; [apply (Kq 264 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P264]|].
    split; [apply (Kq 272 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P272]|].
    apply (Kq 32 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P32]. }
  { split; [apply (Kq 128 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F128]|].
    split; [exact Hstk'|].
    split; [apply (Kq 144 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F144]|].
    exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' (fr + 2691) 17 MU HWsh17 Fid17). }
  split; [apply (Kq 216 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F216]|].
  split; [apply (Kq 224 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F224]|].
  split; [apply (Kq 248 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F248]|].
  split; [split; [exact Kad | exact Kin]|].
  split; [apply (Kq 256 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C256]|].
  split; [apply (Kq 184 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C184]|].
  split; [apply (Kq 192 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C192]|].
  split; [apply (Kq 80 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C80]|].
  split; [apply (Kq 88 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C88]|].
  split; [apply (Kq 96 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C96]|].
  split; [apply (Kq 272 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C272]|].
  split; [apply (Kq 264 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C264]|].
  split; [exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' (A.ACtlCutP.fragb fr) 72 MU HWsh72 A72)|].
  split; [exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' (fr + 2688) 38 MU HWsh38 A38)|].
  split; [apply (Kq 72 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C72]|].
  split; [apply (Kq 64 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C64]|].
  split; [apply (Kq 56 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C56]|].
  apply (Kq 48 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact C48].
Qed.

(* B7Cuts.b7_B7K_keep over ACtlCutP.B7K. *)
Lemma f23g_b7k_keep : forall (cx : A.ACtlCut.ctlcx) (j : nat) (phi fr : Z) (regs regs' : bvmap 5 word)
    (mem mem' : word -> option byte) (W : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (A : Z),
  A.ACtlCutP.B7K cx j phi fr regs mem -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch W mem mem' ->
  A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 18 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 21 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 22 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 23 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 24 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24 ->
  (forall x, A <= x < A + 416 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall x, phi <= x < phi + A.ACtlCutP.flen cx j -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2840 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W x) ->
  (forall i, 0 <= i < 35 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside W (A.AsanRT.shadow_addr (fr + 2880 + i))) ->
  A.ACtlCutP.B7K cx j phi fr regs' mem'.
Proof.
  intros cx j phi fr regs regs' mem mem' W A
    ((Hj & H21 & HOUR) & H23 & H22 & Hp0 & Hp50 & Hfl & Hblk & H280 & H24 & H18 & H152 & Hg & Hph & Hlen &
     ((HIDB & Hidok) & (HFGB & Hfgok) & (S104 & S112 & Hbody & Hab & HFI)) & (S136 & S120 & S176))
    MU H9 HA0 HA E9 E18 E21 E22 E23 E24 HWA HWphi HWfr HWB HWBsh.
  pose proof (f23g_spill_keep regs regs' mem mem' W A) as K.
  unfold A.ACtlCut.rgv in H18, H21, H22, H23, H24.
  split.
  { split; [exact Hj|]. split; [unfold A.ACtlCut.rgv; rewrite E21; exact H21|].
    unfold A.ACtlCutP.OURb in *. apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ HOUR MU).
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.OUR_length.
    intros x Hx. apply HWfr. lia. }
  split; [unfold A.ACtlCut.rgv; rewrite E23; exact H23|]. split; [unfold A.ACtlCut.rgv; rewrite E22; exact H22|].
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|].
  split.
  { apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ Hblk MU). rewrite A.Prog.Seg.B7Cuts.b7_tblk_len.
    intros x Hx. apply HWphi. lia. }
  split; [apply (K 280 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact H280]|].
  split; [unfold A.ACtlCut.rgv; rewrite E24; exact H24|].
  split; [unfold A.ACtlCut.rgv; rewrite E18; exact H18|].
  split; [apply (K 152 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact H152]|].
  split.
  { apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ Hg MU). rewrite A.Prog.Seg.B7Cuts.b7_tg_len.
    intros x Hx. apply HWphi. lia. }
  split.
  { apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ Hph MU). intros x Hx. apply HWphi. lia. }
  split; [exact Hlen|].
  split.
  { split; [|split].
    - split; [|exact Hidok]. unfold A.ACtlCutP.IDBe in *.
      apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ HIDB MU). rewrite A.Prog.Seg.B7Cuts.b7_tID_len.
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.ID_SIZE.
      intros x Hx. apply HWfr. lia.
    - split; [|exact Hfgok]. unfold A.ACtlCutP.FGBe in *.
      apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ HFGB MU). rewrite A.Prog.Seg.B7Cuts.b7_tFG_len.
      intros x Hx. apply HWfr. lia.
    - split; [apply (K 104 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S104]|].
      split; [apply (K 112 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S112]|].
      split.
      { apply (A.Prog.RcAsanFPLib.fl_bytes W mem mem' _ _ Hbody MU).
        pose proof (A.Prog.Seg.B7Cuts.b7_fsbody_len (A.ACtlCut.c_in cx) (S j)) as Hbl.
        intros x Hx. apply HWB. lia. }
      split; [exact (A.Prog.Seg.B7Cuts.b7_addr_munch W mem mem' (fr + 2880) 35 MU HWBsh Hab) | exact HFI]. }
  split; [apply (K 136 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S136]|].
  split; [apply (K 120 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S120]|].
  apply (K 176 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S176].
Qed.

(* A byte a const row of the bundle names (CtrlTSyms' ts_const: as_const B ly = Tfib_const ly) is read by the view
   at every AR state, so it is not hidden (AR's am_const, ProgWorldVisFrame.vis_of_aview).  The extraction is
   a Theorem Labs lane's ctl_gshadow_of_AR's (ProgWorldShadow.v, first drafted as ctl_gshadow_of_AR_fixed at 1888d8b45bf). *)
Lemma f23g_const_vis : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    (B : Reusable.YG0f.asyms) ly S (W : Reusable.YA0n.world segs) m md s k,
  A.AF0m.CtrlTSyms B -> Reusable.YG0n.AR segs B ly S W m md ->
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum s) k) (A.AF0m.Tfib_const ly) ->
  Reusable.YA0n.w_H W (Z_to_bv 64 s) = false.
Proof.
  intros fx rc B ly S W m md s k HTS HAR Hin. destruct HAR as [HARm _].
  assert (Hc : Forall (Reusable.YG0f.cell_holds B ly (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m))
                 (Reusable.YG0f.as_const B ly)) by (destruct HARm; assumption).
  rewrite (A.AF0m.ts_const B HTS ly), Forall_forall in Hc.
  specialize (Hc _ Hin).
  unfold Reusable.YG0f.cell_holds, Reusable.YG0f.z1, Reusable.YG0f.c1 in Hc.
  cbn [Reusable.YG0f.c_at Reusable.YG0f.c_w Reusable.YG0f.c_val Reusable.YG0f.aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)).
  change (Z.of_nat 0) with 0 in Hc. rewrite Z.add_0_r in Hc.
  apply (A.ProgWorldVisFrame.vis_of_aview segs W m s). rewrite Hc. discriminate.
Qed.

(* Route (C) region lemma: an aligned shadow-word range (A.Prog.sh_word_on) inside the owned class-6 frame is a
   cut_shadow byte ((F) disjunct, A.ACtlRtC.v:25-28). *)
Lemma glue_f23_frame_sh : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) pos fr p n a,
  In (6, pos) (Reusable.YG01.frames S) -> Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 32 = 0 ->
  fr + 64 <= p -> p + n + 64 <= fr + 4096 ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S pos fr p n a Hin Efa H32 Hlo Hhi (Hn & Ha).
  left. exists 6, pos. split; [exact Hin|]. rewrite Efa.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueF23.

(* ACtl.v's Section shape, restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A825a0_at := (A.ACtlCutP.C_A825a0_at B).
Local Notation C_A825c8_at := (A.ACtlCutP.C_A825c8_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws and the bundle's symbol facts: ACtl.v's own Section hypotheses LAWS and TFIB_SYMS. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* A class-6 frame of the journal's state lies above the image: a Theorem Labs lane's PROVED, premise-free
   A.ProgWorld_Fs.ctl_frame_above_img (statement ProgWorld.ctl_frame_above_img_stmt, any class) at cid = 6, as
   a Theorem Labs lane's A3 / A4 / R4 cite it (a Theorem Labs lane 07:4xZ); IMG_HI = 0x5fe000 (A/Prog/ImgBounds.v).  This replaces the
   Section hypothesis kit_frame6_above_img the first draft carried. *)
Lemma f23g_frame6_above_img : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  A.Prog.ImgBounds.IMG_HI <= Reusable.YG0f.frame_addr ly 6 pos.
Proof.
  intros ly S W mem md pos HAR Hin. unfold A.Prog.ImgBounds.IMG_HI.
  exact (A.ProgWorld_Fs.ctl_frame_above_img B ly S W mem md 6 pos HAR Hin).
Qed.

(* RECORD AF0m rows, the shadow of PORTSC's 64-byte hull [0x21180, 0x211c0).  The glue base carries a Theorem Labs lane's RECORD
   lib/A/AF0m.v (blob 44930bfd861 (the blob this tree had at release c5e779efe8c) = a working branch e56483f863b), so each row is a proved
   fact about its definitions (the first draft carried them as Section hypotheses; the planning core's zero-shadow
   row 4 (0x20ec0, 0xa4380 - 0x20ec0) was a stand-in, a Theorem Labs lane 05:52Z). *)
(* AF0m.v:2956, Tfib_zero_shadow's second row: the granule 0x21180 (PORTSC's first 8 bytes) has zero shadow. *)
Lemma TFIB_ZSH_21180 : In (0x21180, 0x21188 - 0x21180) A.AF0m.Tfib_zero_shadow.
Proof. unfold A.AF0m.Tfib_zero_shadow. apply in_cons. apply in_eq. Qed.
(* AF0m.v:2956, Tfib_zero_shadow's third row: the granules 0x211a0 .. 0x211df have zero shadow. *)
Lemma TFIB_ZSH_211A0 : In (0x211a0, 0x211e0 - 0x211a0) A.AF0m.Tfib_zero_shadow.
Proof. unfold A.AF0m.Tfib_zero_shadow. do 2 apply in_cons. apply in_eq. Qed.
(* AF0m.v:2176-2178, rows 8 / 9 / 10 of Tfib_const_shadow (Tfib_const = Tfib_const_sym ++ Tfib_const_abs ++
   Tfib_const_shadow, AF0m.v:2954): PORTSC's partial granule 0x21188 (4 bytes addressable) and its redzone granules
   0x21190 / 0x21198 (0xf9). *)
Lemma TFIB_CSH_PORTSC : forall ly,
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum 0x7fffc231) 0x4) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum 0x7fffc232) 0xf9) (A.AF0m.Tfib_const ly) /\
  In (Reusable.YG0f.z1 (Reusable.YG0f.ANum 0x7fffc233) 0xf9) (A.AF0m.Tfib_const ly).
Proof.
  intros ly. unfold A.AF0m.Tfib_const.
  split; [|split]; apply in_or_app; right; apply in_or_app; right; unfold A.AF0m.Tfib_const_shadow.
  - do 8 apply in_cons. apply in_eq.
  - do 9 apply in_cons. apply in_eq.
  - do 10 apply in_cons. apply in_eq.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F23 : forall POST (j : nat), CF POST (ix_cut C_A825c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A825a0_at = FRAC /\ b7_body, ACtlCutP.v:2596-2604). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A825a0_at A.ACtlCutP.ixn A.ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & HBODY).
  destruct HBODY as (phi & HP & Hn & Hj & HHB & HFLSI & HK & HPb).
  destruct HPb as (R10w & R20w).
  (* constants *)
  assert (KFB : A.ACtlCutP.FRAME_BYTES = 3136) by reflexivity.
  assert (KFS : A.ACtlCutP.FRAME_SHADOW = 392) by reflexivity.
  assert (KFB' : A.Prog.SlotInv.FRAME_BYTES = 3136) by reflexivity.
  assert (KFS' : A.Prog.SlotInv.FRAME_SHADOW = 392) by reflexivity.
  assert (KAPP : A.AsanRT.APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : A.AsanRT.HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KMC : A.Prog.asan_memcpy_c.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (KSTK : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (KPO : A.Prog.Seg.F23.PORTSC = 135552) by reflexivity.
  assert (KIL : A.Prog.ImgBounds.IMG_LO = 65536) by reflexivity.
  assert (KIH : A.Prog.ImgBounds.IMG_HI = 6283264) by reflexivity.
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof Reusable.YCbq.asan_consts as (C1 & _).
  (* G2: the journal's pieces *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & Hpres & Hstk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
  (* G2: the owned class-6 frame *)
  assert (Hin : In (6, A.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (E3 : Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & Hfc & Hfapp).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & _ & Hfsh).
  pose proof (f23g_frame6_above_img ly3 S3 W3 mem3 md3 (A.ACtlCut.c_fpos cx) HAR Hin) as HGT.
  rewrite E3 in Hf4096, Hfc, Hfapp, HGT, Hfsh. rewrite FB6 in Hfc, Hfapp, Hfsh.
  destruct Hfapp as (_ & Hfloc).
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfloc.
  (* G2: FRAC's pins and bounds (the destruct ends in `_`: FRAC gains a conjunct, a Theorem Labs lane announced) *)
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hf32; Z.div_mod_to_equations; lia).
  assert (ESf : A.ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  (* G2: B7K's and FLSI's pieces the run reads *)
  pose proof HK as (_ & _ & _ & Hphi0 & Hphi50 & Hfl & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S136 & _ & _)).
  pose proof HFLSI as ((_ & _ & Fstk & _ & _) & _).
  (* G2: a live block of the state lies off the run's writes, and so does its shadow *)
  assert (BLK : forall p n, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> 0 < n ->
     (forall x, p <= x < p + n ->
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
          [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)] x) /\
     (forall i, 0 <= i < n ->
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
          [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)]
          (A.AsanRT.shadow_addr (p + i)))).
  { intros p n Hpn Hn0.
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 (A.ACtlCut.c_fpos cx) HAR Hpn Hin)
      as Hsep.
    assert (Ereq : Reusable.YG00.req_size n = n)
      by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec n 0); lia).
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
    rewrite Ereq in Hpceil, Hpapp, Hsep. rewrite E3, FB6 in Hsep.
    destruct Hpapp as (_ & Hploc).
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hploc.
    split.
    - intros x Hx. rewrite ESf. apply f23g_out3; lia.
    - intros i Hi. rewrite ESf. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. apply f23g_out3; lia. }
  (* the live block of the turn, (phi, flen cx j), from the body's Permutation *)
  assert (Hphin : In (phi, A.ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (BLK phi (A.ACtlCutP.flen cx j) Hphin ltac:(lia)) as (HWphi & HWphish).
  (* the input block (c_p, c_n): in the entry's ablocks by the lib pre (n > 0), still live by the journal (FP = []) *)
  pose proof HB as ((_ & _ & _ & _ & Hpn & Hnlen & _) & _).
  assert (HWin : (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + Z.of_nat (length (A.ACtlCut.c_in cx)) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
       [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)] x) /\
    (forall i, 0 <= i < A.ACtlCut.c_n cx ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
       [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)]
       (A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i)))).
  { destruct Hpn as [(Hn00 & _) | (Hnpos & HinE)].
    - split; intros; lia.
    - assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
      assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { destruct (in_dec Hdec (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
          as [Hi3 | Hni]; [exact Hi3|].
        exfalso.
        assert (Hr0 : 0 <= 0 < Reusable.YG00.req_size (A.ACtlCut.c_n cx))
          by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia).
        destruct (Hblk _ _ 0 HinE Hni Hr0) as (r & Hr & _). destruct Hr. }
      destruct (BLK _ _ Hin3 ltac:(lia)) as (H1 & H2).
      split; [intros x Hx; apply H1; lia | exact H2]. }
  destruct HWin as (HWin & HWinsh).
  (* the 12 destination bytes, carved from FLSH's frame window *)
  assert (Hsub : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs mem3 (fr + 128) (fr + 140)).
  { destruct Fstk as (Hs0 & Hs1 & Hsv). split; [lia|]. split; [lia|].
    intros a Ha. apply Hsv. lia. }
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk_carve A.Img0.rsegs mem3 (fr + 128) (fr + 140) 12
              Hsub ltac:(cbn; lia)) as (_ & junk & RWq).
  replace (fr + 140 - Z.of_nat 12) with (fr + 128) in RWq by (cbn; lia).
  (* G2: the run's premises, then the run (f23_evt_Fs_on at RNG_W (w_H W3), lo := c_sp cx - 32768) *)
  pose proof (A.Prog.Seg.F23Fs_on.f23_evt_Fs_on (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 1)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 2)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 3)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 4)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 5)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 6)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 7)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 8)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 9)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 10)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 11)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 12)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 13)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 14)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 15)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 16)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 17)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 18)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 19)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 20)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 21)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 22)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 23)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 24)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 25)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 26)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 27)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 28)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 29)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 30)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs3 31)
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
    mem3 sp A fr (A.ACtlCutP.Sfr fr) (A.ACtlCut.c_sp cx - 32768) junk) as HRUN.
  specialize (HRUN R2 R9 R19 (eq_trans R10w (eq_sym R20w)) eq_refl ltac:(lia) Hfr8 HGT ltac:(lia)).
  specialize (HRUN ltac:(intros a Ha; unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END; lia)).
  specialize (HRUN ltac:(left; lia) ltac:(lia) HspA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  specialize (HRUN ltac:(rewrite ESf; lia) ltac:(rewrite ESf; lia) ltac:(rewrite ESf; lia)).
  specialize (HRUN (A.Prog.Seg.B7Cuts.b7_spill_at regs3 mem3 A 136 (fr + 128) R9 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia) S136)).
  specialize (HRUN RWq).
  (* PORTSC's 12 bytes: the record's zero-shadow row (0x21180, 8) for the first granule and its partial-granule
     shadow row (0x7fffc231 := 4) for the next 4 bytes (TFIB_ZSH_21180, TFIB_CSH_PORTSC), through
     ProgWorldShadow.ctl_global_shadow_of_AR *)
  assert (Hzin : In (0x21180, 0x21188 - 0x21180) (Reusable.YG0f.as_zero_shadow B))
    by (rewrite (A.AF0m.ts_zsh B TFIB_SYMS); exact TFIB_ZSH_21180).
  assert (Hzin2 : In (0x211a0, 0x211e0 - 0x211a0) (Reusable.YG0f.as_zero_shadow B))
    by (rewrite (A.AF0m.ts_zsh B TFIB_SYMS); exact TFIB_ZSH_211A0).
  destruct (TFIB_CSH_PORTSC ly3) as (Cs1 & Cs2 & Cs3).
  specialize (HRUN (A.ProgWorldShadow.ctl_global_shadow_of_AR B TFIB_SYMS LAWS ly3 S3 W3 mem3 md3
                      A.Prog.Seg.F23.PORTSC 12 _ HAR
                      ltac:(rewrite KPO; reflexivity) ltac:(lia) Hzin ltac:(cbn [fst]; lia) ltac:(cbn [fst snd]; lia)
                      (fun _ => Cs1) ltac:(unfold Reusable.YG0f.kImgEnd; lia))).
  (* the 8 shadow bytes of PORTSC's 64-byte hull, [0x7fffc230, 0x7fffc238), are visible: each one is a zero-shadow
     row byte or a const shadow row byte of the record AF0m, so the view reads it, so it is not hidden *)
  assert (Hvis_sh : forall a, 0x7fffc230 <= a < 0x7fffc238 -> Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha.
    pose proof (Reusable.YG0d.al_zshadow segs B LAWS ly3 S3 W3 mem3 md3 (0x21180, 0x21188 - 0x21180) HAR
                  (or_intror Hzin)) as Z1.
    pose proof (Reusable.YG0d.al_zshadow segs B LAWS ly3 S3 W3 mem3 md3 (0x211a0, 0x211e0 - 0x211a0) HAR
                  (or_intror Hzin2)) as Z2.
    cbn [fst snd] in Z1, Z2. unfold Reusable.YG0v.zero_shadow, Reusable.YG0v.shadow_of_addr in Z1, Z2.
    assert (Ea : a = 0x7fffc230 \/ a = 0x7fffc231 \/ a = 0x7fffc232 \/ a = 0x7fffc233 \/ 0x7fffc234 <= a < 0x7fffc238)
      by lia.
    destruct Ea as [-> | [-> | [-> | [-> | Ea]]]].
    - apply (A.ProgWorldVisFrame.vis_of_aview segs W3 mem3).
      assert (E : Reusable.YG0f.SHADOW_OFF + 0x21180 / 8 + 0 = 0x7fffc230) by reflexivity.
      rewrite <- E, (Z1 0 ltac:(lia)). discriminate.
    - exact (f23g_const_vis B ly3 S3 W3 mem3 md3 _ _ TFIB_SYMS HAR Cs1).
    - exact (f23g_const_vis B ly3 S3 W3 mem3 md3 _ _ TFIB_SYMS HAR Cs2).
    - exact (f23g_const_vis B ly3 S3 W3 mem3 md3 _ _ TFIB_SYMS HAR Cs3).
    - apply (A.ProgWorldVisFrame.vis_of_aview segs W3 mem3).
      assert (E : Reusable.YG0f.SHADOW_OFF + 0x211a0 / 8 + (a - 0x7fffc234) = a)
        by (unfold Reusable.YG0f.SHADOW_OFF; lia).
      rewrite <- E, (Z2 (a - 0x7fffc234) ltac:(lia)). discriminate. }
  (* route (C): the entry's ctl_rt_C B ly3 S3 mem3 (ACtlRtC.v:44-46) and the run's region, from the union of its
     two regions: the frame's own shadow ((F)) and the image's shadow (PORTSC) *)
  destruct Hrt as (Hac & Hcut & Himg & Hro).
  assert (HSW : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.F23Fs_on.f23_evt_Fs_shadow_R fr (A.ACtlCutP.Sfr fr)) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (fun a => A.ACtlRtC.cut_shadow B ly3 S3 a \/ A.ACtlRtC.img_shadow a)
             _ mem3); [| exact (A.ShadowRwOn.shadow_rw_on_union _ _ mem3 Hcut Himg)].
    intros a Ha.
    unfold A.Prog.Seg.F23Fs_on.f23_evt_Fs_shadow_R, A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Ha.
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit in Ha by (rewrite ?KPO; lia).
    destruct Ha as [Ha | [Ha | Ha]].
    - (* the two frame shadow stores: the owned frame's shadow, (F) *)
      left. left. exists 6, (A.ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite E3, FB6.
      rewrite ESf in Ha. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - (* the copy's source words over [PORTSC, PORTSC + 12): the image's shadow *)
      right. destruct Ha as (_ & Ha).
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
      rewrite KPO in Ha.
      exists (8 * (a - Reusable.YG0f.SHADOW_OFF)).
      unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    - (* the copy's destination words over [fr + 128, fr + 140): the owned frame's shadow, (F) *)
      left. exact (glue_f23_frame_sh B ly3 S3 (A.ACtlCut.c_fpos cx) fr (fr + 128) 12 a Hin E3 Hf32
                     ltac:(lia) ltac:(lia) Ha). }
  specialize (HRUN Hac HSW Hro).
  (* the copy's stack window [c_sp - 32768, sp), present by the journal *)
  specialize (HRUN ltac:(split; [lia|]; split; [lia|];
                         intros a Ha; destruct (Hpres a ltac:(lia)) as [_ (b & Hb)];
                         split; [unfold wview, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa; rewrite Hb; discriminate
                                | exists b; unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd,
                                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa; rewrite Hb; reflexivity])).
  (* the footprint ranges, from visibility *)
  specialize (HRUN ltac:(apply A.ProgBridge.rng_RNG_W; [rewrite ESf; lia | rewrite ESf; lia |];
                         intros a Ha; destruct (Hfsh (a - Reusable.YG0f.shadow_addr fr)) as [[Hv _] _];
                         [unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; rewrite ESf in Ha; lia|];
                         replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hv by ring;
                         exact Hv)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
                      (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 136) 8 HJ
                         ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_bytes_RNG_W _)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
                      (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 2224) 2224 HJ
                         ltac:(lia) ltac:(lia)))).
  pose proof (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) (fr + 128) 12 HAR Hin
                ltac:(rewrite E3; lia) ltac:(rewrite E3, FB6; lia)) as (HV128 & HV128s).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ HV128)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _
                      (A.ProgBridge.range_visible_sub _ _ _ A.Prog.Seg.F23.PORTSC 12 (A.ProgBridge.img_vis_W W3)
                         ltac:(lia) ltac:(lia) ltac:(lia)))).
  specialize (HRUN ltac:(destruct (HV128s ltac:(lia) ltac:(rewrite E3; Z.div_mod_to_equations; lia)
                                     ltac:(rewrite E3, FB6; Z.div_mod_to_equations; lia)) as [E0 | V];
                         [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V)])).
  specialize (HRUN ltac:(right; apply A.ProgBridge.rng_RNG_W;
                         unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr,
                           A.AsanRT.ASAN_K; rewrite KPO; [lia | lia |];
                         intros a Ha; apply Hvis_sh; lia)).
  specialize (HRUN ltac:(destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2224) 2224 HAR
                                     ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as [E0 | V];
                         [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V)])).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's map mkR_of regs3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc (ix_cut C_A825a0_at [Z.of_nat j])) with 0x825a0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x825a0) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _
                (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the lift; the continuation keeps the fsteps run *)
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (msE & Hrun & HQ).
  pose proof (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)) as Hfp.
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ msE md3 _ (POST cx) Hrun Hfp).
  intros md' Hsbm.
  pose proof (A.ProgWorld.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) _ _ _ Hrun Hfp) as (Hgr & _).
  (* G5: the run's post *)
  destruct HQ as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K20 &
                  MU & WM & RO' & SW' & ST' & HBS & HAD').
  subst msE.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A825c8_at [Z.of_nat j])) R m' md') (POST cx)).
  (* the write set's facts *)
  assert (HWA : forall x, A <= x < A + 416 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
       [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)] x)
    by (intros x Hx; rewrite ESf; apply f23g_out3; lia).
  assert (HWfr : forall x, fr <= x < fr + 128 \/ fr + 140 <= x < fr + 3136 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
       [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)] x)
    by (intros x Hx; rewrite ESf; apply f23g_out3; lia).
  assert (HWsh : forall c i, 144 <= c -> 0 <= i -> c + i < 3136 ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside
       [(sp - 2224, sp); (fr + 128, fr + 140); (A.ACtlCutP.Sfr fr + 16, A.ACtlCutP.Sfr fr + 18)]
       (A.AsanRT.shadow_addr (fr + c + i))).
  { intros c i Hc Hi Hci. rewrite ESf. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. apply f23g_out3; lia. }
  (* the frame window stays present and writable *)
  assert (Hstk' : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk segs m' fr (fr + A.ACtlCutP.FRAME_BYTES)).
  { destruct Fstk as (Hs0 & Hs1 & Hsv). split; [exact Hs0|]. split; [exact Hs1|].
    intros a Ha. destruct (Hsv a Ha) as (Hwv & (b & Hb)). split; [exact (WM _ Hwv)|].
    destruct (Z_lt_le_dec a (fr + 128)) as [L1|L1]; [| destruct (Z_lt_le_dec a (fr + 140)) as [L2|L2]].
    - exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in *.
      rewrite (MU (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a)); [exact Hb|].
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by lia. apply HWfr. lia.
    - pose proof HBS as (_ & _ & HH).
      pose proof (HH (Z.to_nat (a - (fr + 128))) ltac:(rewrite A.Prog.Seg.F23.f23_ports_len; lia)) as HE.
      rewrite Z2Nat.id in HE by lia.
      replace (fr + 128 + (a - (fr + 128))) with a in HE by lia.
      destruct (nth_error A.Prog.Seg.F23.ports_c_bytes (Z.to_nat (a - (fr + 128)))) as [b'|] eqn:EN.
      + exists b'. exact HE.
      + exfalso. apply nth_error_None in EN. rewrite A.Prog.Seg.F23.f23_ports_len in EN. lia.
    - exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in *.
      rewrite (MU (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a)); [exact Hb|].
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by lia. apply HWfr. lia. }
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: ProgWorld.ajournal_of_fsteps over the run's munch list; each written byte is awr_byte *)
    match type of Hrun with
    | Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
        apply (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _ _
                 HJ Hrun Hfp MU Hsbm)
    end.
    intros a Ha Ho. apply f23g_in3 in Ho.
    unfold Reusable.YCbq.awr_byte.
    destruct Ho as [Ho | [Ho | Ho]].
    + left. lia.
    + right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite E3, FB6. lia.
    + right; right; right. exists 6, (A.ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite E3, FB6.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESf in Ho. lia.
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A825c8_at (ACtlCutP.v:2608-2618) *)
    cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCut.ix_cut A.ACtlCutP.C_A825c8_at A.ACtlCutP.ixn
                              A.ACtlCutP.ixz nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    split.
    { (* FRAC: its memory part kept (kitmem_frac_keep), its registers moved (Kit.kit_frac_move) *)
      apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact K2 | exact K3 | exact K4 | exact K8
                                                                    | exact K9 | exact K19 | exact K26].
      apply (A.ACtlG.KitMem.kitmem_frac_keep B cx fr fr regs3 mem3 m' _ HFRAC MU Hgr ltac:(lia)).
      - intros A0 HA0 x Hx. unfold A.ACtlCut.rgv in HA0, R9.
        pose proof (A.Prog.Seg.F23.f23_bv_eq_Z A0 A (eq_trans (eq_sym HA0) R9)) as Hc.
        rewrite ESf. apply f23g_out3; intros [Q1 Q2]; revert Hc Hx Q1 Q2; Z.div_mod_to_equations; lia.
      - intros x Hx. rewrite ESf. apply f23g_out3; lia.
      - intros x Hx. rewrite ESf. apply f23g_out3; lia. }
    unfold A.ACtlCutP.b7_body.
    exists phi.
    split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hp0 & Hpad). split; [exact Hp0|].
      apply (A.Prog.Seg.B7Cuts.b7_addr_munch _ mem3 m' _ _ MU); [|exact Hpad].
      intros i Hi. apply HWphish. unfold A.ACtlK.a_size in Hi. lia. }
    split.
    { apply (f23g_flsi_keep cx j fr regs3 R mem3 m' _ A HFLSI R9 ltac:(lia) ltac:(lia) K9 MU HWA).
      - intros i Hi. apply (HWsh 2624 i); lia.
      - intros i Hi. apply (HWsh 2688 i); lia.
      - intros i Hi. unfold A.ACtlCutP.fragb. apply (HWsh 2768 i); lia.
      - exact HWin.
      - exact HWinsh.
      - exact Hstk'. }
    split.
    { apply (f23g_b7k_keep cx j phi fr regs3 R mem3 m' _ A HK MU R9 ltac:(lia) ltac:(lia)
               K9 K18 K21 K22 K23 K24 HWA HWphi).
      - intros x Hx. apply HWfr. lia.
      - intros x Hx. apply HWfr. lia.
      - intros i Hi. apply (HWsh 2880 i); lia. }
    (* the exit's own conjuncts: s4 = fr + 128, the three words -7 at fr + 128, the 12 bytes addressable *)
    split; [exact K20|].
    pose proof HBS as HBS'. unfold A.Prog.Seg.F23.ports_c_bytes in HBS'.
    apply (proj1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_app _ m' (fr + 128)
                    A.Prog.Seg.F23.m7w (A.Prog.Seg.F23.m7w ++ A.Prog.Seg.F23.m7w))) in HBS'.
    destruct HBS' as (HBS0 & HBS1).
    unfold A.Prog.Seg.F23.m7w in HBS1 at 1.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in HBS1. cbn [Z.of_nat] in HBS1.
    apply (proj1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_app _ m' (fr + 128 + 4)
                    A.Prog.Seg.F23.m7w A.Prog.Seg.F23.m7w)) in HBS1.
    destruct HBS1 as (HBS1 & HBS2).
    unfold A.Prog.Seg.F23.m7w in HBS2 at 1.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in HBS2. cbn [Z.of_nat] in HBS2.
    split; [unfold A.ACtlCutP.u32, A.Prog.Seg.F23.m7w in *; exact HBS0|].
    split; [unfold A.ACtlCutP.u32, A.Prog.Seg.F23.m7w in *; replace (fr + 132) with (fr + 128 + 4) by lia; exact HBS1|].
    split; [unfold A.ACtlCutP.u32, A.Prog.Seg.F23.m7w in *; replace (fr + 136) with (fr + 128 + 4 + 4) by lia;
            exact HBS2|].
    exact HAD'.
  - (* ctl_rt_C at the same (ly3, S3): asan_cells kept (the writes miss the runtime cells), both regions by the
       run's forall-P post, ro_agree from the run's post *)
    split; [|split; [exact (SW' _ Hcut) | split; [exact (SW' _ Himg) | exact RO']]].
    apply (A.AsanRTFacts.asan_cells_kept _ mem3 m' Hac MU).
    cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.disjoint_from]. rewrite ESf.
    unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. repeat split; try exact I; lia.
Qed.

End GlueF23.
