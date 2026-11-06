(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths and module names changed; 987 of its 1046 lines of code are new or changed and 2016 lines of the source are left out. *)
(* lib/A/ACtlG/R18.v -- GLUE for stage seg_R18 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:700) (an earlier version, blob c4edf0be7fe, not in this delivery), a Theorem Labs lane's route (C) walk shell (from a working branch 1899bed1aee)).
   Written by a Theorem Labs lane's two workers (a Theorem Labs lane, under a Theorem Labs lane's glue programme); single
   writer of this file.  rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R18 : forall POST (b : nat),
       CF POST (ix_cut C_A818d0_at [Z.of_nat b]) -> CF POST (ix_cut C_A81858_at [Z.of_nat b])
   with ACtl.v's own CF / ix_cut / C_* notations (SK := A.AE2k.tfib_sink_head, FP := []), i.e. ACtl.v's (at head :700)
   Section hypothesis seg_R18 character for character.  Segment R18 is [0x81858, 0x818d0): the spill and row
   loads, two shadow-byte checks, the four metadata stores at Sfr fr + 320 .. + 323, and the call to
   declaration_of at 0x818cc, which writes 2304 stack bytes below sp and the 32 declaration bytes at
   decl_slot fr = fr + 2560.

   THE ROUTE (a Theorem Labs lane, 2026-10-29, confirmed to this lane; part of glue-pattern.md, section 8 (a working note, not in this delivery), is SUPERSEDED here)
   The segment's own _F run carries the callee's declaration_of_contract_F_on AS A PREMISE, so the glue SUPPLIES
   that premise with the callee's proved contract and lifts the WHOLE segment run ONCE.  There is no
   split at the call.  THIS STAGE CITES NO LIFT of lib/A/ProgLift/*, and the reason is that an <f>_SRr_at can
   never discharge an <f>_contract_F: it is a different judgement (lib.Reusable.YA0n.SRr against Lib.ExecF.evtF)
   and it takes that very contract as its own premise, so citing it would be circular.  Because the contract
   is supplied directly, the lift's restated premises (ro_agree in place of mem_inv, the per-range
   not-read-only premise, declaration_of_post_ro) are not paid here; what is paid is
   declaration_of_contract_F_on's own premise list, which the _F run discharges internally through
   A.MemNormF.evtF_normalize_ro.  lib.Reusable.YA0nR.SRr_fevt_hid's continuation already hands the hidden-bytes
   fact that lib.Reusable.YCbq.ajournal_exec takes, so there is no _hid placeholder either.

   THE RUN: seg_R18_run_F IS GONE (a Theorem Labs lane 12:59Z).  The run is A.Prog.Seg.R18Fon.r18_evt_F_on, this lane's
   route (C) twin of a Theorem Labs lane's Seg/R18F.v (not in this delivery) r18_evt_F (lib/A/Prog/Seg/R18Fon.v, from a Theorem Labs lane's fold blob
   d8b02189343; Seg/R18F.v (not in this delivery) is unchanged), cited by name.  Its callee premise
   A.Prog.declaration_of_c.declaration_of_contract_F_on (declaration_of_c.v ffd64306c80 (the blob this tree had at release c5e779efe8c), :210) is supplied by
   A.Prog.declaration_ofF.declaration_of_F_holds_on (declaration_ofF.v 0061e2d011e (the blob this tree had at release c5e779efe8c), :2124) at the runtime's
   route (C) proofs A.Prog.asan_memsetF_on.asan_memset_holds_F_on (asan_memsetF_on.v:23, blob 34752af7b24) over
   this image's plain memset proof A.Prog.memset.memset_holds, and A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
   (asan_memcpyF_on.v:24, blob 7fa6770491b).  The twin's HPRE concludes A.Prog.Seg.R18Fon.r18_pre_on, which is
   A.Prog.Seg.R18.r18_pre with its `shadow_rw m1` narrowed to the callee's own region
   A.Prog.declaration_of_c.declaration_of_shadow_R mr D.  A.Prog.Seg.R18 itself builds, and its helper lemmas are
   reused QUALIFIED, never copied.

   ROUTE (C) (L3-recipe.md section 2 (a working note, not in this delivery); lane brief
   L3-lanes.md section 4 (a working note, not in this delivery)).  The entry cut carries
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from), destructed as (HAC & Hcut & Himg & HRO).  No universal
   shadow_rw is derived anywhere; each shadow use reads a region:
   - the stk of the four metadata bytes [Sfr fr + 320, Sfr fr + 324), a premise of the run: Hcut, because the own
     class-6 frame's shadow [Sfr fr, Sfr fr + 512) is cut_shadow's (F) disjunct (HFsh: frames S3 holds
     (6, c_fpos cx), and frame_addr ly3 6 (c_fpos cx) = fr);
   - HPRE's shadow_rw_on (declaration_of_shadow_R mr D) m1: at mem3, the row spans sh_word_on (mr + 24) 32 and
     sh_word_on (mr + 254) 11 from Himg (they lie in the catalogue's shadow-word cover [0x8000bd00, 0x8000be98),
     inside img_shadow: r18g_cat_word_img), and the declaration slot's sh_word_on D 32 from Hcut (it lies in the
     own frame's (F) range: r18g_decl_word_frame); then carried from mem3 to m1 across the four metadata stores
     (r18g_on_keep_meta: the view by wmono, a byte outside [Sfr fr + 320, Sfr fr + 324) by the munch, a byte
     inside by the stores' stk);
   - the exit FRAC's 392 frame-shadow bytes: the (F) range at the exit memory (HFSW').
   EXIT, ROUTE (i), THE REGIONS KEPT: the exit cut's ly / S are the entry's (the journal moves by ajournal_exec at
   ly3 S3), so ctl_rt_C B ly3 S3 m' is asan_cells and ro_agree as before, and Hcut / Himg carried from mem3 to m'
   by the per-byte argument over the composed write set (Hkeep: a byte outside [Sfr fr + 320, Sfr fr + 324) by
   the munch and wmono, a byte inside by the run's four bytes_at .. [Z_to_bv 8 0]).  Route (ii)
   (A.ProgWorldCtlRtC.ctl_rt_C_of_AR) would add ACtl.v's RELRO_IMG; route (i) adds no Section hypothesis.

   THE PROOF, step by step (glue-pattern.md section 3's G1-G5)
   G1  unfold the entry cut: ix_cut's index equation, then C_A81858_at's conjuncts (ACtlCutP.v:1590-1619); the
       index is a NAT index, so ACtlCutP.ixn is in the delta list and Nat2Z.id turns it into b, which the body
       then pins to 0.
   G2  the run's premises, each from VISIBLE state: the geometry (the frame from lib.Reusable.YCbq.frames_bounds
       and A.ProgWorld_Fs.ctl_frame_above_img, the window from the journal's astk_ok and
       lib.Reusable.YG0f.ASAN_CEIL_range, the spill base from FRAC), the memory premises from the body's spills /
       u32s and from the catalogue (all three parts PROVED here, see CAT_GLOBAL below), and the eighteen
       footprint premises through A.ProgBridge.rng_of_visible over A.ProgWorldVisWin.win_vis / win_sh_vis,
       A.ProgWorldVisFrame.frame_vis, A.ProgBridge.img_vis_W / rt_vis_W and the catalogue's shadow-word cover.
   G3  register maps: A.ProgBridge.cfg_at_MS turns the cut's cfg_at into lib.Lib.MState.MS over regs3; the run
       starts at the canonical map, so the WALK is moved there by lib.Reusable.YA0nR.SRr_xregs_eqv.
   G4  lift, at the footprint A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3) (fp_avoids by
       A.ProgBridge.fp_avoids_RNG_W): the run's mstepsF witness is kept, turned into fsteps by
       A.ProgBridge.fsteps_of_mstepsF, and lifted by lib.Reusable.YA0nR.SRr_fsteps together with
       lib.Reusable.YA0nR.fsteps_keeps_hidden -- the two lemmas SRr_fevt_hid is made of (YA0nR.v:64-75).  They
       are used separately because ajournal_exec also needs the run's memory GROWTH (its third premise), which
       comes from the same witness (mem_grows_of_mstepsF below) and which SRr_fevt_hid's continuation, taking
       an arbitrary end state, cannot be connected to.
   G5  the continuation: the run's end map R IS the exit cut's map; the journal moves by
       lib.Reusable.YCbq.ajournal_exec over the composed write set, ctl_rt_C by the kept regions, and each
       exit body conjunct by lib.Lib.Frame.bytes_at_transport / rw_cells_transport or by the run's own post.

   THE WRITE SET is two munches composed: [(Sfr fr + 320, Sfr fr + 324)] for the four metadata stores, then
   [(sp - DECLARATION_OF_K, sp); (decl_slot fr, decl_slot fr + 32)] for the callee; they are weakened onto the
   union Wtot = [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (Sfr fr + 320, Sfr fr + 324)] and composed with
   Lib.Frame.munch_trans / Lib.Frame.wmono_trans.  r18_evt_F_on's CALLER OBLIGATION HPRE (R18Fon.v, as R18F.v:120-124)
   is discharged by producing A.Prog.Seg.R18Fon.r18_pre_on of the memory after the four metadata
   stores.  No byte of a stack-window SHADOW range is written, so lib.Reusable.YCbq.awr_byte's four disjuncts
   suffice (a Theorem Labs lane's 04:50Z gap warning, corrected 04:5xZ, does not apply to this stage).

   FRAC, READ AND RE-ESTABLISHED WITHOUT POSITIONS (a Theorem Labs lane 06:2xZ; the shape of a Theorem Labs lane's R3.v and a Theorem Labs lane's
   r1g_frac_mem).  The entry cut's FRAC is read BY TYPE (r18g_get: each scalar fact asserted by its own statement
   and found by decompose + assumption), and the one lemma here that RE-ESTABLISHES FRAC at a new memory --
   glue_seg_R18 itself, at the exit cut -- walks the goal's conjuncts and closes each by its kind (r18g_frac_leaf):
   a register conjunct through the run's kept registers, an arithmetic one by assumption, every q64 / bytes_at by
   Lib.Frame.bytes_at_transport over the composed write set (the spills by DA, the frame below / above the
   declaration slot by Dfrlo / Dfrhi, the saved registers by Dsaved), the frame shadow re-read from the own frame's
   (F) region at the new memory (the run writes four of its bytes).  No conjunct is named by position, so a Theorem Labs lane's
   announced trailer word q64 m (fr + 4088) (flag_addr ..) needs no edit: the run writes nothing of the frame
   above fr + 2592.  TESTED both ways in a working-tree copy of ACtlCutP.v (reverted, never committed): with
   q64 m (fr + 4088) 0 APPENDED to FRAC and with it INSERTED mid-chain; the build logs are named in the commit
   message.  On a working branch FRAC states the NON-STRICT `c_sp cx <= APPMEM_END` (ACtlCutP.v:1073, batch 4 item B5.4), and
   HSapp reads it in that form.

   SECTION HYPOTHESES (exact text at the declarations below), before -> after this switch:
     before: LAWS, TFIB_SYMS, RELRO_CAT, seg_R18_run_F;  after: LAWS, TFIB_SYMS, RELRO_CAT.
   All three are VERBATIM copies of ACtl.v's Section hypotheses (blob c4edf0be7fe), so ACtl.v discharges seg_R18 with
   glue_seg_R18 B MT XM_LIB RLO RHI LAWS TFIB_SYMS RELRO_CAT.  No ProgWorld statement is carried as a hypothesis.
   - LAWS : ACtl.v:237, the core's AR law record (YCbq.v:207 / YG0d Section j), which ajournal_exec, frames_bounds,
     win_sh_vis and frame_vis take.
   - b7g_frame_GT is GONE (a Theorem Labs lane, 2026-10-29): the frame bound 0x5fe000 <= frame_addr is cited by name as
     A.ProgWorld_Fs.ctl_frame_above_img : A.ProgWorld.ctl_frame_above_img_stmt B (premise-free, every frame class;
     lib/A/ProgWorld.v and ProgWorld_Fs.v taken by path from a working branch fec8db0a380).  It gives
     6283264 <= fr, hence R18F.v's (not in this delivery) `6283264 <= D` and `6283264 <= SHv`.
   The Kit placeholders are GONE: Kit.v builds on the base this file now sits on (a working branch
   46eb24cd4b3, merged), so A.ACtlG.Kit.kit_wx and A.ACtlG.Kit.kit_segs_low are cited by name.
   - CAT_GLOBAL is GONE: all three of its parts are PROVED inside glue_seg_R18 from already-proved lemmas
     (two Theorem Labs lanes, 2026-10-29).  The catalogue BOX_CATALOGUE [CAT, CAT + 3256) = [0x9e800, 0x9f4b8)
     is a registered ASan global of B; in v1.9 its parts were FRA's (lib/A/Prog/Seg/R18.v:798 r18_cat_img, :784
     r18_cat_addr, the shadow cover through AR_zshadow_law), and the cut layer carries none of them.
     . ADDRESSABILITY: A.ProgWorldShadow.ctl_global_shadow_of_AR (: A.ProgWorld.ctl_global_shadow_of_AR_stmt B)
       at g = CAT, n = 3256, r = (0x9e800, 0x9f4b8 - 0x9e800), the catalogue's own entry of the fine list
       A.AF0m.Tfib_zero_shadow (through TFIB_SYMS's ts_zsh); 3256 mod 8 = 0, so no partial-granule row.
     . THE BYTES (route per byte: every byte of the body [0x9e800, 0x9f4b8) takes the arodata route): the entry
       pre's arodata_okS (A.ACfn.tfib_lib_pre_x, ACfn.v:41) at RLO <= a < RHI by ACtl.v's RELRO_CAT, moved to the
       cut by the journal's in-image clause (YCbq.v:362-363); its side conditions hold for the whole body (no
       range of Tfib_owned_static meets it -- the nearest are its redzones [0x9e7d0, 0x9e800) and
       [0x9f4b8, 0x9f7e0) -- the errno word 0x5db76c is far above, the body is below the sink head 0x5fbf08).
       Then A.ProgWorldVisFrame.vis_of_aview and A.ProgWorld.aview_vis_mrd turn the view byte into the memory
       byte (r18g_cat_mbyte), and A.Prog.Seg.R18.r18_img_bytes over A.Prog.Seg.B3Rtm.a_row_img gives the row.
     . THE SHADOW-WORD COVER [0x8000bd00, 0x8000be98) (route per byte): the 407 shadow bytes of the body,
       [0x8000bd00, 0x8000be97), from the catalogue's zero-shadow range (YG0d.al_zshadow) and vis_of_aview; the
       one remaining byte 0x8000be97 = shadow_addr 0x9f4b8, the redzone granule's, is a CONST row
       `z1 (ANum 0x8000be97) 0xf9` (A/AF0m.v:2386), from A.ProgWorld_Fs.pw_row (am_const) and vis_of_aview.
       That composition becomes a citation of A.ProgWorld.ctl_const_vis_of_AR_stmt (a Theorem Labs lane, statement at
       e68ab9226495) when a Theorem Labs lane's proof of it lands.
     . Section hypotheses this adds, both verbatim from ACtl.v: TFIB_SYMS (ACtl.v:252) and RELRO_CAT (ACtl.v:232).
   - seg_R18_run_F is GONE: the run is A.Prog.Seg.R18Fon.r18_evt_F_on (THE RUN above).
   CITED BY NAME, NOT HYPOTHESES: lib.Reusable.YA0nR.SRr_fsteps / fsteps_keeps_hidden / SRr_xregs_eqv;
   A.ProgBridge.fsteps_of_mstepsF, cfg_at_MS, RNG_W, fp_avoids_RNG_W, rng_of_visible, range_visible_sub,
   img_vis_W, rt_vis_W, rng_bytes_RNG_W; A.ProgWorldVisWin.win_vis / win_sh_vis; A.ProgWorldVisFrame.frame_vis;
   lib.Reusable.YCbq.ajournal_exec / frames_bounds / sep_block_frame; lib.Reusable.YG0d.al_frames / al_blocks;
   A.ACtlG.Kit.kit_wx / kit_segs_low; A.Prog.Seg.R18Fon.r18_evt_F_on / r18_pre_on;
   A.Prog.declaration_ofF.declaration_of_F_holds_on, A.Prog.asan_memsetF_on.asan_memset_holds_F_on,
   A.Prog.memset.memset_holds, A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on; A.ShadowRwOn.shadow_rw_on_mono;
   and A.Prog.Seg.R18's helpers (r18_rdn, r18_sub, r18_addr_join, r18_meta0, r18_bytes_of_present,
   r18_addr_keep_rng, r18_keep_low, r18_ro_keep, r18_ro_lt, r18_b1_rd, r18_row_ic, r18_row_oc, r18_row_len,
   r18_decl_len) and A.Prog.Seg.Tac_rt2_b2.a_rtn, A.Prog.Seg.B3Rtm.a_rtm_declok.

   CLOSURE: every Require is qualified, no Import / Export of a project module; no statement here names a
   frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified everywhere.
   Check: grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R18.v -- hits only in comments.
   TWO COPIES OF MANY MODULES are in this file's closure (lib/Reusable vs lib/A/Reusable, lib/Lib vs
   lib/A/Bz/Lib and lib/AZ/Lib), and a partial qualid resolves to whichever was loaded last.  So every core
   name is written lib.Reusable.<M>.x and every lib/Lib name lib.Lib.<M>.x, never Reusable.<M> or Lib.<M>.

   No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every core / lib/Lib name below is written with its unambiguous lib.Reusable. / lib.Lib. prefix (header), so the
   order of these Requires does not decide which copy a name means.  The core's Reusable and lib/Lib are named
   through their directory in the From prefix, so each Require matches exactly one file (ctrlgate rule (c) REQ:
   `Reusable.YK11` under `...lib` also matches A./B./U.Reusable.YK11); the core copies are the intended ones,
   as ACtl.v's walk is stated over them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R18 A.Prog.Seg.Tac_rt2_b2 A.Prog.Seg.B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.declaration_of_c A.Prog.declaration_ofF.
(* the run (this lane's route (C) twin) and its callee's route (C) proofs *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R18Fon A.Prog.sh_word_on A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.memset A.Prog.asan_memsetF_on A.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcDecl Prog.RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Step Cells RngBytes.
(* the core's Reusable, and the walk files stated over it, LAST *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG01 YG0d YG0n YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
Import ListNotations.
Local Open Scope Z_scope.

(* Read one conjunct of a cut shell BY TYPE, never by position, so a conjunct appended to or inserted in the
   shell (a Theorem Labs lane's FRAC trailer word) cannot move it. *)
Ltac r18g_get H T N := assert (N : T) by (decompose [and ex] H; assumption).

(* One conjunct of FRAC at the run's end memory m', from the decomposed FRAC at the start memory m, by its KIND,
   never by its position (glue_seg_R18's exit cut): an arithmetic conjunct by assumption; a register conjunct
   through the kept-register facts K2 .. K26; a q64 / bytes_at conjunct by Lib.Frame.bytes_at_transport over the
   composed write set MU, its range off the writes by one of the four disjointness facts (spills DA, frame below
   the declaration slot Dfrlo, frame above it Dfrhi, saved registers Dsaved); the frame shadow re-read at m' from
   SW : shadow_rw_on (fun a => Sfr fr <= a < Sfr fr + 512) m' (the own frame's (F) region), with the frame-shadow
   range fact SB.  The locals are arguments, as in a Theorem Labs lane's r1g_frac_walk, because a pattern in an `all:` sentence
   cannot name a proof-local variable. *)
Ltac r18g_frac_leaf m m' fr MU DA Dfrlo Dfrhi Dsaved SW SB K2 K3 K4 K8 K9 K19 K26 :=
  first
    [ assumption
    | (unfold ACtlCut.rgv, lib.Reusable.YG0d.spZ in *;
       rewrite ?K2, ?K3, ?K4, ?K8, ?K9, ?K19, ?K26; assumption)
    | (unfold ACtlCutP.q64 in *;
       eapply (lib.Lib.Frame.bytes_at_transport A.AB1v.tfibsegs _ m m'); [eassumption | exact MU |];
       try unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?lib.Lib.Mem.length_le8; cbn [Nat.add Z.of_nat];
       first [ apply DA; lia | apply Dfrlo; lia | apply Dfrhi; lia | apply Dsaved; lia ])
    | (lazymatch goal with |- exists _, _ => idtac end;
       let EFS := fresh "EFS" in
       assert (EFS : Z.to_nat ACtlCutP.FRAME_SHADOW = 392%nat) by (vm_compute; reflexivity);
       rewrite EFS;
       let shx := fresh "shx" in let Hshx := fresh "Hshx" in let Hshl := fresh "Hshl" in
       let kk := fresh "kk" in let Hkk := fresh "Hkk" in let bb := fresh "bb" in let Hbb := fresh "Hbb" in
       destruct (A.Prog.Seg.R18.r18_bytes_of_present 392%nat m' (ACtlCutP.Sfr fr)
                   ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                   ltac:(intros kk Hkk;
                         destruct (SW (ACtlCutP.Sfr fr + Z.of_nat kk) ltac:(cbv beta; lia) ltac:(apply SB; lia))
                           as (_ & bb & Hbb);
                         exists bb; exact Hbb)) as (shx & Hshx & Hshl);
       exists shx; split; [exact Hshx | exact Hshl]) ].

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:155 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Run-level glue this file owns (none of it is a Kit helper). *)

(* The memory of a footprint run only grows (ajournal_exec's third premise). *)
Lemma mem_grows_of_mstepsF : forall RNG ms ms',
  lib.Lib.ExecF.mstepsF A.Img0.rsegs RNG ms ms' -> lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' H. induction H as [ms | ms ms1 ms2 Hs _ IH].
  - apply lib.Reusable.YK1b.mem_grows_refl.
  - eapply lib.Reusable.YK1b.mem_grows_trans; [| exact IH].
    exact (lib.Reusable.YI04.step_mem_grows A.Img0.rsegs _ _
             (lib.Lib.ExecF.mstepF_step A.Img0.rsegs RNG _ _ Hs)).
Qed.

(* Two non-empty intervals that share no point are ordered. *)
Lemma ivl_sep : forall lo1 hi1 lo2 hi2 : Z,
  lo1 < hi1 -> lo2 < hi2 -> (forall x, lo1 <= x < hi1 -> ~ (lo2 <= x < hi2)) ->
  hi1 <= lo2 \/ hi2 <= lo1.
Proof.
  intros lo1 hi1 lo2 hi2 H1 H2 H.
  destruct (Z_le_gt_dec hi1 lo2) as [Hc | G1]; [left; exact Hc |].
  destruct (Z_le_gt_dec hi2 lo1) as [Hc | G2]; [right; exact Hc |].
  exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.

(* The canonical register map of a footprint run's start state, written with YK11's register read. *)
Lemma mkR_of_getr : forall (regs : bvmap 5 word),
  lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 3)
    (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 5) (lib.Reusable.YK11.getr regs 6)
    (lib.Reusable.YK11.getr regs 7) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
    (lib.Reusable.YK11.getr regs 10) (lib.Reusable.YK11.getr regs 11) (lib.Reusable.YK11.getr regs 12)
    (lib.Reusable.YK11.getr regs 13) (lib.Reusable.YK11.getr regs 14) (lib.Reusable.YK11.getr regs 15)
    (lib.Reusable.YK11.getr regs 16) (lib.Reusable.YK11.getr regs 17) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    (lib.Reusable.YK11.getr regs 28) (lib.Reusable.YK11.getr regs 29) (lib.Reusable.YK11.getr regs 30)
    (lib.Reusable.YK11.getr regs 31)
  = lib.Lib.Regs6ss.mkR_of regs.
Proof. intros regs. unfold lib.Lib.Regs6ss.mkR_of, lib.Reusable.YK11.getr. reflexivity. Qed.

(* An empty byte run holds of every memory. *)
Lemma bytes_at_nil : forall (m m0 : word -> option byte) a,
  lib.Lib.Mem.bytes_at segs m a [] -> lib.Lib.Mem.bytes_at segs m0 a [].
Proof.
  intros m m0 a (H1 & H2 & _). split; [exact H1|]. split; [exact H2|].
  intros i Hi. cbn [length] in Hi. lia.
Qed.

(* A present byte of the raw memory gives both halves of lib.Lib.Frame.stk / A.AsanRT.shadow_rw. *)
Lemma present_rw : forall (m : word -> option byte) a b,
  m (Z_to_bv 64 a) = Some b ->
  wview A.Img0.rsegs m (lib.Lib.Mem.wa a) <> None /\
  exists bb, lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa a) = Some bb.
Proof.
  intros m a b Hb. unfold lib.Lib.Mem.wa, wview, lib.Lib.Mem.mrd. rewrite Hb.
  split; [discriminate | exists b; reflexivity].
Qed.

(* Discharge the first premise of a hypothesis HR against its exact type (so that no evar is left for tac). *)
Ltac next_premise HR tac :=
  lazymatch type of HR with
  | ?P -> _ => let G := fresh "G" in assert (G : P) by tac; specialize (HR G); clear G
  end.

(* ---------------------------------------------------------------------------------------------------------
   Route (C): the three region facts this stage needs (header, ROUTE (C)). *)

(* A region's shadow bytes stay present across the four metadata stores: a munch over [(lo, hi)] after which the
   bytes of [lo, hi) are present (stk), every view kept (wmono).  The per-byte argument of the universal form this
   file used before, under the region's guard. *)
Lemma r18g_on_keep_meta : forall (P : Z -> Prop) (m m1 : word -> option byte) lo hi,
  A.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.munch [(lo, hi)] m m1 ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m1 -> lib.Lib.Frame.stk A.Img0.rsegs m1 lo hi ->
  A.ShadowRwOn.shadow_rw_on P m1.
Proof.
  intros P m m1 lo hi HP MU WM ST a Ha Hin.
  destruct (Z_lt_le_dec a lo) as [H1 | H1]; [| destruct (Z_lt_le_dec a hi) as [H2 | H2]].
  - destruct (HP a Ha Hin) as (Hw1 & bb & Hw2). split.
    + apply WM. exact Hw1.
    + exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in *.
      rewrite (MU (Z_to_bv 64 a)); [exact Hw2 |
        rewrite lib.Lib.Mem.wa_unsigned by (pose proof (A.AsanRTFacts.in_shadow_range a Hin); lia);
        cbn [lib.Lib.Frame.outside]; split; [lia | exact I]].
  - destruct ST as (_ & _ & STv). exact (STv a ltac:(lia)).
  - destruct (HP a Ha Hin) as (Hw1 & bb & Hw2). split.
    + apply WM. exact Hw1.
    + exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in *.
      rewrite (MU (Z_to_bv 64 a)); [exact Hw2 |
        rewrite lib.Lib.Mem.wa_unsigned by (pose proof (A.AsanRTFacts.in_shadow_range a Hin); lia);
        cbn [lib.Lib.Frame.outside]; split; [lia | exact I]].
Qed.

(* The aligned shadow-word span (sh_word_on) of bytes inside the catalogue body [0x9e800, 0x9f4b8) lies in the
   image's shadow img_shadow (CtrlRo's [IMG_LO, IMG_HI) = [0x10000, 0x5fe000)): its byte a is the shadow of
   x = 8 * (a - ASAN_K), and x lies within 64 bytes of the span's ends. *)
Lemma r18g_cat_word_img : forall p n a, 649216 <= p -> p + n <= 652472 ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.img_shadow a.
Proof.
  intros p n a Hp Hn (_ & Hlo & Hhi).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hlo, Hhi.
  exists ((a - 0x7fff8000) * 8).
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* The aligned shadow-word span of the 32 declaration bytes at fr + 2560 lies in the frame's shadow
   [Sfr fr, Sfr fr + 512) (it is inside [Sfr fr + 313, Sfr fr + 332)). *)
Lemma r18g_decl_word_frame : forall fr a, 0 <= fr ->
  A.Prog.sh_word_on.sh_word_on (fr + 2560) 32 a -> ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512.
Proof.
  intros fr a Hfr (_ & Hlo & Hhi).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hlo, Hhi.
  unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueR18.

(* ACtl.v's Section shape (ACtl.v:210-214, blob c4edf0be7fe), restricted to what this stage uses; the three
   classes are named by FULL PATH, as ACtlCut.v and ACtl.v now do, so that this stage plugs into ACtl.v's
   Section. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :405-406, blob c4edf0be7fe), verbatim for the two cuts of this
   stage. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81858_at := (ACtlCutP.C_A81858_at B).
Local Notation C_A818d0_at := (ACtlCutP.C_A818d0_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* ACtl.v:237, verbatim: the core's AR law record (YCbq.v:207, Section a0's hypothesis). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

(* ACtl.v:252, verbatim: the core's symbol facts for B.  Used for ts_zsh (the zero-shadow list is the interim's
   fine Tfib_zero_shadow), which places the catalogue's addressability under ctl_global_shadow_of_AR. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ACtl.v:239, verbatim: the catalogue lies in the read-only span [RLO, RHI) (a Theorem Labs lane batch 3).  With the entry
   pre's arodata_okS it makes each catalogue byte read as the image byte. *)
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.

(* Two option bytes with equal unsigned values are equal. *)
Lemma r18g_om_inj : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate H; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* Every byte of the loaded segment [0x9e000, 0xa1000) is an image byte (A.ProgBridge.rsegs_spans). *)
Lemma r18g_in_img_cat : forall a, 0x9e000 <= a < 0xa1000 -> lib.Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (Hin : In (0x9e000, 0x3000)
                  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs)).
  { rewrite A.ProgBridge.rsegs_spans. right. right. left. reflexivity. }
  apply in_map_iff in Hin as (sg & Esg & Hsg). injection Esg as E1 E2.
  exists sg. split; [exact Hsg|]. rewrite E1, E2. lia.
Qed.

(* A byte whose view reads the ROM byte, and which the ROM has, reads the ROM byte in memory too: the view is not
   None, so the byte is visible (A.ProgWorldVisFrame.vis_of_aview), and a visible byte's view is its memory byte
   (A.ProgWorld.aview_vis_mrd). *)
Lemma r18g_cat_mbyte : forall (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a =
    option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)) ->
  (exists b, lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = Some b) ->
  lib.Lib.Mem.mrd A.Img0.rsegs mem (Z_to_bv 64 a) = lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a).
Proof.
  intros W mem a Hv (b & Hb).
  assert (Hvis : lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false).
  { apply (A.ProgWorldVisFrame.vis_of_aview segs W mem). rewrite Hv, Hb. cbn. discriminate. }
  apply r18g_om_inj. transitivity (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a).
  - symmetry. exact (A.ProgWorld.aview_vis_mrd W mem a Hvis).
  - exact Hv.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Two spill transports this file owns (the cut's own ACtlCutP.spill, not SlotInv's). *)

Lemma spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 304 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HS HA HAb Hoff.
  assert (H47 : 2 ^ 47 < 2 ^ 64) by (vm_compute; reflexivity).
  destruct HS as (A0 & H0 & Hq).
  unfold ACtlCut.rgv in H0, HA. rewrite HA in H0.
  assert (E : A0 mod 2 ^ 64 = A).
  { apply (f_equal bv_unsigned) in H0. rewrite !Z_to_bv_unsigned in H0.
    unfold bv_wrap, bv_modulus in H0. change (2 ^ Z.of_N 64) with (2 ^ 64) in H0.
    rewrite (Z.mod_small A (2 ^ 64)) in H0 by lia. symmetry. exact H0. }
  assert (Hqb := Hq). unfold ACtlCutP.q64 in Hqb. destruct Hqb as (Hlo & Hhi & _).
  rewrite lib.Lib.Mem.length_le8 in Hhi. cbn [Z.of_nat] in Hhi.
  assert (EA : A0 = A).
  { destruct (Z_lt_le_dec A0 0) as [Hn | Hp].
    - rewrite <- (Z.mod_add A0 1 (2 ^ 64)) in E by lia.
      rewrite Z.mod_small in E by lia. lia.
    - rewrite Z.mod_small in E by lia. lia. }
  rewrite <- EA. exact Hq.
Qed.

Lemma spill_move : forall (W : list lib.Lib.Frame.ivl) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) off v A,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 304 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Lib.Frame.munch W m m' -> lib.Lib.Frame.disjoint_from W (A + off) 8 ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros W regs regs' m m' off v A HS HA HAb Hoff E MU Hdis.
  pose proof (spill_at regs m off v A HS HA HAb Hoff) as Hq.
  exists A. split.
  - unfold ACtlCut.rgv in *. rewrite E. exact HA.
  - unfold ACtlCutP.q64 in *.
    apply (lib.Lib.Frame.bytes_at_transport segs W m m' (A + off) _ Hq MU).
    rewrite lib.Lib.Mem.length_le8. cbn [Z.of_nat]. exact Hdis.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage.  The statement after the colon is ACtl.v:685's `Hypothesis seg_R18 :` text byte for byte (blob
   c4edf0be7fe). *)
Lemma glue_seg_R18 : forall POST (b : nat), CF POST (ix_cut C_A818d0_at [Z.of_nat b]) -> CF POST (ix_cut C_A81858_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBASE HJ HF HL Hk Hbody Hrt.
  assert (H47 : 2 ^ 47 < 2 ^ 64) by (vm_compute; reflexivity).
  (* ---- G1 : the entry cut at index [Z.of_nat b] ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81858_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPERM & HFRAC & (Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hsp200) & Hb0 & HRFb &
    H27 & Ha0 & HU1 & HU2 & Hsp216 & Hsp8 & Hsp0 & Hsp112 & Hsp128 & HPRO & Hsp104 & Hsp96 & Hsp64 & H21 &
    Hsp144 & Hsp192 & HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWsc & Hsp152 & HAid & HRXS).
  subst b.
  (* route (C): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from) *)
  unfold A.ACtlRtC.ctl_rt_C in Hrt.
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  unfold A.ACtlK.asan_cells_at in HAC.
  (* ---- G2a : the geometry ---- *)
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwinp & Hastk & _ & _).
  pose proof Hlyle as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Estklo & Estkhi & _).
  pose proof Hastk as (_ & _ & Hceil_lo & Hstk32 & Hsphi & _).
  assert (ESTK : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  rewrite ESTK in Hstk32.
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as (Hceilv & _).
  unfold lib.Reusable.YG0f.ASAN_CEIL in Hceilv.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (E4096 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hfr4096 & Hfrceil & Hfrapp0).
  rewrite Efr3 in Hfr4096, Hfrceil, Hfrapp0. rewrite E4096 in Hfrceil, Hfrapp0.
  assert (Hfrgt : 6283264 <= fr).
  { pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as HGT.
    rewrite Efr3 in HGT. lia. }
  (* ---- FRAC gives the spill base A and the machine sp, read BY TYPE (r18g_get), never by position *)
  pose proof HFRAC as (A & sp & HFw).
  r18g_get HFw (lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp) Hr2.
  r18g_get HFw (sp mod 16 = 0) Hspm.
  r18g_get HFw (ACtlCut.rgv regs3 9 A) Hr9.
  r18g_get HFw (ACtlCut.rgv regs3 19 (ACtlCutP.Sfr fr)) Hr19.
  r18g_get HFw (ACtlCut.rgv regs3 26 A.ACtlK.ASAN_K) Hr26.
  r18g_get HFw (fr mod 32 = 0) Hfrm.
  r18g_get HFw (A mod 32 = 0) HAm.
  r18g_get HFw (A <= ACtlCut.c_sp cx) HAS.
  r18g_get HFw (sp <= A) Hspa.
  r18g_get HFw (fr + ACtlCutP.FRAME_BYTES <= A) HfrA.
  r18g_get HFw (A + 416 <= ACtlCut.c_sp cx) HA416.
  r18g_get HFw (ACtlCut.c_sp cx - 4096 < sp) Hsp4096.
  r18g_get HFw (ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) HSapp.
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  assert (HA0 : 0 <= A) by lia.
  assert (HA47 : A < 2 ^ 47) by (assert (0x800000000000 = 2 ^ 47) by (vm_compute; reflexivity); lia).
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (Hframe8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hfrappb : forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a).
  { intros a Ha. destruct Hfrapp0 as (_ & [Hlow | (Hh1 & Hh2)]);
      unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END,
             lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *; [left | right]; lia. }
  assert (Hshb : forall kk, 0 <= kk < 512 -> A.AsanRT.in_shadow (ACtlCutP.Sfr fr + kk)).
  { intros kk Hkk.
    replace (ACtlCutP.Sfr fr + kk) with (A.AsanRT.shadow_addr (fr + kk * 8));
      [ apply A.AsanRTFacts.shadow_of_app; apply Hfrappb; lia
      | unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr; revert Hframe8; Z.div_mod_to_equations; lia ]. }
  (* route (C), region (F): the own class-6 frame's shadow [Sfr fr, Sfr fr + 512) is cut_shadow's first disjunct
     (frames S3 holds (6, c_fpos cx), and frame_addr ly3 6 (c_fpos cx) = fr) *)
  assert (HFsh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6 |].
    rewrite Efr3, E4096.
    unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
           lib.Reusable.YG0f.SHADOW_OFF in Ha |- *.
    try change (4096 / 8) with 512. lia. }
  assert (HSfrlo : 0x7fff8000 <= ACtlCutP.Sfr fr).
  { unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)). lia. }
  assert (HSfrhi : ACtlCutP.Sfr fr + 512 <= 0x10007fff8000).
  { pose proof (Hshb 511 ltac:(lia)) as Hin.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
           A.AsanRT.HIGHMEM_BEG in Hin. lia. }
  assert (HSfr324 : ACtlCutP.Sfr fr + 324 <= 2 ^ 64) by lia.
  assert (Hspbig : 0x7fff7f800000 + 32768 <= ACtlCut.c_sp cx) by lia.
  assert (Hwinapp : forall a, sp - 2304 <= a < sp -> A.AsanRT.app_mem a).
  { intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. right. lia. }
  (* the three intervals of the write set, pairwise ordered *)
  assert (HsepFS : fr + 4096 <= ACtlCutP.Sfr fr + 320 \/ ACtlCutP.Sfr fr + 324 <= fr).
  { apply ivl_sep; [lia | lia |]. intros x Hx Hc.
    pose proof (Hfrappb x Hx) as Hap.
    pose proof (Hshb (x - ACtlCutP.Sfr fr) ltac:(lia)) as Hsx.
    replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hsx by lia.
    exact (A.AsanRTFacts.app_not_shadow x Hap Hsx). }
  (* ---- G2b : the catalogue row ---- *)
  (* ---- the catalogue's 8-aligned shadow-word cover [0x8000bd00, 0x8000be98) is visible (former part 3): the
     shadow bytes of the body [0x9e800, 0x9f4b8) from the catalogue's own zero-shadow range, and the redzone
     granule's shadow byte 0x8000be97 from its CONST row z1 (ANum 0x8000be97) 0xf9 (A/AF0m.v:2386) *)
  assert (HCATsh : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
            (A.Prog.rng_asan.sh_al8_lo A.Prog.SlotModel.CAT)
            (A.Prog.rng_asan.sh_al8_hi A.Prog.SlotModel.CAT 3256 -
             A.Prog.rng_asan.sh_al8_lo A.Prog.SlotModel.CAT)).
  { assert (Ecs1 : A.Prog.rng_asan.sh_al8_lo A.Prog.SlotModel.CAT = 0x8000bd00) by (vm_compute; reflexivity).
    assert (Ecs2 : A.Prog.rng_asan.sh_al8_hi A.Prog.SlotModel.CAT 3256 = 0x8000be98) by (vm_compute; reflexivity).
    rewrite Ecs1, Ecs2. unfold A.ProgBridge.range_visible.
    split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros acs Hacs. apply (A.ProgWorldVisFrame.vis_of_aview segs W3 mem3).
    destruct (Z.eq_dec acs 0x8000be97) as [Ecs3 | Ecs3].
    - subst acs.
      assert (Hcs_z1 : In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum 0x8000be97) 0xf9) (A.AF0m.Tfib_const ly3)).
      { unfold A.AF0m.Tfib_const. apply in_or_app. right. apply in_or_app. right.
        unfold A.AF0m.Tfib_const_shadow. repeat (first [left; reflexivity | right]). }
      pose proof (A.ProgWorld_Fs.pw_row B TFIB_SYMS ly3 S3 W3 mem3 md3 _ HAR Hcs_z1) as Hcs_c.
      unfold lib.Reusable.YG0f.cell_holds in Hcs_c.
      cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z1
           lib.Reusable.YG0f.c1 lib.Reusable.YG0f.aeval] in Hcs_c.
      specialize (Hcs_c 0%nat ltac:(lia)).
      replace (0x8000be97 + Z.of_nat 0) with 0x8000be97 in Hcs_c by lia.
      rewrite Hcs_c. discriminate.
    - assert (Hcs_zr : In (0x9e800, 0x9f4b8 - 0x9e800) (lib.Reusable.YG0n.zero_shadow_ranges B ly3)).
      { unfold lib.Reusable.YG0n.zero_shadow_ranges. right.
        rewrite (@A.AF0m.ts_zsh B TFIB_SYMS). unfold A.AF0m.Tfib_zero_shadow.
        repeat (first [left; reflexivity | right]). }
      pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3 _ HAR Hcs_zr) as Hcs_z.
      unfold lib.Reusable.YG0v.zero_shadow in Hcs_z. cbn [fst snd] in Hcs_z.
      assert (Ecs4 : lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF 0x9e800 = 0x8000bd00)
        by reflexivity.
      assert (Ecs5 : (0x9f4b8 - 0x9e800) / 8 = 407) by reflexivity.
      rewrite Ecs4, Ecs5 in Hcs_z.
      replace acs with (0x8000bd00 + (acs - 0x8000bd00)) by lia.
      rewrite (Hcs_z (acs - 0x8000bd00) ltac:(lia)). discriminate. }
  (* ---- every catalogue byte's view at the cut is its ROM byte (former part 1): the entry pre's arodata_okS
     (A.ACfn.tfib_lib_pre_x, ACfn.v:41; RLO <= a < RHI by RELRO_CAT), moved to the cut by the journal's in-image
     clause (YCbq.v:362-363).  Its side conditions hold for the whole body [0x9e800, 0x9f4b8): no range of
     Tfib_owned_static meets it (the nearest are its redzones [0x9e7d0, 0x9e800) and [0x9f4b8, 0x9f7e0)), the
     errno word 0x5db76c is far above, and the body lies below the sink head 0x5fbf08 *)
  pose proof HBASE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROD & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJimg & _).
  assert (HCATrom : forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 a =
            option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a))).
  { intros a Ha.
    assert (Hcat_o : ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B)).
    { rewrite (@A.AF0m.ts_owned B TFIB_SYMS). intros Hex.
      apply Exists_exists in Hex as (r & Hin & Hr).
      assert (Hall : forallb (fun r : Z * Z => (fst r + snd r <=? 0x9e800) || (0x9f4b8 <=? fst r))
                       A.AF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hall. specialize (Hall r Hin).
      unfold lib.Reusable.YG0n.in_zr, A.Prog.SlotModel.CAT in *.
      apply Bool.orb_true_iff in Hall. destruct Hall as [Hl | Hl]; apply Z.leb_le in Hl; lia. }
    assert (Hcat_e : ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)).
    { rewrite (@A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO, A.Prog.SlotModel.CAT in *. lia. }
    rewrite (HJimg a);
      [| apply r18g_in_img_cat; unfold A.Prog.SlotModel.CAT in Ha; lia | exact Hcat_o | exact Hcat_e |].
    - apply HAROD; [right | exact Hcat_o | exact Hcat_e].
      destruct RELRO_CAT as (Rcl & Rch). unfold A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in Rch. lia.
    - unfold lib.Reusable.YCbq.fp_spares. intros _.
      assert (Ecat_o : @lib.Reusable.YCbq.AOFL_HEAD A.AE2k.tfib_sink_head = 0x5fbf08) by reflexivity.
      rewrite Ecat_o. unfold A.Prog.SlotModel.CAT in Ha. lia. }
  (* the catalogue's addressability, from ctl_global_shadow_of_AR at its own fine-list entry (header) *)
  assert (HCAT : A.AsanRT.addressable mem3 A.Prog.SlotModel.CAT 3256).
  { apply (A.ProgWorldShadow.ctl_global_shadow_of_AR B TFIB_SYMS LAWS ly3 S3 W3 mem3 md3
             A.Prog.SlotModel.CAT 3256 (0x9e800, 0x9f4b8 - 0x9e800) HAR).
    - unfold A.Prog.SlotModel.CAT. reflexivity.
    - lia.
    - rewrite (@A.AF0m.ts_zsh B TFIB_SYMS). unfold A.AF0m.Tfib_zero_shadow.
      repeat (first [left; reflexivity | right]).
    - unfold A.Prog.SlotModel.CAT. cbn [fst]. lia.
    - unfold A.Prog.SlotModel.CAT. cbn [fst snd]. vm_compute. congruence.
    - intros H0. exfalso. apply H0. reflexivity.
    - unfold A.Prog.SlotModel.CAT, lib.Reusable.YG0f.kImgEnd. lia. }
  assert (HCATa : forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
            A.AsanRT.addressable mem3 a 1).
  { intros a Ha.
    pose proof (A.Prog.declaration_ofF.da_addr_sub mem3 A.Prog.SlotModel.CAT 3256 (a - A.Prog.SlotModel.CAT) 1
                  HCAT ltac:(lia) ltac:(lia) ltac:(lia)) as Hs.
    replace (A.Prog.SlotModel.CAT + (a - A.Prog.SlotModel.CAT)) with a in Hs by lia. exact Hs. }
  assert (Hist : 0 <= A.Prog.SlotModel.istar (ACtlCut.c_in cx) < 11).
  { unfold A.Prog.SlotModel.istar, A.Prog.SlotModel.CAT_N. apply Z.mod_pos_bound. lia. }
  assert (Hmrlo : 649216 <= A.Prog.SlotModel.mrow (ACtlCut.c_in cx) /\
                  A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 296 <= 652472).
  { unfold A.Prog.SlotModel.mrow, A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW. lia. }
  assert (Hmr8 : A.Prog.SlotModel.mrow (ACtlCut.c_in cx) mod 8 = 0).
  { unfold A.Prog.SlotModel.mrow, A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW.
    replace (649216 + 296 * A.Prog.SlotModel.istar (ACtlCut.c_in cx))
      with ((81152 + 37 * A.Prog.SlotModel.istar (ACtlCut.c_in cx)) * 8) by lia.
    apply Z_mod_mult. }
  (* the turn's catalogue row reads as the image's row (A.Prog.Seg.R18.r18_img_bytes over B3Rtm.a_row_img) *)
  assert (Hrowb : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))
                    (A.Prog.SlotModel.rt_mb (ACtlCut.c_in cx))).
  { unfold A.Prog.SlotModel.rt_mb.
    pose proof (A.Prog.Seg.B3Rtm.a_row_img _ Hist) as Hcat_img.
    apply (A.Prog.Seg.R18.r18_img_bytes mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) 296
             (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))));
      [| exact Hcat_img | lia | change (Z.of_nat 296) with 296; change (2 ^ 64) with 18446744073709551616; lia].
    intros kk Hkk.
    assert (Hcat_a : A.Prog.SlotModel.CAT <= A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat kk <
                     A.Prog.SlotModel.CAT + 3256) by (unfold A.Prog.SlotModel.CAT; lia).
    pose proof (A.Prog.Seg.R18.r18_img_nth 296 _ _ Hcat_img kk Hkk) as Hcat_nth.
    pose proof (A.Prog.Seg.Tac_rt2_b2.a_row_len (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) as Hcat_len.
    assert (Hcat_some : exists b0, lib.Reusable.YK11.seg_rom segs
                          (Z_to_bv 64 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat kk)) = Some b0).
    { destruct (nth_error (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) kk)
        as [b0|] eqn:Ecat_n.
      - exists b0. try rewrite Ecat_n in Hcat_nth. exact Hcat_nth.
      - exfalso. apply nth_error_None in Ecat_n. lia. }
    exact (r18g_cat_mbyte W3 mem3 _ (HCATrom _ Hcat_a) Hcat_some). }
  pose proof (A.Prog.Seg.R18.r18_row_len (ACtlCut.c_in cx)) as Hrowlen.
  assert (Hrow296 : A.AsanRT.addressable mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) 296).
  { apply A.Prog.Seg.R18.r18_addr_join; [lia | lia | unfold A.AsanRT.APPMEM_END; lia |].
    intros i Hi. apply HCATa. unfold A.Prog.SlotModel.CAT. lia. }
  assert (Hrowgran : A.AsanRT.addressable mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16) 8).
  { apply A.Prog.Seg.R18.r18_addr_join; [lia | lia | unfold A.AsanRT.APPMEM_END; lia |].
    intros i Hi. apply HCATa. unfold A.Prog.SlotModel.CAT. lia. }
  assert (Hrow16 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16)
            (lib.Lib.Mem.le4 (Z_to_bv 64 (4 * Prog.RcLeaf.n_in (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx)))))).
  { rewrite <- (A.Prog.Seg.R18.r18_row_ic (ACtlCut.c_in cx)).
    replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16)
      with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 16) by lia.
    apply (A.Prog.Seg.R18.r18_sub mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))
             (A.Prog.SlotModel.rt_mb (ACtlCut.c_in cx)) 16 4); [exact Hrowb | rewrite Hrowlen; lia]. }
  assert (Hrow20 : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 20)
            (lib.Lib.Mem.le4 (Z_to_bv 64 (4 * Prog.RcLeaf.n_out (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx)))))).
  { rewrite <- (A.Prog.Seg.R18.r18_row_oc (ACtlCut.c_in cx)).
    replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 20)
      with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 20) by lia.
    apply (A.Prog.Seg.R18.r18_sub mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))
             (A.Prog.SlotModel.rt_mb (ACtlCut.c_in cx)) 20 4); [exact Hrowb | rewrite Hrowlen; lia]. }
  (* ---- G2c : the frame's own bytes and its shadow, before the stores ---- *)
  destruct (lib.Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrby & _).
  rewrite Efr3, E4096 in Hfrby.
  assert (HstkFR : lib.Lib.Frame.stk A.Img0.rsegs mem3 fr (fr + 4096)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfrby a ltac:(lia)) as ((_ & bb & Hbb) & _). exact (present_rw mem3 a bb Hbb). }
  (* the four metadata bytes are own-frame shadow: present by Hcut, region (F) *)
  assert (HstkSH : lib.Lib.Frame.stk A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 320) (ACtlCutP.Sfr fr + 324)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    apply (Hcut a); [apply HFsh; lia |].
    replace a with (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) by lia. apply Hshb. lia. }
  (* the callee's own region at a0 := mrow, a1 := fr + 2560, at the cut's memory: the two row spans are image
     shadow (Himg), the declaration slot's span is own-frame shadow (Hcut, region (F)) *)
  assert (HRm3 : A.ShadowRwOn.shadow_rw_on
                   (A.Prog.declaration_of_c.declaration_of_shadow_R (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))
                      (fr + 2560)) mem3).
  { intros a HRa Ha. destruct HRa as [HRa | [HRa | HRa]].
    - exact (Himg a (r18g_cat_word_img (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 24) 32 a
                       ltac:(lia) ltac:(lia) HRa) Ha).
    - exact (Himg a (r18g_cat_word_img (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 254) 11 a
                       ltac:(lia) ltac:(lia) HRa) Ha).
    - exact (Hcut a (HFsh a (r18g_decl_word_frame fr a ltac:(lia) HRa)) Ha). }
  (* ---- G3 : the configuration, then the canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81858_at [Z.of_nat 0])) with 0x81858.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81858) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  rewrite <- (mkR_of_getr regs3).
  (* ---- G2d : visibility ---- *)
  assert (HVwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
            A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len Hlo Hhi.
    exact (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
             ly3 S3 W3 mem3 md3 k lo len HJ ltac:(rewrite ESTK; lia) Hhi). }
  assert (HVfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
            A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len Hlo Hhi.
    refine (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len
                     HAR Hin6 _ _)); rewrite Efr3, ?E4096; lia. }
  assert (HDsh : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
                   (A.Prog.rng_asan.sh_al8_lo (fr + 2560))
                   (A.Prog.rng_asan.sh_al8_hi (fr + 2560) 32 - A.Prog.rng_asan.sh_al8_lo (fr + 2560))).
  { destruct (proj2 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
                       (fr + 2560) 32 HAR Hin6 ltac:(rewrite Efr3, ?E4096; lia)
                       ltac:(rewrite Efr3, ?E4096; lia)) ltac:(lia)
                ltac:(rewrite Efr3; pose proof (Z.div_mod (fr + 2560) 64 ltac:(lia));
                      pose proof (Z.mod_pos_bound (fr + 2560) 64 ltac:(lia)); lia)
                ltac:(rewrite Efr3, ?E4096; pose proof (Z.div_mod (fr + 2560 + 32 - 1) 64 ltac:(lia));
                      pose proof (Z.mod_pos_bound (fr + 2560 + 32 - 1) 64 ltac:(lia)); lia))
      as [Hc | Hc]; [discriminate | exact Hc]. }
  assert (Eshd0 : A.AsanRT.shadow_addr (fr + 2560) = ACtlCutP.Sfr fr + 320).
  { unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. revert Hframe8. Z.div_mod_to_equations. lia. }
  assert (Eshd3 : A.AsanRT.shadow_addr (fr + 2560 + 32 - 1) = ACtlCutP.Sfr fr + 323).
  { unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. revert Hframe8. Z.div_mod_to_equations. lia. }
  assert (HSH4 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (ACtlCutP.Sfr fr + 320) 4).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HDsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi;
      rewrite ?Eshd0, ?Eshd3;
      pose proof (Z.div_mod (ACtlCutP.Sfr fr + 320) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (ACtlCutP.Sfr fr + 320) 8 ltac:(lia));
      pose proof (Z.div_mod (ACtlCutP.Sfr fr + 323) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (ACtlCutP.Sfr fr + 323) 8 ltac:(lia)); lia. }
  assert (HVrowsh : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
            (A.Prog.rng_asan.sh_al8_lo (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)))
            (A.Prog.rng_asan.sh_al8_hi (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) 296 -
             A.Prog.rng_asan.sh_al8_lo (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)))).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HCATsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr,
             A.AsanRT.ASAN_K, A.Prog.SlotModel.CAT in *;
      revert Hmrlo; Z.div_mod_to_equations; lia. }
  assert (HVk16 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
            (Z.shiftr (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16) 3 + A.AsanRT.ASAN_K) 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HCATsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr,
             A.AsanRT.ASAN_K, A.Prog.SlotModel.CAT in *;
      revert Hmrlo; Z.div_mod_to_equations; lia. }
  assert (HVk20 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
            (Z.shiftr (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 20) 3 + A.AsanRT.ASAN_K) 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HCATsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr,
             A.AsanRT.ASAN_K, A.Prog.SlotModel.CAT in *;
      revert Hmrlo; Z.div_mod_to_equations; lia. }
  assert (HVcsh : A.Prog.rng_asan.sh_word_rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (sp - 2304) 2304).
  { right.
    destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2304) 2304 HAR
                ltac:(rewrite Estklo; lia) ltac:(rewrite Estkhi; lia) ltac:(lia)) as [Hc | Hc];
      [discriminate | exact (A.ProgBridge.rng_of_visible _ _ _ Hc)]. }
  (* ---- G4 : the run ---- *)
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (ACtlCut.c_in cx) (Z.of_nat 0) (proj1 (proj2 HRFb)))
    as (_ & Hnb & HFlen).
  change (A.Prog.SlotModel.rt_n (ACtlCut.c_in cx) (Z.of_nat 0)) with (ACtlCutP.rnb cx 0) in Hnb, HFlen.
  (* the run: this lane's twin, its callee premise the route (C) contract at the runtime's route (C) proofs *)
  pose proof (A.Prog.Seg.R18Fon.r18_evt_F_on
                (A.Prog.declaration_ofF.declaration_of_F_holds_on
                   (A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds)
                   A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on)
                (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
                (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
                (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
                (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
                (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
                (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
                (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
                (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
                (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
                (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
                (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
                (lib.Reusable.YK11.getr regs3 31)
                lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
                sp A (ACtlCutP.Sfr fr) (fr + 2560) (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) (fr + 2528)
                (4 * Prog.RcLeaf.n_in (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx)))
                (4 * Prog.RcLeaf.n_out (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx)))
                (A.Prog.SlotModel.rt_mb (ACtlCut.c_in cx)))
    as HRUN.
  unfold A.Prog.declaration_of_c.DECLARATION_OF_K in HRUN.
  specialize (HRUN Hr2 Hr9 Hr19 Hr26 Ha0).
  specialize (HRUN ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia) ltac:(unfold A.AsanRT.APPMEM_END; lia)).
  specialize (HRUN HA0 HA312 ltac:(lia) ltac:(lia) Hmr8 ltac:(lia) HSfr324 ltac:(lia) ltac:(lia)
                   ltac:(lia) ltac:(lia)).
  specialize (HRUN ltac:(right; lia) ltac:(left; lia) ltac:(left; lia) ltac:(left; lia)).
  specialize (HRUN ltac:(destruct HsepFS as [Hc | Hc]; [right; lia | left; lia])).
  specialize (HRUN ltac:(unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; right; lia)).
  specialize (HRUN ltac:(apply Hfrappb; lia)).
  specialize (HRUN Hrowlen (A.Prog.Seg.B3Rtm.a_rtm_declok (ACtlCut.c_in cx))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 (A + 200) _ 8%nat
                      (spill_at regs3 mem3 200 (ACtlCutP.decl_slot fr) A Hsp200 Hr9 ltac:(lia) ltac:(lia))
                      (lib.Lib.Mem.length_le8 _))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 (A + 8) _ 8%nat
                      (spill_at regs3 mem3 8 _ A Hsp8 Hr9 ltac:(lia) ltac:(lia)) (lib.Lib.Mem.length_le8 _))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 (A + 0) _ 8%nat
                      (spill_at regs3 mem3 0 _ A Hsp0 Hr9 ltac:(lia) ltac:(lia)) (lib.Lib.Mem.length_le8 _))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 (A + 216) _ 8%nat
                      (spill_at regs3 mem3 216 _ A Hsp216 Hr9 ltac:(lia) ltac:(lia)) (lib.Lib.Mem.length_le8 _))).
  specialize (HRUN (A.Prog.Seg.R18.r18_meta0 mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16)
                      (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16) Hrowgran
                      ltac:(revert Hmr8; Z.div_mod_to_equations; lia) ltac:(lia))).
  specialize (HRUN (A.Prog.Seg.R18.r18_meta0 mem3 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 16)
                      (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 20) Hrowgran
                      ltac:(revert Hmr8; Z.div_mod_to_equations; lia) ltac:(lia))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 (fr + 2528) _ 4%nat HU1 (lib.Lib.Mem.length_le4 _))).
  specialize (HRUN ltac:(replace (fr + 2528 + 4) with (fr + 2532) by lia;
                exact (A.Prog.Seg.R18.r18_rdn mem3 (fr + 2532) _ 4%nat HU2 (lib.Lib.Mem.length_le4 _)))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 _ _ 4%nat Hrow16 (lib.Lib.Mem.length_le4 _))).
  specialize (HRUN (A.Prog.Seg.R18.r18_rdn mem3 _ _ 4%nat Hrow20 (lib.Lib.Mem.length_le4 _))).
  specialize (HRUN HstkSH HRO).
  (* HPRE, the caller obligation, on the memory after the four metadata stores: the twin's r18_pre_on *)
  assert (HPRE : forall m1, lib.Lib.Frame.munch [(ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)] mem3 m1 ->
       lib.Lib.Frame.wmono A.Img0.rsegs mem3 m1 ->
       lib.Lib.Frame.stk A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 320) (ACtlCutP.Sfr fr + 324) ->
       A.MemNorm.ro_agree A.Img0.rsegs m1 ->
       lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 320) [Z_to_bv 8 0] ->
       lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 321) [Z_to_bv 8 0] ->
       lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 322) [Z_to_bv 8 0] ->
       lib.Lib.Mem.bytes_at A.Img0.rsegs m1 (ACtlCutP.Sfr fr + 323) [Z_to_bv 8 0] ->
       A.Prog.Seg.R18Fon.r18_pre_on m1 A sp (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) (fr + 2560)
         (A.Prog.SlotModel.rt_mb (ACtlCut.c_in cx))).
  { intros m1 MU1 WM1 ST1 MI1 HZ0 HZ1 HZ2 HZ3.
    assert (Dsh1 : forall a n, a + n <= ACtlCutP.Sfr fr + 320 \/ ACtlCutP.Sfr fr + 324 <= a ->
              lib.Lib.Frame.disjoint_from [(ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)] a n)
      by (intros a n H; cbn [lib.Lib.Frame.disjoint_from]; split; [exact H | exact I]).
    unfold A.Prog.Seg.R18Fon.r18_pre_on, A.Prog.declaration_of_c.DECLARATION_OF_K.
    split.
    { apply (A.Prog.Seg.R18.r18_rdn m1 (A + 112) _ 8%nat); [| exact (lib.Lib.Mem.length_le8 _)].
      apply (lib.Lib.Frame.bytes_at_transport A.Img0.rsegs _ mem3 m1 (A + 112) _
               (spill_at regs3 mem3 112 _ A Hsp112 Hr9 ltac:(lia) ltac:(lia)) MU1).
      rewrite lib.Lib.Mem.length_le8. cbn [Z.of_nat]. apply Dsh1; lia. }
    split.
    { split; [lia|]. split; [lia|]. intros a Ha.
      destruct (Hwinp a ltac:(rewrite ESTK; lia)) as (_ & bb & Hbb).
      assert (Em : m1 (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
      { apply MU1. rewrite lib.Lib.Mem.wa_unsigned by lia. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
      assert (Hb1 : m1 (Z_to_bv 64 a) = Some bb) by (rewrite Em; exact Hbb).
      exact (present_rw m1 a bb Hb1). }
    split.
    { apply (lib.Lib.Frame.bytes_at_transport A.Img0.rsegs _ mem3 m1 _ _ Hrowb MU1).
      rewrite Hrowlen. cbn [Z.of_nat]. apply Dsh1; lia. }
    split.
    { destruct (lib.Lib.Frame.stk_carve A.Img0.rsegs mem3 fr (fr + 2592) 32%nat
                  (proj1 (lib.Lib.Frame.stk_split A.Img0.rsegs mem3 fr (fr + 2592) (fr + 4096) HstkFR
                            ltac:(lia))) ltac:(cbn [Z.of_nat]; lia)) as (_ & ob & Hob).
      exists ob.
      replace (fr + 2592 - Z.of_nat 32) with (fr + 2560) in Hob by lia.
      apply (lib.Lib.Frame.rw_cells_transport A.Img0.rsegs _ mem3 m1 _ _ Hob MU1 WM1).
      cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Z.of_nat Nat.add]. apply Dsh1.
      destruct HsepFS as [Hc | Hc]; lia. }
    split.
    { assert (HWlo1 : forall x, 0 <= x < 6283264 ->
                lib.Lib.Frame.outside [(ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)] x)
        by (intros x Hx; cbn [lib.Lib.Frame.outside]; split; [lia | exact I]).
      unfold A.AsanRT.asan_cells in HAC |- *. decompose [and] HAC.
      repeat split;
        (eapply A.Prog.Seg.R18.r18_keep_low; [exact MU1 | eassumption | exact HWlo1 |
           rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4; cbn [length Z.of_nat];
           unfold A.AsanRT.CELL_K, A.AsanRT.GOT_CELL_K, A.AsanRT.INITED, A.AsanRT.REPLACE,
             A.AsanRT.GOT_REPLACE, A.AsanRT.UAR, A.AsanRT.GOT_UAR, A.AsanRT.CANPOISON, A.AsanRT.HIEND,
             A.AsanRT.GOT_HIEND, A.AsanRT.MIDBEG, A.AsanRT.GOT_MIDBEG, A.AsanRT.MIDEND,
             A.AsanRT.GOT_MIDEND, A.AsanRT.REAL_MEMCPY, A.AsanRT.REAL_MEMSET,
             A.AsanRT.GOT_REAL_MEMSET; lia]). }
    split.
    (* the callee's own region: HRm3 at the cut's memory, kept across the four metadata stores *)
    { exact (r18g_on_keep_meta _ mem3 m1 _ _ HRm3 MU1 WM1 ST1). }
    split.
    { apply (A.Prog.Seg.R18.r18_addr_keep_rng mem3 m1 _ _ 296 Hrow296 MU1).
      intros i Hi. cbn [lib.Lib.Frame.outside]. split; [| exact I].
      unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
      revert Hmrlo Hfrgt. Z.div_mod_to_equations. lia. }
    { split; [lia|]. split; [lia|]. split; [unfold A.AsanRT.APPMEM_END; lia|].
      intros i Hi. split.
      - apply Hfrappb. lia.
      - assert (Esh : A.AsanRT.shadow_addr (fr + 2560 + i) = ACtlCutP.Sfr fr + 320 + i / 8)
          by (unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr; revert Hframe8; Z.div_mod_to_equations; lia).
        assert (Hq4 : 0 <= i / 8 < 4)
          by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        rewrite Esh. exists (Z_to_bv 8 0).
        split; [| unfold A.AsanRT.shadow_ok; left; reflexivity].
        assert (E4 : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3) by lia.
        destruct E4 as [->|[->|[-> | ->]]].
        + replace (ACtlCutP.Sfr fr + 320 + 0) with (ACtlCutP.Sfr fr + 320) by lia.
          exact (A.Prog.Seg.R18.r18_b1_rd m1 _ _ HZ0).
        + replace (ACtlCutP.Sfr fr + 320 + 1) with (ACtlCutP.Sfr fr + 321) by lia.
          exact (A.Prog.Seg.R18.r18_b1_rd m1 _ _ HZ1).
        + replace (ACtlCutP.Sfr fr + 320 + 2) with (ACtlCutP.Sfr fr + 322) by lia.
          exact (A.Prog.Seg.R18.r18_b1_rd m1 _ _ HZ2).
        + replace (ACtlCutP.Sfr fr + 320 + 3) with (ACtlCutP.Sfr fr + 323) by lia.
          exact (A.Prog.Seg.R18.r18_b1_rd m1 _ _ HZ3). } }
  specialize (HRUN HPRE).
  (* the eighteen footprint premises *)
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (A + 200) 8 ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (A + 8) 8 ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ HVk16)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (A + 216) 8 ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVfr (fr + 2528) 4 ltac:(lia) ltac:(lia)))).
  next_premise HRUN ltac:(apply A.ProgBridge.rng_of_visible;
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (A + 0) 8 ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ HVk20)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVfr (fr + 2528 + 4) 4 ltac:(lia) ltac:(lia)))).
  next_premise HRUN ltac:(apply A.ProgBridge.rng_of_visible;
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ HSH4)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (A + 112) 8 ltac:(lia) ltac:(lia)))).
  specialize (HRUN (A.ProgBridge.rng_bytes_RNG_W _)).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3))).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVwin (sp - 2304) 2304 ltac:(lia) ltac:(lia)))).
  specialize (HRUN HVcsh).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.rt_vis_W W3))).
  next_premise HRUN ltac:(apply A.ProgBridge.rng_of_visible;
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia).
  next_premise HRUN ltac:(apply A.ProgBridge.rng_of_visible;
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HVrowsh);
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr; lia).
  specialize (HRUN (A.ProgBridge.rng_of_visible _ _ _ (HVfr (fr + 2560) 32 ltac:(lia) ltac:(lia)))).
  next_premise HRUN ltac:(apply A.ProgBridge.rng_of_visible;
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HDsh);
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr; lia).
  (* the lift *)
  destruct HRUN as (msX & HMS & HP).
  pose proof (A.ProgBridge.fsteps_of_mstepsF _ _ _ HMS) as HFST.
  pose proof (mem_grows_of_mstepsF _ _ _ HMS) as HGROW.
  pose proof (lib.Reusable.YA0nR.fsteps_keeps_hidden segs A.ACtlG.Kit.kit_wx (lib.Reusable.YA0n.w_H W3)
                (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _ _ (lib.Reusable.YA0n.w_Hoff W3) HFST
                (A.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W3))) as Hhid.
  apply (lib.Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ msX md3
           (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (POST cx) HFST
           (A.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W3))).
  intros md' Hsbm.
  rename HP into HQ0.
  destruct HQ0 as (R & m1 & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 &
    K27 & K18 & K10 & MU1 & WM1 & ST1 & MU2 & WM2 & ST2 & HRW & HROWq & HZ0 & HZ1 & HZ2 & HZ3).
  subst msX. cbn [ms_mem] in Hhid, HGROW.
  (* the kept registers read with the core's lib.Reusable.YK11.getr, the one ACtlCut.rgv and this file's goals use:
     the twin, like Seg/R18F.v, states them with A.Reusable.YK11.getr (its Import; R18Fon.glob), a copy of the same
     function, so each change is a conversion *)
  change (lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) in K2.
  change (lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) in K3.
  change (lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) in K4.
  change (lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) in K8.
  change (lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) in K9.
  change (lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) in K19.
  change (lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) in K21.
  change (lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) in K22.
  change (lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) in K23.
  change (lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24) in K24.
  change (lib.Reusable.YK11.getr R 25 = lib.Reusable.YK11.getr regs3 25) in K25.
  change (lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) in K26.
  change (lib.Reusable.YK11.getr R 27 = lib.Reusable.YK11.getr regs3 27) in K27.
  change (lib.Reusable.YK11.getr R 18 = Z_to_bv 64 (fr + 2560)) in K18.
  change (lib.Reusable.YK11.getr R 10 = Z_to_bv 64 1) in K10.
  (* ---- G5 : the exit cut ---- *)
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A818d0_at [Z.of_nat 0])) R m' md')
            (POST cx)).
  (* the composed write set *)
  assert (MUa : lib.Lib.Frame.munch
      [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
      mem3 m1).
  { apply (lib.Lib.Frame.munch_weaken [(ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)] _ mem3 m1);
      [| exact MU1].
    unfold lib.Lib.Frame.sub_fp. intros x Hx. cbn [lib.Lib.Frame.outside] in Hx |- *. tauto. }
  assert (MUb : lib.Lib.Frame.munch
      [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
      m1 m').
  { apply (lib.Lib.Frame.munch_weaken [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32)] _ m1 m');
      [| exact MU2].
    unfold lib.Lib.Frame.sub_fp. intros x Hx. cbn [lib.Lib.Frame.outside] in Hx |- *. tauto. }
  pose proof (lib.Lib.Frame.munch_trans _ mem3 m1 m' MUa MUb) as MUtot.
  pose proof (lib.Lib.Frame.wmono_trans A.Img0.rsegs mem3 m1 m' WM1 WM2) as WMtot.
  (* nothing else to compose: HGROW is the run's own memory growth, already about m' *)
  (* disjointness helpers for the composed write set *)
  assert (Dlow : forall a n, 0 <= a -> a + n <= 6283264 ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros a n Ha1 Ha2. cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I; lia. }
  assert (DA : forall a n, A <= a -> a + n <= A + 312 ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros a n Ha1 Ha2. cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I; lia. }
  assert (Dfrlo : forall a n, fr <= a -> a + n <= fr + 2560 ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros a n Ha1 Ha2. cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I;
      destruct HsepFS as [Hc | Hc]; lia. }
  assert (Dfrhi : forall a n, fr + 2592 <= a -> a + n <= fr + 4096 ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros a n Ha1 Ha2. cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I;
      destruct HsepFS as [Hc | Hc]; lia. }
  assert (Dsaved : forall a n, ACtlCut.c_sp cx - 104 <= a -> a + n <= ACtlCut.c_sp cx ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros a n Ha1 Ha2. cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I; lia. }
  (* the blocks: both the input block and the round-trip block are below the window and apart from the frame *)
  assert (Hinblk : In (phi, ACtlCutP.rnb cx 0) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. left. reflexivity. }
  assert (Dblk : forall p n0, In (p, n0) (lib.Reusable.YG0d.ablocks B ly3 S3) ->
            forall a n, p <= a -> a + n <= p + lib.Reusable.YG00.req_size n0 ->
            lib.Lib.Frame.disjoint_from
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a n).
  { intros p n0 Hin a n Ha1 Ha2.
    destruct (lib.Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n0 HAR Hin)
      as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn0).
    assert (Hrq : 1 <= lib.Reusable.YG00.req_size n0).
    { unfold lib.Reusable.YG00.req_size. destruct (n0 =? 0) eqn:E0; [lia | apply Z.eqb_neq in E0; lia]. }
    destruct (lib.Reusable.YG0d.al_sep segs B LAWS ly3 S3 W3 mem3 md3 HAR) as (Hpair & _).
    assert (Hsepbf : p + lib.Reusable.YG00.req_size n0 <= fr \/ fr + 4096 <= p).
    { pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n0 6
                    (ACtlCut.c_fpos cx) HAR Hin Hin6) as Hzd.
      unfold lib.Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd.
      rewrite Efr3, E4096 in Hzd. exact Hzd. }
    cbn [lib.Lib.Frame.disjoint_from]. repeat split; try exact I;
      try (destruct Hsepbf as [Hc | Hc]; lia); try lia.
    - (* the block against the four metadata bytes: block bytes are application memory *)
      assert (Hsepbs : p + lib.Reusable.YG00.req_size n0 <= ACtlCutP.Sfr fr + 320 \/
                       ACtlCutP.Sfr fr + 324 <= p).
      { apply ivl_sep; [lia | lia |].
        intros x Hx Hc.
        destruct (lib.Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n0 HAR Hin)
          as (_ & _ & _ & Hpapp2 & _ & _ & _).
        assert (Happx : A.AsanRT.app_mem x).
        { destruct Hpapp2 as (_ & [Hl | (Hh1 & Hh2)]);
            unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END,
                   lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *; [left | right]; lia. }
        pose proof (Hshb (x - ACtlCutP.Sfr fr) ltac:(lia)) as Hsx.
        replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hsx by lia.
        exact (A.AsanRTFacts.app_not_shadow x Happx Hsx). }
      destruct Hsepbs as [Hc | Hc]; lia. }
  (* ---- ctl_rt_C at the exit: route (i), the regions kept (the exit cut is at ly3 S3) ---- *)
  assert (HWlo : forall x, 0 <= x < 6283264 ->
            lib.Lib.Frame.outside
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              x)
    by (intros x Hx; cbn [lib.Lib.Frame.outside]; repeat split; try exact I; lia).
  assert (HAC' : A.AsanRT.asan_cells m').
  { unfold A.AsanRT.asan_cells in HAC |- *. decompose [and] HAC.
    repeat split;
      (eapply A.Prog.Seg.R18.r18_keep_low; [exact MUtot | eassumption | exact HWlo |
         rewrite ?lib.Lib.Mem.length_le8, ?lib.Lib.Mem.length_le4; cbn [length Z.of_nat];
         unfold A.AsanRT.CELL_K, A.AsanRT.GOT_CELL_K, A.AsanRT.INITED, A.AsanRT.REPLACE,
           A.AsanRT.GOT_REPLACE, A.AsanRT.UAR, A.AsanRT.GOT_UAR, A.AsanRT.CANPOISON, A.AsanRT.HIEND,
           A.AsanRT.GOT_HIEND, A.AsanRT.MIDBEG, A.AsanRT.GOT_MIDBEG, A.AsanRT.MIDEND,
           A.AsanRT.GOT_MIDEND, A.AsanRT.REAL_MEMCPY, A.AsanRT.REAL_MEMSET,
           A.AsanRT.GOT_REAL_MEMSET; lia]). }
  assert (HshW : forall a, A.AsanRT.in_shadow a ->
            ~ (ACtlCutP.Sfr fr + 320 <= a < ACtlCutP.Sfr fr + 324) ->
            lib.Lib.Frame.outside
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              a).
  { intros a Hin Hn. cbn [lib.Lib.Frame.outside].
    split; [| split; [| split; [exact Hn | exact I]]].
    - intro Hc. exact (A.AsanRTFacts.app_not_shadow a (Hwinapp a Hc) Hin).
    - intro Hc. exact (A.AsanRTFacts.app_not_shadow a (Hfrappb a ltac:(lia)) Hin). }
  (* the metadata byte of a live block byte is shadow memory outside the write set *)
  assert (Hblksh : forall p n0, In (p, n0) (lib.Reusable.YG0d.ablocks B ly3 S3) ->
            forall x, p <= x < p + lib.Reusable.YG00.req_size n0 ->
            lib.Lib.Frame.outside
              [(sp - 2304, sp); (fr + 2560, fr + 2560 + 32); (ACtlCutP.Sfr fr + 320, ACtlCutP.Sfr fr + 324)]
              (A.AsanRT.shadow_addr x)).
  { intros p n0 Hin x Hx.
    destruct (lib.Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 p n0 HAR Hin)
      as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn0).
    pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n0 6
                  (ACtlCut.c_fpos cx) HAR Hin Hin6) as Hzd.
    unfold lib.Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite Efr3, E4096 in Hzd.
    apply HshW.
    - apply A.AsanRTFacts.shadow_of_app.
      destruct Hpapp as (_ & [Hl | (Hh1 & Hh2)]);
        unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END,
               lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *; [left | right]; lia.
    - unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. revert Hframe8. Z.div_mod_to_equations. lia. }
  (* every region the cut's memory holds, the exit memory holds: a byte outside [Sfr fr + 320, Sfr fr + 324) is
     outside the composed write set (HshW), so munch and wmono keep it; a byte inside is one of the run's four
     metadata bytes *)
  assert (Hkeep : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m').
  { intros P HP a HPa Hin.
    pose proof (A.AsanRTFacts.in_shadow_range a Hin) as Hrng.
    destruct (Z_lt_le_dec a (ACtlCutP.Sfr fr + 320)) as [H1 | H1];
      [| destruct (Z_lt_le_dec a (ACtlCutP.Sfr fr + 324)) as [H2 | H2]].
    - destruct (HP a HPa Hin) as (Hw1 & bb & Hw2). split; [apply WMtot; exact Hw1 |].
      exists bb. unfold lib.Lib.Mem.mrd in *.
      rewrite (MUtot (lib.Lib.Mem.wa a)); [exact Hw2 |].
      rewrite lib.Lib.Mem.wa_unsigned by lia. apply HshW; [exact Hin | lia].
    - split; [apply WMtot; exact (proj1 (HP a HPa Hin)) |].
      assert (E4 : a = ACtlCutP.Sfr fr + 320 \/ a = ACtlCutP.Sfr fr + 321 \/
                   a = ACtlCutP.Sfr fr + 322 \/ a = ACtlCutP.Sfr fr + 323) by lia.
      destruct E4 as [->|[->|[-> | ->]]]; eexists;
        [ exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ0) | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ1)
        | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ2) | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ3) ].
    - destruct (HP a HPa Hin) as (Hw1 & bb & Hw2). split; [apply WMtot; exact Hw1 |].
      exists bb. unfold lib.Lib.Mem.mrd in *.
      rewrite (MUtot (lib.Lib.Mem.wa a)); [exact Hw2 |].
      rewrite lib.Lib.Mem.wa_unsigned by lia. apply HshW; [exact Hin | lia]. }
  pose proof (Hkeep _ Hcut) as Hcut'.
  pose proof (Hkeep _ Himg) as Himg'.
  (* the own frame's shadow at the exit memory, region (F), for FRAC's 392 frame-shadow bytes *)
  assert (HFSW' : A.ShadowRwOn.shadow_rw_on (fun a => ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512) m')
    by exact (A.ShadowRwOn.shadow_rw_on_mono _ _ m' HFsh Hcut').
  assert (HRO' : A.MemNorm.ro_agree A.Img0.rsegs m').
  { apply (A.Prog.Seg.R18.r18_ro_keep mem3 m' _ HRO MUtot).
    intros a Hroa. pose proof (A.Prog.Seg.R18.r18_ro_lt a Hroa) as Hlt.
    cbn [lib.Lib.Frame.outside]. repeat split; try exact I; lia. }
  (* ---- the exit cut ---- *)
  apply (HX cx [Z.of_nat 0] fr k ly3 S3 W3 R m' md' HBASE).
  - (* the journal *)
    eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (sp - 2304 <= a < sp) \/ (fr + 2560 <= a < fr + 2560 + 32) \/
                           (ACtlCutP.Sfr fr + 320 <= a < ACtlCutP.Sfr fr + 324)).
    + exact HJ.
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict.
      destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity |].
      apply MUtot. cbn [lib.Lib.Frame.outside]. repeat split; try exact I; intro Hc; apply Hx; tauto.
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict in *.
      destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx | exact (HGROW x Hx)].
    + exact Hhid.
    + exact Hsbm.
    + intros a [Hw | [Hd | Hs]].
      * left. lia.
      * right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
        left. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096. lia.
      * right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity |].
        right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, E4096.
        unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
               lib.Reusable.YG0f.SHADOW_OFF in *.
        try change (4096 / 8) with 512. lia.
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body *)
    split; [reflexivity |].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A818d0_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi, 1.
    (* the spill transport this body uses many times *)
    assert (Hspk : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs3 mem3 off v ->
              ACtlCutP.spill R m' off v).
    { intros off v Hoff HS.
      apply (spill_move _ regs3 R mem3 m' off v A HS Hr9 ltac:(lia) Hoff
               ltac:(rewrite K9; reflexivity) MUtot).
      apply DA; lia. }
    assert (Hbtfr : forall a bs, lib.Lib.Mem.bytes_at segs mem3 a bs -> fr <= a ->
              (a + Z.of_nat (length bs) <= fr + 2560 \/
               (fr + 2592 <= a /\ a + Z.of_nat (length bs) <= fr + 4096)) ->
              lib.Lib.Mem.bytes_at segs m' a bs).
    { intros a bs Hb Ha1 Ha2.
      apply (lib.Lib.Frame.bytes_at_transport segs _ mem3 m' a bs Hb MUtot).
      destruct Ha2 as [Hc | (Hc1 & Hc2)]; [apply Dfrlo | apply Dfrhi]; lia. }
    assert (Hadfr : forall p n, A.AsanRT.addressable mem3 p n -> fr <= p ->
              (p + n <= fr + 2560 \/ (fr + 2592 <= p /\ p + n <= fr + 4096)) ->
              A.AsanRT.addressable m' p n).
    { intros p n HAd Hp1 Hp2.
      pose proof HAd as (_ & Hn0 & _).
      apply (A.Prog.Seg.R18.r18_addr_keep_rng mem3 m' _ p n HAd MUtot).
      intros i Hi. apply HshW.
      - apply A.AsanRTFacts.shadow_of_app. apply Hfrappb. lia.
      - unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. revert Hframe8. Z.div_mod_to_equations. lia. }
    assert (Hrwfr : forall a n bs, lib.Lib.Step.rw_cells segs mem3 a [lib.Lib.Cells.CB n bs] ->
              fr + 2592 <= a -> a + Z.of_nat n <= fr + 4096 ->
              lib.Lib.Step.rw_cells segs m' a [lib.Lib.Cells.CB n bs]).
    { intros a n bs Hc Ha1 Ha2.
      apply (lib.Lib.Frame.rw_cells_transport segs _ mem3 m' a _ Hc MUtot WMtot).
      cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add]. rewrite Nat.add_0_r. apply Dfrhi; lia. }
    (* 1 the live list *)
    split; [exact HPERM |].
    (* 2 FRAC *)
    split.
    (* FRAC at (R, m'), RE-ESTABLISHED by a walk over the goal's conjuncts, none named by position (header) *)
    { pose proof HFw as HFd. decompose [and ex] HFd.
      exists A, sp.
      repeat lazymatch goal with |- _ /\ _ => split end.
      all: r18g_frac_leaf mem3 m' fr MUtot DA Dfrlo Dfrhi Dsaved HFSW' Hshb K2 K3 K4 K8 K9 K19 K26. }
    (* 3 the group *)
    split.
    { split; [exact Hgn |].
      destruct HRFb as ((Hb6' & HCUR' & HOUR' & H23' & HIDB & HFGB) & Hnz & H24 & HFb).
      assert (HRFb' : ACtlCutP.RFb cx fr 0 (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 0)
                        (A.Prog.SlotModel.RFG (ACtlCut.c_in cx) 0) phi R m').
      { split.
        { split; [exact Hb6' |]. split.
          { destruct HCUR' as (Hc0 & Hc22 & Hc25). split; [exact Hc0 |].
            split; [unfold ACtlCut.rgv in *; rewrite K22; exact Hc22
                   | unfold ACtlCut.rgv in *; rewrite K25; exact Hc25]. }
          split.
          { unfold ACtlCutP.OURb in *. apply Hbtfr; [exact HOUR' | lia |].
            assert (LO : length (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat) by reflexivity.
            rewrite LO. cbn [Z.of_nat]. lia. }
          split; [unfold ACtlCut.rgv in *; rewrite K23; exact H23' |].
          split.
          { unfold ACtlCutP.IDBr in *. apply Hbtfr; [exact HIDB | lia |].
            assert (LI : length (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 0) = 38%nat) by reflexivity.
            rewrite LI. cbn [Z.of_nat]. lia. }
          { unfold ACtlCutP.FGBr in *. apply Hbtfr; [exact HFGB | lia |].
            assert (LF : length (A.Prog.SlotModel.RFG (ACtlCut.c_in cx) 0) = 72%nat) by reflexivity.
            rewrite LF. cbn [Z.of_nat]. lia. } }
        split; [exact Hnz |].
        split; [unfold ACtlCut.rgv in *; rewrite K24; exact H24 |].
        apply (lib.Lib.Frame.bytes_at_transport segs _ mem3 m' _ _ HFb MUtot).
        rewrite HFlen. rewrite Z2Nat.id by lia.
        apply (Dblk phi (ACtlCutP.rnb cx 0) Hinblk);
          [lia | unfold lib.Reusable.YG00.req_size; destruct (ACtlCutP.rnb cx 0 =? 0) eqn:E0;
                 [apply Z.eqb_eq in E0; lia | lia]]. }
      split; [exact HRFb' |].
      split.
      { unfold ACtlCutP.OUTA in *. apply Hadfr; [exact HOUTA | lia | lia]. }
      split; [unfold ACtlCut.rgv in *; exact K10 |].
      split; [lia |].
      split; [unfold ACtlCut.rgv in *; rewrite K27; exact H27 |].
      split; [unfold ACtlCut.rgv, ACtlCutP.decl_slot in *; rewrite K18; reflexivity |].
      unfold ACtlCutP.decl_slot. destruct HRW as ((_ & HRWb) & _).
      cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HRWb. rewrite app_nil_r in HRWb. exact HRWb. }
    (* 4 b = 0 *)
    split; [reflexivity |].
    (* 5 HB *)
    split.
    { destruct HHB as (Hphinz & HAphi). split; [exact Hphinz |].
      apply (A.Prog.Seg.R18.r18_addr_keep_rng mem3 m' _ phi (A.ACtlK.a_size (ACtlCutP.rnb cx 0))
               HAphi MUtot).
      intros i Hi. apply (Hblksh phi (ACtlCutP.rnb cx 0) Hinblk).
      unfold A.ACtlK.a_size, lib.Reusable.YG00.req_size in *.
      destruct (ACtlCutP.rnb cx 0 =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | lia]. }
    (* 6 vd bounds *)
    split; [lia |].
    (* 7 the declaration's length *)
    split; [exact (A.Prog.Seg.R18.r18_decl_len (ACtlCut.c_in cx)) |].
    (* 8 the declaration slot is addressable *)
    split.
    { unfold ACtlCutP.decl_slot. split; [lia |]. split; [lia |].
      split; [unfold A.AsanRT.APPMEM_END; lia |].
      intros i Hi. split; [apply Hfrappb; lia |].
      assert (Esh : A.AsanRT.shadow_addr (fr + 2560 + i) = ACtlCutP.Sfr fr + 320 + i / 8)
        by (unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr; revert Hframe8; Z.div_mod_to_equations; lia).
      assert (Hq4 : 0 <= i / 8 < 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite Esh. exists (Z_to_bv 8 0). split; [| unfold A.AsanRT.shadow_ok; left; reflexivity].
      assert (E4 : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3) by lia.
      destruct E4 as [->|[->|[-> | ->]]];
        [ replace (ACtlCutP.Sfr fr + 320 + 0) with (ACtlCutP.Sfr fr + 320) by lia
        | replace (ACtlCutP.Sfr fr + 320 + 1) with (ACtlCutP.Sfr fr + 321) by lia
        | replace (ACtlCutP.Sfr fr + 320 + 2) with (ACtlCutP.Sfr fr + 322) by lia
        | replace (ACtlCutP.Sfr fr + 320 + 3) with (ACtlCutP.Sfr fr + 323) by lia ];
        [ exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ0) | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ1)
        | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ2) | exact (A.Prog.Seg.R18.r18_b1_rd m' _ _ HZ3) ]. }
    (* 9 *)
    split; [exact (Hspk 128 _ ltac:(lia) Hsp128) |].
    (* 10 PRO *)
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pn &
        P184 & P256 & P264 & P272 & P32).
      pose proof HBASE as (HPRE0 & _).
      destruct HPRE0 as (_ & _ & _ & _ & Hinp & Hnlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      split; [exact (Hspk 40 _ ltac:(lia) P40) |]. split; [exact (Hspk 120 _ ltac:(lia) P120) |].
      split; [exact (Hspk 136 _ ltac:(lia) P136) |]. split; [exact (Hspk 160 _ ltac:(lia) P160) |].
      split; [exact (Hspk 168 _ ltac:(lia) P168) |]. split; [exact (Hspk 176 _ ltac:(lia) P176) |].
      split; [exact (Hspk 208 _ ltac:(lia) P208) |]. split; [exact (Hspk 248 _ ltac:(lia) P248) |].
      split; [apply Hadfr; [exact Pad | lia | lia] |].
      assert (Hinp3 : 0 < ACtlCut.c_n cx -> In (ACtlCut.c_p cx, ACtlCut.c_n cx)
                        (lib.Reusable.YG0d.ablocks B ly3 S3)).
      { intros Hpos. destruct Hinp as [(H0 & _) | (_ & Hin0)]; [lia |].
        apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hin0. }
      split.
      { destruct (Z.eq_dec (ACtlCut.c_n cx) 0) as [E0 | E0].
        - assert (Enil : ACtlCut.c_in cx = []).
          { apply length_zero_iff_nil. lia. }
          rewrite Enil in Pin |- *. exact (bytes_at_nil mem3 m' _ Pin).
        - apply (lib.Lib.Frame.bytes_at_transport segs _ mem3 m' _ _ Pin MUtot).
          rewrite <- Hnlen.
          assert (Hpos : 0 < ACtlCut.c_n cx).
          { destruct Hinp as [(H0 & _) | (H0 & _)]; lia. }
          apply (Dblk (ACtlCut.c_p cx) (ACtlCut.c_n cx) (Hinp3 Hpos)); [lia |].
          unfold lib.Reusable.YG00.req_size. destruct (ACtlCut.c_n cx =? 0) eqn:Eq0;
            [apply Z.eqb_eq in Eq0; lia | lia]. }
      split.
      { intros Hpos.
        apply (A.Prog.Seg.R18.r18_addr_keep_rng mem3 m' _ (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                 (Pn Hpos) MUtot).
        intros i Hi. apply (Hblksh _ _ (Hinp3 Hpos)).
        unfold lib.Reusable.YG00.req_size. destruct (ACtlCut.c_n cx =? 0) eqn:Eq0;
          [apply Z.eqb_eq in Eq0; lia | lia]. }
      split; [exact (Hspk 184 _ ltac:(lia) P184) |]. split; [exact (Hspk 256 _ ltac:(lia) P256) |].
      split; [exact (Hspk 264 _ ltac:(lia) P264) |]. split; [exact (Hspk 272 _ ltac:(lia) P272) |].
      exact (Hspk 32 _ ltac:(lia) P32). }
    (* 11 .. 14 *)
    split; [exact (Hspk 104 _ ltac:(lia) Hsp104) |].
    split; [exact (Hspk 96 _ ltac:(lia) Hsp96) |].
    split; [exact (Hspk 64 _ ltac:(lia) Hsp64) |].
    split; [unfold ACtlCut.rgv in *; rewrite K21; exact H21 |].
    (* 15 .. 17 *)
    split; [exact (Hspk 112 _ ltac:(lia) Hsp112) |].
    split; [exact (Hspk 144 _ ltac:(lia) Hsp144) |].
    split; [exact (Hspk 192 _ ltac:(lia) Hsp192) |].
    (* 18 .. 19 *)
    split; [destruct HRWid as (idb & Hc); exists idb; exact (Hrwfr _ 38%nat idb Hc ltac:(lia)
              ltac:(cbn [Z.of_nat]; lia)) |].
    split; [destruct HRWjk as (junk & Hc); exists junk; exact (Hrwfr _ 72%nat junk Hc ltac:(lia)
              ltac:(cbn [Z.of_nat]; lia)) |].
    (* 20 .. 23 *)
    split; [exact (Hspk 280 _ ltac:(lia) Hsp280) |].
    split; [exact (Hspk 240 _ ltac:(lia) Hsp240) |].
    split; [destruct HRWjy as (jy & Hc); exists jy; exact (Hrwfr _ 1%nat jy Hc ltac:(lia)
              ltac:(cbn [Z.of_nat]; lia)) |].
    split; [destruct HRWsc as (junk & Hc); exists junk; exact (Hrwfr _ 32%nat junk Hc ltac:(lia)
              ltac:(cbn [Z.of_nat]; lia)) |].
    (* 24 .. 25 *)
    split; [exact (Hspk 152 _ ltac:(lia) Hsp152) |].
    split; [apply Hadfr; [exact HAid | lia | lia] |].
    (* 26 RXS *)
    { destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XAd).
      split; [exact (Hspk 48 _ ltac:(lia) X48) |]. split; [exact (Hspk 56 _ ltac:(lia) X56) |].
      split; [exact (Hspk 88 _ ltac:(lia) X88) |]. split; [exact (Hspk 80 _ ltac:(lia) X80) |].
      split; [exact (Hspk 72 _ ltac:(lia) X72) |]. split; [exact (Hspk 8 _ ltac:(lia) X8) |].
      split; [exact (Hspk 0 _ ltac:(lia) X0) |]. split; [exact (Hspk 200 _ ltac:(lia) X200) |].
      split; [exact (Hspk 216 _ ltac:(lia) X216) |].
      apply Hadfr; [exact XAd | lia | lia]. }
  - (* ctl_rt_C B ly3 S3 m' at the exit, route (i): asan_cells and ro_agree kept as before, the cut's two regions
       carried across the run (Hkeep) *)
    split; [exact HAC' |]. split; [exact Hcut' |]. split; [exact Himg' | exact HRO'].
Qed.

End GlueR18.

Print Assumptions glue_seg_R18.
