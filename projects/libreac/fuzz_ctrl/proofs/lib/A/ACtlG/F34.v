(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1114 of its 1252 lines of code are new or changed and 873 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F34.v, with its module paths and module names changed; 702 of its 781 lines of code are new or changed and 1173 lines of the source are left out. *)
(* lib/A/ACtlG/F34.v -- GLUE for stage seg_F34 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   `Hypothesis seg_F34`, :658 at glue base 7a69ca2336c, :660 at 08fb04899f5, :709 at 8ee48574229 (a Theorem Labs lane's Batch3
   d36efc6152d merged); the statement is unchanged).  Written by a Theorem Labs lane
   (a working branch), re-fitted to Batch3 by a Theorem Labs lane (branch
   a working branch); single writer.  The
   pattern is glue-pattern.md (a working note, not in this delivery) (G1-G5, section 4 for a run that writes
   memory), the template lib/A/ACtlG/F33.v.  rule 24: no function proved (stage glue of a walk from an already-proved
   segment run through the proved bridge).

   WHAT IT PROVES
     glue_seg_F34 : forall POST (j i : nat),
       CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []): exactly ACtl.v's Section hypothesis seg_F34.
   ENTRY C_A8286c_at [j; i] (the row loop head at row i, ACtlCutP.v:2803, pc 0x8286c); EXIT C_A82888_at [j; i]
   (declaration_of returned, ACtlCutP.v:2818, pc 0x82888).  Segment F34 is 0x8286c -> 0x82888: the four shadow stores
   `sb zero,8(s3)` .. `sb zero,11(s3)` (the slot [fr + 64, fr + 96) becomes addressable), `mv a0,s4`, `mv a1,s9` and
   the call of declaration_of(row i, slot).

   THE RUN: lib/A/Prog/Seg/F34F.v f34_evt_F_on, the route (C) twin of f34_evt_F (the refit: asan_cells m in place of
   AsanRTInv.RT, the shadow premise narrowed to shadow_rw_on (f34_evt_F_shadow_R r o) m = declaration_of's region
   DECLc.declaration_of_shadow_R r o, the post's shadow conjunct the transport `forall P, shadow_rw_on P m ->
   shadow_rw_on P m'`, and declaration_of_contract_F's three footprint premises), Required qualified.  Its Section
   hypothesis DECLF_on (declaration_of_c.declaration_of_contract_F_on) is discharged by the callee's CLOSED theorem
   A.Prog.declaration_ofF.declaration_of_F_holds_on_closed (a Theorem Labs lane; no hypothesis left: it closes __asan_memset /
   __asan_memcpy by their _F_on proofs).  The whole run is lifted ONCE with Reusable.YA0nR.SRr_fevt_hid at
   RNG := A.ProgBridge.RNG_W (w_H W3).  No split.

   ROUTE (C) (L3; ACtlCut.v (at head lib/A/ACtlCut.v:243); from a working branch 8ce82d7e310): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 = asan_cells /\ shadow_rw_on (cut_shadow B ly3 S3) /\ shadow_rw_on img_shadow /\
   ro_agree (was ACtlCut.ctl_rt mem3).  The Section never had VIS0 / OWNED_RO.  Consumption rows
   (shadow-rw-consumers-A.md:334-337), each with its region (L3 recipe section 2c):
     - the four shadow stores' wview premise, [Sfr fr + 8, Sfr fr + 12): the owned class-6 frame's shadow, cut_shadow's
       (F) disjunct (HcutF, by f34_cut_frame);
     - the run's region declaration_of_shadow_R rr (fr + 64): the row's aligned shadow words at rr + 24 and rr + 254
       are img_shadow (f34_img_word: the catalogue lies 64 bytes inside [IMG_LO, IMG_HI)), the slot's aligned shadow
       words lie in the frame's shadow, (F) (f34_slot_word); fed by shadow_rw_on_mono over shadow_rw_on_union;
     - FRAC's frame shadow [Sfr fr, Sfr fr + 392) at m': (F), carried across the run by its post;
     - the exit's ctl_rt_C B ly3 S3 m' (ly3, S3 unchanged): asan_cells by asan_cells_kept, the two regions by the
       run's post, ro_agree from the post.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j; Z.of_nat i]: ix_cut's index equation, then C_A8286c_at's conjuncts (the live
       list, FRAC, c_n, j <= 255, HB, FLSI, LK, i <= 10, RL, LT); ixn reads the index back by Nat2Z.id.
   G2  the run's premises, at S := Sfr fr, r := CAT + CAT_ROW * i, o := fr + 64, spv := sp (FRAC's register 2),
       lo := sp - 2304, row := rowb i, ob from Seg/F34.v f34_rw_of_stk on FLSH's frame stk:
       - registers: FRAC (2, 19), RL (20), FLSX (25);
       - the frame: fr = frame_addr ly3 6 pos (frame law + layout_le's ly_F); 6283264 <= fr from
         fr = ly_F + 36864 + 6 * 2^20 + 4096 * pos (YG0f.v:39), 0 <= pos (am_wf's wf_fs.wfs_live, YG01.v:313) and
         4096 <= ly_F (am_layout's lo_app, YG0f.v:319); fr + 4096 <= alloc_ceiling (YCbq.frames_bounds); the frame
         bytes and its 512 shadow bytes present (YG0d.al_frames);
       - the stack window [sp - 2304, sp) inside the journal's [c_sp - 32768, c_sp) (FRAC: c_sp - 4096 < sp <= A,
         A + 416 <= c_sp), present there (the journal's 14th conjunct), above the frame (astk_ok: alloc_ceiling <=
         ly_stk_lo, ly_stk_lo + 32768 <= c_sp);
       - the row: Seg/F34.v f34_row; its bytes: the catalogue lies in the image's WRITABLE third segment
         [0x9e000, 0xa1000) (measured: seg_writable = true), so ctl_rt_C's ro_agree does not reach it; the bytes come
         from the core pre's arodata_okS (ACfn.v:41) on [RLO, RHI) (Section hypothesis RELRO_CAT), carried to the cut
         by the journal's image conjunct (YCbq.v:362); addressable r 296 from CtrlRo.in_zs (a row of B's
         as_zero_shadow covering the catalogue, named by value, under TFIB_SYMS) through CtrlRo.ro_usable;
       - ro_agree / asan_cells from ctl_rt_C; the run's shadow region from ctl_rt_C's two regions (ROUTE (C) above);
       - the footprint at RNG_W (w_H W3): rng_bytes_RNG_W, img_vis_W (the image and the row), rt_vis_W, the window
         (journal presence) and its shadow words (ProgWorldVisWin.win_sh_vis), the four shadow stores (al_frames), the
         row's shadow words (CtrlRo.ro_hull under IMG_SHADOW_VIS), the slot and its shadow words
         (ProgWorldVisFrame.frame_vis).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt_hid at RNG_W (w_H W3); fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the end state MS R .. 0x82888 .. m' (R the run's explicit map: s3 = Sfr fr, s4 = r, s9 = fr + 64, a0 = 1,
       every register the exit body reads regs3's): the exit cut C_A82888_at [j; i] there.  The write set is
       WS = [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] (the run's munch).
         journal  YCbq.ajournal_exec with Wr = WS's three ranges: the frame shadow and the slot by in_frames (own6),
                  the window by the stack case; memory equal outside WS (munch); the restricted memory grows (the
                  written bytes are present after, and no byte of WS is an image byte); hidden bytes from
                  SRr_fevt_hid; same_but_materialized from the lift;
         frames, frame law, k bound  unchanged (own6, the same kmax 14 + 2 j + 1 on both cuts);
         body     the live list unchanged; FRAC by f34_frac_keep (memory, Batch3's trailer word included: see FRAC
                  AND BATCH3'S TRAILER WORD below) + Kit.kit_frac_move (registers); HB, FLSI,
                  LK, RL's FLSX and LT by the f34_*_keep transports below (every byte they read is a spill above
                  sp, the frame outside the slot, the input block, the turn's block, or the shadow of one of those:
                  all outside WS); a0 = 1, the slot's bytes decl_i i and its addressability from the run's post;
         ctl_rt_C asan_cells by AsanRTFacts.asan_cells_kept (WS lies above RT_HI), cut_shadow / img_shadow by the
                  run's post (the regions do not move: ly3, S3 unchanged) and ro_agree from the run's post.

   FRAC AND BATCH3'S TRAILER WORD.  This stage PRODUCES FRAC at its exit C_A82888_at [j; i] at the run's new memory
   m', and since Batch3 (a Theorem Labs lane, d36efc6152d) FRAC's last conjunct is the fake-frame trailer word
   `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))` (ACtlCutP.v (at head lib/A/ACtlCutP.v:1078)).  f34_frac_keep proves it with every other
   q64 / bytes_at conjunct of FRAC, by FRAC's own unfolding (no conjunct is counted): its bytes [fr + 4088, fr + 4096)
   lie in the class-6 frame [fr, fr + 4096) and outside the slot [fr + 64, fr + 96), so the premise Hfr_out (every
   frame byte outside the slot is outside WS) keeps them; WS's other two ranges are the frame's shadow
   [Sfr fr + 8, Sfr fr + 12) and the window [sp - 2304, sp), and fr + 4096 + 26368 <= sp - 2304 (Hwlo).  The frame
   LLVMFuzzerTestOneInput writes is [fr, fr + 3136); 3136 < 4088.  The G1 destruct of FRAC is by statement
   (f34_split + assumption), never by position.

   SECTION HYPOTHESES (the Section mirrors ACtl.v's Section Ctl, ACtl.v:183-238 at 8ee48574229, restricted to what
   this stage uses, in its order):
     - RELRO_CAT : ACtl.v's own Section hypothesis (ACtl.v:205, added by Batch3), same NAME and same TEXT:
       `RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI`;
       ACtl.v passes it by `exact`.  Needed because the catalogue rows [0x9e800, 0x9f4b8) are in a writable segment,
       so their image value is reachable only through the pre's read-only span [RLO, RHI).  Discharged at ACtl.v's
       top (relro_cat_ctrl, at RLO / RHI = 0x9e380 / 0xa07c8).
     - LAWS : the core's AR law record (ACtl.v:210; YCbq Section a0's hypothesis, YCbq.v:207).
     - TFIB_SYMS : A.AF0m.CtrlTSyms B (ACtl.v:225): as_zero_shadow B (ts_zsh), as_owned_static B (ts_owned) and
       as_errno B (ts_errno).
     - IMG_SHADOW_VIS : A.Prog.CtrlRo.img_shadow_vis segs B (CtrlRo.v:44-46, under its own name; glue-base blob
       befbf83b8dc, the blob a Theorem Labs lane's PA layer 40391d573a9 brought; a Theorem Labs lane's record line e56483f863b carries no
       CtrlRo.v).  Owner a Theorem Labs lane (the walk / core start-up side).  Every shadow byte of the image's read range is
       mapped; it gives the row's 8-aligned shadow words through CtrlRo.ro_hull.

   WHY THE ROW'S SHAPE CHANGED (2026-10-29, lane owner + a Theorem Labs lane): the first version took both the row's addressability
   and its shadow-word visibility from Tfib_zero_shadow's 4th row (ProgWorldVisFrame.glob_sh_vis).  That was
   derivable only from the planning core's WIDE stand-in row (port_core_refused_20ec0, 0xa4380 - ..).  The record AF0m
   (a working branch e56483f863b, lib/A/AF0m.v:2955) has a fine per-global list: its row 37,
   (0x9e800, 0xcb8), covers the catalogue exactly, so addressability still holds, but the 64-byte hull of the i = 10
   row reaches 0x9f4c0, past that row's end 0x9f4b8, into the gap before the next row 0x9f7e0.  So the shadow words
   come from CtrlRo.ro_hull under IMG_SHADOW_VIS, as CtrlRo.v's header (:16) prescribes for a walk that reads a table.

   THE COVERING ROW (formerly a known stand-in dependence): the covering row of `CtrlRo.in_zs B (CAT + 296 i) 296` is
   found by a boolean search (existsb, vm_compute) over Tfib_zero_shadow, not by position.  On the old planning core
   the row it found was the stand-in row (port_core_refused_20ec0 -> 0x20ec0, 0xa4380 - 0x20ec0).  The stand-in-free
   base 121bf608343 carries the record AF0m, whose fine list holds (0x9e800, 0x9f4b8 - 0x9e800) (AF0m.v:2963), the
   only row covering the catalogue [0x9e800, 0x9f4b8); the build on that base re-checked this step.

   LOCAL HELPERS (proof-internal, every premise discharged here; candidates for the kit, statements in the report):
   f34_aview_vis_mrd / f34_mrd_of_aview_some (ProgWorld 7f07ac65e7b's aview_vis_mrd / mrd_of_aview_some, not on this
   base), f34_opt_inj, f34_sa_eq, f34_mrd_high, f34_wview_some, f34_spill_keep, f34_stk_keep, f34_hb_keep,
   f34_f1in_keep, f34_flsi_keep, f34_lk_keep, f34_flsx_keep, f34_lt_keep, f34_frac_keep: the transported bundles over
   ANY write set W (the kept set is a parameter: each lemma takes the ranges it reads as `outside W`).
   f34_frac_keep does not count FRAC's conjuncts: it moves every q64 / bytes_at conjunct whose range lies in the frame
   outside the slot or in [spZ regs, c_sp), so it carries Batch3's trailer conjunct at fr + 4088 with no edit.

   CLOSURE (glue closure rule): every project Require below names its module's own directory in the From clause
   (no partial `From ..lib Require X.Y`); no statement here names a frame-route identifier.  The closure reaches the
   frame route only through Seg/F34F.v -> Seg/F34.v (SlotInv, AsanRTInv, Contract, FrameAPI, MemNorm ...), as
   closure rule 1 allows; it holds no lib/AZ/AsanW, W6 or cut-free file (scripted scan).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are qualified everywhere; the core's YK11 / YM05 / YO09 / YP09 (each
   also under lib/A/Reusable) are named by their FULL path OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X>,
   and lib/Lib's Mem / Frame / PropExec / MState (each also under lib/A/Bz/Lib, lib/AZ/Lib, lib/B/Bz/Lib) through the
   full-path aliases LMem / LFrm / LPEx / LMSt.  Every other module this file names exists once (Locate checked).

   BUILD STATE (2026-10-29): TYPE-CHECK ON INTERIM 5da74c9c931, CLOSURE REACHES NO STAND-IN, not acceptance.  The
   glue base a working branch 121bf608343 carries a Theorem Labs lane's stand-in-free 29ddfc3ea99 (a Theorem Labs lane's interim core
   5da74c9c931 + Batch3 + a Theorem Labs lane's ProgWorld files): the closure's lib/A/AE2k.v, AF0l.v and AF0m.v hold no
   port_core_refused name, and the build substitutes nothing.  F34.vo compiles from a fresh clone through
   cb (BASE 23b918fe0c2e; the lane report names the commit, log and .vo mtime); Print Assumptions
   glue_seg_F34 = the Rocq primitives (PrimInt63, PrimString, PrimArray) + functional_extensionality_dep (from
   SRr_fevt_hid); RELRO_CAT, LAWS, TFIB_SYMS and IMG_SHADOW_VIS are its Section-hypothesis arguments.  No Axiom, no
   Parameter, no Admitted.  The Batch3 re-fit itself type-checked first on 8ee48574229 with the stand-ins. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
(* Every project module by its own directory (a partial `From ..lib Require X.Y` can also match lib/A/Bz, lib/AZ,
   lib/B/Bz copies); YK11 / YM05 / YO09 / YP09 are the core's, lib/Reusable. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YA0nR YG0f YG00 YG01 YG0d YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0v YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k AF0m ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorldVisFrame ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss Mem Frame PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel RcAsanFPLib ImgBounds rng_asan CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require declaration_of_c declaration_ofF sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F34 F34F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.
(* lib/Lib's Mem / Frame / PropExec / MState by their full path: each also exists as lib/A/Bz/Lib, lib/AZ/Lib and
   lib/B/Bz/Lib copies, which a partial `Lib.X.n` can bind to. *)
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LPEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Readers and addresses. *)

(* At a visible address the core's view is ctrl's mrd (ProgWorld 7f07ac65e7b aview_vis_mrd, restated). *)
Lemma f34_aview_vis_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (LMem.mrd A.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Hh.
  unfold Reusable.YG0n.aview, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte,
    Reusable.YK04.mrestrict, LMem.mrd.
  rewrite Hh. reflexivity.
Qed.

(* A byte the view reads is what mrd reads (ProgWorld 7f07ac65e7b mrd_of_aview_some, restated; the visibility
   premise comes from the read itself, ProgWorldVisFrame.vis_of_aview). *)
Lemma f34_mrd_of_aview_some : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a v : Z),
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a = Some v ->
  LMem.mrd A.Img0.rsegs mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E.
  assert (Hh : Reusable.YA0n.w_H W (Z_to_bv 64 a) = false)
    by (apply (A.ProgWorldVisFrame.vis_of_aview segs W mem a); rewrite E; discriminate).
  rewrite (f34_aview_vis_mrd W mem a Hh) in E.
  destruct (LMem.mrd A.Img0.rsegs mem (Z_to_bv 64 a)) as [b|]; cbn [option_map] in E; [|discriminate E].
  injection E as Eb. rewrite <- Eb, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma f34_opt_inj : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [a|] [b|] H; cbn [option_map] in H; try discriminate H; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* The core's shadow map is ctrl's: both are a / 8 + 0x7fff8000. *)
Lemma f34_sa_eq : forall a, Reusable.YG0f.shadow_addr a = A.AsanRT.shadow_addr a.
Proof.
  intros a. unfold Reusable.YG0f.shadow_addr, A.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K.
  lia.
Qed.

(* No byte at or above the image top 0x5fe000 is a segment byte (YK04.find_segment1_none_above through
   H_off_segments_above, the segments' tops computed), so a byte there that reads Some through mrd is a byte of the
   memory itself. *)
Lemma f34_mrd_high : forall (m : word -> option byte) (x : word) b,
  0x5fe000 <= bv_unsigned x -> LMem.mrd A.Img0.rsegs m x = Some b -> m x <> None.
Proof.
  intros m x b Hx Hb Hn. unfold LMem.mrd in Hb. rewrite Hn in Hb.
  pose proof (Reusable.YK04.H_off_segments_above A.Img0.rsegs (fun a : word => (0x5fe000 <=? bv_unsigned a)%Z)
                0x5fe000 ltac:(vm_compute; reflexivity)
                ltac:(intros a Ha; apply Z.leb_le in Ha; exact Ha)) as HH.
  unfold LPEx.seg_rom in Hb.
  rewrite (Reusable.YK04.memory_read1_hidden A.Img0.rsegs _ HH x ltac:(apply Z.leb_le; exact Hx)) in Hb.
  cbn in Hb. discriminate Hb.
Qed.

(* A byte that memory holds is in the writable view. *)
Lemma f34_wview_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> wview A.Img0.rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

(* ---------------------------------------------------------------------------------------------------------
   1b. Route (C) regions (L3 recipe section 2c): where each shadow byte the run stores or hands to declaration_of
   lies in ctl_rt_C's two regions, A.ACtlRtC.cut_shadow (its (F) disjunct) and A.ACtlRtC.img_shadow. *)

(* (F): the shadow [Sfr fr, Sfr fr + fs_frame_bytes cid / 8) of an owned frame at fr. *)
Lemma f34_cut_frame : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) cid pos fr a,
  In (cid, pos) (Reusable.YG01.frames S) -> Reusable.YG0f.frame_addr ly cid pos = fr ->
  ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + Reusable.YG00.fs_frame_bytes cid / 8 ->
  A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S cid pos fr a Hin Efa Ha. left. exists cid, pos. split; [exact Hin|].
  rewrite Efa, f34_sa_eq. unfold ACtlCutP.Sfr in Ha. lia.
Qed.

(* (I): an aligned shadow word of a range that lies 64 bytes inside the image hull [IMG_LO, IMG_HI) is the shadow
   of an image byte (x := 8 * (a - SHADOW_OFF), the first byte that word shadows). *)
Lemma f34_img_word : forall p n a,
  A.Prog.CtrlRo.IMG_LO + 64 <= p -> p + n + 64 <= A.Prog.CtrlRo.IMG_HI ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.img_shadow a.
Proof.
  intros p n a Hp Hn (_ & Hlo & Hhi).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hlo, Hhi.
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in Hp, Hn.
  exists (8 * (a - Reusable.YG0f.SHADOW_OFF)).
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  split; [split|].
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - rewrite (Z.mul_comm 8), Z.div_mul by (intros E; discriminate E). ring.
Qed.

(* The aligned shadow words of the slot [fr + 64, fr + 96) lie in the frame's shadow [Sfr fr, Sfr fr + 512)
   (fr is 32-aligned). *)
Lemma f34_slot_word : forall fr a, 0 <= fr -> fr mod 32 = 0 ->
  A.Prog.sh_word_on.sh_word_on (fr + 64) 32 a -> ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512.
Proof.
  intros fr a Hfr H32 (_ & Hlo & Hhi).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Hlo, Hhi.
  unfold ACtlCutP.Sfr. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The cut layer's bundles (ACtlCutP.v) across ANY write set W: each transport takes the ranges its bundle reads
   as `outside W` premises (the kept set is a parameter). *)

(* A spill [A + off] (ACtlCutP.spill: exists A, rgv regs 9 A /\ q64 m (A + off) v) moves with the spill base. *)
Lemma f34_spill_keep : forall (W : list LFrm.ivl) (m m' : word -> option byte) (regs regs' : bvmap 5 word)
    Ab off v,
  LFrm.munch W m m' -> ACtlCut.rgv regs 9 Ab -> 416 <= Ab -> Ab + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  (forall x, Ab <= x < Ab + 416 -> LFrm.outside W x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros W m m' regs regs' Ab off v MU HA H1 H2 Hoff E HW (A' & HA' & Hq).
  pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (EA : A' = Ab).
  { unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
    apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'.
    unfold bv_wrap in HA'. change (bv_modulus 64) with (2 ^ 64) in HA'.
    rewrite (Z.mod_small Ab (2 ^ 64)) in HA' by lia.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as D. rewrite <- HA' in D. lia. }
  subst A'. exists Ab. split.
  - unfold ACtlCut.rgv in *. rewrite E. exact HA.
  - unfold ACtlCutP.q64 in *. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' (Ab + off) _ Hq MU).
    rewrite LMem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HW. lia.
Qed.

(* A stk range moves when each of its bytes is kept or present after the write. *)
Lemma f34_stk_keep : forall (W : list LFrm.ivl) (m m' : word -> option byte) lo hi,
  LFrm.munch W m m' -> LFrm.wmono A.Img0.rsegs m m' ->
  (forall x, lo <= x < hi ->
     LFrm.outside W x \/ exists b, LMem.mrd A.Img0.rsegs m' (LMem.wa x) = Some b) ->
  LFrm.stk A.Img0.rsegs m lo hi -> LFrm.stk A.Img0.rsegs m' lo hi.
Proof.
  intros W m m' lo hi MU WM HK (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
  intros a Ha. split; [apply WM; exact (proj1 (SS a Ha))|].
  destruct (HK a Ha) as [Ho | Hb]; [|exact Hb].
  destruct (SS a Ha) as (_ & b & Hb). exists b.
  rewrite (A.Prog.Seg.F34.f34_mrd_munch W m m' a MU ltac:(lia) Ho). exact Hb.
Qed.

(* HB (ACtlCutP.v:442): the turn's block, whose shadow bytes are kept. *)
Lemma f34_hb_keep : forall (W : list LFrm.ivl) (m m' : word -> option byte) phi len,
  LFrm.munch W m m' ->
  (forall x, phi <= x < phi + A.ACtlK.a_size len -> LFrm.outside W (A.AsanRT.shadow_addr x)) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof.
  intros W m m' phi len MU HW (H0 & Had). split; [exact H0|].
  apply (A.Prog.Seg.F34.f34_addr_keepW W m m' _ _ Had MU). intros i Hi. apply HW. lia.
Qed.

(* f1_IN (ACtlCutP.v:658): the harness input block, its bytes and their shadow kept. *)
Lemma f34_f1in_keep : forall cx (W : list LFrm.ivl) (m m' : word -> option byte),
  LFrm.munch W m m' -> Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
     LFrm.outside W x /\ LFrm.outside W (A.AsanRT.shadow_addr x)) ->
  ACtlCutP.f1_IN cx m -> ACtlCutP.f1_IN cx m'.
Proof.
  intros cx W m m' MU HL HW (Had & Hb). split.
  - apply (A.Prog.Seg.F34.f34_addr_keepW W m m' _ _ Had MU). intros i Hi.
    exact (proj2 (HW (ACtlCut.c_p cx + i) ltac:(lia))).
  - apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hb MU). intros x Hx. exact (proj1 (HW x ltac:(lia))).
Qed.

(* FLSI (ACtlCutP.v:677): spills through register 9, and the facts it reads on the frame and the input block
   given at m' (Seg/F34.v f34_flsi_mem, over ACtlCutP's bundle). *)
Lemma f34_flsi_keep : forall cx j fr (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (W : list LFrm.ivl) Ab,
  ACtlCut.rgv regs 9 Ab -> 416 <= Ab -> Ab + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  LFrm.munch W m m' -> (forall x, Ab <= x < Ab + 416 -> LFrm.outside W x) ->
  A.AsanRT.addressable m' (fr + 2624) 6 -> LFrm.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  A.AsanRT.addressable m' (fr + 2691) 17 -> ACtlCutP.f1_IN cx m' ->
  A.AsanRT.addressable m' (ACtlCutP.fragb fr) 72 -> A.AsanRT.addressable m' (fr + 2688) 38 ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr regs regs' m m' W Ab HA H1 H2 E MU HW Ha' Hs' Ha17' HIN' Hfg' Hrec'
    (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & _ & _ & _ & P184 & P256 & P264 & P272 & P32) &
      S128 & _ & S144 & _) &
     S216 & S224 & S248 & _ &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & _ & _ & C72 & C64 & C56 & C48)).
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f34_spill_keep W m m' regs regs' Ab off v MU HA H1 H2 Hoff E HW)
    as T.
  pose proof HIN' as (Hpad' & Hpb').
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC.
  split.
  { split.
    { split; [exact (T 40 _ ltac:(lia) P40)|]. split; [exact (T 120 _ ltac:(lia) P120)|].
      split; [exact (T 136 _ ltac:(lia) P136)|]. split; [exact (T 160 _ ltac:(lia) P160)|].
      split; [exact (T 168 _ ltac:(lia) P168)|]. split; [exact (T 176 _ ltac:(lia) P176)|].
      split; [exact (T 208 _ ltac:(lia) P208)|]. split; [exact (T 248 _ ltac:(lia) P248)|].
      split; [exact Ha'|]. split; [exact Hpb'|].
      split; [intros _; exact Hpad'|].
      split; [exact (T 184 _ ltac:(lia) P184)|]. split; [exact (T 256 _ ltac:(lia) P256)|].
      split; [exact (T 264 _ ltac:(lia) P264)|].
      split; [exact (T 272 _ ltac:(lia) P272) | exact (T 32 _ ltac:(lia) P32)]. }
    split; [exact (T 128 _ ltac:(lia) S128)|]. split; [exact Hs'|].
    split; [exact (T 144 _ ltac:(lia) S144) | exact Ha17']. }
  split; [exact (T 216 _ ltac:(lia) S216)|]. split; [exact (T 224 _ ltac:(lia) S224)|].
  split; [exact (T 248 _ ltac:(lia) S248)|]. split; [exact HIN'|].
  split; [exact (T 256 _ ltac:(lia) C256)|]. split; [exact (T 184 _ ltac:(lia) C184)|].
  split; [exact (T 192 _ ltac:(lia) C192)|]. split; [exact (T 80 _ ltac:(lia) C80)|].
  split; [exact (T 88 _ ltac:(lia) C88)|]. split; [exact (T 96 _ ltac:(lia) C96)|].
  split; [exact (T 272 _ ltac:(lia) C272)|]. split; [exact (T 264 _ ltac:(lia) C264)|].
  split; [exact Hfg'|]. split; [exact Hrec'|].
  split; [exact (T 72 _ ltac:(lia) C72)|]. split; [exact (T 64 _ ltac:(lia) C64)|].
  split; [exact (T 56 _ ltac:(lia) C56) | exact (T 48 _ ltac:(lia) C48)].
Qed.

(* LK (ACtlCutP.v:556): register 21 and the six bytes out[] at fr + 2624. *)
Lemma f34_lk_keep : forall cx fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list LFrm.ivl),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 21 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 ->
  LFrm.munch W m m' -> (forall x, fr + 2624 <= x < fr + 2630 -> LFrm.outside W x) ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' W E MU HW (Hj & H21 & HO). split; [exact Hj|].
  split; [unfold ACtlCut.rgv in *; rewrite E; exact H21|].
  unfold ACtlCutP.OURb in *. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HO MU).
  rewrite A.Prog.SlotModel.OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. apply HW. lia.
Qed.

(* FLSX (ACtlCutP.v:696): registers 18 22 23 25, the record bytes in the turn's block, two spills (Seg/F34.v
   f34_flsx_mem, over ACtlCutP's bundle). *)
Lemma f34_flsx_keep : forall cx j phi fr (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (W : list LFrm.ivl) Ab,
  ACtlCut.rgv regs 9 Ab -> 416 <= Ab -> Ab + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 18 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 22 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 23 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 25 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25 ->
  LFrm.munch W m m' -> (forall x, Ab <= x < Ab + 416 -> LFrm.outside W x) ->
  (forall x, phi <= x < phi + ACtlCutP.flen cx j -> LFrm.outside W x) ->
  ACtlCutP.FLSI cx j fr regs' m' -> ACtlCutP.FLSX cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' W Ab HA H1 H2 E9 E18 E22 E23 E25 MU HW HWp HI'
    (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  unfold ACtlCutP.FLSX.
  split; [exact HI'|].
  split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
  split; [unfold ACtlCut.rgv in *; rewrite E22; exact H22|].
  split; [unfold ACtlCut.rgv in *; rewrite E23; exact H23|].
  split; [unfold ACtlCut.rgv in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hph & Hpl).
    assert (Lg : length (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) = 50%nat)
      by (unfold A.Prog.SlotModel.t_g, A.Prog.SlotModel.fr50;
          rewrite length_firstn, length_app, repeat_length; lia).
    split; [exact Hp0|]. split; [exact Hp1|].
    split.
    { apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hg MU). rewrite Lg. intros x Hx. apply HWp. lia. }
    split; [|exact Hpl].
    apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Hph MU). intros x Hx. apply HWp. lia. }
  split; [exact (f34_spill_keep W m m' regs regs' Ab 152 _ MU HA H1 H2 ltac:(lia) E9 HW H152)|].
  exact (f34_spill_keep W m m' regs regs' Ab 280 _ MU HA H1 H2 ltac:(lia) E9 HW H280).
Qed.

(* LT (ACtlCutP.v:724, IFS of turn j + 1): the frame records at fr + 2688 / fr + 2768, two spills, the body bytes
   at fr + 2880 and their addressability (Seg/F34.v f34_lt_mem, over ACtlCutP's bundle). *)
Lemma f34_lt_keep : forall cx fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (W : list LFrm.ivl) Ab,
  ACtlCut.rgv regs 9 Ab -> 416 <= Ab -> Ab + 416 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  LFrm.munch W m m' -> (forall x, Ab <= x < Ab + 416 -> LFrm.outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> LFrm.outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 ->
     LFrm.outside W x /\ LFrm.outside W (A.AsanRT.shadow_addr x)) ->
  ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' W Ab HA H1 H2 E MU HW HWr HWb
    ((HID & Hidok) & (HFG & Hfgok) & (Q104 & Q112 & Qbody & Qad & HFI)).
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f34_spill_keep W m m' regs regs' Ab off v MU HA H1 H2 Hoff E HW)
    as T.
  assert (LID : length (A.Prog.SlotModel.t_ID (ACtlCut.c_in cx) (S j)) = 38%nat)
    by exact (A.Prog.Seg.F34.f34_tID_length (ACtlCut.c_in cx) (S j)).
  pose proof (A.Prog.Seg.F34.f34_tFG_length (ACtlCut.c_in cx) (S j)) as LFG.
  pose proof (A.Prog.Seg.F34.f34_fs_body_len (ACtlCut.c_in cx) (S j)) as LB.
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.FGj, ACtlCutP.IDb, ACtlCutP.FGb, ACtlCutP.FSj,
    ACtlCutP.FSb.
  split.
  { split; [|exact Hidok]. unfold ACtlCutP.IDBe in *. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HID MU).
    rewrite LID. intros x Hx. apply HWr. lia. }
  split.
  { split; [|exact Hfgok]. unfold ACtlCutP.FGBe in *. apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ HFG MU).
    rewrite LFG. intros x Hx. apply HWr. lia. }
  split; [exact (T 104 _ ltac:(lia) Q104)|]. split; [exact (T 112 _ ltac:(lia) Q112)|].
  split.
  { apply (A.Prog.RcAsanFPLib.fl_bytes W m m' _ _ Qbody MU). intros x Hx. exact (proj1 (HWb x ltac:(lia))). }
  split; [|exact HFI].
  apply (A.Prog.Seg.F34.f34_addr_keepW W m m' _ _ Qad MU). intros i Hi. exact (proj2 (HWb (fr + 2880 + i) ltac:(lia))).
Qed.

(* FRAC's memory part (the registers stay the map's own; Kit.kit_frac_move moves them).  It does not count FRAC's
   conjuncts: every q64 / bytes_at conjunct is moved from its own range, which lies in the frame outside the slot
   [fr + 64, fr + 96) or in [spZ regs, c_sp) (the spill base A is at or above sp, the saved bytes at c_sp - 104),
   and the frame-shadow conjunct is re-taken at m'. *)
Lemma f34_frac_keep : forall (B : Reusable.YG0f.asyms) cx fr sel (regs : bvmap 5 word) (W : list LFrm.ivl)
    (m m' : word -> option byte),
  LFrm.munch W m m' ->
  (forall x, fr <= x < fr + 4096 -> ~ (fr + 64 <= x < fr + 96) -> LFrm.outside W x) ->
  (forall x, Reusable.YG0d.spZ regs <= x < ACtlCut.c_sp cx -> LFrm.outside W x) ->
  (exists sh, LMem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros B cx fr sel regs W m m' MU Hfr Hst Hsh' H.
  unfold ACtlCutP.FRAC in *. destruct H as (Ab & sp & H). exists Ab, sp.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    unfold ACtlCutP.q64 in *;
    match goal with
    | Hb : LMem.bytes_at _ m ?a ?bs |- LMem.bytes_at _ m' ?a ?bs =>
        apply (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs Hb MU);
        unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?LMem.length_le8; intros x Hx;
        unfold ACtlCutP.FRAME_BYTES in *;
        first [ apply Hst; lia | apply Hfr; lia ]
    end.
Qed.

(* Split a conjunction hypothesis into its atoms (fresh names), so that a bundle's facts are found by their
   statements and not by their positions. *)
Local Ltac f34_split H :=
  lazymatch type of H with
  | _ /\ _ =>
      let H1 := fresh "HFR" in let H2 := fresh "HFR" in destruct H as [H1 H2]; f34_split H1; f34_split H2
  | _ => idtac
  end.

(* ---------------------------------------------------------------------------------------------------------
   3. The stage. *)
Section GlueF34.

(* ACtl.v's Section shape (ACtl.v:183-238), restricted to what this stage uses, in ACtl.v's order. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v's own Section hypothesis RELRO_CAT (ACtl.v (at head lib/A/ACtl.v:239; written on a working branch 8ee48574229), added by Batch3), mirrored
   with its NAME and TEXT, which ACtl.v passes by `exact`.  The catalogue rows [CAT, CAT + 11 * 296) =
   [0x9e800, 0x9f4b8) lie in the core pre's read-only span [RLO, RHI) (the arodata_okS of A.ACfn.tfib_lib_pre_x,
   ACfn.v:41).  NEEDED because they lie in the image's WRITABLE third segment [0x9e000, 0xa1000) (seg_writable =
   true, measured by vm_compute), so lib/Lib/Mem.ro_addr is false there and ctl_rt's ro_agree does not reach them.
   Discharged at ACtl.v's top by relro_cat_ctrl (RLO / RHI = 0x9e380 / 0xa07c8). *)
Hypothesis RELRO_CAT :
  RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
(* The core's AR law record (ACtl.v:210; YCbq Section a0's hypothesis, YCbq.v:207). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The core's symbol facts for B (ACtl.v:225). *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* Every shadow byte of the image's read range [0x10000, 0x5fe000) is mapped in every state: CtrlRo.v's own
   start-up fact (lib/A/Prog/CtrlRo.v (at head lib/A/Prog/CtrlRo.v:44-46) (an earlier version, blob befbf83b8dc, not in this delivery), which came with a Theorem Labs lane's PA layer
   40391d573a9; owner a Theorem Labs lane), taken under its own name as that file's header (at head lib/A/Prog/CtrlRo.v:16) prescribes for a walk that
   reads an image table.  It gives the row's 8-aligned shadow words through CtrlRo.ro_hull. *)
Hypothesis IMG_SHADOW_VIS : A.Prog.CtrlRo.img_shadow_vis segs B.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :350-351), verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8286c_at := (ACtlCutP.C_A8286c_at B).
Local Notation C_A82888_at := (ACtlCutP.C_A82888_at B).

Lemma glue_seg_F34 : forall POST (j i : nat), CF POST (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i]) -> CF POST (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i]).
Proof.
  intros POST j i HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut at index [j; i] (ix_cut, ACtlCut.v:234-236; C_A8286c_at, ACtlCutP.v:2803-2816) ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8286c_at ACtlCutP.ixn nth] in Hb.
  rewrite !Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hcn & Hj & HHB & HFLSI & HLK & Hi10 & HRL & HLT).
  pose proof HRL as (_ & R20 & R24 & Hprev & Hsel & HFLSX).
  pose proof HFLSX as (_ & _ & _ & _ & R25 & _).
  pose proof HFLSI as ((HPRO & _ & Hstkfr & _ & Had2691) & _ & _ & _ & HIN & HFLC).
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & Had2624 & _).
  pose proof HFLC as (_ & _ & _ & _ & _ & _ & _ & _ & Hadfg & Hadrec & _).
  (* route (C): ctl_rt_C B ly3 S3 mem3 (ctl_from, ACtlCut.v:243) *)
  destruct Hrt as (HAC & Hcut & HimgC & HROrt).
  unfold A.ACtlK.asan_cells_at in HAC.
  (* ---- G2a: the entry pre, the journal, the layout ---- *)
  pose proof HB as ((_ & _ & _ & _ & Hpn & Hlen & _ & _ & _ & _ & HROent & _) & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & HimgK & _ & Hgone & Hwin & Hastk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  pose proof Hastk as (_ & _ & Hceil & Hstklo & Hstkhi & _).
  unfold A.ACfn.LLVMF_STK in Hstklo, Hwin.
  pose proof Reusable.YCbq.asan_consts as (Hac0 & _).
  (* ---- G2b: the frame ---- *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfceil & _).
  rewrite Efa, E4096 in Hfceil.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfapp & _ & Hfsh).
  rewrite Efa, E4096 in Hfapp. rewrite Efa, E4096 in Hfsh. change (4096 / 8) with 512 in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (HFAPP : forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y).
  { intros y Hy. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hfapp as (Hf1 & [Hf2 | (Hf2 & Hf3)]); [left | right]; lia. }
  (* the frame lies above the image top: fr = ly_F + 36864 + 6 * 2^20 + 4096 * pos, 0 <= pos, 4096 <= ly_F *)
  assert (Hfrlo : 6283264 <= fr).
  { pose proof (Reusable.YG01.wfs_live _
      (Reusable.YG01.wf_fakestack _ _ _ _ _ (Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR)))) as Hlive.
    pose proof (proj1 (Forall_forall _ _) Hlive (6, ACtlCut.c_fpos cx) Hin6) as (_ & Hpos & _).
    cbn [fst snd] in Hpos.
    pose proof (Reusable.YG0f.lo_app _ (Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR))) as Happ.
    unfold Reusable.YG0f.owned_extents in Happ.
    pose proof (proj1 (Forall_forall _ _) Happ (Reusable.YG0f.ly_F ly3, Reusable.YG0f.kFakeStackSize)
      ltac:(cbn [In]; right; right; right; left; reflexivity)) as (HF4096 & _).
    cbn [fst snd] in HF4096.
    assert (EOFF : Reusable.YG0f.fs_frame_off 6 (ACtlCut.c_fpos cx) = 6328320 + ACtlCut.c_fpos cx * 4096).
    { unfold Reusable.YG0f.fs_frame_off. rewrite E4096. reflexivity. }
    rewrite <- Efa. unfold Reusable.YG0f.frame_addr. rewrite EOFF. lia. }
  (* FRAC's facts, found by their statements *)
  pose proof HFRAC as (Ab & sp & HFR). f34_split HFR.
  assert (R2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp)
    by assumption.
  assert (HspZ : Reusable.YG0d.spZ regs3 = sp) by assumption.
  assert (R9 : ACtlCut.rgv regs3 9 Ab) by assumption.
  assert (R19 : ACtlCut.rgv regs3 19 (ACtlCutP.Sfr fr)) by assumption.
  assert (Hfr32 : fr mod 32 = 0) by assumption.
  assert (HspA : sp <= Ab) by assumption.
  assert (HA416 : Ab + 416 <= ACtlCut.c_sp cx) by assumption.
  assert (Hspc : ACtlCut.c_sp cx - 4096 < sp) by assumption.
  assert (HfrA : fr + 3136 <= Ab) by (unfold ACtlCutP.FRAME_BYTES in *; lia).
  assert (HcAPP : ACtlCut.c_sp cx <= 0x800000000000) by (unfold A.AsanRT.APPMEM_END in *; lia).
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Efr8 : 8 * (fr / 8) = fr) by (clear - Hfr8; Z.div_mod_to_equations; lia).
  (* the window [sp - 2304, sp) lies above the frame, in the journal's present stack window *)
  assert (Hwlo : fr + 4096 + 26368 <= sp - 2304) by lia.
  (* the frame's shadow bytes *)
  assert (HinSh : forall kk, 0 <= kk < 512 -> A.AsanRT.in_shadow (ACtlCutP.Sfr fr + kk)).
  { intros kk Hkk. unfold ACtlCutP.Sfr.
    rewrite <- (A.Prog.Seg.F34.f34_sh_frame_of fr kk ltac:(lia) Hfr8 ltac:(lia)).
    apply A.AsanRTFacts.shadow_of_app. apply HFAPP. lia. }
  assert (HSb : A.AsanRT.LOWMEM_END <= ACtlCutP.Sfr fr).
  { pose proof (HinSh 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in *. lia. }
  assert (HSh : ACtlCutP.Sfr fr + 512 <= A.AsanRT.HIGHMEM_BEG).
  { pose proof (HinSh 511 ltac:(lia)) as H0.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in *. lia. }
  unfold A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG in HSb, HSh.
  (* route (C): the owned class-6 frame's 512 shadow bytes are cut_shadow's (F) disjunct, and every region inside
     cut_shadow \/ img_shadow is shadow_rw_on at mem3 *)
  assert (HcutF : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. apply (f34_cut_frame B ly3 S3 6 (ACtlCut.c_fpos cx) fr a Hin6 Efa).
    rewrite E4096. change (4096 / 8) with 512. exact Ha. }
  assert (Hsw_on : forall Rg : Z -> Prop,
            (forall a, Rg a -> A.ACtlRtC.cut_shadow B ly3 S3 a \/ A.ACtlRtC.img_shadow a) ->
            A.ShadowRwOn.shadow_rw_on Rg mem3).
  { intros Rg HRg.
    exact (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 HRg (A.ShadowRwOn.shadow_rw_on_union _ _ mem3 Hcut HimgC)). }
  (* ---- G2c: the turn's block and the input block: app memory below alloc_ceiling, apart from the frame ---- *)
  assert (Hl50 : 50 <= ACtlCutP.flen cx j)
    by (unfold ACtlCutP.flen; exact (A.Prog.Seg.F34.f34_rowsel_len (ACtlCut.c_in cx) j Hsel)).
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  assert (HPH : forall y, phi <= y < phi + ACtlCutP.flen cx j ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096) /\ y < sp - 2304).
  { intros y Hy.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hinphi) as (_ & _ & Hpc & Hpa & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR
                  Hinphi Hin6) as Hd.
    rewrite Efa, E4096 in Hd. unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold Reusable.YG00.req_size in *. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0) as [E0|_]; [lia|].
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Hpa.
    split; [|split; [lia | lia]].
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hpa as (Hp1 & [Hp2 | (Hp2 & Hp3)]); [left | right]; lia. }
  assert (HLEN : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hlen).
  assert (HCP : forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096) /\ y < sp - 2304).
  { intros y Hy. destruct Hpn as [(Hn0 & _) | (Hn0 & Hinp)]; [lia|].
    assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x0 y0; decide equality; apply Z.eq_dec).
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { destruct (in_dec Hdec (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)) as [Hi|Hni];
        [exact Hi|].
      exfalso. destruct (Hgone _ _ 0 Hinp Hni ltac:(unfold Reusable.YG00.req_size;
                           destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia)) as (r0 & Hr0 & _).
      destruct Hr0. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinp3) as (_ & _ & Hpc & Hpa & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR
                  Hinp3 Hin6) as Hd.
    rewrite Efa, E4096 in Hd. unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold Reusable.YG00.req_size in *. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0) as [E0|_]; [lia|].
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Hpa.
    split; [|split; [lia | lia]].
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hpa as (Hp1 & [Hp2 | (Hp2 & Hp3)]); [left | right]; lia. }
  (* ---- G2d: the row ---- *)
  set (rr := A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_ROW * Z.of_nat i).
  assert (Err : rr = 649216 + 296 * Z.of_nat i) by reflexivity.
  assert (Hi11 : (i < 11)%nat) by lia.
  destruct (A.Prog.Seg.F34.f34_row i Hi11) as (Himg & Hok & Hrlen).
  fold rr in Himg.
  (* the row's image bytes: the pre's read-only span (RELRO_CAT), carried to the cut by the journal *)
  pose proof (A.ProgBridge.img_vis_W W3) as VIMG.
  assert (Hrow : LMem.bytes_at A.Img0.rsegs mem3 rr (A.Prog.SlotModel.rowb (Z.of_nat i))).
  { split; [lia|]. split; [rewrite Hrlen; lia|].
    intros kk Hkk. rewrite Hrlen in Hkk.
    assert (Ha1 : 649216 <= rr + Z.of_nat kk < 652472) by lia.
    assert (Hin3 : Reusable.YG0d.in_img segs (rr + Z.of_nat kk)).
    { assert (V : forall b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) ->
                    b <= rr + Z.of_nat kk < b + sz -> Reusable.YG0d.in_img segs (rr + Z.of_nat kk)).
      { intros b sz Hin Hbs. apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
        exists s. split; [exact Hs | exact Hbs]. }
      rewrite A.ProgBridge.rsegs_spans in V.
      apply (V 0x9e000 0x3000); [apply in_cons, in_cons, in_eq | lia]. }
    assert (Hown : ~ Exists (Reusable.YG0n.in_zr (rr + Z.of_nat kk)) (Reusable.YG0f.as_owned_static B)).
    { rewrite (A.AF0m.ts_owned B TFIB_SYMS). intros HE. rewrite Exists_exists in HE.
      destruct HE as (r0 & Hr0 & Hzr). unfold A.AF0m.Tfib_owned_static in Hr0. cbn [In] in Hr0.
      unfold Reusable.YG0n.in_zr in Hzr.
      repeat (destruct Hr0 as [Hr0 | Hr0]; [subst r0; cbn [fst snd] in Hzr; lia |]). destruct Hr0. }
    assert (Herr : ~ (Reusable.YG0f.as_errno B <= rr + Z.of_nat kk < Reusable.YG0f.as_errno B + 4)).
    { rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO. lia. }
    assert (Hsp : Reusable.YCbq.fp_spares (SK := A.AE2k.tfib_sink_head) ([] : list (Z * Z)) (rr + Z.of_nat kk)).
    { apply Reusable.YCbq.fp_spares_closed. intros (r0 & Hr0 & _). destruct Hr0. }
    pose proof (HimgK (rr + Z.of_nat kk) Hin3 Hown Herr Hsp) as Ejrn.
    destruct RELRO_CAT as (Hrlo & Hrhi).
    unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in Hrlo, Hrhi.
    assert (Hrel : RLO <= rr + Z.of_nat kk < RHI) by lia.
    pose proof (HROent (rr + Z.of_nat kk) (or_intror Hrel) Hown Herr) as Erom.
    rewrite Erom in Ejrn. clear Erom.
    rewrite (f34_aview_vis_mrd W3 mem3 (rr + Z.of_nat kk)
               ltac:(apply (proj2 (proj2 VIMG)); unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia))
      in Ejrn.
    pose proof (f34_opt_inj _ _ Ejrn) as Ebyte.
    unfold LMem.wa. rewrite Ebyte.
    exact (A.Prog.Seg.F34.f34_img_nth 296 rr (A.Prog.SlotModel.rowb (Z.of_nat i)) kk Himg ltac:(lia)). }
  (* the catalogue's coverage as CtrlRo.in_zs, named by VALUE and not by position: some row of B's zero-shadow list
     (as_zero_shadow B = Tfib_zero_shadow under TFIB_SYMS) covers [CAT, CAT + 11 * 296), found by a boolean search
     over the list (KNOWN STAND-IN DEPENDENCE, see the header) *)
  assert (Hzs : A.Prog.CtrlRo.in_zs B rr 296).
  { assert (EZ : existsb (fun r0 : Z * Z => (fst r0 <=? 649216) && (649216 + 3256 <=? fst r0 + snd r0))
                   A.AF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
    apply existsb_exists in EZ as ([q mz] & Hq & Hb). cbn [fst snd] in Hb.
    apply andb_true_iff in Hb as (Hb1 & Hb2). apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
    exists q, mz. split; [rewrite (A.AF0m.ts_zsh B TFIB_SYMS); exact Hq | lia]. }
  (* the row's addressability: CtrlRo.ro_usable (the zero-shadow law at that row) read through mrd *)
  assert (Hraddr : A.AsanRT.addressable mem3 rr 296).
  { pose proof (A.Prog.CtrlRo.ro_usable segs B LAWS ly3 S3 W3 mem3 md3 rr 296 HAR Hzs) as HU.
    split; [lia|]. split; [lia|]. split; [unfold A.AsanRT.APPMEM_END; lia|].
    intros kk Hkk. split.
    - unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END. left. lia.
    - destruct (HU (rr + kk) ltac:(lia)) as (sv & Hsv & Hsok).
      replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (rr + kk)) with (A.AsanRT.shadow_addr (rr + kk))
        in Hsv by (unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr,
                     A.AsanRT.ASAN_K; lia).
      exists (Z_to_bv 8 sv). split; [exact (f34_mrd_of_aview_some W3 mem3 _ sv Hsv)|].
      unfold Reusable.YG0v.saddr_ok in Hsok. unfold A.AsanRT.shadow_ok.
      destruct Hsok as [-> | (Ho1 & Ho2)]; [left; reflexivity|].
      assert (Hs7 : sv = 1 \/ sv = 2 \/ sv = 3 \/ sv = 4 \/ sv = 5 \/ sv = 6 \/ sv = 7)
        by (pose proof (Z.mod_pos_bound (rr + kk) 8 ltac:(lia)); lia).
      assert (Esg : bv_signed (Z_to_bv 8 sv) = sv)
        by (destruct Hs7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity).
      rewrite Esg. right. lia. }
  (* ---- G2e: the slot ---- *)
  unfold ACtlCutP.FRAME_BYTES in Hstkfr.
  pose proof (A.Prog.Seg.F34.f34_sub_stk mem3 fr (fr + 3136) (fr + 64) (fr + 96) Hstkfr
                ltac:(lia) ltac:(lia) ltac:(lia)) as Hslotstk.
  destruct (A.Prog.Seg.F34.f34_rw_of_stk mem3 (fr + 64) (fr + 96) Hslotstk ltac:(lia)) as (ob & Hoblen & Hob).
  (* ---- G2f: the footprint at RNG_W (w_H W3) ---- *)
  assert (V8 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (ACtlCutP.Sfr fr + 8) 4).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as ((Hv & _) & _).
    rewrite f34_sa_eq in Hv. unfold ACtlCutP.Sfr in Ha.
    replace (A.AsanRT.shadow_addr fr + (a - ACtlCutP.Sfr fr)) with a in Hv by (unfold ACtlCutP.Sfr; lia).
    exact Hv. }
  assert (VW : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 2304) 2304).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - 2304) 2304 HAR
              ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as [Hc | VWS]; [lia|].
  assert (VR : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) rr 296).
  { apply (A.ProgBridge.range_visible_sub _ _ _ _ _ VIMG);
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  (* the row's 8-aligned shadow words: CtrlRo.ro_hull under IMG_SHADOW_VIS (every shadow byte of the image's read
     range is mapped); the zero-shadow row alone does not reach them on the record AF0m (see the header) *)
  assert (VRS : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) ((rr / 8 + A.AsanRT.ASAN_K) / 8 * 8)
                  (((rr + 295) / 8 + A.AsanRT.ASAN_K) / 8 * 8 + 8 - (rr / 8 + A.AsanRT.ASAN_K) / 8 * 8)).
  { pose proof (A.Prog.CtrlRo.ro_hull segs B ly3 S3 W3 mem3 md3 rr 296 IMG_SHADOW_VIS HAR ltac:(lia)
                  ltac:(unfold A.Prog.CtrlRo.IMG_LO; lia) ltac:(unfold A.Prog.CtrlRo.IMG_HI; lia)) as HH.
    unfold Reusable.YG0d.shadow_hull_vis in HH.
    split; [unfold A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
    split; [unfold A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia|].
    intros s Hs. apply (A.ProgWorldVisFrame.vis_of_aview segs W3 mem3). apply HH.
    rewrite !f34_sa_eq. unfold A.AsanRT.shadow_addr. replace (rr + 296 - 1) with (rr + 295) by lia. lia. }
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 64) 32 HAR Hin6
              ltac:(rewrite Efa; lia) ltac:(rewrite Efa, E4096; lia)) as (VO & VOSH).
  destruct (VOSH ltac:(lia) ltac:(rewrite Efa; Z.div_mod_to_equations; lia)
              ltac:(rewrite Efa, E4096; Z.div_mod_to_equations; lia)) as [Hc | VOS]; [lia|].
  unfold A.Prog.rng_asan.sh_al8_hi in VOS. replace (fr + 64 + 32 - 1) with (fr + 64 + 31) in VOS by lia.
  (* route (C): the run's region f34_evt_F_shadow_R rr (fr + 64) = DECLc.declaration_of_shadow_R rr (fr + 64), the
     union below (declaration_of_c.v): the row's aligned shadow words at rr + 24 (32 bytes) and rr + 254 (11 bytes)
     are image shadow; the slot's aligned shadow words lie in the owned frame's shadow *)
  assert (HRcov : forall a,
            A.Prog.sh_word_on.sh_word_on (rr + 24) 32 a \/ A.Prog.sh_word_on.sh_word_on (rr + 254) 11 a \/
            A.Prog.sh_word_on.sh_word_on (fr + 64) 32 a ->
            A.ACtlRtC.cut_shadow B ly3 S3 a \/ A.ACtlRtC.img_shadow a).
  { intros a [Ha | [Ha | Ha]].
    - right. apply (f34_img_word (rr + 24) 32 a);
        [unfold A.Prog.CtrlRo.IMG_LO; lia | unfold A.Prog.CtrlRo.IMG_HI; lia | exact Ha].
    - right. apply (f34_img_word (rr + 254) 11 a);
        [unfold A.Prog.CtrlRo.IMG_LO; lia | unfold A.Prog.CtrlRo.IMG_HI; lia | exact Ha].
    - left. apply HcutF. exact (f34_slot_word fr a ltac:(lia) Hfr32 Ha). }
  (* ---- G2g: the run, at S := Sfr fr, r := rr, o := fr + 64, spv := sp, lo := sp - 2304 ---- *)
  pose proof (A.Prog.Seg.F34F.f34_evt_F_on A.Prog.declaration_ofF.declaration_of_F_holds_on_closed
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 1) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 3) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 4)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 5) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 6)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 7) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 8)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 9) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 10)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 11) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 12)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 13) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 14)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 15) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 16)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 17) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 18)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 19) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 20)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 21) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 22)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 23) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 24)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 25) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 26)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 27) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 28)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 29) (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 30)
    (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 31)
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
    mem3 (ACtlCutP.Sfr fr) rr (fr + 64) sp (sp - 2304) (A.Prog.SlotModel.rowb (Z.of_nat i)) ob
    (* registers: sp, s3, s4, s9 *)
    R2 R19 R20 R25
    (* the four shadow stores *)
    ltac:(unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; clear - Hfrlo; Z.div_mod_to_equations; lia)
    ltac:(lia)
    (fun kk Hkk => proj1 (Hcut (ACtlCutP.Sfr fr + 8 + kk) (HcutF (ACtlCutP.Sfr fr + 8 + kk) ltac:(lia))
                     ltac:(replace (ACtlCutP.Sfr fr + 8 + kk) with (ACtlCutP.Sfr fr + (8 + kk)) by lia;
                           apply HinSh; lia)))
    (fun kk Hkk => ltac:(replace (ACtlCutP.Sfr fr + 8 + kk) with (ACtlCutP.Sfr fr + (8 + kk)) by lia;
                         apply HinSh; lia))
    (* the slot *)
    ltac:(lia) ltac:(unfold A.AsanRT.APPMEM_END; lia)
    (fun kk Hkk => HFAPP (fr + 64 + kk) ltac:(lia)) (HFAPP (fr + 64 + 32) ltac:(lia))
    (fun kk Hkk => ltac:(unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr; clear - Efr8 Hkk; Z.div_mod_to_equations; lia))
    Hob Hoblen
    (* the row *)
    ltac:(lia) ltac:(lia)
    ltac:(rewrite Err; replace (649216 + 296 * Z.of_nat i) with ((81152 + 37 * Z.of_nat i) * 8) by lia;
          apply Z.mod_mul; lia)
    Hrlen Hok Hrow Hraddr
    (* the window *)
    ltac:(split; [lia|]; split; [lia|]; intros a Ha;
          destruct (Hwin a ltac:(lia)) as (_ & bb & Hbb);
          split; [exact (f34_wview_some mem3 (LMem.wa a) bb Hbb)
                 | exists bb; unfold LMem.mrd, LMem.wa; rewrite Hbb; reflexivity])
    ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia) ltac:(lia) ltac:(unfold A.AsanRT.APPMEM_END; lia)
    ltac:(left; lia) ltac:(unfold A.AsanRT.RT_HI; lia) ltac:(lia)
    (* ctl_rt_C: ro_agree, asan_cells, and the callee's region inside cut_shadow \/ img_shadow *)
    HROrt HAC (Hsw_on (A.Prog.Seg.F34F.f34_evt_F_shadow_R rr (fr + 64)) (fun a Ha => HRcov a Ha))
    (* the footprint *)
    (A.ProgBridge.rng_of_visible _ _ _ V8)
    (A.ProgBridge.rng_bytes_RNG_W _)
    (A.ProgBridge.rng_of_visible _ _ _ VIMG)
    (A.ProgBridge.rng_of_visible _ _ _ VW)
    (or_intror (A.ProgBridge.rng_of_visible _ _ _ VWS))
    (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.rt_vis_W W3))
    (A.ProgBridge.rng_of_visible _ _ _ VR)
    (A.ProgBridge.rng_of_visible _ _ _ VRS)
    (A.ProgBridge.rng_of_visible _ _ _ VO)
    (A.ProgBridge.rng_of_visible _ _ _ VOS)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  (* ---- G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8286c_at [Z.of_nat j; Z.of_nat i])) with 0x8286c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8286c)
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* ---- G4: the lift (the run writes memory: SRr_fevt_hid) ---- *)
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Ems & MU & WM & RO' & SW' & ST' & BA' & AD' & HPR).
  subst ms'.
  change (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
  replace (fr + 64 + 32) with (fr + 96) in MU by lia.
  replace (fr + 64 + 32) with (fr + 96) in HPR by lia.
  set (WS := [(ACtlCutP.Sfr fr + 8, ACtlCutP.Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)]) in MU, HPR.
  (* ---- G5: the end state MS R .. 0x82888 .. m': the exit cut C_A82888_at [j; i] there ---- *)
  match goal with |- context [LMSt.MS ?R0 _ _ _ _ _ _] => set (R := R0) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82888_at [Z.of_nat j; Z.of_nat i])) R m' md')
            (POST cx)).
  assert (E2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19)
    by (unfold ACtlCut.rgv in R19; rewrite R19; reflexivity).
  assert (E21 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E24 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 24 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E25 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25)
    by (unfold ACtlCut.rgv in R25; rewrite R25; reflexivity).
  assert (E26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (K20 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 20 = Z_to_bv 64 rr) by reflexivity.
  assert (K10 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 1) by reflexivity.
  (* what the write set misses: an app byte outside the slot and the window, the shadow of an app byte outside
     the slot (Seg/F34.v f34_sh_outW) *)
  assert (Hout_app : forall x, A.AsanRT.app_mem x -> ~ (fr + 64 <= x < fr + 96) -> ~ (sp - 2304 <= x < sp) ->
            LFrm.outside WS x).
  { intros x Hx H1 H2. unfold WS. cbn [LFrm.outside].
    split; [|split; [exact H2 | split; [exact H1 | exact I]]].
    intros Hc. apply (A.AsanRTFacts.app_not_shadow x Hx).
    replace x with (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) by lia. apply HinSh. lia. }
  assert (Hout_sh : forall y, A.AsanRT.app_mem y -> ~ (fr + 64 <= y < fr + 96) ->
            LFrm.outside WS (A.AsanRT.shadow_addr y)).
  { intros y Hy Hn. unfold WS.
    exact (A.Prog.Seg.F34.f34_sh_outW fr sp y ltac:(lia) Hfr8 ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia)
             (fun y0 Hy0 => HFAPP y0 ltac:(lia)) Hy Hn). }
  assert (Hout_hi : forall q, ~ LFrm.outside WS q -> 0x5fe000 <= q).
  { intros q Hq. destruct (Z_lt_le_dec q 0x5fe000) as [Hl|Hl]; [|exact Hl]. exfalso. apply Hq.
    unfold WS. cbn [LFrm.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (Hslot_in : forall x, fr + 64 <= x < fr + 96 -> ~ LFrm.outside WS x).
  { intros x Hx Ho. unfold WS in Ho. cbn [LFrm.outside] in Ho. destruct Ho as (_ & _ & Hc & _). lia. }
  (* the bundles' ranges *)
  assert (Hsp_out : forall x, Ab <= x < Ab + 416 -> LFrm.outside WS x).
  { intros x Hx. apply Hout_app; [|lia|lia].
    unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. right. lia. }
  assert (Hfr_out : forall x, fr <= x < fr + 4096 -> ~ (fr + 64 <= x < fr + 96) -> LFrm.outside WS x).
  { intros x Hx Hn. apply Hout_app; [apply HFAPP; lia | exact Hn | lia]. }
  assert (Hfrsh_out : forall x, fr <= x < fr + 4096 -> ~ (fr + 64 <= x < fr + 96) ->
            LFrm.outside WS (A.AsanRT.shadow_addr x)).
  { intros x Hx Hn. apply Hout_sh; [apply HFAPP; lia | exact Hn]. }
  (* the transported bundles *)
  assert (HFLSI' : ACtlCutP.FLSI cx j fr R m').
  { apply (f34_flsi_keep cx j fr regs3 R mem3 m' WS Ab R9 ltac:(lia) ltac:(lia) E9 MU Hsp_out).
    - apply (A.Prog.Seg.F34.f34_addr_keepW WS mem3 m' _ _ Had2624 MU). intros kk Hkk. apply Hfrsh_out; lia.
    - unfold ACtlCutP.FRAME_BYTES.
      apply (f34_stk_keep WS mem3 m' fr (fr + 3136) MU WM); [|exact Hstkfr].
      intros x Hx. destruct (Z_le_gt_dec (fr + 64) x) as [H1|H1];
        [destruct (Z_lt_ge_dec x (fr + 96)) as [H2|H2]|].
      + right. apply (HPR x ltac:(lia)). apply Hslot_in. lia.
      + left. apply Hfr_out; lia.
      + left. apply Hfr_out; lia.
    - apply (A.Prog.Seg.F34.f34_addr_keepW WS mem3 m' _ _ Had2691 MU). intros kk Hkk. apply Hfrsh_out; lia.
    - apply (f34_f1in_keep cx WS mem3 m' MU HLEN); [|exact HIN].
      intros x Hx. destruct (HCP x Hx) as (Hxa & Hxf & Hxc).
      split; [apply Hout_app; [exact Hxa | lia | lia] | apply Hout_sh; [exact Hxa | lia]].
    - apply (A.Prog.Seg.F34.f34_addr_keepW WS mem3 m' _ _ Hadfg MU). intros kk Hkk.
      unfold ACtlCutP.fragb. apply Hfrsh_out; lia.
    - apply (A.Prog.Seg.F34.f34_addr_keepW WS mem3 m' _ _ Hadrec MU). intros kk Hkk. apply Hfrsh_out; lia.
    - exact HFLSI. }
  apply (HX cx [Z.of_nat j; Z.of_nat i] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: the write set is the owned frame's shadow, the window and the owned frame (ajournal_exec) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (ACtlCutP.Sfr fr + 8 <= a < ACtlCutP.Sfr fr + 12) \/ (sp - 2304 <= a < sp) \/
                           (fr + 64 <= a < fr + 96)).
    + exact HJ.
    + intros x Hx. cbv beta in Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. unfold WS. cbn [LFrm.outside].
      split; [intros Hc; apply Hx; left; exact Hc|].
      split; [intros Hc; apply Hx; right; left; exact Hc|].
      split; [intros Hc; apply Hx; right; right; exact Hc | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      destruct (A.Prog.Seg.F34.f34_outside_dec WS (bv_unsigned x)) as [Ho|Ho].
      * rewrite (MU x Ho). exact Hx.
      * destruct (HPR (bv_unsigned x) Rx Ho) as (bb & Hbb).
        unfold LMem.wa in Hbb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hbb.
        exact (f34_mrd_high m' x bb (Hout_hi _ Ho) Hbb).
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. cbv beta in Ha. unfold Reusable.YCbq.awr_byte.
      destruct Ha as [Ha | [Ha | Ha]].
      * right. right. right. unfold Reusable.YCbq.in_frames. exists 6, (ACtlCut.c_fpos cx).
        split; [left; reflexivity|]. right.
        rewrite Efa, E4096, f34_sa_eq. unfold Reusable.YG0n.in_zr. cbn [fst snd].
        change (4096 / 8) with 512. unfold ACtlCutP.Sfr in Ha. lia.
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * right. right. right. unfold Reusable.YCbq.in_frames. exists 6, (ACtlCut.c_fpos cx).
        split; [left; reflexivity|]. left.
        rewrite Efa, E4096. unfold Reusable.YG0n.in_zr. cbn [fst snd]. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A82888_at [j; i] (ACtlCutP.v:2805-2819) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82888_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite !Nat2Z.id.
    exists phi.
    split; [exact Hperm|].
    split.
    { (* FRAC: memory across the write set, then the registers along the run's map *)
      assert (Hsh' : exists sh, LMem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\
                       length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
      { assert (Hstksh : LFrm.stk A.Img0.rsegs m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
        { (* the frame's shadow at m': cut_shadow's (F) region, carried across the run by its post *)
          split; [lia|]. split; [lia|]. intros a Ha.
          replace a with (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) by lia.
          exact (SW' _ Hcut (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr))
                   (HcutF (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) ltac:(lia))
                   (HinSh (a - ACtlCutP.Sfr fr) ltac:(lia))). }
        destruct (LFrm.stk_bytes A.Img0.rsegs m' _ _ Hstksh ltac:(lia)) as (sh' & Hl' & Hb').
        exists sh'. split; [exact Hb'|]. rewrite Hl'.
        replace (ACtlCutP.Sfr fr + 392 - ACtlCutP.Sfr fr) with 392 by lia. reflexivity. }
      pose proof (f34_frac_keep B cx fr fr regs3 WS mem3 m' MU Hfr_out
                    ltac:(intros x Hx; rewrite HspZ in Hx; apply Hout_app; [| lia | lia];
                          unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END; right; lia)
                    Hsh' HFRAC) as HFRAC'.
      exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m' HFRAC' E2 E3 E4 E8 E9 E19 E26). }
    split; [exact Hcn|]. split; [exact Hj|].
    split.
    { apply (f34_hb_keep WS mem3 m' phi _ MU); [|exact HHB].
      intros x Hx. assert (Ea : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
        by (unfold A.ACtlK.a_size; lia).
      rewrite Ea in Hx. destruct (HPH x Hx) as (Hxa & Hxf & _). apply Hout_sh; [exact Hxa | lia]. }
    split; [exact HFLSI'|].
    split.
    { apply (f34_lk_keep cx fr j regs3 R mem3 m' WS E21 MU); [|exact HLK].
      intros x Hx. apply Hfr_out; lia. }
    split; [exact Hi10|].
    split.
    { unfold ACtlCutP.RL.
      split; [exact Hi10|].
      split; [unfold ACtlCut.rgv; exact K20|].
      split; [unfold ACtlCut.rgv in *; rewrite E24; exact R24|].
      split; [exact Hprev|]. split; [exact Hsel|].
      apply (f34_flsx_keep cx j phi fr regs3 R mem3 m' WS Ab R9 ltac:(lia) ltac:(lia) E9 E18 E22 E23 E25 MU
               Hsp_out); [|exact HFLSI' | exact HFLSX].
      intros x Hx. destruct (HPH x Hx) as (Hxa & Hxf & Hxc). apply Hout_app; [exact Hxa | lia | lia]. }
    split; [unfold ACtlCut.rgv; exact K10|].
    split; [exact BA'|].
    split; [exact AD'|].
    apply (f34_lt_keep cx fr j regs3 R mem3 m' WS Ab R9 ltac:(lia) ltac:(lia) E9 MU Hsp_out); [| |exact HLT].
    + intros x Hx. apply Hfr_out; lia.
    + intros x Hx. split; [apply Hfr_out | apply Hfrsh_out]; lia.
  - (* ctl_rt_C B ly3 S3 m' (ly3, S3 unchanged): asan_cells kept (WS lies above RT_HI); cut_shadow and img_shadow
       carried across the run by its post (forall P, shadow_rw_on P mem3 -> shadow_rw_on P m'); ro_agree from the
       post *)
    split; [|split; [|split]].
    + unfold A.ACtlK.asan_cells_at. apply (A.AsanRTFacts.asan_cells_kept WS mem3 m' HAC MU).
      unfold WS. cbn [LFrm.disjoint_from]. unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia | exact I].
    + exact (SW' _ Hcut).
    + exact (SW' _ HimgC).
    + exact RO'.
Qed.

End GlueF34.

Print Assumptions glue_seg_F34.
