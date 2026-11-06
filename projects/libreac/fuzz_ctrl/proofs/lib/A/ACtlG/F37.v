(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module names, addresses and numbers changed; 633 of its 661 lines of code are new or changed and 531 lines of the source are left out. *)
(* lib/A/ACtlG/F37.v -- GLUE for stage seg_F37 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   piece W4f).  Written by a Theorem Labs lane (glue owner of the B8 stretch); single writer.  rule 24: no
   function proved (stage glue of a walk: an already-proved segment run, through an already-proved bridge, to a fixed
   stage statement).

   WHAT IT PROVES
     glue_seg_F37 : forall POST (j : nat),
       CF POST (ix_cut C_A82940_at [Z.of_nat j]) -> CF POST (ix_cut C_A828d8_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F37.  The ENTRY is C_A828d8_at [j] (pc 0x828d8, own6, k <= 14+2j+1, live list entry ++ [(phi, flen cx j)]),
   the EXIT is C_A82940_at [j] (pc 0x82940 = the free's return address, own6, k <= 14+2j+2, live list = entry).
   Segment F37 (Seg/F37.v seg_F37 :787 at U 6a74d5929d2): 0x828d8 `bne a0,s4,82bf4` (not taken: t_want j =
   t_want_m j, F37.f37_want_eq), the 23 frame-shadow stores `sb s11,o(s3)` at S(fr)+22 .. S(fr)+66, `mv a0,s7`,
   `jal 0x53378` = free(phi) (the free wrapper, pc_wrap_free of the core's code, ra = 0x82940).

   THE ALLOCATOR CASE (glue-pattern.md section 9, exactly).  The run f37_evt_body ends AT the allocator entry with
   ra set; the free's return address 0x82940 IS the exit cut.  So:
   G1  unfold the entry cut (ix_cut's index equation, C_A828d8_at's body, ACtlCutP.v:2924-2935).
   G2  the run's premises: s3 = S(fr) (FRAC), a0 = s4 (the body's a0 = t_want j, s4 = t_want_m j, F37.f37_want_eq),
       the 67 frame-shadow cells present (FRAC's 392 shadow bytes) and writable (ctl_rt_C's cut_shadow conjunct,
       its (F) disjunct: the shadow of the owned class-6 frame), their bounds,
       and the footprint rng (S(fr) + 22) 45 by visibility of the owned frame's shadow (the AR frames law).
   G3  register maps: ProgBridge.cfg_at_MS, then Reusable.YA0nR.SRr_xregs_eqv to the run's canonical map
       (mkR (reg_get regs3 1) .. (reg_get regs3 31) = Regs6ss.mkR_of regs3).
   G4  lift: ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid (the run writes memory) at
       RNG_W (w_H W3); the journal crosses the run by Reusable.YCbq.ajournal_exec (write set = the 45 stored shadow
       bytes, each awr_byte as a byte of the owned class-6 frame's shadow).
   G5  the free: ONE local lemma, f37_free, applies the core's free rule through the donor's afree04_sub (the
       planning core has no Reusable.YC85; a Theorem Labs lane's PA-layer copy A.Prog.YC85.afree04_sub is on the glue base
       and is the one cited); nothing else in this file touches the allocator.  Its continuation is the exit cut at
       0x82940: journal at k + 1, frames unchanged, the live list back to the entry blocks, callee-saved registers
       kept (aregs_preserved), memory kept outside the ASTACK window and the freed block (acall_kept), every exit
       body byte fact moved by a KEPT CLASS of acall_kept read at a visible address; ctl_rt_C by ctl_rt_C_of_AR.

   SECTION 9 PREMISES OF THE FREE RULE AND WHERE EACH IS DISCHARGED (all in glue_seg_F37 / f37_free)
     journal at the call       ajournal_exec across the run (G4) from the entry cut's journal
     In (phi, n) (ablocks)     the entry body's Permutation (ablocks ly3 S3) (entry ++ [(phi, flen cx j)])
     a0 = phi                  the run's post (a0 := s7) and FLSX's s7 = phi
     sp = sp0 + o, o mod 16,   FRAC: sp mod 16 = 0, c_sp cx - 4096 < sp <= A <= c_sp cx; the journal's astk_ok:
       o <= 0, ASTACK-o<=STK   c_sp cx mod 16 = 0; 16384 + 4096 <= 32768 = LLVMF_STK
     gp / tp                   FRAC's s3 = entry s3, the entry afn_pre's gp; FRAC's tp
     ra = 0x82940, ret_ok      the run's post; ret_ok_even
     st_nev Sc < EV_MAX        the journal's st_nev S3 <= st_nev S + k, k <= 14+2j+1 <= 525, the pre's
                               st_nev S + EV_LIB <= EV_MAX
     chain_pre, trace          ACtl.v's CHAIN_OF_CUT at (pc_free_ra0, 0x82940), from the run's end journal, FRAC's
                               s0 = c_sp cx, saved bytes and spill-base window
     entry-block premise       phi is not an entry block (f37_not_entry: AR's block separation makes the live
                               list duplicate-free)
     meter                     MT_FREE (the core's own name for the trivial meter, A/AD1m.v:29)
   After the call: ctl_rt_C (route (C)) by a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR, cited by name; the exit
   body has NO HB conjunct (the block is freed), so plan Appendix B OPEN item 1 (a_size 0 = 1) does not arise at this
   site.

   THE FAKE-FRAME TRAILER WORD (Batch3, a Theorem Labs lane's glue base d36efc6152d; FRAC's last conjunct, ACtlCutP.v:997,
   `q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))`).  The entry body's FRAC is destructed
   with it named (Htrail), and the exit FRAC (HFRAC2, at the free's post memory mem2, then kit_frac_move to regs2)
   PRODUCES it: [fr + 4088, fr + 4096) is outside the run's write set [S(fr) + 22, S(fr) + 67) (KR), and the free
   keeps it by acall_kept's FRAME class (YCbq.v:831-833, `In (cid, pos) (frames Sc) -> in_zr a (frame_rng ..) ->
   ~ E a -> aview .. = aview ..`, at (6, c_fpos cx), with the freed block disjoint from the frame by
   YCbq.sep_block_frame), read at a byte visible in W3 (AR's frames law) -- the same KFR step that carries the frame
   header words, the identity / fragment / OUR bytes.

   SECTION HYPOTHESES (exact text below; source of each)
   - LAWS, TFIB_LIB, CHAIN_OF_CUT: ACtl.v's own Section hypotheses (ACtl.v Section Ctl, :210 / :226 / :478 at blob
     a3c6b7b35017), same text; ACtl.v passes its own.
   - AFREE4 : the core's free rule, Reusable.YC5d.afree04_rule segs B MT, as the donor's walk states it
     (proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v:110 at origin/ossv/recipes c8557374ad2e, `Hypothesis AFREE4 :
     afree04_rule tfibsegs B MT`); glue-pattern.md section 9: the rules are Section hypotheses of the walk.  NEW for
     ACtl.v (discharged at its section 9 by Reusable.YCbp.afree04_rule_triv and the core's afree_realizes).
   - MT_FREE : the trivial meter, the core's own hypothesis text (lib/A/AD1m.v:29 `Hypothesis MT_FREE : forall S m,
     mo_ok MT S m`); NEW for ACtl.v (discharged at section 9 by `fun _ _ => I` for Reusable.YCbp.ameter_triv).
   - TFIB_SYMS : A.AF0m.CtrlTSyms B, ACtl.v's own hypothesis (Section Ctl, ACtl.v:225 at blob a3c6b7b35017), same
     text and the same place in the order; it is ctl_rt_C_of_AR's first premise.
   - route (C): the entry cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from on a working branch shell); the
     exit's ctl_rt_C B ly2 S2 mem2 comes from a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR
     (lib/A/ProgWorldCtlRtC.v), which needs neither A.ProgWorld.AR_states_vis0_shadow nor
     A.ProgWorld.AR_states_owned_ro: the Section hypotheses VIS0 / OWNED_RO and the local ctlrt_of_AR notation are
     GONE.
   CITED BY NAME, NOT HYPOTHESES: Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt_hid (a Theorem Labs lane), A.ProgBridge.cfg_at_MS /
   fevt_of_evtF / tfibsegs_rsegs / RNG_W / fp_avoids_RNG_W / rng_of_visible (a Theorem Labs lane), the _F run
   F37F.f37_evt_body_F (this worker's, lib/A/Prog/Seg/F37F.v), A.Prog.YC85.afree04_sub (a Theorem Labs lane's PA copy of
   the donor's YC85.v:110), the core's Reusable.YCbq (ajournal_exec, frames_bounds, sep_blocks, sep_block_frame,
   range_addressable_of_block, seg_rom_none, req_size_pos, asan_consts) and Reusable.APostBase.arodata_ok_journalP,
   the kit A.ACtlG.Kit.kit_wx / kit_segs_low / kit_frac_move, Seg/F37.v's model facts f37_want_eq, f37_ID_len,
   f37_FG_len, f37_fs_body_len and its byte helpers f37_ba_sub / f37_ba_present (Seg/F37.v is in F37F.v's closure),
   and a Theorem Labs lane's A.ProgWorldCtlRtC.ctl_rt_C_of_AR.

   CLOSURE (the glue closure rule, measured with closure_scan.py sha256
   039e7d56edc33b08e7d2b05bc9c3d98593c711ff8ef313a5f33ca4d1f7592c8f, which self-tests 16 rule-3 cases on every
   run, from this file's own Requires on a Theorem Labs lane's stand-in-free glue base 29ddfc3ea99 merged: 551 unit files):
   every Require is qualified; no statement names a frame-route identifier.  The frame route IS in the closure,
   through the `_F` file (Seg/F37F.v Requires Seg/F37.v, which Requires SlotInv / AsanRTInv / Contract / FrameAPI /
   MemNorm), which closure rule 1 allows.  Rule 3 holds, measured: `closure-rule-3 files: NONE` -- no SegCF path,
   no `_cfw.v`, no `Cf_<word>.v`, no lib/AZ/AsanW, W6 only lib/A/W6/QSlot.v.  Rule 5, the v1.9
   blobs of record in the closure (on that base): SlotModel 04dc7903221, AsanRT b67d26f8ec7 (mcs 30),
   AsanRTFacts 1657e654e8c, SlotInv 4cf85db229a, AsanRTInv 2a8602e8526, Contract fa6fd478d9a, FrameAPI f6ffefa9bb4,
   MemNorm cb518fc0304, W6/QSlot 60dca47b79a, Seg/F37.v 7dd37c7d21b, Seg/F37F.v 5615dde6494.
   DOUBLED MODULES: the six that exist as both lib/Reusable/<X> and lib/A/Reusable/<X> (YI04, YI16, YK11, YK1b,
   YM05, YO09), and YK0s / YP09, are Required through the lib.Reusable prefix and named through the full-path
   aliases CK11 / CM05 / CO09 / CI16 / CP09 / CK0s (porter 04:24Z and 04:33Z).  lib/Lib is doubled the same way
   (lib/A/Bz/Lib, lib/A/Tk/UL, lib/AZ/Lib), so every lib/Lib name below is written by its FULL path
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.<X>.<n> -- the copy the cut records use (ACtlCutP.v's MEM / CEL /
   STP / FRM aliases, ACtl.v's CHAIN_OF_CUT).  MEASURED (refit-f3738, 8ee48574229): in this file's closure WITHOUT an
   alias the partial `Lib.Mem.n` / `Lib.Cells.n` / `Lib.Step.rw_cells` / `Lib.MState.MS` expand to the lib/A/Bz/Lib
   copy (`Lib.Cells.CB` to lib.A.Bz.Lib.Cells.CB, a different `cell`); the local nested `Module Lib` alias block this
   file carried until then bound all of them to lib/Lib (About: `alias of lib.Lib.X.n`), but the module gate cannot
   see a nested alias, so the names are now written out and the block is gone.  SHADOWED NAMES: getr / mkst /
   seg_rom / cfg_at only CK11.* / Reusable.YG0d.cfg_at.  `Z_to_bv_bv_unsigned` is doubled too (lib/Lib/MState.v,
   lib/A/Bz/Lib/MState.v, lib/A/Tk/UL/MState.v, ...), and its two uses below are written out.  MEASURED in this
   file's own context, not guessed: `Locate Z_to_bv_bv_unsigned` lists
   `Constant stdpp.bitvector.definitions.Z_to_bv_bv_unsigned` FIRST and `About Z_to_bv_bv_unsigned` prints
   `Expands to: Constant stdpp.bitvector.definitions.Z_to_bv_bv_unsigned` (stdpp/bitvector/definitions.v:392) --
   NEITHER MState copy.  The two uses therefore name stdpp's constant, which is the one they already cited.

   DISCHARGE CALL in ACtl.v (the Section order of glue_seg_F37 on the route (C) walk shell):
     exact (glue_seg_F37 B MT XM_LIB RLO RHI LAWS TFIB_SYMS TFIB_LIB CHAIN_OF_CUT AFREE4 MT_FREE)
   (fx / rc stay implicit, resolved by ACtl.v's own Context instances.)

   BUILD STATE: TYPE-CHECK ON INTERIM 5da74c9c931, CLOSURE REACHES NO STAND-IN.  rc=0 by cb
   on a build machine (a fresh worktree; workspace from the packed base 23b918fe0c2e) with NO port_core_refused
   substitution: on the stand-in-free glue base 29ddfc3ea99 the five planning-core files the type-check workspaces
   used to substitute (lib/A/AE2k.v, AF0m.v, AF0l.v, ACej.v, ACeh.v; this file's closure reaches all five, through
   A.ProgWorld's A.AF0m among others) carry no port_core_refused_ name and compile from their own text.  No Axiom, no
   Parameter, no Admitted, no admit.  `Print Assumptions glue_seg_F37`: Rocq primitives (PrimInt63 / PrimString /
   PrimArray) and FunctionalExtensionality.functional_extensionality_dep, nothing else. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* reg_get (the run's canonical register map, Lib/Regs6ss.v:20-21) is LPS's; the same Import line as Regs6ss.v. *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The doubled modules (YI04, YI16, YK11, YK1b, YM05, YO09, and also YK0s / YP09) are Required through the
   lib.Reusable prefix, never the partial `Reusable.X` form, which matches both copies (porter 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YI16 YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0v Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase Reusable.YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.ACeh A.AsanRT A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.YC85 A.Prog.SlotModel.
(* a Theorem Labs lane's ProgWorld (on the glue base); A.AF0m carries ACtl.v's TFIB_SYMS type (A.AF0m.CtrlTSyms), the first premise
   of a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR, cited by name. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ProgWorld.
(* route (C): the narrowed cut conjunct and its producer from AR (no VIS0 / OWNED_RO). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F37 F37F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The doubled modules this file names, by their full path (porter 04:24Z / 04:33Z). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module CP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module CK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Byte-level helpers (no Section argument). *)

(* At a byte visible in W, a view equality across a world step W -> W2 (hidden set shrinking, wle) is an mrd
   equality. *)
Lemma f37_vis_mrd : forall {fx : CK11.FPState} {rc : CM05.RunCeil}
    (W W2 : Reusable.YA0n.world segs) (m m2 : word -> option byte) (a : Z),
  Reusable.YA0n.wle W W2 -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) m2 a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a).
Proof.
  intros fx rc W W2 m m2 a Hle Hv E.
  assert (Hv2 : Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
  { destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 a)) eqn:E2; [|reflexivity].
    rewrite (Hle _ E2) in Hv. discriminate Hv. }
  pose proof (Reusable.YCbq.mbyte_of_aview segs (Reusable.YA0n.w_H W) (Reusable.YA0n.w_H W2) m m2 a E) as Em.
  unfold CP09.mbyte, Reusable.YK04.mrestrict in Em. cbv beta in Em.
  rewrite Hv, Hv2 in Em.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. exact Em.
Qed.

(* A byte list survives a memory change that keeps every byte of its range. *)
Lemma f37_ba_keep : forall (m m' : word -> option byte) a (bs : list byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. etransitivity; [apply K; lia | exact (H i Hi)].
Qed.

Lemma f37_le8_len : forall v : word, length (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 v) = 8%nat.
Proof. intros v. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8. apply length_Z_to_le_bytes. Qed.

Lemma f37_q64_keep : forall (m m' : word -> option byte) a v,
  ACtlCutP.q64 m a v ->
  (forall x, a <= x < a + 8 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)) ->
  ACtlCutP.q64 m' a v.
Proof.
  intros m m' a v H K. unfold ACtlCutP.q64 in *. apply (f37_ba_keep m m' a _ H).
  rewrite f37_le8_len. exact K.
Qed.

(* A spill read through register 9 is the spill at the known spill base A (the base is below 2^63, the offset
   small, so the two representatives mod 2^64 agree). *)
Lemma f37_spill_at : forall {fx : CK11.FPState} (regs : bvmap 5 word) (m : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros fx regs m A off v HA HAr Hoff (A' & HA' & Hq).
  assert (E : A' = A).
  { unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
    apply (f_equal bv_unsigned) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
    change (bv_modulus 64) with (2 ^ 64) in HA'.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite f37_le8_len in Hq1. cbn [Z.of_nat Pos.of_succ_nat] in Hq1.
    rewrite (Z.mod_small A) in HA' by lia.
    assert (Hr : -2 ^ 62 < A' < 2 ^ 64) by lia.
    Z.div_mod_to_equations. nia. }
  subst A'. exact Hq.
Qed.

Lemma f37_spill_keep : forall {fx : CK11.FPState} (regs regs' : bvmap 5 word) (m m' : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> ACtlCut.rgv regs' 9 A -> 0 <= A < 2 ^ 63 -> 0 <= off < 2 ^ 62 ->
  ACtlCutP.spill regs m off v ->
  (forall x, A + off <= x < A + off + 8 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros fx regs regs' m m' A off v HA HA' HAr Hoff Hs K.
  exists A. split; [exact HA'|].
  exact (f37_q64_keep m m' (A + off) v (f37_spill_at regs m A off v HA HAr Hoff Hs) K).
Qed.

(* addressable reads only the shadow bytes of its range. *)
Lemma f37_addr_keep : forall (m m' : word -> option byte) p n,
  A.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) K. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [|exact Hok]. etransitivity; [exact (K i Hi) | exact Hb].
Qed.

(* A small unsigned byte is its signed value. *)
Lemma f37_signed_small : forall b : byte, 0 <= bv_unsigned b < 8 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A pairwise-disjoint live list with nonnegative sizes has no duplicate. *)
Lemma f37_pw_nodup : forall l : list (Z * Z),
  (forall b, List.In b l -> 0 <= snd b) ->
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint (map (fun b => (fst b, Reusable.YG00.req_size (snd b))) l) ->
  List.NoDup l.
Proof.
  induction l as [|x t IH]; intros Hn Hp; [constructor|].
  cbn [map Reusable.YG0f.pairwise] in Hp. destruct Hp as (Hf & Hp).
  constructor.
  - intros Hin.
    pose proof (proj1 (List.Forall_forall _ _) Hf _
                  (List.in_map (fun b => (fst b, Reusable.YG00.req_size (snd b))) t x Hin)) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (Reusable.YCbq.req_size_pos (snd x) (Hn x (or_introl eq_refl))) as (Hr & _). lia.
  - apply IH; [intros b Hb; apply Hn; right; exact Hb | exact Hp].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The stage. *)
Section GlueF37.

(* ACtl.v's Section shape (Section Ctl), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).
Local Notation C_A82940_at := (ACtlCutP.C_A82940_at B).
(* The walk's journal at an own6 cut (ACtlCut.v ctl_from's second premise with own := own6, FP := []). *)
Local Notation AJ cx ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k).
Local Notation ENTRYBL cx := (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)).

(* ---- Section hypotheses (sources in the header) ---- *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* ACtl.v's own TFIB_SYMS (Section Ctl, ACtl.v:225), ctl_rt_C_of_AR's first premise; same text, same place in the
   order. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k
    (regsT : bvmap 5 word) (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  CK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  CK11.getr regsT 1 = Z_to_bv 64 ra ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 27) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 26) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 25) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 24) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 23) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 22) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 21) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 20) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 19) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 18) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 9) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (CK11.getr (ACtlCut.c_regs cx) 8) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.
(* The core's free rule (donor A/ACfj.v:110). *)
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
(* The trivial meter (the core's text, A/AD1m.v:29). *)
Hypothesis MT_FREE : forall S m, Reusable.YC5d.mo_ok MT S m.
(* route (C): VIS0 / OWNED_RO (A.ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) and the local ctlrt_of_AR
   notation are GONE: the exit's ctl_rt_C comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* ---------------------------------------------------------------------------------------------------------
   The allocator site 0x8293c (free(phi), return 0x82940): the ONE local lemma of this file that touches the
   allocator.  The core's free rule through the donor's afree04_sub (A.Prog.YC85.afree04_sub, Section g with LAWS
   and segs_low), its continuation handed to the caller. *)
Lemma f37_free : forall (cx : ACtlCut.ctlcx) (n phi : Z) ly3 S3 W3 (regsT : bvmap 5 word) memT md3 k (o : Z) ch
    (Q : Reusable.YA0n.world segs -> config -> Prop),
  AJ cx ly3 S3 W3 memT md3 k ->
  In (phi, n) (Reusable.YG0d.ablocks B ly3 S3) -> ~ In (phi, n) (ENTRYBL cx) ->
  CK11.getr regsT 10 = Z_to_bv 64 phi ->
  Reusable.YG0d.spZ regsT = ACtlCut.c_sp cx + o -> o mod 16 = 0 -> o <= 0 ->
  Reusable.YG0d.ASTACK - o <= A.ACfn.LLVMF_STK ->
  CK11.getr regsT 3 = Z_to_bv 64 (Reusable.YG0f.as_gp B) ->
  CK11.getr regsT 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) ->
  CK11.getr regsT 1 = Z_to_bv 64 0x82940 ->
  Reusable.YG00.st_nev S3 < Reusable.YG00.EV_MAX ->
  ACtlCut.ctl_chain ly3 W3 memT regsT ch ->
  ACtlCut.ctl_trace_in B (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) regsT ch ->
  (forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     Reusable.YA0n.wle W3 W2 ->
     AJ cx ly2 S2 W2 mem2 md2 (k + 1) ->
     Reusable.YG0d.aregs_preserved regsT regs2 ->
     (exists l1 l2, Reusable.YG0d.ablocks B ly3 S3 = l1 ++ (phi, n) :: l2 /\
                    Reusable.YG0d.ablocks B ly2 S2 = l1 ++ l2) ->
     Reusable.YG01.frames S2 = Reusable.YG01.frames S3 ->
     Reusable.YCbq.acall_kept segs B ly3 S3 W3 memT W2 mem2
       (ACtlCut.c_sp cx + o - Reusable.YG0d.ASTACK) (ACtlCut.c_sp cx + o)
       (fun a => phi <= a < phi + Reusable.YG00.req_size n) ->
     Reusable.YA0n.SRr segs W2 (Reusable.YG0d.cfg_at segs 0x82940 regs2 mem2 md2) Q) ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 regsT memT md3) Q.
Proof.
  intros cx n phi ly3 S3 W3 regsT memT md3 k o ch Q HJ Hin Hnot Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hnev Hch Htr HK.
  assert (Epc : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code B) = 0x53378)
    by (rewrite (A.ACeh.tl_code B TFIB_LIB); reflexivity).
  assert (Hret : CK0s.ret_ok (Z_to_bv 64 0x82940))
    by (apply CK0s.ret_ok_even; reflexivity).
  change (Reusable.YA0n.SRr segs W3
            (mkCfg (CK11.mkst regsT (Z_to_bv 64 0x53378) memT (CK11.seg_rom segs)) md3) Q).
  rewrite <- Epc.
  eapply Reusable.YA0n.SRr_bind.
  - exact (A.Prog.YC85.afree04_sub (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low MT AFREE4
             W3 regsT memT A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
             (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md3 k phi n o
             (Z_to_bv 64 0x82940) ch HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hret Hnev Hch Htr
             (fun Hi => False_ind _ (Hnot Hi)) (MT_FREE S3 (Reusable.YC5d.mo_free MT))).
  - intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hpres & Hsplit & Hfr2 & Hkept & _ & _).
    exact (HK W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpres Hsplit Hfr2 Hkept).
Qed.

(* phi, the block the frame turn allocated, is not an entry block: AR's block separation makes the live list
   duplicate-free, and the cut lists it as entry ++ [(phi, n)]. *)
Lemma f37_not_entry : forall (cx : ACtlCut.ctlcx) ly3 S3 W3 mem3 md3 phi n,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (ENTRYBL cx ++ [(phi, n)]) ->
  ~ List.In (phi, n) (ENTRYBL cx).
Proof.
  intros cx ly3 S3 W3 mem3 md3 phi n HAR Hperm Hin.
  assert (HND : List.NoDup (Reusable.YG0d.ablocks B ly3 S3)).
  { apply f37_pw_nodup.
    - intros [p m] Hb. cbn [snd].
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
      lia.
    - destruct (Reusable.YG0d.al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as [Hp _].
      apply (proj1 (Reusable.YCbq.pairwise_app_l _ _ _ Hp)). }
  pose proof (Permutation_NoDup Hperm HND) as HND2.
  rewrite <- (app_nil_r (ENTRYBL cx)) in Hin.
  exact (List.NoDup_remove_2 (ENTRYBL cx) [] (phi, n) HND2 Hin).
Qed.

(* The two transport steps of the exit body, used only in glue_seg_F37 below: a spill through register 9 and an
   addressable range read through its shadow bytes (a byte list is f37_ba_keep, applied directly). *)
Ltac f37_sp R9a R9b HA64 KS :=
  eapply (f37_spill_keep _ _ _ _ _ _ _ R9a R9b HA64);
    [ | eassumption | intros ?x ?Hx; apply KS; lia ]; lia.
Ltac f37_ad KFS :=
  eapply f37_addr_keep; [eassumption | intros ?i ?Hi; apply KFS; try unfold ACtlCutP.fragb; lia].

Lemma glue_seg_F37 : forall POST (j : nat),
  CF POST (ix_cut C_A82940_at [Z.of_nat j]) -> CF POST (ix_cut C_A828d8_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut C_A828d8_at at index [j] (ACtlCutP.v:2924-2935) ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828d8_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hn & Hj & _ & HFLSI & HLK & HFLSX & H20 & H10 & HLT).
  change (k <= 14 + 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat j]) + 1) in Hk.
  unfold ACtlCutP.ixn in Hk. cbn [nth] in Hk. rewrite Nat2Z.id in Hk.
  change (Reusable.YG01.frames S3 = [(6, ACtlCut.c_fpos cx)]) in HF.
  change (forall cid pos, In (cid, pos) [(6, ACtlCut.c_fpos cx)] ->
            fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) in HL.
  change (AJ cx ly3 S3 W3 mem3 md3 k) in HJ.
  (* the entry facts: the core's pre (ctl_base), the journal, FRAC and the body bundles *)
  pose proof HB as ((Hafn & _ & _ & _ & Hpn & Hlen & _ & _ & Hnev0 & _ & Hros & _) & _).
  pose proof Hafn as (_ & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (Hsp0al & _ & Hceil & Hstklo & _).
  pose proof HFRAC as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416 & Hsp4096 & HSapp & Q304 & Q24 & Q16 & Qhdr & Qent & Hsh & Hsaved & Htrail).
  pose proof HFLSX as (_ & R18 & R22 & R23 & R25 & H50 & S152 & S280).
  pose proof HLK as (_ & R21 & HOUR).
  pose proof HFLSI as (HFLSH & S216 & S224 & S248 & HF1IN & HFLC).
  pose proof HFLSH as (HPRO & S128 & Hstk & S144 & HA2691).
  pose proof HPRO as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248b & HA2624 & HBin & HAinP & S184 & S256 &
    S264 & S272 & S32).
  pose proof HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & HAfg & HA2688 & C72 & C64 & C56 & C48).
  pose proof HF1IN as (HAin & HBin').
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FSj,
    ACtlCutP.FSb in HLT.
  destruct HLT as ((HIDB & Hidok) & (HFGB & Hfgok) & (S104 & S112 & HFSB & HA2880 & HFI)).
  pose proof HfrA as HfrA'. unfold ACtlCutP.FRAME_BYTES in HfrA'.
  pose proof HSapp as HSapp'. unfold A.AsanRT.APPMEM_END in HSapp'.
  pose proof Hstklo as Hstklo'. unfold A.ACfn.LLVMF_STK in Hstklo'.
  (* constants and the frame *)
  pose proof Reusable.YCbq.asan_consts as (C1 & _ & _ & _ & _).
  assert (Hfb6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite ?Efr3, ?Hfb6 in Hf4096, Hfceil, Hfapp.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfrb & Hfrsh).
  rewrite ?Efr3, ?Hfb6 in Hfrb, Hfrsh.
  replace (4096 / 8) with 512 in Hfrsh by reflexivity.
  assert (ESh : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr).
  { unfold Reusable.YG0f.shadow_addr, ACtlCutP.Sfr, A.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF,
      A.AsanRT.ASAN_K. lia. }
  rewrite ESh in Hfrsh.
  assert (HSfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  (* the owned frame lies in low or high application memory, so its shadow is in the matching shadow band *)
  assert (Hfrapp : 4096 <= fr /\ (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/
                    (Reusable.YG0f.kHighMemBeg <= fr /\ fr + 4096 <= CM05.alloc_ceiling))).
  { unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL in Hfapp. exact Hfapp. }
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfrapp.
  assert (HS0 : 0x7fff8000 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= 0x10007fff8000).
  { rewrite HSfr. clear - Hfrapp C1 Hfr8. Z.div_mod_to_equations. lia. }
  assert (Hshb : forall i, 0 <= i < 512 -> A.AsanRT.in_shadow (ACtlCutP.Sfr fr + i)).
  { intros i Hi. rewrite HSfr. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
      A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG.
    clear - Hfrapp C1 Hfr8 Hi. Z.div_mod_to_equations. lia. }
  (* ---- G2: the run's premises ---- *)
  destruct Hsh as (sh & Hshb0 & Hshl).
  unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hshl. cbn in Hshl.
  pose proof (F37.f37_ba_sub mem3 (ACtlCutP.Sfr fr) sh 0 67 Hshb0 ltac:(lia)) as Hbs.
  cbn [skipn Z.of_nat] in Hbs. rewrite Z.add_0_r in Hbs.
  set (bs := firstn 67 sh) in Hbs.
  assert (Hbsl : length bs = 67%nat) by (unfold bs; rewrite length_firstn; lia).
  pose proof Hrt as (_ & Hcut & _ & _).
  assert (HRW : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (ACtlCutP.Sfr fr) [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.CB 67 bs]).
  { split.
    - split; [split; [exact Hbsl | exact I] |]. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_bytes OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cbytes]. rewrite app_nil_r.
      exact Hbs.
    - cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_size OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.csize]. split; [lia|]. split; [lia|].
      intros i Hi.
      (* route (C): the shadow of the owned class-6 frame is in cut_shadow's (F) disjunct *)
      assert (HFi : A.ACtlRtC.cut_shadow B ly3 S3 (ACtlCutP.Sfr fr + i)).
      { left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
        rewrite Efr3, ESh, Hfb6. replace (4096 / 8) with 512 by reflexivity. lia. }
      exact (proj1 (Hcut (ACtlCutP.Sfr fr + i) HFi (Hshb i ltac:(lia)))). }
  assert (H1020 : reg_get regs3 10 = reg_get regs3 20).
  { change (CK11.getr regs3 10 = CK11.getr regs3 20). unfold ACtlCut.rgv in H10, H20.
    rewrite H10, H20, F37.f37_want_eq. reflexivity. }
  assert (Hvis : forall a, ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 22 + 45 ->
                   Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hfrsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as ((Hv & _) & _).
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hv by lia. exact Hv. }
  assert (RV : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (ACtlCutP.Sfr fr + 22) 45).
  { unfold A.ProgBridge.range_visible. split; [lia|]. split; [lia|]. exact Hvis. }
  pose proof (A.ProgBridge.rng_of_visible (Reusable.YA0n.w_H W3) (ACtlCutP.Sfr fr + 22) 45 RV) as RG.
  (* ---- G3: the cut's configuration in the run's state form, then the run's canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A828d8_at [Z.of_nat j])) with 0x828d8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x828d8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* ---- G4: the lift (memory-writing run: SRr_fevt_hid) ---- *)
  pose proof (F37F.f37_evt_body_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 (ACtlCutP.Sfr fr) bs R19 H1020 HRW ltac:(lia) ltac:(lia) RG) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  refine (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS
            (A.ProgBridge.fp_avoids_RNG_W _) _).
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (m1 & Ems & MU & WM & cs & Hcs & Hcsl). subst ms'.
  (* the run changes only the 45 stored shadow bytes *)
  assert (KR : forall x, 0 <= x < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 22 <= x < ACtlCutP.Sfr fr + 67) ->
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs m1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)).
  { intros x Hx Hnx. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite (MU (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)); [reflexivity|].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by lia. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [exact Hnx | exact I]. }
  (* the 67 shadow cells are present after the stores *)
  assert (Hpres1 : forall x : word, ACtlCutP.Sfr fr <= bv_unsigned x < ACtlCutP.Sfr fr + 67 -> m1 x <> None).
  { intros x Hx Hnone. destruct Hcs as ((Hwf & Hba) & _).
    pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_bytes_length cs Hwf) as Hlen1.
    destruct (F37.f37_ba_some m1 (ACtlCutP.Sfr fr) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_bytes cs) (bv_unsigned x - ACtlCutP.Sfr fr)
                Hba ltac:(rewrite Hlen1, Hcsl; cbn; lia)) as (b & Hb).
    replace (ACtlCutP.Sfr fr + (bv_unsigned x - ACtlCutP.Sfr fr)) with (bv_unsigned x) in Hb by lia.
    (* `Z_to_bv_bv_unsigned` is a DOUBLED bare name (lib/Lib/MState.v, lib/A/Bz/Lib/MState.v and more), and in
       this file's context it binds NEITHER: `About Z_to_bv_bv_unsigned` here expands it to
       `Constant stdpp.bitvector.definitions.Z_to_bv_bv_unsigned` (stdpp/bitvector/definitions.v:392), which
       `Locate` lists first.  Written out, so no later Import can move it (a Theorem Labs lane 07:01Z). *)
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hnone in Hb.
    assert (Hrom : CK11.seg_rom segs (Z_to_bv 64 (bv_unsigned x)) = None).
    { apply Reusable.YCbq.seg_rom_none; [pose proof (bv_unsigned_in_range 64 x) as Hr; exact Hr |].
      intros Himg. pose proof (A.ACtlG.Kit.kit_segs_low _ Himg) as Hlo.
      unfold Reusable.YG0f.kLowMemEnd in Hlo. lia. }
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hrom.
    change (CK11.seg_rom segs x = None) in Hrom.
    change (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom A.Img0.rsegs x = Some b) in Hb.
    assert (Erom : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom A.Img0.rsegs x = CK11.seg_rom segs x) by reflexivity.
    rewrite Erom, Hrom in Hb. discriminate Hb. }
  (* the journal across the run (ajournal_exec, YCbq.v:636) *)
  assert (HJ1 : AJ cx ly3 S3 W3 m1 md' k).
  { eapply (Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => ACtlCutP.Sfr fr + 22 <= a < ACtlCutP.Sfr fr + 67).
    - exact HJ.
    - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity|].
      cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 22) (bv_unsigned x));
        [destruct (Z_lt_ge_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 67))|].
      + apply Hpres1. lia.
      + rewrite (MU x); [exact Hx|]. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [lia | exact I].
      + rewrite (MU x); [exact Hx|]. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [lia | exact I].
    - exact Hhid.
    - exact Hsbm.
    - intros a Ha. cbv beta in Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx).
      split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Hfb6, ESh.
      replace (4096 / 8) with 512 by reflexivity. lia. }
  (* ---- G5: the call ---- *)
  (* the run's end map: ra := 0x82940, a0 := s7, every other register the entry's *)
  match goal with |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ (Z_to_bv 64 0x53378) _ _ _ _] => set (R1 := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 R1 m1 md') (POST cx)).
  assert (E1_1 : CK11.getr R1 1 = Z_to_bv 64 0x82940) by reflexivity.
  assert (E1_10 : CK11.getr R1 10 = CK11.getr regs3 23) by reflexivity.
  assert (E1_2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
  assert (E1_3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
  assert (E1_4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
  assert (E1_8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
  assert (E1_9 : CK11.getr R1 9 = CK11.getr regs3 9) by reflexivity.
  assert (E1_18 : CK11.getr R1 18 = CK11.getr regs3 18) by reflexivity.
  assert (E1_19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
  assert (E1_21 : CK11.getr R1 21 = CK11.getr regs3 21) by reflexivity.
  assert (E1_22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
  assert (E1_23 : CK11.getr R1 23 = CK11.getr regs3 23) by reflexivity.
  assert (E1_25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
  assert (E1_26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
  assert (Hspz1 : Reusable.YG0d.spZ R1 = sp) by (unfold Reusable.YG0d.spZ; rewrite E1_2; exact Hspz).
  (* the stack window above sp is untouched by the run *)
  assert (Hsvl : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !f37_le8_len; reflexivity).
  assert (Hsaved1 : ACtlCutP.MEM.bytes_at segs m1 (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
  { apply (f37_ba_keep mem3 m1 _ _ Hsaved). intros x Hx. rewrite Hsvl in Hx.
    apply KR; [lia|]. lia. }
  (* the free's premises *)
  assert (HinL : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (f37_not_entry cx ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hperm) as Hnot.
  assert (Hnev3 : Reusable.YG00.st_nev S3 < Reusable.YG00.EV_MAX).
  { unfold A.ACfn.EV_LIB in Hnev0. unfold Reusable.YG00.EV_MAX in *. lia. }
  destruct (CHAIN_OF_CUT [] cx (ACtlCut.own6 cx) ly3 S3 W3 m1 md' k R1
              (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) 0x82940 HB HJ1
              ltac:(rewrite E1_8; exact R8) E1_1 Hsaved1 ltac:(lia) ltac:(lia)
              ltac:(right; right; right; left; reflexivity))
    as (ch & Hch & Htr).
  apply (f37_free cx (ACtlCutP.flen cx j) phi ly3 S3 W3 R1 m1 md' k (sp - ACtlCut.c_sp cx) ch (POST cx)
           HJ1 HinL Hnot ltac:(rewrite E1_10; exact R23) ltac:(lia)
           ltac:(clear - Hsp0al Hsp16; Z.div_mod_to_equations; lia)
           ltac:(lia) ltac:(unfold Reusable.YG0d.ASTACK, A.ACfn.LLVMF_STK; lia)
           ltac:(rewrite E1_3; etransitivity; [exact R3 | exact Hgp0]) ltac:(rewrite E1_4; exact R4) E1_1 Hnev3 Hch Htr).
  (* ---- after the free: the exit cut C_A82940_at [j] at 0x82940 ---- *)
  intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hkeep Hsplit Hfr2 Hkept.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  pose proof Hkept as (Kst & Kbl & _ & Kfr & _ & _).
  (* the callee-saved registers *)
  assert (G2 : CK11.getr regs2 2 = CK11.getr regs3 2)
    by (rewrite <- E1_2; exact (Hkeep 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G3 : CK11.getr regs2 3 = CK11.getr regs3 3)
    by (rewrite <- E1_3; exact (Hkeep 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G4 : CK11.getr regs2 4 = CK11.getr regs3 4)
    by (rewrite <- E1_4; exact (Hkeep 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G8 : CK11.getr regs2 8 = CK11.getr regs3 8)
    by (rewrite <- E1_8; exact (Hkeep 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G9 : CK11.getr regs2 9 = CK11.getr regs3 9)
    by (rewrite <- E1_9; exact (Hkeep 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G18 : CK11.getr regs2 18 = CK11.getr regs3 18)
    by (rewrite <- E1_18; exact (Hkeep 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G19 : CK11.getr regs2 19 = CK11.getr regs3 19)
    by (rewrite <- E1_19; exact (Hkeep 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G21 : CK11.getr regs2 21 = CK11.getr regs3 21)
    by (rewrite <- E1_21; exact (Hkeep 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G22 : CK11.getr regs2 22 = CK11.getr regs3 22)
    by (rewrite <- E1_22; exact (Hkeep 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G23 : CK11.getr regs2 23 = CK11.getr regs3 23)
    by (rewrite <- E1_23; exact (Hkeep 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G25 : CK11.getr regs2 25 = CK11.getr regs3 25)
    by (rewrite <- E1_25; exact (Hkeep 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (G26 : CK11.getr regs2 26 = CK11.getr regs3 26)
    by (rewrite <- E1_26; exact (Hkeep 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia))).
  assert (R9' : ACtlCut.rgv regs2 9 A) by (unfold ACtlCut.rgv in *; rewrite G9; exact R9).
  assert (HA64 : 0 <= A < 2 ^ 63) by lia.
  (* the live list: back to the entry blocks *)
  assert (Hperm2 : Permutation (Reusable.YG0d.ablocks B ly2 S2) (ENTRYBL cx)).
  { destruct Hsplit as (l1 & l2 & E3 & E2). rewrite E2.
    pose proof Hperm as Hperm'. rewrite E3 in Hperm'.
    rewrite <- (app_nil_r (ENTRYBL cx)).
    exact (Permutation_app_inv l1 l2 (ENTRYBL cx) [] (phi, ACtlCutP.flen cx j) Hperm'). }
  (* KEPT CLASSES of acall_kept (YCbq.v:824-835), each read at a byte visible in W3 *)
  assert (KS : forall x, sp <= x < ACtlCut.c_sp cx ->
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)).
  { intros x Hx. rewrite <- (KR x ltac:(lia) ltac:(lia)).
    apply (f37_vis_mrd W3 W2 m1 mem2 x Hle).
    - destruct (Hpres x ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hv & _). exact Hv.
    - apply Kst; [lia|]. lia. }
  assert (KFR : forall x, fr <= x < fr + 4096 ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)).
  { intros x Hx. rewrite <- (KR x ltac:(lia) ltac:(lia)).
    apply (f37_vis_mrd W3 W2 m1 mem2 x Hle).
    - destruct (Hfrb x Hx) as ((Hv & _) & _). exact Hv.
    - apply (Kfr 6 (ACtlCut.c_fpos cx) x Hin6).
      + left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3, Hfb6. lia.
      + intros Hblk. cbv beta in Hblk.
        pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                      6 (ACtlCut.c_fpos cx) HAR HinL Hin6) as Hd.
        unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr3, Hfb6 in Hd. lia. }
  assert (KFS : forall x, fr + 536 <= x < fr + 4096 ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr x)) =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr x))).
  { intros x Hx.
    assert (Hi : ACtlCutP.Sfr fr + 67 <= A.AsanRT.shadow_addr x < ACtlCutP.Sfr fr + 512).
    { rewrite HSfr. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. clear - Hx Hfr8. Z.div_mod_to_equations. lia. }
    rewrite <- (KR (A.AsanRT.shadow_addr x) ltac:(lia) ltac:(lia)).
    apply (f37_vis_mrd W3 W2 m1 mem2 _ Hle).
    - destruct (Hfrsh (A.AsanRT.shadow_addr x - ACtlCutP.Sfr fr) ltac:(lia)) as ((Hv & _) & _).
      replace (ACtlCutP.Sfr fr + (A.AsanRT.shadow_addr x - ACtlCutP.Sfr fr)) with (A.AsanRT.shadow_addr x)
        in Hv by lia.
      exact Hv.
    - apply (Kfr 6 (ACtlCut.c_fpos cx) _ Hin6).
      + right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Hfb6, ESh.
        replace (4096 / 8) with 512 by reflexivity. lia.
      + intros Hblk. cbv beta in Hblk.
        destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR HinL)
          as (_ & _ & _ & Hbapp & _).
        unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
          Reusable.YG0f.ASAN_CEIL in Hbapp. lia. }
  assert (KIN : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd segs mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)).
  { intros x Hx. destruct Hpn as [(Hn0 & _) | ((Hnpos & _) & HinE)]; [lia|].
    assert (HinP : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact HinE. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR HinP)
      as (_ & H4096 & Hbceil & Hbapp & Hbp & _).
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as (_ & Hrs).
    rewrite <- (KR x ltac:(unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL in Hbapp; lia)
                  ltac:(unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL,
                          Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hbapp; lia)).
    apply (f37_vis_mrd W3 W2 m1 mem2 x Hle).
    - destruct (Hbp x ltac:(lia)) as ((Hv & _) & _). exact Hv.
    - replace x with (ACtlCut.c_p cx + (x - ACtlCut.c_p cx)) by lia.
      apply (Kbl (ACtlCut.c_p cx) (ACtlCut.c_n cx) (x - ACtlCut.c_p cx) HinP ltac:(lia)).
      intros Hblk. cbv beta in Hblk.
      assert (Hne : (phi, ACtlCutP.flen cx j) <> (ACtlCut.c_p cx, ACtlCut.c_n cx))
        by (intros E; apply Hnot; rewrite E; exact HinE).
      pose proof (Reusable.YCbq.sep_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ _ _ HAR HinL HinP Hne) as Hd.
      unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  (* the frame after the call: frames S2 = own6, its bytes and shadow present (AR's frames law at the post) *)
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfr2; exact Hin6).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF2; reflexivity).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
    as (_ & _ & Hfrb2 & Hfrsh2).
  rewrite ?Efr2, ?Hfb6 in Hfrb2, Hfrsh2. rewrite ESh in Hfrsh2.
  replace (4096 / 8) with 512 in Hfrsh2 by reflexivity.
  (* lengths the byte facts need *)
  pose proof (F37.f37_ID_len (ACtlCut.c_in cx) (S j)) as HIDl.
  unfold ACtlCutP.RIM.ID_SIZE in HIDl.
  pose proof (F37.f37_FG_len (ACtlCut.c_in cx) (S j)) as HFGl.
  pose proof (F37.f37_fs_body_len (ACtlCut.c_in cx) (S j)) as HFBl.
  assert (HOURl : length (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat)
    by (unfold A.Prog.SlotModel.OUR; rewrite length_map, length_seq; reflexivity).
  (* the input block's addressable bytes at the post (AR's shadow law; for n = 0 the empty range) *)
  assert (HAin2 : A.AsanRT.addressable mem2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { destruct Hpn as [(Hn0 & _) | ((Hnpos & _) & HinE)].
    - apply (f37_addr_keep mem3 mem2 _ _ HAin). intros i Hi. lia.
    - assert (HinP2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2))
        by (apply (Permutation_in _ (Permutation_sym Hperm2)); exact HinE).
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HinP2)
        as (_ & H4096 & Hbceil & Hbapp & _).
      pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as (_ & Hrs).
      pose proof (Reusable.YCbq.range_addressable_of_block segs B LAWS ly2 S2 W2 mem2 md2
                    (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR2 HinP2
                    ltac:(lia) ltac:(lia)) as Hra.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL, Reusable.YG0f.kLowShadowBeg,
        Reusable.YG0f.kHighMemBeg in Hbapp.
      split; [lia|]. split; [lia|]. split; [unfold A.AsanRT.APPMEM_END; lia|].
      intros i Hi. destruct (Hra (ACtlCut.c_p cx + i) ltac:(lia)) as (s & Hs & Hok).
      split.
      + unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
      + unfold Reusable.YG0n.aview, CP09.mbyte, Reusable.YK04.mrestrict in Hs. cbv beta in Hs.
        assert (Esh : Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (ACtlCut.c_p cx + i) =
                      A.AsanRT.shadow_addr (ACtlCut.c_p cx + i))
          by (unfold Reusable.YG0v.shadow_of_addr, A.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF,
                A.AsanRT.ASAN_K; lia).
        rewrite Esh in Hs.
        assert (Hshr : 0x7fff8000 <= A.AsanRT.shadow_addr (ACtlCut.c_p cx + i) < 2 ^ 64)
          by (clear - Hbapp H4096 Hi Hrs C1; unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
              Z.div_mod_to_equations; lia).
        rewrite (Reusable.YCbq.seg_rom_none segs (A.AsanRT.shadow_addr (ACtlCut.c_p cx + i)) ltac:(lia)
                   ltac:(intros Himg; pose proof (A.ACtlG.Kit.kit_segs_low _ Himg) as Hlo;
                         unfold Reusable.YG0f.kLowMemEnd in Hlo; lia)) in Hs.
        destruct (Reusable.YA0n.w_H W2 (Z_to_bv 64 (A.AsanRT.shadow_addr (ACtlCut.c_p cx + i))));
          [cbn in Hs; discriminate Hs|].
        destruct (mem2 (Z_to_bv 64 (A.AsanRT.shadow_addr (ACtlCut.c_p cx + i)))) as [b|] eqn:Eb;
          cbn in Hs; [|discriminate Hs].
        injection Hs as Hs. exists b. split.
        * unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. rewrite Eb. reflexivity.
        * unfold Reusable.YG0v.saddr_ok in Hok. unfold A.AsanRT.shadow_ok.
          pose proof (bv_unsigned_in_range 8 b) as Hbr.
          rewrite f37_signed_small; [|unfold Reusable.YG0v.saddr_ok in Hok; lia]. lia. }
  (* ---- the exit body, C_A82940_at [j] (ACtlCutP.v:2939-2948) ---- *)
  assert (HFRAC2 : ACtlCutP.FRAC B cx fr fr regs3 mem2).
  { unfold ACtlCutP.FRAC. exists A, sp.
    do 17 (split; [assumption|]).
    split; [apply (f37_q64_keep mem3 mem2 _ _ Q304); intros x Hx; apply KS; lia|].
    split; [apply (f37_q64_keep mem3 mem2 _ _ Q24); intros x Hx; apply KS; lia|].
    split; [apply (f37_q64_keep mem3 mem2 _ _ Q16); intros x Hx; apply KS; lia|].
    split; [apply (f37_q64_keep mem3 mem2 _ _ Qhdr); intros x Hx; apply KFR; lia|].
    split; [apply (f37_q64_keep mem3 mem2 _ _ Qent); intros x Hx; apply KFR; lia|].
    split.
    - apply (F37.f37_ba_present mem2 392 (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)).
      intros i Hi. destruct (Hfrsh2 (Z.of_nat i) ltac:(lia)) as ((_ & b & Hb) & _).
      exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. rewrite Hb. reflexivity.
    - split; [apply (f37_ba_keep mem3 mem2 _ _ Hsaved); intros x Hx; apply KS; lia|].
      (* the fake-frame trailer word [fr + 4088, fr + 4096) (Batch3): the run writes only the shadow bytes
         [S(fr) + 22, S(fr) + 67), and the free keeps it by acall_kept's FRAME class (KFR) *)
      apply (f37_q64_keep mem3 mem2 _ _ Htrail). intros x Hx. apply KFR. lia. }
  assert (HPRO2 : ACtlCutP.PRO cx fr regs2 mem2).
  { unfold ACtlCutP.PRO.
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_ad KFS|].
    split; [apply (f37_ba_keep mem3 mem2 _ _ HBin); intros x Hx; apply KIN; lia|].
    split; [intros _; exact HAin2|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_sp R9 R9' HA64 KS|]. f37_sp R9 R9' HA64 KS. }
  assert (HFLSI2 : ACtlCutP.FLSI cx j fr regs2 mem2).
  { unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.FLC, ACtlCutP.f1_IN.
    split.
    { split; [exact HPRO2|]. split; [f37_sp R9 R9' HA64 KS|].
      split.
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk, ACtlCutP.FRAME_BYTES. split; [lia|]. split; [lia|]. intros a Ha.
        destruct (Hfrb2 a ltac:(lia)) as ((_ & b & Hb) & _).
        split.
        - unfold wview, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. rewrite Hb. discriminate.
        - exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
      split; [f37_sp R9 R9' HA64 KS|]. f37_ad KFS. }
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [split; [exact HAin2 | apply (f37_ba_keep mem3 mem2 _ _ HBin'); intros x Hx; apply KIN; lia]|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [f37_ad KFS|]. split; [f37_ad KFS|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    f37_sp R9 R9' HA64 KS. }
  assert (HLK2 : ACtlCutP.LK cx fr j regs2 mem2).
  { unfold ACtlCutP.LK. split; [exact Hj|]. split; [unfold ACtlCut.rgv in *; rewrite G21; exact R21|].
    unfold ACtlCutP.OURb in *. apply (f37_ba_keep mem3 mem2 _ _ HOUR). intros x Hx. apply KFR. lia. }
  assert (HFLSF2 : ACtlCutP.FLSF cx j phi fr regs2 mem2).
  { unfold ACtlCutP.FLSF. split; [exact HFLSI2|].
    split; [unfold ACtlCut.rgv in *; rewrite G18; exact R18|].
    split; [unfold ACtlCut.rgv in *; rewrite G22; exact R22|].
    split; [unfold ACtlCut.rgv in *; rewrite G23; exact R23|].
    split; [unfold ACtlCut.rgv in *; rewrite G25; exact R25|].
    split; [intros H50'; destruct (H50 H50') as (Hp1 & Hp2 & _); split; [exact Hp1 | exact Hp2]|].
    split; [f37_sp R9 R9' HA64 KS | f37_sp R9 R9' HA64 KS]. }
  assert (HLT2 : ACtlCutP.LT cx fr j regs2 mem2).
  { unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb,
      ACtlCutP.FGBe, ACtlCutP.FSj, ACtlCutP.FSb.
    unfold ACtlCutP.IDBe, ACtlCutP.FGBe in HIDB, HFGB.
    split; [split; [apply (f37_ba_keep mem3 mem2 _ _ HIDB); intros x Hx; apply KFR; lia | exact Hidok]|].
    split; [split; [apply (f37_ba_keep mem3 mem2 _ _ HFGB); intros x Hx; apply KFR; lia | exact Hfgok]|].
    split; [f37_sp R9 R9' HA64 KS|]. split; [f37_sp R9 R9' HA64 KS|].
    split; [apply (f37_ba_keep mem3 mem2 _ _ HFSB); intros x Hx; apply KFR; lia|].
    split; [f37_ad KFS | exact HFI]. }
  (* ctl_rt_C after the world step: ctl_rt_C_of_AR at the post's AR, with the read-only view of the entry kept by the
     journal (Reusable.APostBase.arodata_ok_journalP at the empty extra span [0, 0)) *)
  assert (HRO0 : Reusable.APostBase.arodata_okP segs 0 0 B
                   (Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))).
  { unfold Reusable.APostBase.arodata_okP. unfold Reusable.YE01.arodata_okS in Hros.
    intros a Hro Ho He. apply Hros; [|exact Ho | exact He].
    unfold Reusable.APostBase.in_roP in Hro. destruct Hro as [Hs | Hr]; [left; exact Hs | lia]. }
  assert (HRB : @Reusable.APostBase.ro_below_ofl segs 0 0 A.AE2k.tfib_sink_head).
  { intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
    pose proof (List.in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0), seg_writable s0))
                  segs s Hs) as Hm.
    cbv beta in Hm. rewrite Hw in Hm.
    remember (Z.of_N (seg_base s)) as b0 eqn:Eb. remember (Z.of_N (seg_size s)) as z0 eqn:Ez.
    clear Eb Ez.
    vm_compute in Hm.
    cbn [CI16.sk_ofl_head A.AE2k.tfib_sink_head]. unfold A.AE2k.A_ofl_head.
    repeat (destruct Hm as [Hm | Hm]; [injection Hm; intros; subst; first [discriminate | lia] |]).
    destruct Hm. }
  assert (HRO2 : Reusable.APostBase.arodata_okP segs 0 0 B
                   (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W2) mem2)).
  { eapply (Reusable.APostBase.arodata_ok_journalP (SK := A.AE2k.tfib_sink_head)).
    - intros ? ?; lia.
    - exact HRB.
    - exact HJ2.
    - exact HRO0. }
  pose proof (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly2 S2 W2 mem2 md2 HAR2 HRO2) as Hrt2.
  (* the exit cut *)
  change (Reusable.YA0n.SRr segs W2
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82940_at [Z.of_nat j])) regs2 mem2 md2) (POST cx)).
  apply (HX cx [Z.of_nat j] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB).
  - exact HJ2.
  - change (Reusable.YG01.frames S2 = [(6, ACtlCut.c_fpos cx)]). rewrite Hfr2. exact HF.
  - exact HL.
  - change (k + 1 <= 14 + 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat j]) + 2).
    unfold ACtlCutP.ixn. cbn [nth]. rewrite Nat2Z.id. lia.
  - split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82940_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact Hperm2|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 regs2 mem2 HFRAC2 G2 G3 G4 G8 G9 G19 G26)|].
    split; [exact Hn|].
    split; [exact HLK2|].
    split; [exact HFLSF2 | exact HLT2].
  - exact Hrt2.
Qed.

End GlueF37.
