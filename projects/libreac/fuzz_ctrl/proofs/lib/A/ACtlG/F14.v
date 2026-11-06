(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v; 542 of its 570 lines of code are new or changed and 938 lines of the source are left out. *)
(* lib/A/ACtlG/F14.v -- GLUE for stage seg_F14 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:784).  Written by a Theorem Labs lane (piece W4c); single writer.  rule 24: no function
   proved (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_F14 : forall POST (j : nat),
       CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A82154_at [Z.of_nat j])
   with ACtl.v's own CF notation, i.e. exactly ACtl.v's Section hypothesis seg_F14.  Segment F14 (Seg/F14.v:1-16):
     0x82154 bltz a0 (not taken: a0 = fg_ret of the class, 0 or 1) ; mv s9,a0 ; ld a0,280(s1) ; bnez a0,.. ;
     [A+280] <> 0: exit cut C_A82178_at (Seg/F14F.f14_evt_e0_F, one 8-byte load, no store);
     [A+280] = 0: li a2,72 ; ld a0,184(s1) ; ld a1,192(s1) ; jal wrapper_bcmp, exit cut C_A82174_at
       (Seg/F14F_on.f14_evt_dc_ro_F_on, three loads and the bcmp wrapper, which writes only its stack window
       [sp - BCMP_WRAP_K, sp)).  The wrapper's footprint contract (route (C): bcmp_wrap_contract_F_on) is DISCHARGED
       by its proved closed theorem lib/A/Prog/bcmp_wrap_on.v bcmp_wrap_holds_F_on: no split, the run is lifted whole.

   THE PROOF (glue-pattern.md section 3; Seg/F14.v:325-894 is the v1.9 source of record over SlotInv)
   G1  the entry cut C_A82154_at (ACtlCutP.v:2267-2295).
   G2  bounds from VISIBLE state: KitMem.kitmem_own6 (the class-6 frame below alloc_ceiling <= c_sp cx - LLVMF_STK,
       4096 <= fr, fr mod 32 = 0); FRAC's spill base A and sp (c_sp cx - 4096 < sp <= A, A + 416 <= c_sp cx); the
       record block phi and the input block are live blocks (the body's Permutation and the lib pre), below
       alloc_ceiling by the AR block law.  The rng premises: spills and the wrapper's window in the journal's stack
       window (KitMem.kitmem_rng_win), the two 72-byte records and their shadow-word covers in the owned frame
       (kitmem_rng_frame / kitmem_rng_frame_sh), the image (ProgBridge.img_vis_W), rng_bytes (rng_bytes_RNG_W).
       The wrapper's stk window premise from the journal (kitmem_stk_of_journal).
   G3  the walk moved from regs3 to the run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  e0 arm: SRr_fevt at RNG_W (read-only).  dc arm: SRr_fevt_hid at RNG_W (the wrapper writes its window).
   G5  exit cut at the run's end map R.  Journal: ajournal_exec; e0 arm with no write, dc arm with
       Wr = [sp - BCMP_WRAP_K, sp): memory equal outside Wr by the wrapper's munch, mem_grows by
       KitMem.kitmem_grows_munch_stk (the window is present after, the post's stk), hidden bytes by SRr_fevt_hid,
       every written byte in the LLVMF stack window (KitMem.kitmem_awr_win).  Body: registers through
       Kit.kit_frac_move, the local w4c_flsi_move / w4c_flsi_keep (ACtlCutP.FLSI is not SlotInv's text, see below)
       and the v1.9 source's lemmas (Seg/F13 ifs2_regs / ifs2_keep / f16carry_keep, Seg/F15 lk_regs /
       f16carry_regs) applied to a SlotInv ghost with g_in = c_in cx (their texts equal ACtlCutP's); memory across
       the wrapper's window by KitMem's munch lemmas (q64 / bytes / addressable / spill / FRAC) and
       lib/Lib/Frame.rw_cells_transport; ctl_rt_C after the call from the wrapper's own post (asan_cells, ro_agree)
       and its forall-P transport of the cut's two regions (see ROUTE (C) below).
   TRANSCRIPTION DIFFERENCES met here (a Theorem Labs lane's rule, recorded, not worked around): ACtlCutP.FLSI's PRO and
   f1_IN name the input block by c_p / c_n and drop SlotInv's `0 < g_n g -> In (g_p g, g_n g) (g_H g)`, and
   ACtlCutP.f14_tail drops SlotInv's asan_cells / shadow_rw (carried by the cut's ctl_rt_C instead), so Seg/F14's flsi_regs and
   Seg/F15's f14_tail_regs do not apply by conversion; the local w4c_flsi_move / w4c_flsi_keep are the same proofs
   over ACtlCutP's text, and f14_tail is rebuilt conjunct by conjunct.

   ROUTE (C) (L3 switch, a Theorem Labs lane, recipe L3-recipe.md (a working note, not in this delivery)): the
   cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (a working branch shell 1899bed1aee).  Entry:
   `pose proof Hrt as (Hcells & Hcut & Himg & Hroag)`; the e0 arm keeps Hrt whole (same ly3 S3 mem3 at its exit).
   dc arm: the run is Seg/F14F_on.f14_evt_dc_ro_F_on (the route (C) twin of F14F.f14_evt_dc_ro_F, F14F.v
   unchanged apart from comment text), whose shadow premise is shadow_rw_on (bcmp_wrap_shadow_R (fr + 336) (fragb fr) 72): the
   wrapper's aligned shadow words of the two 72-byte records, both in the owned class-6 frame [fr, fr + 4096), so
   the region lies in cut_shadow's (F) disjunct (shadow_rw_on_mono from Hcut).  The wrapper's contract is
   discharged by a Theorem Labs lane's closed A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on (bcmp_wrap_on.v 49fcbf2eeed (the blob this tree had at release c5e779efe8c), with
   A/MemNormP.v e45ea6f496f (the blob this tree had at release c5e779efe8c) and Prog/bcmp_wrap_Fk.v 1fa5b214cf3 (the blob this tree had at release c5e779efe8c), no root lib/MemNorm*; leaf bcmp_wrap_c_on.v blob
   ca2f37ea2b6 (the blob this tree had at release c5e779efe8c), bcmp_wrap_c.v 64293314ee8 (the blob this tree had at release c5e779efe8c); by path from a working branch f4423e55886).  Exit:
   ly3 S3 are kept, so ctl_rt_C B ly3 S3 m' is rebuilt from the post's asan_cells / ro_agree and the post's
   `forall P, shadow_rw_on P mem3 -> shadow_rw_on P m'` at P := cut_shadow B ly3 S3 and P := img_shadow.

   SECTION HYPOTHESES: LAWS (the core's AR laws, YCbq.v:207, as ACtl.v:237 states it).  No other.  Runs Required
   from Seg/F14F.v (a Theorem Labs lane's re-run) and Seg/F14F_on.v; the wrapper contract discharged by
   bcmp_wrap_on.bcmp_wrap_holds_F_on.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (SlotInv / Seg names appear only
   inside proofs, qualified).  The six modules present both as lib/Reusable/<X> and lib/A/Reusable/<X> (YI04 YI16
   YK11 YK1b YM05 YO09) are written with their full path and loaded by an absolute Require.  The blob list is in the
   commit message.

   FRAC AT A NEW MEMORY (a Theorem Labs lane 05:5xZ, the coming trailer conjunct q64 (fr + 4088) ..): the dc arm
   re-establishes FRAC after the wrapper's write only through KitMem.kitmem_frac_munch, which proves FRAC by shape
   and whose frame premise covers [fr + 4088, fr + 4096) (discharged here: the frame lies below alloc_ceiling, far
   from the wrapper's window); every other FRAC here is moved along registers only (Kit.kit_frac_move).  Every
   destruct of FRAC ends in `& _`.

   BUILD STATE: TYPE-CHECK on a working branch shell 1899bed1aee (cb build, BASE row 23b918fe0c2e, a build machine,
   workspace (internal path)); the build of record is cbrec.sh's, named in the lane's report. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.SlotInv Prog.RcFrag Prog.RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_fragment_c A.Prog.bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Spec.StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F13 A.Prog.Seg.F14 A.Prog.Seg.F15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F14F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
(* route (C): the cut's ctl_rt_C (ACtlRtC.v), the region form (ShadowRwOn.v), the wrapper's _on leaf / proof
   (a working branch f4423e55886, by path) and the F14F run's _on twin (Seg/F14F_on.v). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.Prog.rng_asan A.Prog.sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.bcmp_wrap_c_on A.Prog.bcmp_wrap_on A.Prog.Seg.F14F_on.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
(* The core's register reader, the module path written in full (the six-module clash). *)
Local Notation Kgetr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch.

(* ---------------------------------------------------------------------------------------------------------
   FLSI along a register map that keeps s1 (no memory change), and across a write set that misses its bytes.
   ACtlCutP's FLSI differs from SlotInv's (header), so Seg/F14.flsi_regs / Seg/F13.pro_keep do not apply by
   conversion: these are the same proofs over ACtlCutP's text. *)
Lemma w4c_flsi_move : forall cx j fr (regs regs' : bvmap 5 word) m,
  ACtlCutP.FLSI cx j fr regs m -> Kgetr regs' 9 = Kgetr regs 9 -> ACtlCutP.FLSI cx j fr regs' m.
Proof.
  intros cx j fr regs regs' m H E9.
  assert (K : forall off v, ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m off v).
  { intros off v (A & HA & Hq). exists A. split; [|exact Hq]. unfold ACtlCut.rgv in *. rewrite E9. exact HA. }
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC in *.
  destruct H as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pa & Pin & Pn & P184 & P256 & P264 &
    P272 & P32) & S128 & Hstk & S144 & Ha17) & S216 & S224 & S248 & HIN &
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cid & C72 & C64 & C56 & C48)).
  split; [split; [|split; [exact (K _ _ S128)|split; [exact Hstk|split; [exact (K _ _ S144)|exact Ha17]]]]|].
  - exact (conj (K _ _ P40) (conj (K _ _ P120) (conj (K _ _ P136) (conj (K _ _ P160) (conj (K _ _ P168)
      (conj (K _ _ P176) (conj (K _ _ P208) (conj (K _ _ P248) (conj Pa (conj Pin (conj Pn (conj (K _ _ P184)
      (conj (K _ _ P256) (conj (K _ _ P264) (conj (K _ _ P272) (K _ _ P32)))))))))))))))).
  - split; [exact (K _ _ S216)|]. split; [exact (K _ _ S224)|]. split; [exact (K _ _ S248)|].
    split; [exact HIN|].
    exact (conj (K _ _ C256) (conj (K _ _ C184) (conj (K _ _ C192) (conj (K _ _ C80) (conj (K _ _ C88)
      (conj (K _ _ C96) (conj (K _ _ C272) (conj (K _ _ C264) (conj Cfa (conj Cid (conj (K _ _ C72)
      (conj (K _ _ C64) (conj (K _ _ C56) (K _ _ C48)))))))))))))).
Qed.

Lemma w4c_flsi_keep : forall cx j fr (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (A : Z),
  ACtlCutP.FLSI cx j fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  Kgetr regs' 9 = Kgetr regs 9 -> LFr WR m m' ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  (forall x, A <= x < A + 416 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, A.AsanRT.in_shadow x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr regs regs' m m' WR A H H9 HA0 HA E9 MU WM HoA Hofr Hosh Hoin.
  assert (K : forall off v, ACtlCutP.spill regs m off v -> 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs' m' off v).
  { intros off v Hs Ho1 Ho2.
    apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs regs' m m' off v A Hs H9 HA0 Ho1 ltac:(lia) MU E9).
    intros x Hx. apply HoA. lia. }
  assert (KA : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n)
    by (intros p n Ha; exact (A.ACtlG.KitMem.kitmem_addr_munch WR m m' p n Ha MU Hosh)).
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.f1_IN in *.
  destruct H as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pa & Pin & Pn & P184 & P256 & P264 &
    P272 & P32) & S128 & Hstk & S144 & Ha17) & S216 & S224 & S248 & (Hia & Hib) &
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cid & C72 & C64 & C56 & C48)).
  assert (Hin' : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m'
                   (ACtlCut.c_p cx) (ACtlCut.c_in cx))
    by (exact (A.ACtlG.KitMem.kitmem_bytes_munch WR m m' _ _ Pin MU Hoin)).
  split.
  - split.
    + exact (conj (K _ _ P40 ltac:(lia) ltac:(lia)) (conj (K _ _ P120 ltac:(lia) ltac:(lia))
        (conj (K _ _ P136 ltac:(lia) ltac:(lia)) (conj (K _ _ P160 ltac:(lia) ltac:(lia))
        (conj (K _ _ P168 ltac:(lia) ltac:(lia)) (conj (K _ _ P176 ltac:(lia) ltac:(lia))
        (conj (K _ _ P208 ltac:(lia) ltac:(lia)) (conj (K _ _ P248 ltac:(lia) ltac:(lia)) (conj (KA _ _ Pa)
        (conj Hin' (conj (fun Hn => KA _ _ (Pn Hn)) (conj (K _ _ P184 ltac:(lia) ltac:(lia))
        (conj (K _ _ P256 ltac:(lia) ltac:(lia)) (conj (K _ _ P264 ltac:(lia) ltac:(lia))
        (conj (K _ _ P272 ltac:(lia) ltac:(lia)) (K _ _ P32 ltac:(lia) ltac:(lia))))))))))))))))).
    + split; [exact (K _ _ S128 ltac:(lia) ltac:(lia))|].
      split.
      { apply (A.Prog.Seg.F13.stk_keep WR m m' fr (fr + ACtlCutP.FRAME_BYTES) Hstk MU WM).
        intros x Hx Ho. exfalso. exact (Ho (Hofr x Hx)). }
      split; [exact (K _ _ S144 ltac:(lia) ltac:(lia)) | exact (KA _ _ Ha17)].
  - split; [exact (K _ _ S216 ltac:(lia) ltac:(lia))|].
    split; [exact (K _ _ S224 ltac:(lia) ltac:(lia))|].
    split; [exact (K _ _ S248 ltac:(lia) ltac:(lia))|].
    split; [exact (conj (KA _ _ Hia) Hin')|].
    exact (conj (K _ _ C256 ltac:(lia) ltac:(lia)) (conj (K _ _ C184 ltac:(lia) ltac:(lia))
      (conj (K _ _ C192 ltac:(lia) ltac:(lia)) (conj (K _ _ C80 ltac:(lia) ltac:(lia))
      (conj (K _ _ C88 ltac:(lia) ltac:(lia)) (conj (K _ _ C96 ltac:(lia) ltac:(lia))
      (conj (K _ _ C272 ltac:(lia) ltac:(lia)) (conj (K _ _ C264 ltac:(lia) ltac:(lia)) (conj (KA _ _ Cfa)
      (conj (KA _ _ Cid) (conj (K _ _ C72 ltac:(lia) ltac:(lia)) (conj (K _ _ C64 ltac:(lia) ltac:(lia))
      (conj (K _ _ C56 ltac:(lia) ltac:(lia)) (K _ _ C48 ltac:(lia) ltac:(lia))))))))))))))).
Qed.

Section GlueF14.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :282-284), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82154_at := (ACtlCutP.C_A82154_at B).
Local Notation C_A82174_at := (ACtlCutP.C_A82174_at B).
Local Notation C_A82178_at := (ACtlCutP.C_A82178_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F14 : forall POST (j : nat),
  CF POST (ix_cut C_A82178_at [Z.of_nat j]) -> CF POST (ix_cut C_A82174_at [Z.of_nat j]) -> CF POST (ix_cut C_A82154_at [Z.of_nat j]).
Proof.
  intros POST j He0 Hdc cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* route (C): the cut carries ctl_rt_C B ly3 S3 mem3 (ACtlRtC.v:44-46); the e0 arm keeps it whole *)
  pose proof Hrt as (Hcells & Hcut & Himg & Hroag).
  (* G1: the entry cut (ix_cut, ACtlCut.v:232-234; C_A82154_at, ACtlCutP.v:2267-2295). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82154_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & A & v280 & H9 & H10 & HAb & Hv280b & Hv280s &
    Hphifr & Hphisep & H184 & H192 & H280 & HbL & HaL & HbR & HaR & HB1 & HB2 & HB3 & HB4 & HB5 & Hc256 &
    H80 & H88 & H96 & H272 & H264 & HFGM & HCAR & HIFS2).
  (* G2: the owned frame and the stack window (KitMem.kitmem_own6) *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin & Efa & Hfr4096 & Hfr32 & Hfceil & Hceil).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  unfold A.ACfn.LLVMF_STK in Hceil.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  pose proof HJ as (HAR & _).
  (* G2: FRAC's spill base and sp *)
  pose proof HFRAC as (A2 & sp & HR2 & Hspm & Hspz & HR4 & HR8 & HR9 & HR3 & HR19 & HR26 & Hfrm & HAm & HAS &
    HspA & HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in HfrA, HSapp.
  assert (EA : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold ACtlCut.rgv in HR9, H9; rewrite <- HR9; exact H9).
    apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  assert (Esp : bv_unsigned (Kgetr regs3 2) = sp) by exact Hspz.
  (* G2: the record block and the input block lie below alloc_ceiling (the AR block law) *)
  assert (Hblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hblk)
    as (_ & Hp4096 & Hpceil & _).
  assert (Hrq : forall n, 0 <= n -> n <= Reusable.YG00.req_size n)
    by (intros n Hn0; unfold Reusable.YG00.req_size; destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En; lia | lia]).
  assert (Hinp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                   x < OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling).
  { pose proof HB as ((_ & _ & _ & _ & Hblk0 & Hlen0 & _) & _).
    intros x Hx. rewrite <- Hlen0 in Hx. destruct Hblk0 as [(Hn0 & _) | (Hn0 & Hinb)]; [lia|].
    assert (Hinb' : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinb. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb') as (_ & _ & Hcb & _).
    pose proof (Hrq (ACtlCut.c_n cx) ltac:(lia)). lia. }
  (* G2: the wrapper's stack window is present (the journal's stack window) *)
  assert (Hstkc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs mem3
                    (sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
      unfold A.ACfn.LLVMF_STK, A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia. }
  (* G2: model facts of the turn's fragment class (Seg/F13-F15, over a SlotInv ghost with g_in = c_in cx) *)
  pose (gx := A.Prog.SlotInv.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
  assert (Hfnz : ACtlCutP.fragb fr <> 0) by (unfold ACtlCutP.fragb; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hrlen : length (ACtlCutP.frrec cx j fr phi) = 72%nat) by exact (A.Prog.Seg.F13.frrec_length gx j fr phi).
  assert (Hrr : 0 <= Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi) <= 1).
  { unfold ACtlCutP.frcl. apply A.Prog.Seg.F14.fg_ret_range; unfold ACtlCutP.fragb in *; lia. }
  assert (Htrf : A.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
    by (exact (A.Prog.Seg.F14.trf_of_frcl gx j fr phi Hfnz Hphinz ltac:(lia) ltac:(lia) ltac:(lia))).
  (* FLV's conditional part, from the fragment's post (fg_mem at FgClose) *)
  assert (Hfcond : forall m, A.Prog.reac_ctrl_identity_fragment_c.fg_mem (ACtlCutP.fragb fr) (fr + 256) (fr + 272)
                     (fr + 304) (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)
                     (ACtlCutP.frcl cx j fr phi) m ->
                   A.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = 1 ->
                   ACtlCutP.q64 m (fr + 272) (ACtlCutP.fragb fr + 19) /\
                   ACtlCutP.q64 m (fr + 304) (A.Prog.SlotModel.f_pll (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                                               (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))).
  { intros m Hm Hrf. rewrite Htrf in Hrf. apply A.Prog.Seg.F14.ret1_close in Hrf. rewrite Hrf in Hm.
    cbn [A.Prog.reac_ctrl_identity_fragment_c.fg_mem] in Hm. destruct Hm as (_ & _ & Hpp & Hpn).
    split; [exact Hpp | exact Hpn]. }
  (* G3: the cut's configuration in the run's state form, the walk moved to mkR_of regs3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82154_at [Z.of_nat j])) with 0x82154.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82154) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _
                (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  destruct (Z.eq_dec v280 0) as [Hv0 | Hvn].
  - (* ===== [A+280] = 0: the bcmp wrapper call, exit cut C_A82174_at (Seg/F14.v:415-784) ===== *)
    rewrite Hv0 in H280, Hv280b, Hv280s.
    destruct (A.Spec.StrFun.memcmp_model_total (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                (ACtlCutP.frrec cx j fr phi) 72
                ltac:(rewrite A.Prog.Seg.F13.t_FG_length; lia)
                ltac:(rewrite Hrlen; lia)) as (vcmp & Hmm).
    (* the frame is application memory *)
    assert (Hfrapp : forall a, fr <= a < fr + 4096 -> A.AsanRT.app_mem a).
    { destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
        as (_ & _ & Hiapp).
      rewrite Efa in Hiapp. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hiapp.
      pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[_ Hc1] _].
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
        in Hiapp.
      intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
    (* G4: the run (Seg/F14F.v:283-326) at RNG_W (w_H W3), the wrapper by its closed theorem *)
    assert (HRUN : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF A.Img0.rsegs
                     (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (fun ms' => exists R m',
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82174)
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None m'
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
         Kgetr R 2 = Kgetr regs3 2 /\
         Kgetr R 3 = Kgetr regs3 3 /\
         Kgetr R 4 = Kgetr regs3 4 /\
         Kgetr R 8 = Kgetr regs3 8 /\
         Kgetr R 18 = Kgetr regs3 18 /\
         Kgetr R 19 = Kgetr regs3 19 /\
         Kgetr R 20 = Kgetr regs3 20 /\
         Kgetr R 21 = Kgetr regs3 21 /\
         Kgetr R 22 = Kgetr regs3 22 /\
         Kgetr R 23 = Kgetr regs3 23 /\
         Kgetr R 24 = Kgetr regs3 24 /\
         Kgetr R 26 = Kgetr regs3 26 /\
         Kgetr R 9 = Kgetr regs3 9 /\ Kgetr R 10 = Z_to_bv 64 vcmp /\
         Kgetr R 25 = Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)) /\
         LFr [(bv_unsigned (Kgetr regs3 2) - A.Prog.bcmp_wrap_c.BCMP_WRAP_K, bv_unsigned (Kgetr regs3 2))] mem3 m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono A.Img0.rsegs mem3 m' /\
         A.ACtlK.ro_agree_at m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs m'
           (sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned (Kgetr regs3 2)) /\
         A.AsanRT.asan_cells m' /\ (forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m') /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m' (fr + 336)
           (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m' (ACtlCutP.fragb fr)
           (ACtlCutP.frrec cx j fr phi))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3)
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82154)
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
    { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_mono.
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of.
        eapply (A.Prog.Seg.F14F_on.f14_evt_dc_ro_F_on) with (sp := Kgetr regs3 2) (A := A)
          (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)) (L := fr + 336) (R := ACtlCutP.fragb fr)
          (vcmp := vcmp) (lo := sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K)
          (ls := A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j) (rs := ACtlCutP.frrec cx j fr phi);
          rewrite ?Esp.
        - exact A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on.
        - exact H9.
        - exact H10.
        - exact Hrr.
        - lia.
        - unfold ACtlCutP.fragb; lia.
        - exact H280.
        - exact H184.
        - exact H192.
        - exact HbL.
        - apply A.Prog.Seg.F13.t_FG_length.
        - exact HbR.
        - exact Hrlen.
        - exact Hmm.
        - exact Hroag.
        - exact HaL.
        - exact HaR.
        - apply Hfrapp; lia.
        - apply Hfrapp; lia.
        - apply Hfrapp; unfold ACtlCutP.fragb; lia.
        - apply Hfrapp; unfold ACtlCutP.fragb; lia.
        - left. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
        - left. unfold ACtlCutP.fragb, A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
        - exact Hstkc.
        - unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K, A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K.
          lia.
        - unfold A.AsanRT.HIGHMEM_BEG, A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
        - unfold A.AsanRT.APPMEM_END. lia.
        - exact Hcells.
        - (* the wrapper's region, the aligned shadow words of the two 72-byte records: both records lie in the
             owned class-6 frame [fr, fr + 4096), so the region is inside cut_shadow's (F) disjunct *)
          apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
          intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|].
          rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
          unfold A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R, A.Prog.sh_word_on.sh_word_on,
            A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, ACtlCutP.fragb in Ha.
          unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
          destruct Ha as [(_ & Ha) | (_ & Ha)]; Z.div_mod_to_equations; lia.
        - exact HB1.
        - exact HB2.
        - exact HB3.
        - exact HB4.
        - exact HB5.
        - apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
            unfold A.ACfn.LLVMF_STK; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
            unfold A.ACfn.LLVMF_STK; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
            unfold A.ACfn.LLVMF_STK; lia.
        - exact (A.ProgBridge.rng_bytes_RNG_W _).
        - apply A.ProgBridge.rng_of_visible. pose proof (A.ProgBridge.img_vis_W W3) as HI.
          unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in HI. exact HI.
        - apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
            unfold A.ACfn.LLVMF_STK, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ _ HAR Hin);
            rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ _ HAR Hin);
            rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096;
            unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ _ HAR Hin);
            rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096; unfold ACtlCutP.fragb; lia.
        - apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ _ HAR Hin);
            rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096;
            unfold ACtlCutP.fragb, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; Z.div_mod_to_equations; lia. }
      intros ms' Hp. cbv beta in Hp.
      destruct Hp as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m' &
        E & MU & WM & RO & ST & AC & SW & BL & BR).
      subst ms'. eexists _, m'. split; [reflexivity|].
      repeat (split; [first [reflexivity | exact (eq_sym H9)]|]).
      split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
      split; [exact AC|]. split; [exact SW|]. split; [exact BL | exact BR]. }
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
             (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    (* G5: the exit cut C_A82174_at at the run's end map R and memory m' *)
    intros ms' md' HQ0 Hhid Hsbm.
    destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K26 & K9 & K10 &
      K25 & MU & WM & RO' & ST' & AC' & SW' & TbL & TbR).
    subst ms'.
    rewrite Esp in MU, ST'.
    assert (Hhid' : forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) by exact Hhid.
    set (WR := [(sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K, sp)]) in MU.
    assert (Hout : forall x, (x < sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K \/ sp <= x) ->
                     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x).
    { intros x Hx. subst WR. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [lia | exact I]. }
    assert (Hlow : forall x, x < OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling ->
                     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x).
    { intros x Hx. apply Hout. left. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia. }
    assert (Hsh_all : forall x, A.AsanRT.in_shadow x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x).
    { intros x Hx. apply Hout. left. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
        A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *. lia. }
    assert (AW : A.AsanRTFacts.all_app WR).
    { subst WR. cbn [A.AsanRTFacts.all_app]. split; [|exact I]. intros a Ha.
      unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *. lia. }
    assert (MK : A.AsanRTFacts.meta_kept mem3 m') by exact (A.AsanRTFacts.munch_meta WR mem3 m' MU AW).
    assert (HR9' : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv in *; rewrite K9; exact H9).
    assert (Hsp2 : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite K2; exact Hspz).
    assert (Hq : forall a v, ACtlCutP.q64 mem3 a v -> (a + 8 <= sp - 4560 \/ sp <= a) ->
                   ACtlCutP.q64 m' a v).
    { intros a v Hqa Ha. apply (A.ACtlG.KitMem.kitmem_q64_munch WR mem3 m' a v Hqa MU). intros x Hx. apply Hout.
      unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia. }
    assert (Hbm : forall a bs, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 a bs ->
                    a + Z.of_nat (length bs) <= sp - 4560 ->
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs).
    { intros a bs Hb Ha. apply (A.ACtlG.KitMem.kitmem_bytes_munch WR mem3 m' a bs Hb MU). intros x Hx. apply Hout.
      unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia. }
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82174_at [Z.of_nat j])) R m' md') (POST cx)).
    apply (Hdc cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB).
    + (* journal: the wrapper wrote its window [sp - BCMP_WRAP_K, sp), inside the LLVMF stack window *)
      eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a => sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K <= a < sp).
      * exact HJ.
      * intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (MU x); [reflexivity|].
        subst WR. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [exact Hx | exact I].
      * destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk_split A.Img0.rsegs m'
                    (sp - A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K)
                    (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K) sp ST'
                    ltac:(unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K,
                            A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K; lia)) as (_ & ST2).
        apply (A.ACtlG.KitMem.kitmem_grows_munch_stk (Reusable.YA0n.w_H W3) mem3 m'
                 (sp - A.Prog.bcmp_wrap_c.BCMP_WRAP_K) sp MU ST2).
        unfold A.Prog.ImgBounds.IMG_HI, A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
      * exact Hhid'.
      * exact Hsbm.
      * intros a Ha. apply A.ACtlG.KitMem.kitmem_awr_win. unfold A.ACfn.LLVMF_STK, A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *.
        lia.
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82174_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|].
      rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split.
      { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [|exact K2|exact K3|exact K4|exact K8|exact K9
              |exact K19|exact K26].
        apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' WR HFRAC MU).
        - intros x Hx. apply Hout. right. lia.
        - intros x Hx. apply Hlow. lia.
        - intros x Hx. apply Hout. left.
          unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K,
            A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *.
          Z.div_mod_to_equations. lia. }
      split; [exact Hn|]. split; [exact Hj|].
      split.
      { destruct HHB as (Hpz & Hpa). split; [exact Hpz|].
        exact (A.ACtlG.KitMem.kitmem_addr_munch WR mem3 m' _ _ Hpa MU Hsh_all). }
      split.
      { apply (w4c_flsi_keep cx j fr regs3 R mem3 m' WR A HFLSI H9 ltac:(lia) ltac:(lia) K9 MU WM).
        - intros x Hx. apply Hout. right. lia.
        - intros x Hx. apply Hlow. unfold ACtlCutP.FRAME_BYTES in *. lia.
        - exact Hsh_all.
        - intros x Hx. apply Hlow. apply Hinp. exact Hx. }
      split.
      { destruct HLK as (Hj' & H21 & HOUR). split; [exact Hj'|].
        split; [unfold ACtlCut.rgv in *; rewrite K21; exact H21|].
        unfold ACtlCutP.OURb in *. apply Hbm; [exact HOUR|].
        rewrite A.Prog.SlotModel.OUR_length. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
      split.
      { unfold ACtlCutP.FLV, ACtlCutP.spill.
        split; [exists A; split; [exact HR9' | apply Hq; [exact H80 | lia]]|].
        split; [exists A; split; [exact HR9' | apply Hq; [exact H88 | lia]]|].
        split; [exists A; split; [exact HR9' | apply Hq; [exact H96 | lia]]|].
        split; [exists A; split; [exact HR9' | apply Hq; [exact H272 | lia]]|].
        split; [exists A; split; [exact HR9' | apply Hq; [exact H264 | lia]]|].
        intros Hrf. destruct (Hfcond mem3 HFGM Hrf) as (Hpp & Hpn).
        split; (apply Hq; [assumption | unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia]). }
      exists vcmp, A.
      split; [exact Hmm|].
      split.
      2:{ apply (A.Prog.Seg.F13.ifs2_keep gx fr j A regs3 R mem3 m' WR HIFS2 H9 ltac:(lia) ltac:(lia) K9 MU MK).
          - intros x Hx. apply Hlow. lia.
          - intros x Hx. apply Hout. right. lia.
          - intros x Hx. apply Hlow. lia. }
      unfold ACtlCutP.f14_tail.
      split; [exact HR9'|].
      split; [exact K25|].
      split; [exact K10|].
      split; [exact HAb|].
      split; [lia|].
      split; [exact Hv280s|].
      split; [exact Hphifr|].
      split; [rewrite Hsp2; rewrite Hspz in Hphisep; exact Hphisep|].
      split; [rewrite Hsp2; exact ST'|].
      split; [apply Hq; [exact H184 | lia]|].
      split; [apply Hq; [exact H192 | lia]|].
      split; [apply Hq; [exact H280 | lia]|].
      split; [exact TbL|].
      split; [exact (A.ACtlG.KitMem.kitmem_addr_munch WR mem3 m' _ _ HaL MU Hsh_all)|].
      split; [exact TbR|].
      split; [exact (A.ACtlG.KitMem.kitmem_addr_munch WR mem3 m' _ _ HaR MU Hsh_all)|].
      split; [apply Hbm; [exact HB1 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8;
                         unfold A.Prog.bcmp_wrap_c.REAL_BCMP, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; cbn; lia]|].
      split; [apply Hbm; [exact HB2 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8;
                         unfold A.Prog.bcmp_wrap_c.REAL_MEMCMP, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; cbn; lia]|].
      split; [apply Hbm; [exact HB3 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8;
                         unfold A.Prog.bcmp_wrap_c.GOT_CF, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; cbn; lia]|].
      split; [apply Hbm; [exact HB4 | unfold A.Prog.bcmp_wrap_c.CF, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; cbn; lia]|].
      split; [apply Hbm; [exact HB5 | unfold A.Prog.bcmp_wrap_c.CF, A.Prog.bcmp_wrap_c.BCMP_WRAP_K; cbn; lia]|].
      split.
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport; [exact Hc256 | exact MU | exact WM |].
        subst WR. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.disjoint_from]. split; [right; lia | exact I]. }
      split.
      { pose proof (A.Prog.Seg.F13.frrec_length gx j fr phi) as Hreclen.
        change (length (A.Prog.SlotModel.fg_next (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                  (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) (ACtlCutP.frcl cx j fr phi)) = 72%nat) in Hreclen.
        revert HFGM Hreclen. destruct (ACtlCutP.frcl cx j fr phi);
          cbn [A.Prog.reac_ctrl_identity_fragment_c.fg_mem A.Prog.SlotModel.fg_next]; intros HFGM0 Hreclen.
        - exact I.
        - exact I.
        - apply Hbm; [exact HFGM0 | rewrite Hreclen; unfold ACtlCutP.fragb in *; lia].
        - apply Hbm; [exact HFGM0 | rewrite Hreclen; unfold ACtlCutP.fragb in *; lia].
        - apply Hbm; [exact HFGM0 | rewrite Hreclen; unfold ACtlCutP.fragb in *; lia].
        - destruct HFGM0 as (Hf0 & Hpa0 & Hpp0 & Hpn0).
          split; [apply Hbm; [exact Hf0 | rewrite Hreclen; unfold ACtlCutP.fragb in *; lia]|].
          split; [apply Hbm; [exact Hpa0 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le2; cbn; lia]|].
          split; [apply Hbm; [exact Hpp0 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; cbn; lia]|].
          apply Hbm; [exact Hpn0 | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; cbn; lia]. }
      apply (A.Prog.Seg.F13.f16carry_keep gx j fr phi A regs3 R mem3 m' WR HCAR MU AW H9 ltac:(lia)
               ltac:(unfold A.Prog.SlotInv.FRAME_BYTES; lia) ltac:(lia) K9 K18 K20 K22 K23 K24).
      * intros x Hx. apply Hout. right. lia.
      * intros Hl x Hx. change (50 <= ACtlCutP.flen cx j) in Hl.
        change (phi <= x < phi + ACtlCutP.flen cx j) in Hx.
        apply Hlow. pose proof (Hrq (ACtlCutP.flen cx j) ltac:(lia)). lia.
      * intros x Hx. apply Hlow. lia.
      * intros x Hx. apply Hlow. lia.
      * intros x Hx. apply Hlow. lia.
    + (* ctl_rt_C after the call: asan_cells / ro_agree from the wrapper's post; the two regions do not move
         (same ly3 S3) and cross the call by the post's forall-P transport *)
      exact (conj AC' (conj (SW' _ Hcut) (conj (SW' _ Himg) RO'))).
  - (* ===== [A+280] <> 0: the branch at 0x82160 is taken, exit cut C_A82178_at (Seg/F14.v:785-893) ===== *)
    assert (HRUN : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF A.Img0.rsegs
                     (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (fun ms' => exists R,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82178)
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
         Kgetr R 2 = Kgetr regs3 2 /\
         Kgetr R 3 = Kgetr regs3 3 /\
         Kgetr R 4 = Kgetr regs3 4 /\
         Kgetr R 8 = Kgetr regs3 8 /\
         Kgetr R 18 = Kgetr regs3 18 /\
         Kgetr R 19 = Kgetr regs3 19 /\
         Kgetr R 20 = Kgetr regs3 20 /\
         Kgetr R 21 = Kgetr regs3 21 /\
         Kgetr R 22 = Kgetr regs3 22 /\
         Kgetr R 23 = Kgetr regs3 23 /\
         Kgetr R 24 = Kgetr regs3 24 /\
         Kgetr R 26 = Kgetr regs3 26 /\
         Kgetr R 9 = Kgetr regs3 9 /\ Kgetr R 10 = Z_to_bv 64 v280 /\
         Kgetr R 25 = Z_to_bv 64 (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3)
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82154)
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
    { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_mono.
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of.
        eapply (A.Prog.Seg.F14F.f14_evt_e0_F) with (A := A) (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
          (v280 := v280).
        - exact H9.
        - exact H10.
        - exact Hrr.
        - exact Hv280b.
        - exact Hvn.
        - exact H280.
        - apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ);
            unfold A.ACfn.LLVMF_STK; lia. }
      intros ms' E. cbv beta in E. subst ms'. eexists. split; [reflexivity|].
      repeat (split; [first [reflexivity | exact (eq_sym H9)]|]). reflexivity. }
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
             (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    (* G5: the exit cut C_A82178_at at the run's end map R, the same memory *)
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & Ems & K2 & K3 & K4 & K8 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K26 & K9 & K10 & K25).
    subst ms'.
    assert (HR9' : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv in *; rewrite K9; exact H9).
    assert (Hsp2 : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ; rewrite K2; exact Hspz).
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82178_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (He0 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82178_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|].
      rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4c_flsi_move cx j fr regs3 R mem3 HFLSI K9)|].
      split; [exact (A.Prog.Seg.F15.lk_regs gx fr j regs3 R mem3 HLK K21)|].
      split.
      { unfold ACtlCutP.FLV, ACtlCutP.spill.
        split; [exists A; split; [exact HR9' | exact H80]|].
        split; [exists A; split; [exact HR9' | exact H88]|].
        split; [exists A; split; [exact HR9' | exact H96]|].
        split; [exists A; split; [exact HR9' | exact H272]|].
        split; [exists A; split; [exact HR9' | exact H264]|].
        exact (Hfcond mem3 HFGM). }
      split; [|exact (A.Prog.Seg.F13.ifs2_regs gx fr j regs3 R mem3 HIFS2 K9)].
      exists A, v280, v280.
      unfold ACtlCutP.f14_tail.
      split; [exact HR9'|].
      split; [exact K25|].
      split; [exact K10|].
      split; [exact HAb|].
      split; [exact Hv280b|].
      split; [exact Hv280s|].
      split; [exact Hphifr|].
      split; [rewrite Hsp2; rewrite Hspz in Hphisep; exact Hphisep|].
      split; [rewrite Hsp2; exact Hstkc|].
      split; [exact H184|]. split; [exact H192|]. split; [exact H280|].
      split; [exact HbL|]. split; [exact HaL|]. split; [exact HbR|]. split; [exact HaR|].
      split; [exact HB1|]. split; [exact HB2|]. split; [exact HB3|]. split; [exact HB4|]. split; [exact HB5|].
      split; [exact Hc256|]. split; [exact HFGM|].
      exact (A.Prog.Seg.F15.f16carry_regs gx j fr phi A regs3 R mem3 HCAR K9 K18 K20 K22 K23 K24).
    + exact Hrt.
Qed.

End GlueF14.
