(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e2.v, with its module paths and module names changed; 4090 of its 4391 lines of code are new or changed and 2544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4c.v, with its module names, addresses and numbers changed; 602 of its 682 lines of code are new or changed and 4311 lines of the source are left out. *)
(* lib/A/ACtlG/F26.v -- GLUE for stage seg_F26 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:824).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F26 : forall POST (j : nat),
       CF POST (ix_cut C_A82604_at [Z.of_nat j]) -> CF POST (ix_cut C_A825f4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F26.  Segment F26 is 0x825f4 -> 0x82604 (Seg/F26.v:1-6): mv s4,a0; mv a0,s6; li a1,0;
   jal reac_ports_unknown@0x87848, landing at 0x82604.

   ROUTE (a) -- NO LIFT, NO SPLIT (a Theorem Labs lane, 2026-10-29 "WHICH ROUTE APPLIES IS DECIDED BY YOUR SEGMENT'S
   _F TEXT").  The run lifted is Seg/F26Fon.v's f26_evt_F_on (this lane's route (C) twin of Seg/F26F.v's
   f26_evt_F, with no shadow premise); it takes reac_ports_unknown_c.reac_ports_unknown_contract_F_on AS A PREMISE
   and its run SPANS the call, so this file supplies that premise with the PROVED contract
   (A/Prog/reac_ports_unknownF.v reac_ports_unknown_F_holds_on) and lifts the WHOLE run once with
   Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  It cites NO <f>_SRr_at: the caller
   obligation here is the CONTRACT's premises (which f26_evt_F_on states), not a lift's premises.

   ROUTE (C) (a Theorem Labs lane 1502cba0417 / 1899bed1aee): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3, the
   runtime cells, shadow_rw_on over cut_shadow B ly3 S3 and over img_shadow, and ro_agree.  The run needs no shadow
   byte (its callee's _on contract dropped the premise), so the entry's two regions are only carried to the exit cut,
   which has the same state (ly3, S3): each by A.ShadowRwOnT.shadow_rw_on_kept across the run's write set, the
   callee's stack window, which is app memory and so moves no shadow byte (AsanRTFacts.munch_meta).

   THE PROOF, step by step
   G1  unfold the entry cut: ix_cut's index equation, then C_A825f4_at (ACtlCutP.v:2634-2644) = FRAC + b7_body
       with the tail (s9 = t_rp, a0 = t_unk, PORTS, FIRSTb, two addressable ranges).
   G2  the run's premises from the body and from VISIBLE state.  The one geometric fact of this stage:
         fr + FRAME_BYTES <= alloc_ceiling <= ly_stk_lo (c_ly cx) <= c_sp cx - LLVMF_STK < sp - 16,
       from YCbq.frames_bounds on the journal's own frame (6, c_fpos cx), the shell's frame law, layout_le's
       ly_F equation and the journal's astk_ok, with FRAC's c_sp cx - 4096 < sp.  So the callee's 16-byte
       stack window [sp - 16, sp) lies ABOVE every byte the cut body reads except the spill area [A, A + 416)
       and the saved registers at [c_sp cx - 104, c_sp cx), which lie at or above sp (FRAC: sp <= A,
       A + 416 <= c_sp cx).  Every transport below is that disjointness.
   G3  register maps: ProgBridge.cfg_at_MS turns the cut's cfg_at into MState.MS, and
       Reusable.YA0nR.SRr_xregs_eqv moves the WALK from the cut's map regs3 to the run's canonical
       Regs6ss.mkR_of regs3.
   G4  lift: ProgBridge.fevt_of_evtF + ProgBridge.tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid at
       RNG := ProgBridge.RNG_W (w_H W3); fp_avoids by ProgBridge.fp_avoids_RNG_W, each ExecF.rng premise by
       ProgBridge.rng_of_visible from a range_visible fact (ProgWorldVisWin.win_vis for the stack window,
       ProgBridge.rt_vis_W for GOT_CELL_K / CELL_K, ProgWorldVisHeap.heap_vis / heap_sh_vis for the 20 block
       bytes and their shadow).
   G5  the continuation: the end state is MS R .. 0x82604 .. m' with R the run's own end map, so the exit cut
       is taken at regs := R.  The journal crosses the write with Reusable.YCbq.ajournal_exec at
       Wr := [sp - 16, sp) (awr_byte's stack case); the body's memory conjuncts transport with the b7g_*
       helpers below; ctl_rt_C with AsanRTFacts.asan_cells_kept, two ShadowRwOnT.shadow_rw_on_kept and b7g_ro.

   SECTION HYPOTHESES (exact text in the file; why)
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record (YCbq.v:207), as ACtl.v:183 has it.
   No other Section hypothesis.  The kit's image facts are CITED from lib/A/ACtlG/Kit.v (glue base
   46eb24cd4b3, Kit.v blob 7e164a09a73, which builds): A.ACtlG.Kit.kit_wx (SRr_fevt_hid's wx_segs_nowrap) and
   A.ACtlG.Kit.kit_segs_low (ajournal_exec's image placement).  On the first base (eb89fed7fac, commit
   28c54b3cbdd) they were named Section hypotheses with the kit's exact text, because Kit.v did not compile
   there.  kit_frac_move is NOT used: this stage rebuilds FRAC from its own destructuring (the run keeps
   2 3 4 8 9 19 26).  kit_RNG0 is NOT used: the run reads and writes memory, so the footprint is RNG_W.

   CLOSURE: every Require below is qualified; no statement of this file names a frame-route identifier
   (A.Contract and A/Prog/Seg/F24.v are named only inside proofs closed by Qed, which a Theorem Labs lane's 23:54Z ruling
   allows).  A module with a second copy under the lib root (a Theorem Labs lane 05:27Z) is Required by its FULL path,
   not by a `From lib Require` suffix: core Reusable.YK11 / YK1b / YM05 / YO09 / YI16 (whose lib/A/Reusable
   copies the _F closure also loads) and Lib.Mem / Frame / PropExec / MState (copies on disk under
   lib/{A,B}/Bz/Lib and lib/AZ/Lib (not in this delivery)).  The body names YK11 / YM05 / YO09 as lib.Reusable.<X> and the other core
   Reusable modules through the local alias block below.

   SHADOWED NAMES: getr / mkst / seg_rom are lib.Reusable.YK11-qualified and cfg_at Reusable.YG0d-qualified
   (through the local Reusable alias block) everywhere.

   BUILD STATE: type-checks on a working branch 1899bed1aee (a working branch); its build of
   record (cbrec) is reported by the lane, not here.  No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0n Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.SlotModel A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_unknown_c A.Prog.reac_ports_unknownF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.B7Cuts A.Prog.Seg.F24 A.Prog.Seg.F26Fon.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Contract A.Reusable.YP09 A.MemNorm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.

(* The CORE's lib/Reusable modules that have NO second copy, bound once under the short name this file uses.  The
   three that do (YK11, YM05, YO09: ctrl's ASan-side copies lib/A/Reusable/<X>.v are in the _F closure, with
   DIFFERENT constants -- the trap glue-pattern.md section 6 names) are written lib.Reusable.<X>.<name> everywhere,
   which names the core copy only (ctrlgate's DUP rule reads a partial `Reusable.YK11` as ambiguous). *)
Module Reusable.
  Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
  Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
  Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
  Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
  Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
  Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
  Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
  Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
  Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
  Module YG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
  Module YI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
  Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
  Module YK06 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK06.
  Module YK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
End Reusable.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. The transport helpers of the b7 cut bodies (ACtlCutP.v's FLSI / B7K / HB bundles), shared by the three
   stages of this lane (F24, F25, F26).  They are stated over an ABSTRACT "kept range" predicate KEEP, so each
   stage instantiates it with its own write set: F26 and F24 with Lib.Frame.disjoint_from W, F25 with that
   plus its shadow-byte side condition.  None of them is a Kit helper and none is copied from Kit.v. *)

Definition b7g_tr (KEEP : Z -> Z -> Prop) (m m' : word -> option byte) (regs regs' : bvmap 5 word) : Prop :=
  (forall p n p' n', KEEP p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> KEEP p' n') /\
  (forall a bs n, KEEP a n -> Z.of_nat (length bs) = n ->
     Lib.Mem.bytes_at segs m a bs -> Lib.Mem.bytes_at segs m' a bs) /\
  (forall p n, KEEP p n -> A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n) /\
  (forall off v, 0 <= off -> off + 8 <= 416 ->
     ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).

Lemma b7g_sub : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall p n p' n', KEEP p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> KEEP p' n'.
Proof. intros KEEP m m' regs regs' (H & _ & _ & _). exact H. Qed.

Lemma b7g_by : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall a bs n, KEEP a n -> Z.of_nat (length bs) = n ->
  Lib.Mem.bytes_at segs m a bs -> Lib.Mem.bytes_at segs m' a bs.
Proof. intros KEEP m m' regs regs' (_ & H & _ & _). exact H. Qed.

Lemma b7g_ad : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall p n, KEEP p n -> A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof. intros KEEP m m' regs regs' (_ & _ & H & _). exact H. Qed.

Lemma b7g_sp : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall off v, 0 <= off -> off + 8 <= 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof. intros KEEP m m' regs regs' (_ & _ & _ & H). exact H. Qed.

Lemma b7g_q64 : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall a v, KEEP a 8 -> ACtlCutP.q64 m a v -> ACtlCutP.q64 m' a v.
Proof.
  intros KEEP m m' regs regs' TR a v HK H. unfold ACtlCutP.q64 in *.
  apply (b7g_by KEEP m m' regs regs' TR a _ 8 HK); [rewrite Lib.Mem.length_le8; reflexivity | exact H].
Qed.

Lemma b7g_u32 : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall a v, KEEP a 4 -> ACtlCutP.u32 m a v -> ACtlCutP.u32 m' a v.
Proof.
  intros KEEP m m' regs regs' TR a v HK H. unfold ACtlCutP.u32 in *.
  apply (b7g_by KEEP m m' regs regs' TR a _ 4 HK); [rewrite Lib.Mem.length_le4; reflexivity | exact H].
Qed.

Lemma b7g_b8 : forall KEEP m m' regs regs', b7g_tr KEEP m m' regs regs' ->
  forall a v, KEEP a 1 -> ACtlCutP.b8 m a v -> ACtlCutP.b8 m' a v.
Proof.
  intros KEEP m m' regs regs' TR a v HK H. unfold ACtlCutP.b8 in *.
  apply (b7g_by KEEP m m' regs regs' TR a _ 1 HK); [reflexivity | exact H].
Qed.

(* The frame-data window every b7 bundle reads: [fr + 2624, fr + FRAME_BYTES). *)
Lemma b7g_frame_sub : forall KEEP m m' regs regs' fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  forall a n, 2624 <= a -> 0 <= n -> a + n <= ACtlCutP.FRAME_BYTES -> KEEP (fr + a) n.
Proof.
  intros KEEP m m' regs regs' fr TR KF a n Ha Hn Han.
  apply (b7g_sub KEEP m m' regs regs' TR (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624)); [exact KF | lia | lia | lia].
Qed.

(* ---- PRO (ACtlCutP.v:466-475) ---- *)
Lemma b7g_PRO : forall KEEP m m' regs regs' cx fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  KEEP (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  ACtlCutP.PRO cx fr regs m -> ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros KEEP m m' regs regs' cx fr TR KF KI Hlen
    (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 & P272 & P32).
  assert (K2624 : KEEP (fr + 2624) 6)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2624 6); unfold ACtlCutP.FRAME_BYTES; lia).
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P40] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P120] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P136] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P160] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P168] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P176] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P208] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P248] |].
  split; [exact (b7g_ad KEEP m m' regs regs' TR _ _ K2624 Pad) |].
  split; [exact (b7g_by KEEP m m' regs regs' TR _ _ _ KI Hlen Pin) |].
  split; [intros Hn; exact (b7g_ad KEEP m m' regs regs' TR _ _ KI (Pg Hn)) |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P184] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P256] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P264] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P272] |].
  apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact P32].
Qed.

(* ---- FLC (ACtlCutP.v:668-674) ---- *)
Lemma b7g_FLC : forall KEEP m m' regs regs' fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  ACtlCutP.FLC fr regs m -> ACtlCutP.FLC fr regs' m'.
Proof.
  intros KEEP m m' regs regs' fr TR KF
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cad1 & Cad2 & C72 & C64 & C56 & C48).
  assert (Kfrag : KEEP (ACtlCutP.fragb fr) 72).
  { unfold ACtlCutP.fragb.
    apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2768 72); unfold ACtlCutP.FRAME_BYTES; lia. }
  assert (K2688 : KEEP (fr + 2688) 38)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2688 38); unfold ACtlCutP.FRAME_BYTES; lia).
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C256] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C184] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C192] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C80] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C88] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C96] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C272] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C264] |].
  split; [exact (b7g_ad KEEP m m' regs regs' TR _ _ Kfrag Cad1) |].
  split; [exact (b7g_ad KEEP m m' regs regs' TR _ _ K2688 Cad2) |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C72] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C64] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C56] |].
  apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact C48].
Qed.

(* ---- FLSH (ACtlCutP.v:662-665): the frame window `stk` is the caller's own fact. ---- *)
Lemma b7g_FLSH : forall KEEP m m' regs regs' cx j fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  KEEP (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLSH cx j fr regs m -> ACtlCutP.FLSH cx j fr regs' m'.
Proof.
  intros KEEP m m' regs regs' cx j fr TR KF KI Hlen HSTK (HPRO & S128 & Hstk & S144 & Had).
  assert (K2691 : KEEP (fr + 2691) 17)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2691 17); unfold ACtlCutP.FRAME_BYTES; lia).
  split; [exact (b7g_PRO KEEP m m' regs regs' cx fr TR KF KI Hlen HPRO) |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S128] |].
  split; [exact HSTK |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S144] |].
  exact (b7g_ad KEEP m m' regs regs' TR _ _ K2691 Had).
Qed.

(* ---- f1_IN (ACtlCutP.v:658-659) ---- *)
Lemma b7g_f1_IN : forall KEEP m m' regs regs' cx, b7g_tr KEEP m m' regs regs' ->
  KEEP (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  ACtlCutP.f1_IN cx m -> ACtlCutP.f1_IN cx m'.
Proof.
  intros KEEP m m' regs regs' cx TR KI Hlen (Had & Hby).
  split; [exact (b7g_ad KEEP m m' regs regs' TR _ _ KI Had)
         | exact (b7g_by KEEP m m' regs regs' TR _ _ _ KI Hlen Hby)].
Qed.

(* ---- FLSI (ACtlCutP.v:677-680) ---- *)
Lemma b7g_FLSI : forall KEEP m m' regs regs' cx j fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  KEEP (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx ->
  Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES) ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros KEEP m m' regs regs' cx j fr TR KF KI Hlen HSTK (HFLSH & S216 & S224 & S248 & HIN & HFLC).
  split; [exact (b7g_FLSH KEEP m m' regs regs' cx j fr TR KF KI Hlen HSTK HFLSH) |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S216] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S224] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S248] |].
  split; [exact (b7g_f1_IN KEEP m m' regs regs' cx TR KI Hlen HIN) |].
  exact (b7g_FLC KEEP m m' regs regs' fr TR KF HFLC).
Qed.

(* ---- IFS (ACtlCutP.v:540-553): the identity record, the fragment record and the FIRST state. ---- *)
Lemma b7g_IFS : forall KEEP m m' regs regs' cx j fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  ACtlCutP.IFS cx fr j regs m -> ACtlCutP.IFS cx fr j regs' m'.
Proof.
  intros KEEP m m' regs regs' cx j fr TR KF ((HID & Hidok) & (HFG & Hfgok) & (S104 & S112 & Hbody & Had & HFI)).
  assert (K2688 : KEEP (fr + 2688) 38)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2688 38); unfold ACtlCutP.FRAME_BYTES; lia).
  assert (K2768 : KEEP (fr + 2768) 72)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2768 72); unfold ACtlCutP.FRAME_BYTES; lia).
  assert (K2880 : KEEP (fr + 2880) 35)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2880 35); unfold ACtlCutP.FRAME_BYTES; lia).
  pose proof (A.Prog.Seg.B7Cuts.b7_fsbody_len (ACtlCut.c_in cx) j) as Hbl.
  split.
  { split; [| exact Hidok]. unfold ACtlCutP.IDBe in *.
    apply (b7g_by KEEP m m' regs regs' TR _ _ 38 K2688); [| exact HID].
    rewrite (A.Prog.Seg.B7Cuts.b7_tID_len (ACtlCut.c_in cx) j). reflexivity. }
  split.
  { split; [| exact Hfgok]. unfold ACtlCutP.FGBe in *.
    apply (b7g_by KEEP m m' regs regs' TR _ _ 72 K2768); [| exact HFG].
    rewrite (A.Prog.Seg.B7Cuts.b7_tFG_len (ACtlCut.c_in cx) j). reflexivity. }
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S104] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S112] |].
  split.
  { apply (b7g_by KEEP m m' regs regs' TR _ _
             (Z.of_nat (length (A.Prog.SlotModel.fs_body (A.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)))));
      [| reflexivity | exact Hbody].
    apply (b7g_sub KEEP m m' regs regs' TR (fr + 2880) 35); [exact K2880 | lia | lia | lia]. }
  split; [exact (b7g_ad KEEP m m' regs regs' TR _ _ K2880 Had) | exact HFI].
Qed.

(* ---- LK (ACtlCutP.v:556-557) ---- *)
Lemma b7g_LK : forall KEEP m m' regs regs' cx j fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  lib.Reusable.YK11.getr regs' 21 = lib.Reusable.YK11.getr regs 21 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros KEEP m m' regs regs' cx j fr TR KF E21 (Hj & R21 & HOUR).
  assert (K2624 : KEEP (fr + 2624) 6)
    by (apply (b7g_frame_sub KEEP m m' regs regs' fr TR KF 2624 6); unfold ACtlCutP.FRAME_BYTES; lia).
  split; [exact Hj |].
  split; [unfold ACtlCut.rgv in *; etransitivity; [exact E21 | exact R21] |].
  unfold ACtlCutP.OURb in *.
  apply (b7g_by KEEP m m' regs regs' TR _ _ 6 K2624); [| exact HOUR].
  rewrite (A.Prog.SlotModel.OUR_length (ACtlCut.c_in cx)). reflexivity.
Qed.

(* ---- B7K (ACtlCutP.v:941-950) ---- *)
Lemma b7g_B7K : forall KEEP m m' regs regs' cx j phi fr, b7g_tr KEEP m m' regs regs' ->
  KEEP (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624) ->
  KEEP phi (ACtlCutP.flen cx j) ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 21 = lib.Reusable.YK11.getr regs 21 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  ACtlCutP.B7K cx j phi fr regs m -> ACtlCutP.B7K cx j phi fr regs' m'.
Proof.
  intros KEEP m m' regs regs' cx j phi fr TR KF KB E18 E21 E22 E23 E24
    (HLK & R23 & R22 & Hphi0 & Hphi2 & Hflen & Hblk & S280 & R24 & R18 & S152 & Hg & Hphib & Hlenphi & HLT &
     (SP136 & SP120 & SP176)).
  split; [exact (b7g_LK KEEP m m' regs regs' cx j fr TR KF E21 HLK) |].
  split; [unfold ACtlCut.rgv in *; etransitivity; [exact E23 | exact R23] |].
  split; [unfold ACtlCut.rgv in *; etransitivity; [exact E22 | exact R22] |].
  split; [exact Hphi0 |]. split; [exact Hphi2 |]. split; [exact Hflen |].
  split.
  { apply (b7g_by KEEP m m' regs regs' TR _ _ 32); [| | exact Hblk].
    - apply (b7g_sub KEEP m m' regs regs' TR phi (ACtlCutP.flen cx j)); [exact KB | lia | lia | lia].
    - rewrite (A.Prog.Seg.B7Cuts.b7_tblk_len (ACtlCut.c_in cx) j). reflexivity. }
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S280] |].
  split; [unfold ACtlCut.rgv in *; etransitivity; [exact E24 | exact R24] |].
  split; [unfold ACtlCut.rgv in *; etransitivity; [exact E18 | exact R18] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact S152] |].
  split.
  { apply (b7g_by KEEP m m' regs regs' TR _ _ 50); [| | exact Hg].
    - apply (b7g_sub KEEP m m' regs regs' TR phi (ACtlCutP.flen cx j)); [exact KB | lia | lia | lia].
    - rewrite (A.Prog.Seg.B7Cuts.b7_tg_len (ACtlCut.c_in cx) j). reflexivity. }
  split.
  { apply (b7g_by KEEP m m' regs regs' TR _ _
             (Z.of_nat (length (A.Prog.SlotModel.t_phi (ACtlCut.c_in cx) j)))); [| reflexivity | exact Hphib].
    apply (b7g_sub KEEP m m' regs regs' TR phi (ACtlCutP.flen cx j)); [exact KB | lia | lia | lia]. }
  split; [exact Hlenphi |].
  split; [exact (b7g_IFS KEEP m m' regs regs' cx (S j) fr TR KF HLT) |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact SP136] |].
  split; [apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact SP120] |].
  apply (b7g_sp KEEP m m' regs regs' TR); [lia | lia | exact SP176].
Qed.

(* ---- HB (ACtlCutP.v:442-443) ---- *)
Lemma b7g_HB : forall KEEP m m' regs regs' phi len, b7g_tr KEEP m m' regs regs' ->
  KEEP phi (A.ACtlK.a_size len) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof.
  intros KEEP m m' regs regs' phi len TR KH (Hnz & Had).
  split; [exact Hnz | exact (b7g_ad KEEP m m' regs regs' TR _ _ KH Had)].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   0b. Three facts about the write set of a run of this region, used to build b7g_tr and ctl_rt. *)

(* A spill survives a run that keeps s1 and misses the spill area [A, A + 416). *)
Lemma b7g_spill_keep : forall (W : list Lib.Frame.ivl) (m m' : word -> option byte)
    (regs regs' : bvmap 5 word) (Aa off v : Z),
  lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 Aa -> 0 <= Aa -> Aa + 416 <= 2 ^ 64 ->
  0 <= off -> off + 8 <= 416 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  Lib.Frame.munch W m m' -> Lib.Frame.disjoint_from W Aa 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros W m m' regs regs' Aa off v H9 HA0 HA Ho0 Ho E9 MU DJ (A1 & H9' & Hq).
  unfold ACtlCut.rgv in H9'. unfold ACtlCutP.q64 in Hq.
  assert (EA : A1 = Aa).
  { pose proof Hq as (Hb0 & Hb1 & _). rewrite Lib.Mem.length_le8 in Hb1.
    assert (Ebv : Z_to_bv 64 Aa = Z_to_bv 64 A1)
      by (etransitivity; [symmetry; exact H9 | exact H9']).
    apply (f_equal (@bv_unsigned 64)) in Ebv.
    rewrite !Lib.MState.unsigned_lit_wrap in Ebv.
    change (Z.of_nat 8) with 8 in Hb1. Z.div_mod_to_equations. lia. }
  subst A1. exists Aa. split; [unfold ACtlCut.rgv; etransitivity; [exact E9 | exact H9] |].
  unfold ACtlCutP.q64.
  apply (Lib.Frame.bytes_at_transport segs W m m' (Aa + off) _ Hq MU).
  rewrite Lib.Mem.length_le8.
  apply (A.AsanRTFacts.disjoint_from_sub W Aa 416); [exact DJ | lia | lia].
Qed.

(* addressable survives a run whose write set is app memory (its shadow bytes are untouched). *)
Lemma b7g_addr_app : forall (W : list Lib.Frame.ivl) (m m' : word -> option byte) (p n : Z),
  Lib.Frame.munch W m m' -> A.AsanRTFacts.all_app W ->
  A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n.
Proof.
  intros W m m' p n MU AW H.
  apply (A.AsanRTFacts.addressable_kept m m' p n H).
  exact (A.AsanRTFacts.munch_meta W m m' MU AW).
Qed.

(* ro_agree survives a run that writes only above the image. *)
Lemma b7g_ro : forall (W : list Lib.Frame.ivl) (m m' : word -> option byte),
  A.ACtlK.ro_agree_at m -> Lib.Frame.munch W m m' ->
  (forall lo hi, In (lo, hi) W -> A.Prog.ImgBounds.IMG_HI <= lo) -> A.ACtlK.ro_agree_at m'.
Proof.
  intros W m m' HRO MU HW a Ha.
  assert (Hlt : bv_unsigned a < A.Prog.ImgBounds.IMG_HI).
  { unfold Lib.Mem.ro_addr in Ha.
    destruct (find_segment A.Img0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [| discriminate Ha].
    pose proof (A.Prog.Seg.F24.b7_seg_lt _ s E) as Hs.
    unfold A.Contract.GT in Hs. unfold A.Prog.ImgBounds.IMG_HI. lia. }
  assert (Hout : Lib.Frame.outside W (bv_unsigned a)).
  { clear -HW Hlt. induction W as [| [lo hi] W IH]; cbn [Lib.Frame.outside]; [exact I |].
    split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia |].
    apply IH. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin. }
  unfold A.ACtlK.ro_agree_at in HRO. unfold Lib.Mem.mrd in *.
  rewrite (MU a Hout). exact (HRO a Ha).
Qed.

(* A byte present at or above the image stays present across a run that keeps writability. *)
Lemma b7g_grow : forall (m m' : word -> option byte) (x : word),
  A.Prog.ImgBounds.IMG_HI <= bv_unsigned x -> Lib.Frame.wmono A.Img0.rsegs m m' -> m x <> None -> m' x <> None.
Proof.
  intros m m' x Hgt WM Hx.
  pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  assert (Hgt' : A.Contract.GT <= bv_unsigned x) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Hgt; lia).
  destruct (m x) as [b |] eqn:E; [| exfalso; exact (Hx eq_refl)].
  assert (Hmrd : Lib.Mem.mrd A.Img0.rsegs m (Lib.Mem.wa (bv_unsigned x)) = Some b).
  { unfold Lib.Mem.mrd, Lib.Mem.wa. rewrite Z_to_bv_bv_unsigned, E. reflexivity. }
  assert (HW : A.Reusable.YP09.writable_at A.Img0.rsegs m (bv_unsigned x))
    by exact (A.Prog.Seg.F24.b7_hi_wr m (bv_unsigned x) Hgt' Hr (ex_intro _ b Hmrd)).
  unfold A.Reusable.YP09.writable_at in HW. rewrite Z_to_bv_bv_unsigned in HW.
  pose proof (WM x HW) as HW'.
  assert (HW2 : A.Reusable.YP09.writable_at A.Img0.rsegs m' (bv_unsigned x))
    by (unfold A.Reusable.YP09.writable_at; rewrite Z_to_bv_bv_unsigned; exact HW').
  destruct (A.Prog.Seg.F24.b7_hi_rd m' (bv_unsigned x) Hgt' Hr HW2) as (b' & Hb').
  unfold Lib.Mem.mrd, Lib.Mem.wa in Hb'. rewrite Z_to_bv_bv_unsigned in Hb'.
  intros Heq. rewrite Heq in Hb'.
  rewrite (A.MemNorm.seg_rom_unmapped A.Img0.rsegs x) in Hb'; [discriminate Hb' |].
  exact (A.Prog.Seg.F24.b7_find_none (bv_unsigned x) Hgt').
Qed.

(* The two shadow maps agree: AsanRT's a / 8 + ASAN_K is the core's SHADOW_OFF + a / 8. *)
Lemma b7g_sh_eq : forall x, A.AsanRT.shadow_addr x = Reusable.YG0f.shadow_addr x.
Proof.
  intros x. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, Reusable.YG0f.shadow_addr,
    Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* A byte of an owned frame is app memory: the core's in_app of the frame (AR_frames_law, YG0d.v:450)
   lands in one of AsanRT's two app bands (kLowShadowBeg < LOWMEM_END, kHighMemBeg = HIGHMEM_BEG,
   ASAN_CEIL < APPMEM_END). *)
Lemma b7g_frame_app : forall {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}
    (B : Reusable.YG0f.asyms) ly S (W : Reusable.YA0n.world segs) mem md cid pos a,
  Reusable.YG0d.AR_laws segs B -> Reusable.YG0n.AR segs B ly S W mem md ->
  In (cid, pos) (Reusable.YG01.frames S) ->
  Reusable.YG0f.frame_addr ly cid pos <= a <
    Reusable.YG0f.frame_addr ly cid pos + Reusable.YG00.fs_frame_bytes cid ->
  A.AsanRT.app_mem a.
Proof.
  intros fx rc B ly S W mem md cid pos a LAWS HAR Hin Ha.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Happ.
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
  destruct Happ as (H4096 & [HL | (HH1 & HH2)]); [left | right]; lia.
Qed.

(* The frame-above-image bound is NOT proved here: F25 and F24 cite a Theorem Labs lane's
   A.ProgWorld.ctl_frame_above_img_stmt, proved premise-free by A.ProgWorld_Fs.ctl_frame_above_img.  The local copy
   b7g_frame_GT (commits 3a0d3ca9bdf .. a65aa4b8dfd) is deleted. *)

(* One writable byte at or above the image, from the core's apresent. *)
Lemma b7g_wr1 : forall (m : word -> option byte) (a : Z),
  A.Prog.ImgBounds.IMG_HI <= a -> 0 <= a < 2 ^ 64 ->
  (exists b, m (Z_to_bv 64 a) = Some b) -> Lib.Mem.wr_at A.Img0.rsegs m a 1.
Proof.
  intros m a Hgt Ha (b & Hb).
  assert (Hgt' : A.Contract.GT <= a) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Hgt; lia).
  assert (Hmrd : Lib.Mem.mrd A.Img0.rsegs m (Lib.Mem.wa a) = Some b)
    by (unfold Lib.Mem.mrd, Lib.Mem.wa; rewrite Hb; reflexivity).
  split; [lia |]. split; [lia |]. intros i Hi.
  replace (a + i) with a by lia.
  exact (A.Prog.Seg.F24.b7_hi_wr m a Hgt' Ha (ex_intro _ b Hmrd)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The stage. *)

Section GlueF26.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :296-297), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A825f4_at := (ACtlCutP.C_A825f4_at B).
Local Notation C_A82604_at := (ACtlCutP.C_A82604_at B).

(* The core's AR law record (YCbq.v:207, Section a0's hypothesis), as ACtl.v:183 states it. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The kit's image facts are cited by name below: A.ACtlG.Kit.kit_wx and A.ACtlG.Kit.kit_segs_low. *)

Lemma glue_seg_F26 : forall POST (j : nat), CF POST (ix_cut C_A82604_at [Z.of_nat j]) -> CF POST (ix_cut C_A825f4_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ACtlCut.v:232-234; C_A825f4_at, ACtlCutP.v:2634-2644). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825f4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & HBODY).
  destruct HBODY as (phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HB7K & HP).
  cbv beta in HP.
  destruct HP as (R25 & R10 & HPORTS & HFIRST & HADq & HADf).
  destruct Hrt as (HAC & Hcut & Himgsh & HRO).
  (* G2: the geometry. *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkok & _ & _).
  destruct Hstkok as (_ & _ & Hceil & Hstklo & _ & _ & _ & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite HF. cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825f4_at ACtlCut.own6].
    left. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { apply HL. cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825f4_at ACtlCut.own6].
    left. reflexivity. }
  assert (Hfr4096 : 4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling).
  { change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
    rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. split; [exact Hf4096 | exact Hfceil]. }
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hcmin Hcmax] _].
  (* FRAC's own names. *)
  destruct HFRAC as (Aa & sp & HC).
  pose proof HC as (R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA416 & Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo.
  unfold A.AsanRT.APPMEM_END in HSapp.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hwin : fr + 3136 < sp - 16 /\ A.Prog.ImgBounds.IMG_HI <= sp - 16 /\ sp <= ACtlCut.c_sp cx).
  { unfold A.Prog.ImgBounds.IMG_HI. repeat split; lia. }
  destruct Hwin as (Hfrwin & Himg & Hspsp).
  assert (Hsp0 : 0 <= sp - 16 /\ sp < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  (* the block of this turn is live, so it sits below the window *)
  assert (Hinblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  pose proof HB7K as (_ & _ & _ & Hphi0 & Hphi2 & Hflen & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinblk)
    as (_ & Hphi4096 & Hphiceil & _).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  rewrite Hreq in Hphiceil.
  (* the input block *)
  pose proof HB as (HBpre & _).
  pose proof HBpre as (_ & _ & _ & _ & Hinp & Hinlen & _).
  assert (Hinbound : 0 <= ACtlCut.c_p cx /\
                     ACtlCut.c_p cx + ACtlCut.c_n cx <= lib.Reusable.YM05.alloc_ceiling).
  { destruct Hinp as [(Hn0 & Hp0) | (Hn0 & Hinb)].
    - rewrite Hp0, Hn0. unfold A.ACfn.A_EMPTY. lia.
    - destruct (Reusable.YG0d.al_blocks _ _ LAWS (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                  (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                  (proj1 (proj1 HBpre)) Hinb) as (_ & Hp4096 & Hpceil & _).
      unfold Reusable.YG00.req_size in Hpceil.
      destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (Hinlen' : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by lia.
  (* G2b: the run's premises *)
  assert (Hstk : Lib.Frame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { split; [lia |]. split; [change (2 ^ 64) with 18446744073709551616; lia |].
    intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hbv).
    assert (Hmrd : Lib.Mem.mrd A.Img0.rsegs mem3 (Lib.Mem.wa a) = Some b)
      by (unfold Lib.Mem.mrd, Lib.Mem.wa; rewrite Hbv; reflexivity).
    split; [| exists b; exact Hmrd].
    assert (Hga : A.Contract.GT <= a) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Himg; lia).
    pose proof (A.Prog.Seg.F24.b7_hi_wr mem3 a Hga ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                  (ex_intro _ b Hmrd)) as HWa.
    unfold A.Reusable.YP09.writable_at in HWa. exact HWa. }
  assert (HOUT : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                           A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
                  Lib.Frame.outside [(sp - 16, sp)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [| exact I].
    unfold A.AsanRT.GOT_CELL_K, A.AsanRT.CELL_K, A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
      A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *.
    unfold A.Prog.ImgBounds.IMG_HI in Himg. lia. }
  assert (HADp : A.AsanRT.addressable mem3 (phi + 18) 20).
  { destruct HHB as (_ & Hadphi). unfold A.ACtlK.a_size in Hadphi.
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.flen cx j) 1) 18 20 Hadphi); lia. }
  pose proof HB7K as (_ & _ & R22 & _ & _ & _ & Hblk & _).
  (* visibility of the four footprint regions *)
  assert (V1 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.cut_own (ix_cut C_A825f4_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (VRT : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.RT_LO
                  (A.AsanRT.RT_HI - A.AsanRT.RT_LO)) by exact (A.ProgBridge.rt_vis_W W3).
  assert (V2 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.GOT_CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.GOT_CELL_K; lia. }
  assert (V3 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.CELL_K; lia. }
  assert (V4 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (phi + 18) 20).
  { apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 20
             HAR Hinblk); rewrite ?Hreq; lia. }
  assert (V5 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                 (A.AsanRT.shadow_addr (phi + 18))
                 (A.AsanRT.shadow_addr (phi + 18 + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                (phi + 18) 20 HAR Hinblk ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(lia)) as [Hz | Vsh];
      [lia |].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (phi + 18))
             (A.Prog.rng_asan.sh_al8_hi (phi + 18) 20 - A.Prog.rng_asan.sh_al8_lo (phi + 18)) _ _ Vsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr;
      Z.div_mod_to_equations; lia. }
  (* G3: the cut's configuration in the run's state form, then the walk at the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A825f4_at [Z.of_nat j])) with 0x825f4.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x825f4) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run, and the lift at RNG_W. *)
  unfold Lib.Regs6ss.mkR_of.
  pose proof (A.Prog.Seg.F26Fon.f26_evt_F_on (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                A.Prog.reac_ports_unknownF.reac_ports_unknown_F_holds_on
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
                sp phi (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j) (sp - 16)
                (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)
                R2 R22 R10 Hphi0 Hphi2 ltac:(lia) Hstk ltac:(lia)
                (A.Prog.Seg.F24.b7_pbs_length (ACtlCut.c_in cx) j)
                (A.Prog.Seg.F24.b7_pbs_bytes mem3 (phi + 18) (ACtlCut.c_in cx) j Hblk)
                ltac:(left; lia) HAC HADp HOUT
                (A.ProgBridge.rng_of_visible _ _ _ V1)
                (A.ProgBridge.rng_of_visible _ _ _ V2)
                (A.ProgBridge.rng_of_visible _ _ _ V3)
                (A.ProgBridge.rng_of_visible _ _ _ V4)
                (A.ProgBridge.rng_of_visible _ _ _ V5)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
           _ (POST cx) HFS); [exact (A.ProgBridge.fp_avoids_RNG_W _) |].
  (* G5: the continuation. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (ra' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM).
  subst ms'.
  cbn [ms_mem] in Hhid.
  (* the write set of this run *)
  set (W := [(sp - 16, sp)] : list Lib.Frame.ivl).
  assert (AW : A.AsanRTFacts.all_app W).
  { unfold W. cbn [A.AsanRTFacts.all_app]. split; [| exact I].
    intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    unfold A.Prog.ImgBounds.IMG_HI in Himg. right. lia. }
  assert (Dlo : forall a n, 0 <= n -> a + n <= sp - 16 -> Lib.Frame.disjoint_from W a n).
  { intros a n Hn Ha. unfold W. cbn [Lib.Frame.disjoint_from]. split; [left; lia | exact I]. }
  assert (Dhi : forall a n, sp <= a -> Lib.Frame.disjoint_from W a n).
  { intros a n Ha. unfold W. cbn [Lib.Frame.disjoint_from]. split; [right; lia | exact I]. }
  (* the register map of the end state *)
  set (R1 := Lib.Frame.mkR ra' (lib.Reusable.YK11.getr regs3 2)
               (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) t0' t1' t2'
               (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
               (Z_to_bv 64 (if Prog.RcPorts.pu_decl (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)
                            then 4 * Prog.RcPorts.pu_nunk (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) 12
                            else -1))
               (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
               (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19)
               (Z_to_bv 64 (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j))
               (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
               (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26)
               (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29)
               (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  (* the register equalities of the end map *)
  assert (E2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : lib.Reusable.YK11.getr R1 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E25 : lib.Reusable.YK11.getr R1 25 = lib.Reusable.YK11.getr regs3 25) by reflexivity.
  assert (E26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (E20 : lib.Reusable.YK11.getr R1 20 = Z_to_bv 64 (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j))
    by reflexivity.
  assert (E10 : lib.Reusable.YK11.getr R1 10 = Z_to_bv 64 (A.Prog.SlotModel.t_unk (ACtlCut.c_in cx) j))
    by reflexivity.
  (* the transporter record *)
  assert (TR : b7g_tr (fun p n => Lib.Frame.disjoint_from W p n) mem3 m' regs3 R1).
  { split; [intros p n p' n' HK Hp Hn Hpn; exact (A.AsanRTFacts.disjoint_from_sub W p n p' n' HK Hp Hpn) |].
    split; [intros a bs n HK Hl Hby; apply (Lib.Frame.bytes_at_transport segs W mem3 m' a bs Hby MU);
            rewrite Hl; exact HK |].
    split; [intros p n _ Had; exact (b7g_addr_app W mem3 m' p n MU AW Had) |].
    intros off v Ho0 Ho Hs.
    apply (b7g_spill_keep W mem3 m' regs3 R1 Aa off v R9 ltac:(lia)
             ltac:(change (2 ^ 64) with 18446744073709551616; lia) Ho0 Ho E9 MU); [| exact Hs].
    apply Dhi. lia. }
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82604_at [Z.of_nat j])) R1 m' md')
            (POST cx)).
  (* the exit cut *)
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
  - (* the journal crosses the callee's stack window *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => sp - 16 <= a < sp).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity |].
      apply (MU x). unfold W. cbn [Lib.Frame.outside]. split; [exact Hx | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx |].
      destruct (A.Prog.Seg.F24.b7_out_dec W (bv_unsigned x)) as [Hout | Hout].
      * rewrite (MU x Hout). exact Hx.
      * destruct (A.Prog.Seg.F24.b7_in_cases W (bv_unsigned x) Hout) as (lo & hi & Hin & Hr).
        unfold W in Hin. cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
        apply (b7g_grow mem3 m' x); [unfold A.Prog.ImgBounds.IMG_HI in *; lia | exact WM | exact Hx].
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A82604_at (ACtlCutP.v:2648-2658) *)
    split; [reflexivity |].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82604_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    (* FRAC, re-established on the end map and the new memory by WALKING its conjuncts (so a conjunct
       appended to FRAC needs no edit here as long as one of the leaf cases closes it): a register or
       arithmetic fact carries over by conversion (R1 keeps registers 2 3 4 8 9 19 26 of regs3); a q64 word
       or byte list moves across the run's write set [sp - 16, sp), which lies above every frame / shadow
       byte (Dlo) and below the spill area and the saved registers (Dhi). *)
    split.
    { exists Aa, sp.
      let leaf H :=
        lazymatch goal with
        | |- ACtlCutP.q64 _ _ _ =>
            apply (b7g_q64 _ _ _ _ _ TR); [first [apply Dhi; lia | apply Dlo; lia] | exact H]
        | |- Lib.Mem.bytes_at _ _ _ _ =>
            eapply (b7g_by _ _ _ _ _ TR); [| reflexivity | exact H];
            first [apply Dhi; lia | apply Dlo; lia]
        | |- exists _, _ =>
            let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hshl := fresh "Hshl" in
            destruct H as (sh & Hsh & Hshl); exists sh; split; [| exact Hshl];
            eapply (b7g_by _ _ _ _ _ TR); [| reflexivity | exact Hsh];
            apply Dlo; [lia |]; rewrite Hshl;
            unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, ACtlCutP.FRAME_SHADOW,
              ACtlCutP.FRAME_BYTES;
            change (Z.of_nat (Z.to_nat (3136 / 8))) with 392; Z.div_mod_to_equations; lia
        | |- _ => exact H
        end in
      let rec walk H :=
        lazymatch type of H with
        | _ /\ _ => let H1 := fresh "Hc" in let H2 := fresh "Hr" in
                    destruct H as [H1 H2]; split; [leaf H1 | walk H2]
        | _ => leaf H
        end in
      walk HC. }
    (* b7_body *)
    exists phi.
    split; [exact HPerm |]. split; [exact Hn26 |]. split; [exact Hj255 |].
    assert (KF : Lib.Frame.disjoint_from W (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624))
      by (apply Dlo; unfold ACtlCutP.FRAME_BYTES; lia).
    assert (KI : Lib.Frame.disjoint_from W (ACtlCut.c_p cx) (ACtlCut.c_n cx)) by (apply Dlo; lia).
    assert (KB : Lib.Frame.disjoint_from W phi (ACtlCutP.flen cx j)) by (apply Dlo; lia).
    split.
    { apply (b7g_HB _ _ _ _ _ phi (ACtlCutP.flen cx j) TR); [| exact HHB].
      apply Dlo; unfold A.ACtlK.a_size; lia. }
    split; [exact (b7g_FLSI _ _ _ _ _ cx j fr TR KF KI Hinlen'
                     ltac:(apply (Lib.Frame.stk_transport_disjoint segs W mem3 m' fr
                                    (fr + ACtlCutP.FRAME_BYTES));
                           [exact (proj1 (proj2 (proj2 (proj1 HFLSI)))) | exact MU | exact WM
                           | apply Dlo; unfold ACtlCutP.FRAME_BYTES; lia])
                     HFLSI) |].
    split; [exact (b7g_B7K _ _ _ _ _ cx j phi fr TR KF KB E18 E21 E22 E23 E24 HB7K) |].
    (* the tail of C_A82604_at *)
    split; [unfold ACtlCut.rgv in *; etransitivity; [exact E25 | exact R25] |].
    split; [unfold ACtlCut.rgv; exact E20 |].
    split; [unfold ACtlCut.rgv; exact E10 |].
    split.
    { unfold ACtlCutP.PORTS in *. destruct HPORTS as (Hz & Hnz). split; intros E.
      - destruct (Hz E) as (Q0 & Q4 & Q8).
        split; [apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q0] |].
        split; [apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q4]
               | apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q8]].
      - destruct (Hnz E) as (Q0 & Q4 & Q8).
        split; [apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q0] |].
        split; [apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q4]
               | apply (b7g_u32 _ _ _ _ _ TR); [apply Dlo; lia | exact Q8]]. }
    split.
    { unfold ACtlCutP.FIRSTb in *. apply (b7g_b8 _ _ _ _ _ TR); [apply Dlo; lia | exact HFIRST]. }
    split; [exact (b7g_ad _ _ _ _ _ TR (fr + 128) 12 ltac:(apply Dlo; lia) HADq) |].
    exact (b7g_ad _ _ _ _ _ TR (fr + 160) 1 ltac:(apply Dlo; lia) HADf).
  - (* ctl_rt_C at the same state (ly3, S3): the write set is the callee's stack window, far above the runtime
       cells, and app memory, so no shadow byte moves and both regions carry over *)
    unfold A.ACtlRtC.ctl_rt_C.
    split.
    { unfold A.ACtlK.asan_cells_at in *.
      apply (A.AsanRTFacts.asan_cells_kept W mem3 m' HAC MU).
      apply Dlo; [unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia |].
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. unfold A.Prog.ImgBounds.IMG_HI in Himg. lia. }
    split.
    { exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut (A.AsanRTFacts.munch_meta W mem3 m' MU AW) WM). }
    split.
    { exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himgsh (A.AsanRTFacts.munch_meta W mem3 m' MU AW) WM). }
    apply (b7g_ro W mem3 m' HRO MU).
    intros lo hi Hin. unfold W in Hin. cbn [In] in Hin. destruct Hin as [E | []].
    injection E as <- <-. lia.
Qed.

End GlueF26.

Print Assumptions glue_seg_F26.
