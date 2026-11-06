(* lib/A/ACtlG/F21.v -- GLUE for stage seg_F21 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:813-814) (an earlier version, blob 84ef756918c, not in this delivery)).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F21 : forall POST (j : nat),
       CF POST (ix_cut C_A82554_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A824b4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F21, character for character (checked against the base's ACtl.v before the commit).
   Segment F21 is 0x824b4 -> 0x82554 (the head-amp sum loop head) or 0x825a0 (the record verifier returned):
   the checksum result is compared with the sum_ok spill, the two record type bytes phi+18 / phi+19 are read
   under their instrumented shadow checks, and on either mismatch the segment calls
   reac_ctrl_headamp_record_verify at 0x8259c and lands at 0x825a0.

   THE CHOICE THE TASK ASKS FOR (a) OR (b): THIS FILE TAKES (a), the segment's own `_F` with the PLAIN
   contract.  Reason, measured in the files on the base: Seg/F21F.v's `f21_evt_F` (:227) has NO contract
   premise at all -- its `f21_harvc_F` (:69) discharges `reac_ctrl_headamp_record_verify_contract_F` outright
   with the callee's own proof `reac_ctrl_headamp_record_verify_F.reac_ctrl_headamp_record_verify_holds_F`
   (F21F.v:105), and the run SPANS the call, from 0x824b4 to the two exits.  So the glue has exactly one
   obligation at the call site, the callee's `ExecF.rng` regions (the record bytes, their shadow bytes, the
   callee frame [sp-16, sp), GOT_CELL_K and CELL_K), which it pays from the walk's own visibility facts, and
   ONE lift of the WHOLE run.  Route (b), a Theorem Labs lane's cgif-form walk `pb_ctrl_headamp_record_verify`, would
   need the run CUT at the jal (no such `_F` exists: F21F.v has no pre/post split), a new stretch lemma, the
   spec's `afn_pre` / `afobj_any` / chain obligations at the call, and a second lift for the tail -- strictly
   more obligations for the same stage statement.  This also matches a Theorem Labs lane's 04:10Z ruling (route (a)
   where the segment's `_F` already carries or discharges the callee contract; never cut at the call) and the
   04:01Z split rule (headamp is not one of the eight fake-stack callees and its `_F` IS proved on the base).
   NO `<f>_SRr_at` AND NO `_hid` PLACEHOLDER IS CITED BY THIS FILE: SRr_fevt_hid's own continuation carries
   ajournal_exec's hidden-bytes premise.

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index equation, then C_A824b4_at's conjuncts (ACtlCutP.v:2558-2578);
       `Nat2Z.id` turns the index back into j.
   G2  the run's premises from the body and from VISIBLE state only: the frame bound from frames_bounds + the
       shell's frame law + layout_le's ly_F; the stack bounds from the journal's astk_ok; the live block's
       bound from AR_blocks_law; the input block's from the core's lib pre (ACfn.v:38, the n = 0 arm is
       vacuous); the spill base A and sp from FRAC.  The window the segment writes is [sp - 16, sp), the
       record verifier's own frame.
   G3  the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl), the four registers the
       run pins rewritten into the canonical map (Estart), then the WALK moved from the cut's map regs3 to the
       run's canonical one by Reusable.YA0nR.SRr_xregs_eqv.
   G4  the lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then ONE
       Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3) over the WHOLE run (the call is
       inside it).  fp_avoids by ProgBridge.fp_avoids_RNG_W; each ExecF.rng premise by
       ProgBridge.rng_of_visible from a visibility fact: ProgWorldVisHeap.heap_vis / heap_sh_vis for the
       record bytes and their shadow, ProgWorldVisWin.win_vis for the callee frame and the sum_ok spill,
       ProgBridge.rt_vis_W for GOT_CELL_K and CELL_K.
   G5  the continuation: the run's end map IS the exit cut's map.  The journal crosses the write with
       Reusable.YCbq.ajournal_exec at Wr := [sp - 16, sp) (its awr_byte case is the stack window, since
       LLVMF_STK = 32768 and the cut's FRAC gives c_sp - 4096 < sp); ctl_rt_C by f21_rt_move; FRAC by
       kit_frac_move (registers) + f21_frac_mem (memory); HB / FLSI / B7K by f21_core_move; then the exit cut
       at the arm the run reached (0x82554 with the two type bytes 4 / 3, or 0x825a0 with a0 = s4 = t_want_v).

   ROUTE (C), L3 switch (a Theorem Labs lane's L3 brief; a working branch 1899bed1aee, L3 recipe
   L3-recipe.md (a working note, not in this delivery)).  ctl_from's premise is now
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (cells, shadow_rw_on cut_shadow, shadow_rw_on img_shadow, ro_agree).
   - ENTRY: the stage reads only the cells (HAC) from it.  The one shadow consumer the walk's cut fed before, the
     run's universal `shadow_rw m`, is GONE: Seg/F21F.v's f21_evt_F only handed that premise on to the record
     verifier's contract, so the run is now Seg/F21Fon.v's twin f21_evt_F_on (no shadow_rw premise), whose callee is
     reac_ctrl_headamp_record_verify_contract_F_on (premise DROPPED) proved by ..._holds_F_on (both LANDED).
     So no region proof is needed at the entry (class (b) of the consumer list, row F21.v:417,480, closes with no
     consumer left).
   - EXIT: the run keeps the state (both exit cuts are at ly3 S3), so f21_rt_move keeps the regions across the
     write window [sp - 16, sp) with A.ShadowRwOnK.fl_shadow_rw_on (the window misses the shadow), instead of
     ctl_rt_C_of_AR, which would need TFIB_SYMS as a new Section hypothesis.
   - The Section never had VIS0 / OWNED_RO and never called ctlrt_of_AR / rt_of_core: nothing to delete there.
   The stage statement is unchanged (ACtl.v at 8ce82d7e310 and at a working branch 1899bed1aee, diffed).

   SECTION HYPOTHESES: ONE, and it is ACtl.v's own.
   - LAWS: the core's AR law record (YCbq.v:207), ACtl.v:185's own Section hypothesis; ajournal_exec,
     frames_bounds, al_blocks and the two ProgWorldVis files are stated under it.
   THE KIT IS CITED, NOT RESTATED (a Theorem Labs lane via another Theorem Labs lane, 2026-10-29 ~05:1xZ): on the newer glue base
   a working branch 46eb24cd4b3 lib/A/ACtlG/Kit.v (blob 7e164a09a73) BUILDS, so the three
   placeholders this file carried on the eb89fed7fac base (kit_wx, kit_segs_low, kit_frac_move) are deleted
   and A.ACtlG.Kit.kit_wx / kit_segs_low / kit_frac_move are cited instead.  The proof did not change: the
   placeholder text was the kit's.
   NO OTHER HYPOTHESIS IS LEFT: the callee contract is discharged inside Seg/F21F.v, and every bound is
   proved here from the walk's state (the bounded-corollary rule, a Theorem Labs lane).

   CITED BY NAME: Seg/F21Fon.v's f21_evt_F_on (the route (C) twin of Seg/F21F.v's f21_evt_F; see ROUTE (C) below);
   Seg/F21.v's k6_rec, sh0, blk_cp, t_blk_len, t_g_len, t_g6_len, sumok_b2z, ckv_sub, want_hv (all top level,
   outside its Section S); Seg/F20.v's t_ID_len / t_FG_len and Seg/F13.v's fs_body_len (top level too);
   Reusable.YA0nR's SRr_xregs_eqv and SRr_fevt_hid; A.ProgBridge's fevt_of_evtF, tfibsegs_rsegs, cfg_at_MS,
   RNG_W, fp_avoids_RNG_W, rng_of_visible, range_visible_sub, rt_vis_W; A.ProgWorldVisHeap's heap_vis /
   heap_sh_vis and A.ProgWorldVisWin's win_vis - the RE-POINTED files (a Theorem Labs lane's consumer head
   a working branch 240201dbe73), which prove A.ProgWorld.heap_vis_stmt / heap_sh_vis_stmt /
   win_vis_stmt B themselves, not local look-alikes; the core's YCbq ajournal_exec / frames_bounds / asan_consts /
   seg_rom_none and YG0d's al_blocks.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here names
   a frame-route identifier (the Seg/* files are Required only for their run and their pure model lemmas).
   Module paths are written `lib.<X>` throughout, because Requiring the Seg/* files brings ctrl's ASan-side
   lib/A/Reusable into scope and a bare `Reusable.YM05` then resolves to the WRONG copy (measured: the first
   build of this file failed on exactly that).
   The twin-family modules (lib/Reusable YK11 / YK1b / YM05 / YO09, lib/Lib MState / Mem / Frame) are Required in
   their FULL path (ctrlgate e6d4e5fa5fb2's REQ rule: a partial path that matches several copies is refused).  Each
   of them loads the CORE copy ON PURPOSE, which is what ctrlgate's WARN rows ask the owner to confirm: the cut layer
   (ACtlCut / ACtlCutP), the kit and the bridge are stated over the core's YK11 / YM05 / YO09, and the cut bodies and
   the _F runs over lib/Lib's Mem / Frame / MState; the ASan-side lib/A/Reusable and lib/A/Bz/Lib copies are reached
   only inside the Seg/* files, never named here.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/F21.v   -- no hit.
   ONE deliberate exception, inside a Qed-closed proof: `lib.Lib.PropExec.seg_rom` in the ajournal_exec
   mem_grows step, because the fact being read there is lib/Lib's own `Lib.Mem.mrd`, whose ROM fallback IS
   PropExec's constant; the core's YCbq.seg_rom_none is transported onto it by `exact` (the two have the same
   body).  No statement of this file names it.

   BUILD STATE (honest), on a working branch: the interim core
   a working branch 5da74c9c931 (NO port_core_refused_ name in lib/A or lib/Reusable) merged
   over the glue base 46eb24cd4b3, with the six Tk/AW files taken BY PATH from 5da74c9c931 and a Theorem Labs lane's
   ProgWorld files taken BY PATH from a working branch fec8db0a380.  MEASURED Require closure:
   406 lib files, NONE substituted - no closure file names port_core_refused_ in its code, the worktree
   carries no modified file, and `git diff --name-status 5da74c9c931` over lib/Reusable, lib/A/A*.v and the
   two Tk trees lists only glue-side ADDITIONS (the walk / cut layer, this file and F22.v, a Theorem Labs lane's
   YA0nR / YK04R, a Theorem Labs lane's ShadowPresent), no modified core or Tk file.  lib/A/AE2k.v is the interim's resolved
   file; this proof reads none of its addresses except tfib_sink_head = A_ofl_head = 0x5fbf08, which no
   resolution changed.  (On the eb89fed7fac / 46eb24cd4b3 bases this file was built with AE2k.v
   substituted in the working tree: those builds were provisional.)
   No Axiom, no Parameter, no unproved step.
   Print Assumptions glue_seg_F21: Rocq primitives (PrimInt63 / PrimString / PrimArray) and
   functional_extensionality_dep only. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0n Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACfn A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisHeap A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcParse Prog.RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F21Fon A.Prog.Seg.F21 A.Prog.Seg.F20 A.Prog.Seg.F13.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueF21.

(* ACtl.v's Section shape (ACtl.v:170-183), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:216-218 and the cut records), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A824b4_at := (ACtlCutP.C_A824b4_at B).
Local Notation C_A82554_at := (ACtlCutP.C_A82554_at B).
Local Notation C_A825a0_at := (ACtlCutP.C_A825a0_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses. *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis), ACtl.v:183's LAWS. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   1. Memory facts across a write confined to one window [lo, hi) of the stack (lib.Lib.Frame.munch [(lo, hi)]). *)

Lemma f21_bytes_keep : forall lo hi (m m' : word -> option byte) a bs,
  lib.Lib.Mem.bytes_at segs m a bs -> lib.Lib.Frame.munch [(lo, hi)] m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> x < lo \/ hi <= x) ->
  lib.Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros lo hi m m' a bs (H0 & H1 & H) MU Hd. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold lib.Lib.Mem.mrd.
  rewrite (MU (lib.Lib.Mem.wa (a + Z.of_nat i))); [reflexivity|].
  cbn [lib.Lib.Frame.outside]. rewrite lib.Lib.Mem.wa_unsigned by lia.
  split; [|exact I]. pose proof (Hd (a + Z.of_nat i) ltac:(lia)). lia.
Qed.

Lemma f21_q64_keep : forall lo hi (m m' : word -> option byte) a v,
  ACtlCutP.q64 m a v -> lib.Lib.Frame.munch [(lo, hi)] m m' -> (a + 8 <= lo \/ hi <= a) ->
  ACtlCutP.q64 m' a v.
Proof.
  intros lo hi m m' a v H MU Hd. unfold ACtlCutP.q64 in *.
  apply (f21_bytes_keep lo hi m m' a _ H MU). rewrite lib.Lib.Mem.length_le8. intros x Hx. lia.
Qed.

Lemma f21_stk_keep : forall lo hi (m m' : word -> option byte) a b,
  lib.Lib.Frame.stk segs m a b -> lib.Lib.Frame.munch [(lo, hi)] m m' -> (b <= lo \/ hi <= a) ->
  lib.Lib.Frame.stk segs m' a b.
Proof.
  intros lo hi m m' a b (H0 & H1 & H) MU Hd. split; [exact H0|]. split; [exact H1|].
  intros x Hx.
  assert (E : m' (lib.Lib.Mem.wa x) = m (lib.Lib.Mem.wa x)).
  { apply MU. cbn [lib.Lib.Frame.outside]. rewrite lib.Lib.Mem.wa_unsigned by lia. split; [lia | exact I]. }
  destruct (H x Hx) as (Hw & b0 & Hb). split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b0. unfold lib.Lib.Mem.mrd in *. rewrite E. exact Hb.
Qed.

(* A spill read through s1 = A: its base is A (the spill's own bytes bound it below 2^64). *)
Lemma f21_spill_base : forall (regs : bvmap 5 word) m A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1. cbn in Hq1.
    unfold ACtlCut.rgv in H9, H9'. rewrite H9 in H9'. apply (f_equal bv_unsigned) in H9'.
    rewrite (lib.Lib.MState.unsigned_lit A) in H9' by lia. rewrite Z_to_bv_unsigned in H9'.
    unfold bv_wrap, bv_modulus in H9'. change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

Lemma f21_saved_len : forall cx, length (ACtlCutP.saved_bytes cx) = 104%nat.
Proof.
  intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. reflexivity.
Qed.

(* FRAC's memory part (ACtlCutP.v, FRAC) across the window: the spills and the saved registers lie above the
   cut's sp; the frame header words, the frame shadow and (batch 3, a Theorem Labs lane d36efc6152d) the class-6 frame's
   TRAILER WORD q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) lie below the window.  The trailer is past
   FRAME_BYTES = 3136 but inside the class-6 frame of fs_frame_bytes 6 = 4096 bytes, so the frame premise is
   fr + 4096 <= lo (the stage gets it from frames_bounds, fr + 4096 <= alloc_ceiling, and the journal's astk_ok). *)
Lemma f21_frac_mem : forall cx fr sel (regs : bvmap 5 word) (m m' : word -> option byte) lo hi,
  ACtlCutP.FRAC B cx fr sel regs m -> lib.Lib.Frame.munch [(lo, hi)] m m' ->
  hi <= lib.Reusable.YG0d.spZ regs -> 0 <= fr -> fr + 4096 <= lo ->
  ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW <= lo ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' lo hi
    (A & sp & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 &
     Q304 & Q24 & Q16 & Qh & Qe & (sh & Hsh & Lsh) & Hsav & Htr) MU Hhi Hfr0 Hlo Hshlo.
  exists A, sp.
  do 17 (split; [assumption|]).
  change ACtlCutP.FRAME_SHADOW with 392 in *. unfold ACtlCutP.FRAME_BYTES in *.
  split; [apply (f21_q64_keep lo hi m m' _ _ Q304 MU); lia|].
  split; [apply (f21_q64_keep lo hi m m' _ _ Q24 MU); lia|].
  split; [apply (f21_q64_keep lo hi m m' _ _ Q16 MU); lia|].
  split; [apply (f21_q64_keep lo hi m m' _ _ Qh MU); lia|].
  split; [apply (f21_q64_keep lo hi m m' _ _ Qe MU); lia|].
  split.
  { exists sh. split; [|exact Lsh]. apply (f21_bytes_keep lo hi m m' _ _ Hsh MU).
    assert (Lsh' : Z.of_nat (length sh) = 392) by (rewrite Lsh; reflexivity).
    intros x Hx. left. lia. }
  split.
  { apply (f21_bytes_keep lo hi m m' _ _ Hsav MU). rewrite f21_saved_len. intros x Hx. right. lia. }
  (* the trailer word [fr + 4088, fr + 4096), below the window *)
  apply (f21_q64_keep lo hi m m' _ _ Htr MU). lia.
Qed.

(* The body of a B7CUT cut without its tail predicate (b7_body, ACtlCutP.v:1052-1060: HB, FLSI, B7K) across the
   window: every byte it names lies in the live block [phi, phi + flen), the frame [fr, fr + FRAME_BYTES), the
   input block, or the spill area above s1 = A, or is a shadow byte (addressable reads only the shadow, which a
   write to application memory keeps). *)
Lemma f21_core_move : forall cx j fr phi (regs R : bvmap 5 word) (m m' : word -> option byte) lo hi A,
  ACtlCutP.HB m phi (ACtlCutP.flen cx j) ->
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.B7K cx j phi fr regs m ->
  lib.Lib.Frame.munch [(lo, hi)] m m' ->
  A.AsanRT.HIGHMEM_BEG <= lo -> hi <= A.AsanRT.APPMEM_END ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> hi <= A ->
  0 <= fr -> fr + ACtlCutP.FRAME_BYTES <= lo -> phi + ACtlCutP.flen cx j <= lo ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> x < lo) ->
  lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs 9 -> lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs 21 -> lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs 23 -> lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs 24 ->
  ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\ ACtlCutP.FLSI cx j fr R m' /\ ACtlCutP.B7K cx j phi fr R m'.
Proof.
  intros cx j fr phi regs R m m' lo hi A HHB HFL HB7 MU Hlo Hhi H9 HA0 HA HhiA Hfr0 HfrL HphL Hin
    E9 E18 E21 E22 E23 E24.
  assert (MK : A.AsanRTFacts.meta_kept m m').
  { apply (A.AsanRTFacts.munch_meta [(lo, hi)] m m' MU). cbn [A.AsanRTFacts.all_app]. split; [|exact I].
    intros a Ha. unfold A.AsanRT.app_mem. right. lia. }
  assert (Kad : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n)
    by (intros p n H; exact (A.AsanRTFacts.addressable_kept m m' p n H MK)).
  assert (Ksp : forall off v, 0 <= off -> off + 8 <= 416 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v).
  { intros off v Ho0 Ho1 Hs. exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact H9|].
    apply (f21_q64_keep lo hi m m' (A + off) v (f21_spill_base regs m A off v H9 HA0 HA Ho0 Ho1 Hs) MU). lia. }
  pose proof (A.Prog.SlotModel.OUR_length (ACtlCut.c_in cx)) as LO.
  pose proof (A.Prog.Seg.F20.t_ID_len (ACtlCut.c_in cx) (S j)) as LID.
  pose proof (A.Prog.Seg.F20.t_FG_len (ACtlCut.c_in cx) (S j)) as LFG.
  pose proof (A.Prog.Seg.F13.fs_body_len (ACtlCut.c_in cx) (S j)) as LFS.
  pose proof (A.Prog.Seg.F21.t_g_len (ACtlCut.c_in cx) j) as LG.
  pose proof (A.Prog.Seg.F21.t_blk_len (ACtlCut.c_in cx) j) as LB.
  unfold ACtlCutP.HB, ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.f1_IN, ACtlCutP.FLC, ACtlCutP.B7K,
    ACtlCutP.LK, ACtlCutP.OURb, ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe,
    ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe, ACtlCutP.FSj, ACtlCutP.FSb, ACtlCutP.B7SPL in *.
  unfold ACtlCutP.FRAME_BYTES in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
  first
    [ assumption
    | match goal with H : ACtlCutP.spill regs m ?o ?v |- ACtlCutP.spill R m' ?o ?v =>
        apply (Ksp o v); [lia | lia | exact H] end
    | match goal with H : A.AsanRT.addressable m ?p ?n |- A.AsanRT.addressable m' ?p ?n =>
        exact (Kad p n H) end
    | match goal with H : ?P -> A.AsanRT.addressable m ?p ?n |- ?P -> A.AsanRT.addressable m' ?p ?n =>
        let Hx := fresh "Hx" in intros Hx; exact (Kad p n (H Hx)) end
    | match goal with H : ACtlCut.rgv regs ?r ?v |- ACtlCut.rgv R ?r ?v =>
        unfold ACtlCut.rgv in H |- *;
        first [rewrite E9 | rewrite E18 | rewrite E21 | rewrite E22 | rewrite E23 | rewrite E24]; exact H end
    | match goal with H : lib.Lib.Mem.bytes_at _ m ?a ?bs |- lib.Lib.Mem.bytes_at _ m' ?a ?bs =>
        apply (f21_bytes_keep lo hi m m' a bs H MU);
        let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; left; first [exact (Hin x Hx) | lia] end
    | match goal with H : lib.Lib.Frame.stk _ m ?a ?b |- lib.Lib.Frame.stk _ m' ?a ?b =>
        apply (f21_stk_keep lo hi m m' a b H MU); left; lia end ].
Qed.

(* ctl_rt_C (ACtlRtC.v:44-46, the route (C) walk's cut form) across the window, at the SAME ly S (the run changes no world): the
   runtime cells and every read-only byte are image bytes, below the window; both shadow regions, cut_shadow B ly S
   and img_shadow, are carried by A.ShadowRwOnK.fl_shadow_rw_on, because the window [lo, hi) lies at or above
   HIGHMEM_BEG and so misses every shadow byte (in_shadow ends at HIGHMEM_BEG).  The regions do not move: this is
   the L3 recipe's "keep the regions" exit (L3-recipe.md section 2 (d)), and it needs no hypothesis. *)
Lemma f21_rt_move : forall ly (S : lib.Reusable.YG00.astate) (m m' : word -> option byte) lo hi,
  A.ACtlRtC.ctl_rt_C B ly S m -> lib.Lib.Frame.munch [(lo, hi)] m m' -> lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  A.AsanRT.HIGHMEM_BEG <= lo -> hi <= A.AsanRT.APPMEM_END ->
  A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros ly S m m' lo hi (HAC & Hcut & Himg & HRO) MU WM Hlo Hhi.
  assert (Hout : forall x, A.AsanRT.in_shadow x -> lib.Lib.Frame.outside [(lo, hi)] x).
  { intros x Hx. cbn [lib.Lib.Frame.outside]. split; [|exact I].
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in *. lia. }
  split; [|split; [|split]].
  - unfold A.ACtlK.asan_cells_at in *. apply (A.AsanRTFacts.asan_cells_kept [(lo, hi)] m m' HAC MU).
    cbn [lib.Lib.Frame.disjoint_from]. split; [left | exact I].
    unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.HIGHMEM_BEG in *. lia.
  - exact (A.ShadowRwOnK.fl_shadow_rw_on _ [(lo, hi)] m m' Hcut MU WM Hout).
  - exact (A.ShadowRwOnK.fl_shadow_rw_on _ [(lo, hi)] m m' Himg MU WM Hout).
  - unfold A.ACtlK.ro_agree_at in *. intros a Ha. rewrite <- (HRO a Ha). unfold lib.Lib.Mem.mrd.
    rewrite (MU a); [reflexivity|]. cbn [lib.Lib.Frame.outside]. split; [|exact I].
    pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
    destruct (Z_lt_le_dec (bv_unsigned a) lib.Reusable.YG0f.kLowMemEnd) as [Hl|Hl].
    + unfold lib.Reusable.YG0f.kLowMemEnd, A.AsanRT.HIGHMEM_BEG in *. lia.
    + exfalso. unfold lib.Lib.Mem.ro_addr in Ha.
      rewrite (lib.Reusable.YCbq.find_segment_none A.Img0.rsegs (bv_unsigned a)) in Ha; [discriminate|].
      intros Hi. apply A.ACtlG.Kit.kit_segs_low in Hi. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The stage. *)
Lemma glue_seg_F21 : forall POST (j : nat),
  CF POST (ix_cut C_A82554_at [Z.of_nat j]) -> CF POST (ix_cut C_A825a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A824b4_at [Z.of_nat j]).
Proof.
  intros POST j H554 H5a0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut, ACtlCut.v:232-234; C_A824b4_at, ACtlCutP.v:2558-2578). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A824b4_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hn26 & Hj255 & HHB & HFLSI & HLK & R10 & R23 & R20 & R22 & R24 &
    Hphi0 & Hphi50 & Hbig & Hk64 & Hblk & Hrec & S280 & S136 & S120 & S176 & R18 & S152 & Hgb & Hpb & Hpl & HLT).
  (* G2: the bounds, from visible state: the journal's stack bounds (astk_ok), the frame (frames_bounds and the
     frame law), the live block (AR_blocks_law), the input block (the lib pre), FRAC's spill base. *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & Hsphi & H47 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (Hac & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : fr = lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite <- Efr3 in Hf4096, Hfceil.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  pose proof HFRAC as (A & sp & Esp & _ & Hspz & _ & _ & R9 & _ & _ & R26 & _ & _ & HAc & HspA & HfrA & HA416 &
    Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo. unfold A.AsanRT.APPMEM_END in HSapp. unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (Hphi16 & Hphi4096 & Hphiceil & _).
  assert (Ereq : lib.Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j)
    by (unfold lib.Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia).
  rewrite Ereq in Hphiceil.
  assert (Hinp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                  x < sp - 16).
  { pose proof HB as ((HPRE & _ & _ & _ & Hpn & Hnl & _) & _).
    intros x Hx. rewrite <- Hnl in Hx.
    destruct Hpn as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HPRE) Hinp) as (_ & _ & Hpc & _).
    unfold lib.Reusable.YG00.req_size in Hpc. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (Hspr : 0 <= sp < 2 ^ 64) by lia.
  assert (Hhm : A.AsanRT.HIGHMEM_BEG <= sp - 16) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (Hsapp : sp <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  assert (Hfrlo : fr + ACtlCutP.FRAME_BYTES <= sp - 16) by (unfold ACtlCutP.FRAME_BYTES; lia).
  (* the class-6 frame's last byte, for FRAC's trailer word at fr + 4088 (batch 3): frames_bounds gives
     fr + 4096 <= alloc_ceiling, astk_ok gives alloc_ceiling + LLVMF_STK <= c_sp, FRAC gives c_sp - 4096 < sp *)
  assert (Hftlo : fr + 4096 <= sp - 16) by lia.
  assert (Hshlo : ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW <= sp - 16).
  { change ACtlCutP.FRAME_SHADOW with 392. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    pose proof (Z.div_le_upper_bound fr 8 fr ltac:(lia) ltac:(lia)). lia. }
  assert (Hphilo : phi + ACtlCutP.flen cx j <= sp - 16) by lia.
  (* the run's register and memory premises *)
  assert (Hdec : exists b0 b1 rest, A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j = b0 :: b1 :: rest).
  { pose proof (A.Prog.Seg.F21.t_blk_len (ACtlCut.c_in cx) j) as L.
    destruct (A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j) as [|x [|y r]]; cbn [length] in L; try lia. eauto. }
  destruct Hdec as (b0 & b1 & rest & Eblk).
  assert (Hblk2 : lib.Lib.Mem.bytes_at segs mem3 (phi + 18) (b0 :: b1 :: rest)) by (rewrite <- Eblk; exact Hblk).
  assert (Ey0 : bv_unsigned b0 = lib.Prog.RcParse.cp_v (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 18).
  { pose proof (A.Prog.Seg.F21.blk_cp (ACtlCut.c_in cx) j 0 ltac:(lia)) as X. rewrite Eblk in X.
    cbn [nth Nat.add] in X. unfold lib.Prog.RcParse.cp_v. rewrite <- X. reflexivity. }
  assert (Ey1 : bv_unsigned b1 = lib.Prog.RcParse.cp_v (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 19).
  { pose proof (A.Prog.Seg.F21.blk_cp (ACtlCut.c_in cx) j 1 ltac:(lia)) as X. rewrite Eblk in X.
    cbn [nth Nat.add] in X. unfold lib.Prog.RcParse.cp_v. rewrite <- X. reflexivity. }
  assert (Hk6 : A.Prog.SlotModel.t_k (ACtlCut.c_in cx) j = 6 -> bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3).
  { intros Hk6. destruct (A.Prog.Seg.F21.k6_rec _ _ Hk6) as (K1 & K2). rewrite Ey0, Ey1. split; assumption. }
  set (g6 := lib.Prog.RcFrag.bsl (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) 34 6) in *.
  set (sv := A.Prog.SlotModel.b2z (A.Prog.SlotModel.t_sum_ok (ACtlCut.c_in cx) j)) in *.
  assert (Ewant : A.Prog.SlotModel.t_want_v (ACtlCut.c_in cx) j = (if lib.Prog.RcLeaf.hv b0 b1 g6 then 0 else -1))
    by (rewrite A.Prog.Seg.F21.want_hv, Eblk; reflexivity).
  assert (Esp' : lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp) by exact Esp.
  assert (R10' : lib.Reusable.YK11.getr regs3 10 = Z_to_bv 64 (sv + -1)).
  { unfold sv. rewrite (A.Prog.Seg.F21.sumok_b2z _ _ Hbig). rewrite <- A.Prog.Seg.F21.ckv_sub. exact R10. }
  assert (R20' : lib.Reusable.YK11.getr regs3 20 = Z_to_bv 64 (phi + 18)) by exact R20.
  assert (R23' : lib.Reusable.YK11.getr regs3 23 = Z_to_bv 64 phi) by exact R23.
  pose proof (f21_spill_base regs3 mem3 A 280 sv R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S280) as Hq280.
  assert (Hal8 : phi mod 8 = 0).
  { pose proof (Z.div_mod phi 16 ltac:(lia)). pose proof (Z.div_mod phi 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound phi 8 ltac:(lia)). lia. }
  pose proof HHB as (_ & Hadr). unfold A.ACtlK.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  pose proof (A.Prog.Seg.F21.sh0 mem3 phi (ACtlCutP.flen cx j) 18 Hadr Hal8 ltac:(lia)
    ltac:(change (8 * (18 / 8) + 8) with 24; lia)) as Sh18.
  pose proof (A.Prog.Seg.F21.sh0 mem3 phi (ACtlCutP.flen cx j) 19 Hadr Hal8 ltac:(lia)
    ltac:(change (8 * (19 / 8) + 8) with 24; lia)) as Sh19.
  pose proof (A.AsanRTFacts.addressable_sub mem3 phi _ 18 2 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr2.
  pose proof (A.AsanRTFacts.addressable_sub mem3 phi _ 34 6 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr6.
  pose proof Hrt as (HAC & _ & _ & _).
  assert (Hstk : lib.Lib.Frame.stk segs mem3 (sp - 16) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hbb).
    split.
    - unfold wview, lib.Lib.Mem.wa. rewrite Hbb. discriminate.
    - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  (* the footprint: every region the run reads or writes is visible in W3 (ProgWorldVis*, ProgBridge) *)
  set (RNG := A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)).
  (* the re-pointed win_vis states A.ProgWorld.win_vis_stmt B, whose journal's sink head is ProgWorld's own
     instance A.AE2k.tfib_sink_head (ProgWorld.v:77), the one this stage's journal takes *)
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (V18 : lib.Lib.ExecF.rng RNG (phi + 18) 2).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j));
      [exact HAR | exact Hinphi | lia | rewrite Ereq; lia]. }
  assert (V34 : lib.Lib.ExecF.rng RNG (phi + 34) 6).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j));
      [exact HAR | exact Hinphi | lia | rewrite Ereq; lia]. }
  assert (VS18 : lib.Lib.ExecF.rng RNG (A.AsanRT.shadow_addr (phi + 18))
                   (A.AsanRT.shadow_addr (phi + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 2
                HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV]; [lia|].
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      Z.div_mod_to_equations; lia. }
  assert (VS34 : lib.Lib.ExecF.rng RNG (A.AsanRT.shadow_addr (phi + 34))
                   (A.AsanRT.shadow_addr (phi + 39) - A.AsanRT.shadow_addr (phi + 34) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 34) 6
                HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0|HV]; [lia|].
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      Z.div_mod_to_equations; lia. }
  assert (VFr : lib.Lib.ExecF.rng RNG (sp - 16) 16).
  { apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | |]; unfold A.ACfn.LLVMF_STK; lia. }
  assert (VA280 : lib.Lib.ExecF.rng RNG (A + 280) 8).
  { apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | |]; unfold A.ACfn.LLVMF_STK; lia. }
  assert (VGOT : lib.Lib.ExecF.rng RNG A.AsanRT.GOT_CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.rt_vis_W W3));
      unfold A.AsanRT.GOT_CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  assert (VCK : lib.Lib.ExecF.rng RNG A.AsanRT.CELL_K 8).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.rt_vis_W W3));
      unfold A.AsanRT.CELL_K, A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia. }
  (* the _F run, route (C) twin (Seg/F21Fon.v f21_evt_F_on: no shadow_rw premise), its registers the cut's, the
     four the run pins rewritten *)
  pose proof (A.Prog.Seg.F21Fon.f21_evt_F_on RNG
    (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4)
    (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6) (lib.Reusable.YK11.getr regs3 7)
    (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
    (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12) (lib.Reusable.YK11.getr regs3 13)
    (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15) (lib.Reusable.YK11.getr regs3 16)
    (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19)
    (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 24)
    (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
    (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
    (lib.Reusable.YK11.getr regs3 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
    phi A (A.Prog.SlotModel.t_k (ACtlCut.c_in cx) j) sv (sp - 16) sp b0 b1 rest g6
    R9 R24 R26 Hspr Hphi0 ltac:(unfold A.AsanRT.APPMEM_END; lia) ltac:(lia) HspA ltac:(lia) Hk64
    Hhm ltac:(lia) Hblk2 (A.Prog.Seg.F21.t_g6_len _ _) Hrec Hq280 Hstk HAC Hadr2 Hadr6 Sh18 Sh19 Hk6
    V18 V34 VS18 VS34 VFr VGOT VCK VA280) as HRUN.
  (* G3: the cut's configuration in the run's state form, moved to the run's canonical register map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A824b4_at [Z.of_nat j])) with 0x824b4.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x824b4) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  assert (Estart : lib.Lib.Regs6ss.mkR_of regs3 =
    lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs3 1) (Z_to_bv 64 sp) (lib.Reusable.YK11.getr regs3 3)
      (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
      (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
      (Z_to_bv 64 (sv + -1)) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
      (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
      (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
      (lib.Reusable.YK11.getr regs3 19) (Z_to_bv 64 (phi + 18)) (lib.Reusable.YK11.getr regs3 21)
      (lib.Reusable.YK11.getr regs3 22) (Z_to_bv 64 phi) (lib.Reusable.YK11.getr regs3 24)
      (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
      (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
      (lib.Reusable.YK11.getr regs3 31)).
  { rewrite <- Esp', <- R10', <- R20', <- R23'. reflexivity. }
  rewrite Estart.
  (* G4: the lift of the whole run (the record verifier's call is inside it, through its proved contract) *)
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the continuation *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & m' & pcv & Ems & MU & WM & ST' & Harm).
  subst ms'.
  match goal with |- context [lib.Lib.MState.MS ?R0 _ _ _ _ _ _] => remember R0 as R eqn:ER end.
  assert (G2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by (rewrite ER, Esp'; reflexivity).
  assert (G3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by (rewrite ER; reflexivity).
  assert (G4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by (rewrite ER; reflexivity).
  assert (G8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by (rewrite ER; reflexivity).
  assert (G9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by (rewrite ER; reflexivity).
  assert (G18 : lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18) by (rewrite ER; reflexivity).
  assert (G19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by (rewrite ER; reflexivity).
  assert (G21 : lib.Reusable.YK11.getr R 21 = lib.Reusable.YK11.getr regs3 21) by (rewrite ER; reflexivity).
  assert (G22 : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by (rewrite ER; reflexivity).
  assert (G23 : lib.Reusable.YK11.getr R 23 = lib.Reusable.YK11.getr regs3 23) by (rewrite ER, R23'; reflexivity).
  assert (G24 : lib.Reusable.YK11.getr R 24 = lib.Reusable.YK11.getr regs3 24) by (rewrite ER; reflexivity).
  assert (G26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by (rewrite ER; reflexivity).
  assert (HspzR : lib.Reusable.YG0d.spZ R = sp).
  { unfold lib.Reusable.YG0d.spZ in *. rewrite G2. exact Hspz. }
  (* the journal across the write of the record verifier's frame [sp - 16, sp) (ajournal_exec) *)
  assert (HJ' : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => sp - 16 <= a < sp); [exact HJ | | | exact Hhid | exact Hsbm | ].
    - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
      change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 16)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [lib.Lib.Frame.outside]; split; [lia | exact I]]].
      destruct ST' as (_ & _ & HST). destruct (HST (bv_unsigned x) ltac:(lia)) as (_ & b & Hbb).
      unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in Hbb. rewrite Z_to_bv_bv_unsigned in Hbb.
      assert (Hr0 : lib.Lib.PropExec.seg_rom segs x = None).
      { pose proof (lib.Reusable.YCbq.seg_rom_none segs (bv_unsigned x) Rx
          ltac:(intros Hi; apply A.ACtlG.Kit.kit_segs_low in Hi; unfold lib.Reusable.YG0f.kLowMemEnd in Hi; lia)) as Hz.
        rewrite Z_to_bv_bv_unsigned in Hz. exact Hz. }
      intros Em. rewrite Em, Hr0 in Hbb. discriminate.
    - intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia. }
  assert (Hrt' : A.ACtlRtC.ctl_rt_C B ly3 S3 m') by exact (f21_rt_move ly3 S3 mem3 m' (sp - 16) sp Hrt MU WM Hhm Hsapp).
  assert (HFRAC' : ACtlCutP.FRAC B cx fr fr R m').
  { apply (f21_frac_mem cx fr fr R mem3 m' (sp - 16) sp); [| exact MU | lia | lia | exact Hftlo | exact Hshlo].
    exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC G2 G3 G4 G8 G9 G19 G26). }
  assert (HB7 : ACtlCutP.B7K cx j phi fr regs3 mem3)
    by exact (conj HLK (conj R23 (conj R22 (conj Hphi0 (conj Hphi50 (conj Hbig (conj Hblk (conj S280
      (conj R24 (conj R18 (conj S152 (conj Hgb (conj Hpb (conj Hpl (conj HLT (conj S136 (conj S120 S176))))))))))))))))).
  destruct (f21_core_move cx j fr phi regs3 R mem3 m' (sp - 16) sp A HHB HFLSI HB7 MU Hhm Hsapp R9
              ltac:(lia) ltac:(lia) HspA ltac:(lia) Hfrlo Hphilo Hinp G9 G18 G21 G22 G23 G24)
    as (HHB' & HFLSI' & HB7').
  destruct Harm as [(Epc & E10 & E11 & E12 & E13 & Eb0 & Eb1) | (Epc & E10 & Ehv)].
  - (* exit 1: the head-amp sum loop head 0x82554 (C_A82554_at, ACtlCutP.v:2582-2592) *)
    subst pcv a0' a1' a2' a3'.
    change (lib.Reusable.YA0n.SRr segs W3
              (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82554_at [Z.of_nat j])) R m' md') (POST cx)).
    apply (H554 cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB); [exact HJ' | exact HF | exact HL | exact Hk | | exact Hrt'].
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82554_at ACtlCutP.ixn ACtlCutP.b7_body nth].
    rewrite Nat2Z.id.
    split; [exact HFRAC'|].
    exists phi.
    split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
    split; [exact HHB'|]. split; [exact HFLSI'|]. split; [exact HB7'|].
    split.
    { apply (f21_bytes_keep (sp - 16) sp mem3 m' _ _ Hrec MU).
      pose proof (A.Prog.Seg.F21.t_g6_len (ACtlCut.c_in cx) j) as L6. fold g6 in L6.
      intros x Hx. left. lia. }
    split; [rewrite <- Ey0; exact Eb0|]. split; [rewrite <- Ey1; exact Eb1|].
    unfold ACtlCut.rgv. rewrite ER.
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - (* exit 2: the record verifier returned, 0x825a0 (C_A825a0_at, ACtlCutP.v:2596-2604) *)
    subst pcv a0'.
    change (lib.Reusable.YA0n.SRr segs W3
              (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A825a0_at [Z.of_nat j])) R m' md') (POST cx)).
    apply (H5a0 cx [Z.of_nat j] fr k ly3 S3 W3 R m' md' HB); [exact HJ' | exact HF | exact HL | exact Hk | | exact Hrt'].
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825a0_at ACtlCutP.ixn ACtlCutP.b7_body nth].
    rewrite Nat2Z.id.
    split; [exact HFRAC'|].
    exists phi.
    split; [exact Hperm|]. split; [exact Hn26|]. split; [exact Hj255|].
    split; [exact HHB'|]. split; [exact HFLSI'|]. split; [exact HB7'|].
    unfold ACtlCut.rgv. rewrite ER, Ewant.
    split; [reflexivity|]. rewrite Ehv. reflexivity.
Qed.

End GlueF21.

Print Assumptions glue_seg_F21.
