(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e2.v, with its module paths and module names changed; 4090 of its 4391 lines of code are new or changed and 2544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4c.v, with its module names and addresses changed; 578 of its 611 lines of code are new or changed and 4358 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F25.v, with its module names and addresses changed; 497 of its 569 lines of code are new or changed and 539 lines of the source are left out. *)
(* lib/A/ACtlG/R17.v -- GLUE for stage seg_R17 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:698) (an earlier version, blob c4edf0be7fe, not in this delivery), the same text as on a Theorem Labs lane's route (C) walk shell (from a working branch 1899bed1aee)
   and in ACtl.v:517 on the glue base 46eb24cd4b3, blob 84ef756918c).  Written by
   a Theorem Labs lane (route (C) switch by a Theorem Labs lane); single writer of this file.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R17 : forall POST (b : nat), CF POST (ix_cut C_A81858_at [Z.of_nat b]) ->
                                           CF POST (ix_cut C_A8183c_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_R17, character for character.  Segment R17 is [0x8183c, 0x81858):
     0x8183c ld a1,112(s1)   0x81840 beq a0,a1,81848   0x81848 addi s11,s8,18
     0x8184c mv a0,s11       0x81850 ld a1,216(s1)     0x81854 jal reac_ports_parse
   The call writes the 12 output bytes at q = fr + 2528 and 16 stack bytes below sp, and nothing else.

   THE ROUTE (decided by a Theorem Labs lane; glue-pattern.md section 8 (a working note, not in this delivery) is SUPERSEDED for this stage).
   The run r17_evt_F_on (lib/A/Prog/Seg/R17Fon.v:60-148, Qed; this lane's route (C) twin of a Theorem Labs lane's
   A.Prog.Seg.R17F.r17_evt_F, see ROUTE (C) below) does NOT stop at the callee entry: it runs THROUGH the call and
   takes the callee's footprint contract as its FIRST premise.  There is no _F for a pre-stretch ending at the
   callee entry, so the superseded part's (section 8's) split cannot be taken without re-proving a run.  So the WHOLE segment run is
   lifted ONCE, at footprint RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3), with
   Reusable.YA0nR.SRr_fevt_hid (YA0nR.v:64-75); the contract premise is discharged by the callee's own closed
   theorem A.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on (reac_ports_parseF.v 00b9eb3405b (the blob this tree had at release c5e779efe8c), :436, Qed),
   of A.Prog.reac_ports_parse_c.reac_ports_parse_contract_F_on (reac_ports_parse_c.v 3cb58b9552c (the blob this tree had at release c5e779efe8c), :141).
   reac_ports_parse_SRr_at is NOT used: it takes the callee contract as a premise, so citing it for the premise
   would be circular.

   ROUTE (C) (L3 recipe L3-recipe.md section 2 (a working note, not in this delivery); a Theorem Labs lane's L3 brief).
   The cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from, ACtlCut.v:243), destructured at the entry as
   (HAC & Hcut & Himg & HRO).  The old run r17_evt_F took the universal A.AsanRT.shadow_rw m, which ctl_rt_C cannot
   give; its only use there fed the callee's asan bundle, which the _on contract no longer has.  So the run is the
   twin A.Prog.Seg.R17Fon.r17_evt_F_on (premise REMOVED, not narrowed; the twin's header gives the proof lines), and
   this stage consumes NO shadow byte of the cut (Hcut / Himg are only carried).  At the exit cut ctl_rt_C B ly3 S3 m'
   is SUPPLIED by keeping the regions (recipe section 2(d), route (i)): the exit cut has the entry's ly3 S3, so
   asan_cells and ro_agree are kept as before, and Hcut / Himg are carried across the run's write set
   [sp - 16, sp) U [fr + 2528, fr + 2540), which is app memory and so misses the shadow (HSVout), by
   A.ShadowRwOnK.fl_shadow_rw_on (ShadowRwOnK.v 07ccb82106b (the blob this tree had at release c5e779efe8c), :12).  No Section hypothesis is added; no universal
   shadow_rw is derived anywhere in this file.

   THE PROOF, step by step
   G1  unfold the entry cut: ix_cut's index equation, then C_A8183c_at's conjuncts (ACtlCutP.v:1559-1586);
       the index is a NAT index (ACtlCutP.ixn), and the body pins b = 0.
   G2  the run's 36 premises.  Registers from the body's rgv / a0v conjuncts and from FRAC; the two spill loads
       as ro_cells (R17.r17_spill_ro); the 20 port bytes from RFb's block bytes (r17g_pbs_at below, which is
       R17.v:449-464's argument); the geometry (frame vs stack window, frame vs image, block vs frame) from the
       core's AR laws, the journal's astk_ok and YG0f's alloc_ceiling bounds, never from a hypothesis; the
       visibility premises from ProgWorldVisWin.win_vis / ProgWorldVisFrame.frame_vis /
       ProgWorldVisHeap.heap_vis(+_sh) and ProgBridge.img_vis_W, narrowed with ProgBridge.range_visible_sub and
       turned into footprint ranges by ProgBridge.rng_of_visible.
   G3  register maps: ProgBridge.cfg_at_MS turns the cut's cfg_at into MS regs3 ...; the run starts at the
       canonical map, and the walk is moved there by Reusable.YA0nR.SRr_xregs_eqv.
   G4  lift: the run's post is first strengthened with its own mem_grows (r17g_evtF_grows, which ajournal_exec
       needs), then ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt_hid at RNG_W, fp_avoids by
       ProgBridge.fp_avoids_RNG_W.
   G5  the continuation at the run's end state: the exit cut's ctl_from at the same cx, fr, k, ly3, S3, W3, the
       run's end map R, its memory m' and the materialized model md':
         journal  YCbq.ajournal_exec with Wr = the run's write set [sp - 16, sp) U [q, q + 12); each written
                  byte is awr_byte (the stack case for the window, in_frames for the port cells);
         frames, frame law, k bound   unchanged (own6 and the same kmax term on both cuts);
         body     memory conjuncts by Tac_rt2_b2.a_keep / R17.r17_spill_keep / R17.r17_rwcb_keep /
                  AsanRTFacts.addressable_kept; register conjuncts through the run's post;
         ctl_rt_C asan_cells by AsanRTFacts.asan_cells_kept, the two shadow regions (Hcut, Himg) by
                  ShadowRwOnK.fl_shadow_rw_on (write set off the shadow), ro_agree by R17.r17_ro_keep with
                  R17.r17_ro_lt.
   FRAC, READ AND RE-ESTABLISHED WITHOUT POSITIONS (a Theorem Labs lane 06:2xZ; the shape of a Theorem Labs lane's R3.v and a Theorem Labs lane's
   r1g_frac_mem).  The entry cut's FRAC is read BY TYPE (r17g_get: each scalar fact asserted by its own statement
   and found by decompose + assumption), and the one lemma here that RE-ESTABLISHES FRAC at a new memory --
   glue_seg_R17 itself, at the exit cut -- walks the goal's conjuncts and closes each by its kind: a register
   conjunct through the run's kept registers, an arithmetic one by assumption, every q64 / bytes_at by Hbkeep off
   the write set, the frame shadow carried unchanged (the run writes no shadow byte).  No conjunct is named by
   position, so a Theorem Labs lane's announced trailer word q64 m (fr + 4088) (flag_addr ..) needs no edit: the run writes
   nothing above fr + 2540.  TESTED both ways in a working-tree copy of ACtlCutP.v (reverted, never committed):
   with q64 m (fr + 4088) 0 APPENDED to FRAC and with it INSERTED mid-chain; the build logs are named in the
   commit message.
   TYPES-ONLY: no value or bound below depends on the substituted port_core_refused_* numerals.

   SECTION HYPOTHESES (exact text at the Section; source of each)
   - LAWS : Reusable.YG0d.AR_laws segs B.  The core's AR law record (YCbq.v:207, YG0d Section j), which
     ajournal_exec, frames_bounds, al_frames, al_blocks, sep_block_frame, al_client_img, frame_vis, heap_vis
     and heap_sh_vis all take; ACtl.v states it too (ACtl.v:237, blob c4edf0be7fe) and discharges it in its
     section 9.  Unchanged by the route (C) switch: it is the ONLY Section hypothesis, before and after.
   - NO kit placeholder: the two image facts come from the shared kit, Required qualified and cited by name,
     A.ACtlG.Kit.kit_wx (wx_segs_nowrap segs, for SRr_fevt_hid) and A.ACtlG.Kit.kit_segs_low (the image
     placement premise of ajournal_exec); Kit.v (an earlier version, blob 9ce90f0b988, not in this delivery) on a working branch 1899bed1aee.  kit_frac_move
     is not used (FRAC is destructured and rebuilt, because this run writes memory) and kit_RNG0 is not used
     (the footprint is RNG_W).
   CITED BY NAME, NOT HYPOTHESES: the callee contract proof (reac_ports_parse_F_holds_on), the run
   (R17Fon.r17_evt_F_on), the region transport (ShadowRwOnK.fl_shadow_rw_on), the
   lifts (YA0nR.SRr_fevt_hid, SRr_xregs_eqv), the bridge lemmas of A.ProgBridge, the visibility lemmas
   (ProgWorldVis{Win,Frame,Heap}), and the v1.9 helpers of lib/A/Prog/Seg/R17.v, reused QUALIFIED.

   CLOSURE: every Require below is qualified, no Import / Export of a project module; no statement here names a
   frame-route identifier.  The proof-internal uses of A.Prog.Seg.R17's helpers are Qed-closed lemmas over
   lib/Lib memory predicates only (a Theorem Labs lane 23:54Z allows that).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / Reusable.YG0d-qualified everywhere.
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R17.v  -- hits only inside comments.
   NAME RESOLUTION (measured at the first builds): the _F closure loads lib/A/Reusable, whose YK11 / YK1b / YI04 /
   YM05 / YO09 also end in `Reusable.<name>`, so a bare `Reusable.YK11` resolves to the A copy (a different
   FPState / RunCeil class).  Those five are written `lib.Reusable.<name>` here, as ProgWorldVisWin.v does.  Likewise
   R17Fon's post states munch / wmono over lib/Lib's `Frame` by its full path; the proof still pins them to
   Lib.Frame once, by conversion (MUL / WML), as it did for R17F's post.

   BUILD STATE: types-only.  Built with pgbc make (a build machine; the commit message names the log and rc) on
   a working branch = the interim glue + a working branch 1899bed1aee + the callee files by path (5541f8cc3cd).
   Print Assumptions glue_seg_R17: Rocq primitives (PrimInt63 / PrimString / PrimArray) and
   FunctionalExtensionality.functional_extensionality_dep only.

   No Axiom, no Parameter, no Abort, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
(* The core's Reusable and lib/Lib are named through their directory in the From prefix, so each Require matches
   exactly one file (ctrlgate rule (c) REQ: `Reusable.YK11` under `...lib` also matches A./B./U.Reusable.YK11).
   The core copies are the intended ones: ACtl.v's walk is stated over them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG01 YG0d YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Step Cells PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.MemMono A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.Tac_rt2_b2 A.Prog.Seg.B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R17.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_parse_c A.Prog.reac_ports_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R17Fon.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:80 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local helpers.  None of these is a Kit helper: they are run-level / image-level glue for this stage. *)

(* Read one conjunct of a cut shell BY TYPE, never by position, so a conjunct appended to or inserted in the
   shell (a Theorem Labs lane's FRAC trailer word) cannot move it. *)
Ltac r17g_get H T N := assert (N : T) by (decompose [and ex] H; assumption).

(* One conjunct of FRAC at the run's end memory, from the decomposed FRAC at the start memory m, by its KIND,
   never by its position (glue_seg_R17's exit cut): an arithmetic conjunct by assumption; a register conjunct
   through the kept-register facts C2 .. C26; a q64 / bytes_at conjunct by the keep step Hbkeep off the write set;
   the frame shadow carried unchanged, its range outside the write set by HSHout.  The locals are arguments, as in
   a Theorem Labs lane's r1g_frac_walk, because a pattern in an `all:` sentence cannot name a proof-local variable. *)
Ltac r17g_frac_leaf m fr Hbkeep HSHout C2 C3 C4 C8 C9 C19 C26 :=
  first
    [ assumption
    | (unfold ACtlCut.rgv, Reusable.YG0d.spZ in *;
       rewrite ?C2, ?C3, ?C4, ?C8, ?C9, ?C19, ?C26; assumption)
    | (unfold ACtlCutP.q64 in *; apply Hbkeep;
       [ try unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?lib.Lib.Mem.length_le8;
         let x := fresh "x" in let Hx := fresh "Hx" in
         intros x Hx; cbn [Lib.Frame.outside]; split; [lia | split; [lia | exact I]]
       | assumption ])
    | (lazymatch goal with
       | Hb : lib.Lib.Mem.bytes_at _ m (ACtlCutP.Sfr fr) ?s, Hl : length ?s = _ |- exists _, _ =>
           exists s; split; [apply Hbkeep; [rewrite Hl | exact Hb] | exact Hl]
       end;
       unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES;
       try change (Z.of_nat (Z.to_nat (3136 / 8))) with 392;
       exact HSHout) ].

(* A byte the memory map answers is writable through the view. *)
Lemma r17g_wv_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> wview A.Img0.rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

(* ... and the byte it answers is the byte the reader gives. *)
Lemma r17g_mrd_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> lib.Lib.Mem.mrd A.Img0.rsegs m x = Some b.
Proof. intros m x b H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

(* A footprint run only grows the memory map. *)
Lemma r17g_mem_grows_of_mstepsF : forall RNG ms ms',
  Lib.ExecF.mstepsF A.Img0.rsegs RNG ms ms' -> lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' H. induction H as [ms | ms ms1 ms2 Hs _ IH].
  - apply lib.Reusable.YK1b.mem_grows_refl.
  - eapply lib.Reusable.YK1b.mem_grows_trans; [| exact IH].
    exact (lib.Reusable.YI04.step_mem_grows A.Img0.rsegs _ _
             (Lib.ExecF.mstepF_step A.Img0.rsegs RNG _ _ Hs)).
Qed.

(* ... so an evtF may carry that fact into its post, which is where ajournal_exec reads it. *)
Lemma r17g_evtF_grows : forall RNG (P : machine_state -> Prop) ms,
  Lib.ExecF.evtF A.Img0.rsegs RNG P ms ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms' => lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms') /\ P ms') ms.
Proof.
  intros RNG P ms (ms1 & HMS & HP). exists ms1. split; [exact HMS|].
  split; [exact (r17g_mem_grows_of_mstepsF RNG ms ms1 HMS) | exact HP].
Qed.

(* An address of one of the image's four loaded spans is an image address. *)
Lemma r17g_in_img_lo : forall a, 0x10000 <= a < 0x5fe000 -> Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (HIN : forall b sz,
            In (b, sz) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) ->
            b <= a < b + sz -> Reusable.YG0d.in_img segs a).
  { intros b sz Hin Hr. apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
    exists s. split; [exact Hs | exact Hr]. }
  rewrite A.ProgBridge.rsegs_spans in HIN.
  destruct (Z_lt_le_dec a 0x30000) as [h1|h1];
    [apply (HIN 0x10000 0x20000); [left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 0x9e000) as [h2|h2];
    [apply (HIN 0x30000 0x6e000); [right; left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 0xa1000) as [h3|h3];
    [apply (HIN 0x9e000 0x3000); [right; right; left; reflexivity | lia]|].
  apply (HIN 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

(* The 20 port bytes of the round trip: rt_pbs inp = firstn 20 (skipn 18 (rt_F inp 0)) (R17.v:449-464). *)
Lemma r17g_pbs_at : forall (inp : list byte) (m : word -> option byte) (phi : Z),
  (50 <= length (A.Prog.SlotModel.rt_F inp 0))%nat ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m phi (A.Prog.SlotModel.rt_F inp 0) ->
  length (A.Prog.SlotModel.rt_pbs inp) = 20%nat /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (phi + 18) (A.Prog.SlotModel.rt_pbs inp).
Proof.
  intros inp m phi Hlen50 HF.
  assert (EX : A.Prog.SlotModel.rt_pbs inp = firstn 20 (skipn 18 (A.Prog.SlotModel.rt_F inp 0))).
  { unfold A.Prog.SlotModel.rt_pbs, Prog.RcFrag.bsl, A.Prog.SlotModel.rt_g, A.Prog.SlotModel.fr50.
    change (Z.to_nat 20) with 20%nat. change (Z.to_nat 18) with 18%nat.
    rewrite firstn_app. replace (50 - length (A.Prog.SlotModel.rt_F inp 0))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn.
    rewrite Nat.min_l by lia. reflexivity. }
  split.
  { rewrite EX, length_firstn, length_skipn. rewrite Nat.min_l by lia. reflexivity. }
  assert (HLS : lib.Lib.Mem.bytes_at A.Img0.rsegs m (phi + 18)
                  (firstn 20 (skipn 18 (A.Prog.SlotModel.rt_F inp 0)))).
  { pose proof HF as HF'. rewrite <- (firstn_skipn 18 (A.Prog.SlotModel.rt_F inp 0)) in HF'.
    apply lib.Lib.Mem.bytes_at_app in HF' as [_ HF'].
    rewrite length_firstn, Nat.min_l in HF' by lia.
    rewrite <- (firstn_skipn 20 (skipn 18 (A.Prog.SlotModel.rt_F inp 0))) in HF'.
    apply lib.Lib.Mem.bytes_at_app in HF' as [HF' _]. exact HF'. }
  rewrite EX. exact HLS.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)

Section GlueR17.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :244-245), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8183c_at := (ACtlCutP.C_A8183c_at B).
Local Notation C_A81858_at := (ACtlCutP.C_A81858_at B).

(* The core's AR law record (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The two image facts (wx_segs_nowrap, segs_low) are A.ACtlG.Kit.kit_wx / kit_segs_low, cited below. *)

Lemma glue_seg_R17 : forall POST (b : nat), CF POST (ix_cut C_A81858_at [Z.of_nat b]) -> CF POST (ix_cut C_A8183c_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A8183c_at, ACtlCutP.v:1559) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8183c_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPERM & HFRAC &
    (Hgn & Hb6 & HHB & R23 & HOUR & HOUTA & HCUR & Hsp216) & Hb0 & HRF & Ha0 &
    Hsp112 & Hsp8 & Hsp0 & Hsp200 & HAQ & Hsp128 & HPRO & Hsp104 & Hsp96 & Hsp64 & R21 &
    Hsp144 & Hsp192 & HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWsc & Hsp152 & HAD38 & HRXS).
  subst b.
  (* ---- the carried runtime facts: ctl_rt_C's four conjuncts (ACtlRtC.v:44-46).  Hcut / Himg are only carried to
     the exit; the stage reads no shadow byte through them (the run's twin takes no shadow premise). *)
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  (* ---- the journal's own facts *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hstk as (_ & _ & Hceil & Hlo32 & _ & _ & _).
  unfold A.ACfn.LLVMF_STK in Hlo32, Hpres.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [HC1 _].
  unfold Reusable.YG0f.ASAN_CEIL in HC1.
  (* ---- the frame: its address, its bounds, its presence *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (EFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  rewrite Efr3 in Hf4096. rewrite Efr3, EFB in Hfceil.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfapp & Hfpres & _).
  rewrite Efr3, EFB in Hfapp. rewrite Efr3, EFB in Hfpres.
  (* ---- FRAC gives the spill base A and the machine sp, read BY TYPE (r17g_get), never by position *)
  pose proof HFRAC as (A & sp & HFw).
  r17g_get HFw (lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 sp) F2r.
  r17g_get HFw (sp mod 16 = 0) Fspm.
  r17g_get HFw (ACtlCut.rgv regs3 9 A) F9r.
  r17g_get HFw (fr mod 32 = 0) Ffrm.
  r17g_get HFw (A mod 32 = 0) FAm.
  r17g_get HFw (A <= ACtlCut.c_sp cx) FAle.
  r17g_get HFw (sp <= A) FspA.
  r17g_get HFw (fr + ACtlCutP.FRAME_BYTES <= A) FfrA.
  r17g_get HFw (A + 416 <= ACtlCut.c_sp cx) FA416.
  r17g_get HFw (ACtlCut.c_sp cx - 4096 < sp) Fsp4.
  (* the route (C) walk's FRAC states the entry sp's top NON-strictly (ACtlCutP.v FRAC, batch 4 item B5.4) *)
  r17g_get HFw (ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) FSapp.
  unfold ACtlCutP.FRAME_BYTES in FfrA. unfold A.AsanRT.APPMEM_END in FSapp.
  assert (HA0 : 0 <= A) by lia.
  assert (Hfrsp : fr + 4096 < sp - 16) by lia.
  (* ---- app memory of the two written windows *)
  assert (HappW1 : A.AsanRTFacts.app_ivl (sp - 16) sp).
  { intros a Ha. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. right. lia. }
  assert (HappF : A.AsanRTFacts.app_ivl fr (fr + 4096)).
  { intros a Ha.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Hfapp.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hfapp as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia | right; lia]. }
  assert (HAW : A.AsanRTFacts.all_app [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]).
  { cbn [A.AsanRTFacts.all_app]. split; [exact HappW1|]. split; [|exact I].
    intros a Ha. apply HappF. lia. }
  (* ---- the outside sets *)
  assert (HOutF : forall x, fr <= x < fr + 2528 \/ fr + 2540 <= x < fr + 4096 ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [lia|]. split; [lia|exact I]. }
  assert (HAout : forall x, A <= x < A + 416 ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [lia|]. split; [lia|exact I]. }
  assert (HSVout : forall x, A.AsanRT.in_shadow x ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [|split; [|exact I]]; intro Hc.
    - exact (A.AsanRTFacts.app_not_shadow x (HappW1 x Hc) Hx).
    - exact (A.AsanRTFacts.app_not_shadow x (HappF x ltac:(lia)) Hx). }
  assert (Hfrnimg : forall a, fr <= a < fr + 4096 -> ~ Reusable.YG0d.in_img segs a).
  { intros a Ha.
    refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR _)).
    right. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr3, EFB. exact Ha. }
  assert (Hfrlo : fr + 4096 <= 0x10000 \/ 0x5fe000 <= fr).
  { destruct (Z_le_gt_dec (fr + 4096) 0x10000) as [HL1|HL1]; [left; exact HL1|].
    destruct (Z_le_gt_dec 0x5fe000 fr) as [HL2|HL2]; [right; exact HL2|].
    exfalso. apply (Hfrnimg (Z.max fr 0x10000) ltac:(lia)). apply r17g_in_img_lo. lia. }
  assert (HIout : forall x, Reusable.YG0d.in_img segs x ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. pose proof (A.ACtlG.Kit.kit_segs_low x Hx) as Hxl. unfold Reusable.YG0f.kLowMemEnd in Hxl.
    cbn [Lib.Frame.outside]. split; [lia|]. split; [|exact I].
    intro Hc. exact (Hfrnimg x ltac:(lia) Hx). }
  assert (HROout : forall a : word, lib.Lib.Mem.ro_addr A.Img0.rsegs a = true ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] (bv_unsigned a)).
  { intros a Hro. pose proof (A.Prog.Seg.R17.r17_ro_lt a Hro) as Hlt.
    cbn [Lib.Frame.outside]. split; [lia|]. split; [|exact I]. intro Hc.
    assert (Hn : ~ Reusable.YG0d.in_img segs (bv_unsigned a)) by (apply Hfrnimg; lia).
    assert (HFS : find_segment A.Img0.rsegs (bv_unsigned a) 1 = None)
      by exact (Reusable.YCbq.find_segment_none segs (bv_unsigned a) Hn).
    unfold lib.Lib.Mem.ro_addr in Hro. rewrite HFS in Hro. discriminate Hro. }
  assert (HRTdisj : Lib.Frame.disjoint_from [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]
                      A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO)).
  { unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. cbn [Lib.Frame.disjoint_from].
    split; [lia|]. split; [lia|exact I]. }
  (* ---- the live block of this turn *)
  assert (Hinblk : In (phi, ACtlCutP.rnb cx 0) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPERM)).
    apply in_or_app. right. left. reflexivity. }
  assert (Hnz : ACtlCutP.rnb cx 0 <> 0) by exact (proj1 (proj2 HRF)).
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (ACtlCut.c_in cx) 0 Hnz) as (_ & Hnb & HLn).
  assert (Hrnb : 124 <= ACtlCutP.rnb cx 0 <= 1492) by exact Hnb.
  assert (Hlen50 : (50 <= length (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) 0))%nat)
    by (rewrite HLn; lia).
  assert (ELen : Z.of_nat (length (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) (Z.of_nat 0)))
                 = ACtlCutP.rnb cx 0).
  { change (Z.of_nat 0) with 0. rewrite HLn, Z2Nat.id by lia. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx 0) HAR Hinblk)
    as (_ & Hphi4096 & Hphiceil & _ & _ & _ & _).
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.rnb cx 0) = ACtlCutP.rnb cx 0).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hnz). reflexivity. }
  rewrite Ereq in Hphiceil.
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  (* block vs frame *)
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx 0)
                6 (ACtlCut.c_fpos cx) HAR Hinblk Hin6) as Hsep.
  unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep.
  rewrite Ereq, Efr3, EFB in Hsep.
  assert (HblkW : forall x, phi <= x < phi + ACtlCutP.rnb cx 0 ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [lia|]. split; [lia|exact I]. }
  (* ---- the block's bytes and the 20 port bytes *)
  assert (HFb : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 phi
                  (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) (Z.of_nat 0)))
    by exact (proj2 (proj2 (proj2 HRF))).
  destruct (r17g_pbs_at (ACtlCut.c_in cx) mem3 phi Hlen50 HFb) as (Hpbslen & Hpbsat).
  (* ---- the two spill loads, as read-only cells at the good base A *)
  assert (RO1 : lib.Lib.Step.ro_cells A.Img0.rsegs mem3 (A + 112)
                  [lib.Lib.Cells.C8 (Z_to_bv 64 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)))])
    by exact (A.Prog.Seg.R17.r17_spill_ro regs3 mem3 112 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) A
                Hsp112 F9r HA0 ltac:(lia) ltac:(lia)).
  assert (RO2 : lib.Lib.Step.ro_cells A.Img0.rsegs mem3 (A + 216) [lib.Lib.Cells.C8 (Z_to_bv 64 (fr + 2528))])
    by exact (A.Prog.Seg.R17.r17_spill_ro regs3 mem3 216 (fr + 2528) A Hsp216 F9r HA0 ltac:(lia) ltac:(lia)).
  (* ---- the stack window of the run *)
  assert (ST : Lib.Frame.stk A.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) sp).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros a Ha. destruct (Hpres a ltac:(lia)) as (_ & bb & Hbb).
    split; [exact (r17g_wv_some mem3 (lib.Lib.Mem.wa a) bb Hbb)|].
    exists bb. exact (r17g_mrd_some mem3 (lib.Lib.Mem.wa a) bb Hbb). }
  (* ---- the 12 output bytes are writable *)
  assert (HWRq : lib.Lib.Mem.wr_at A.Img0.rsegs mem3 (fr + 2528) 12).
  { split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros i Hi. destruct (Hfpres (fr + 2528 + i) ltac:(lia)) as ((_ & bb & Hbb) & _).
    exact (r17g_wv_some mem3 (lib.Lib.Mem.wa (fr + 2528 + i)) bb Hbb). }
  (* ---- addressability of the port buffer *)
  assert (HAp : A.AsanRT.addressable mem3 (phi + 18) 20).
  { destruct HHB as (Hphinz & HAphi). unfold A.ACtlK.a_size in HAphi.
    exact (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.rnb cx 0) 1) 18 20
             HAphi ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* ---- ports_ok *)
  assert (Hok : Prog.RcLeaf.ports_ok (phi + 18) (fr + 2528)
                  (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx)) = true).
  { unfold Prog.RcLeaf.ports_ok.
    rewrite (A.Prog.Seg.B3Rtm.a_rtm_decl (ACtlCut.c_in cx)).
    replace (phi + 18 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (fr + 2528 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity. }
  (* ---- the outside premise of the run *)
  assert (HOutside : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                               A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
            Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x [HG|[HC|HSh]].
    - apply HIout, r17g_in_img_lo. unfold A.AsanRT.GOT_CELL_K in HG. lia.
    - apply HIout, r17g_in_img_lo. unfold A.AsanRT.CELL_K in HC. lia.
    - exact (HSVout x HSh). }
  (* ---- the visibility premises *)
  assert (Vwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
            Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len Hlo Hhi. apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
             (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k lo len HJ Hlo Hhi). }
  assert (Vimg : forall lo len, 0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 ->
            Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ A.Prog.ImgBounds.IMG_LO
             (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO));
      [exact (A.ProgBridge.img_vis_W W3) | | |];
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  assert (Vheap : Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (phi + 18) 20).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx 0) (phi + 18) 20
             HAR Hinblk ltac:(lia) ltac:(rewrite Ereq; lia)). }
  assert (Vheapsh : Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                      (A.AsanRT.shadow_addr (phi + 18))
                      (A.AsanRT.shadow_addr (phi + 18 + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx 0)
                (phi + 18) 20 HAR Hinblk ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia))
      as [Hz | Hv]; [exfalso; lia|].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (phi + 18))
             (A.Prog.rng_asan.sh_al8_hi (phi + 18) 20 - A.Prog.rng_asan.sh_al8_lo (phi + 18)));
      [exact Hv | | |];
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      replace (phi + 18 + 20 - 1) with (phi + 18 + 19) by lia; Z.div_mod_to_equations; lia. }
  assert (Vfrm : Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (fr + 2528) 12).
  { apply A.ProgBridge.rng_of_visible.
    refine (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
                     (fr + 2528) 12 HAR Hin6 _ _)); rewrite Efr3, ?EFB; lia. }
  assert (Vfrmsh : Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                     (A.AsanRT.shadow_addr (fr + 2528))
                     (A.AsanRT.shadow_addr (fr + 2528 + 11) - A.AsanRT.shadow_addr (fr + 2528) + 1)).
  { apply A.ProgBridge.rng_of_visible.
    destruct (proj2 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
                       (fr + 2528) 12 HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, EFB; lia))
                ltac:(lia) ltac:(rewrite Efr3; Z.div_mod_to_equations; lia)
                ltac:(rewrite Efr3, EFB; Z.div_mod_to_equations; lia)) as [Hz | Hv]; [exfalso; lia|].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (fr + 2528))
             (A.Prog.rng_asan.sh_al8_hi (fr + 2528) 12 - A.Prog.rng_asan.sh_al8_lo (fr + 2528)));
      [exact Hv | | |];
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
      replace (fr + 2528 + 12 - 1) with (fr + 2528 + 11) by lia; Z.div_mod_to_equations; lia. }
  (* ---- G3: the cut's configuration in the run's state form, then the walk at the run's register map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8183c_at [Z.of_nat 0])) with 0x8183c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8183c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* ---- G4: the run, and the lift at RNG_W *)
  pose proof (A.Prog.Seg.R17Fon.r17_evt_F_on A.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
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
                sp A phi (fr + 2528) (A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) (ACtlCut.c_sp cx - 32768)
                (A.Prog.SlotModel.rt_pbs (ACtlCut.c_in cx))
                F2r F9r Ha0 (proj1 (proj2 (proj2 HRF)))
                ltac:(lia) Hphi50 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                RO1 RO2 Hpbslen Hpbsat
                ltac:(clear - Ffrm; Z.div_mod_to_equations; lia) HWRq
                ltac:(lia) ltac:(lia) ltac:(lia)
                ST ltac:(lia) HAC HAp HAQ HOutside Hok
                (Vwin (A + 112) 8 ltac:(lia) ltac:(lia)) (Vwin (A + 216) 8 ltac:(lia) ltac:(lia))
                (Vwin (sp - A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME)
                      A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME
                      ltac:(unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; lia)
                      ltac:(unfold A.Prog.reac_ports_parse_c.REAC_PORTS_PARSE_FRAME; lia))
                (Vimg A.AsanRT.GOT_CELL_K 8 ltac:(unfold A.AsanRT.GOT_CELL_K; lia) ltac:(lia)
                      ltac:(unfold A.AsanRT.GOT_CELL_K; lia))
                (Vimg A.AsanRT.CELL_K 8 ltac:(unfold A.AsanRT.CELL_K; lia) ltac:(lia)
                      ltac:(unfold A.AsanRT.CELL_K; lia))
                Vheap Vheapsh Vfrm Vfrmsh) as HRUN.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
           (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
           (A.ProgBridge.fevt_of_evtF _ _ _ (r17g_evtF_grows _ _ _ HRUN)));
    [ exact (A.ProgBridge.fp_avoids_RNG_W (Reusable.YA0n.w_H W3)) |].
  (* ---- G5: the continuation *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (HGROW & R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 &
                   K24 & K10 & K27 & MU & WM & STq & HIq & HOq & H8q).
  subst ms'.
  (* R17Fon's post states munch / wmono over lib/Lib's Frame by its full path; pin them here once to the names this
     file uses, by conversion. *)
  assert (MUL : Lib.Frame.munch [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem3 m') by exact MU.
  assert (WML : Lib.Frame.wmono A.Img0.rsegs mem3 m') by exact WM.
  (* the meta bytes, hence the kept addressability, and the byte transports *)
  pose proof (A.AsanRTFacts.munch_meta [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem3 m' MUL HAW) as HMETA.
  assert (Hbkeep : forall a (bs : list byte),
            (forall x, a <= x < a + Z.of_nat (length bs) ->
               Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x) ->
            lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs)
    by (intros a bs Hout Hbb;
        exact (A.Prog.Seg.Tac_rt2_b2.a_keep [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]
                 mem3 m' a bs MUL Hout Hbb)).
  assert (Hspk : forall off v, 0 <= off <= 304 ->
            ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v Hoff Hs.
    exact (A.Prog.Seg.R17.r17_spill_keep regs3 R mem3 m' off v A
             [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]
             Hs F9r K9 HA0 ltac:(lia) ltac:(lia) MUL
             ltac:(intros x Hx; exact (HAout x ltac:(lia)))). }
  assert (Hrwk : forall a (n : nat) (bs : list byte), fr + 2540 <= a -> a + Z.of_nat n <= fr + 4096 ->
            lib.Lib.Step.rw_cells A.Img0.rsegs mem3 a [lib.Lib.Cells.CB n bs] ->
            lib.Lib.Step.rw_cells A.Img0.rsegs m' a [lib.Lib.Cells.CB n bs]).
  { intros a n bs H1 H2 Hc.
    exact (A.Prog.Seg.R17.r17_rwcb_keep [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem3 m' a n bs
             MUL WML ltac:(intros x Hx; exact (HOutF x ltac:(lia))) Hc). }
  assert (Haddrk : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Hd; exact (A.AsanRTFacts.addressable_kept mem3 m' p n Hd HMETA)).
  (* ---- the exit configuration *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81858_at [Z.of_nat 0])) R m' md')
            (POST cx)).
  apply (HX cx [Z.of_nat 0] fr k ly3 S3 W3 R m' md' HB).
  - (* the journal across the write set *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (sp - 16 <= a < sp) \/ (fr + 2528 <= a < fr + 2528 + 12)).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MUL. cbn [Lib.Frame.outside]. split; [intro Hc; apply Hx; left; exact Hc|].
      split; [intro Hc; apply Hx; right; exact Hc | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in Hx |- *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx | exact (HGROW x Hx)].
    + exact Hhid.
    + exact Hsbm.
    + intros a [Ha | Ha].
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * right. right. right. exists 6, (ACtlCut.c_fpos cx).
        split; [unfold ACtlCut.own6; apply in_eq|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3, EFB. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax term on both cuts *)
    exact Hk.
  - (* the exit body, C_A81858_at (ACtlCutP.v:1590-1619) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81858_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact HPERM|].
    (* FRAC at (R, m'), RE-ESTABLISHED by a walk over the goal's conjuncts, none named by position (header) *)
    split.
    { assert (C2 : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact K2.
      assert (C3 : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact K3.
      assert (C4 : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact K4.
      assert (C8 : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact K8.
      assert (C9 : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
      assert (C19 : lib.Reusable.YK11.getr R 19 = lib.Reusable.YK11.getr regs3 19) by exact K19.
      assert (C26 : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact K26.
      (* the frame shadow [S(fr), S(fr) + 392) is shadow memory, so outside the write set *)
      assert (HSHout : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 392 ->
                Lib.Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
      { intros x Hx. apply HSVout.
        assert (Ex : A.AsanRT.shadow_addr (fr + 8 * (x - ACtlCutP.Sfr fr)) = x).
        { rewrite (A.Prog.MemMono.sh_add8 fr (x - ACtlCutP.Sfr fr)
                     ltac:(clear - Ffrm; Z.div_mod_to_equations; lia)).
          unfold ACtlCutP.Sfr. lia. }
        rewrite <- Ex. apply A.AsanRTFacts.shadow_of_app. apply HappF.
        unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr in Hx |- *.
        clear - Ffrm Hx Hf4096. Z.div_mod_to_equations; lia. }
      pose proof HFw as HFd. decompose [and ex] HFd.
      exists A, sp.
      repeat lazymatch goal with |- _ /\ _ => split end.
      all: r17g_frac_leaf mem3 fr Hbkeep HSHout C2 C3 C4 C8 C9 C19 C26. }
    (* the inner group *)
    split.
    { split; [exact Hgn|]. split; [exact Hb6|].
      split; [destruct HHB as (Hnz0 & HAphi); split; [exact Hnz0 | exact (Haddrk _ _ HAphi)]|].
      split; [unfold ACtlCut.rgv in *;
              transitivity (lib.Reusable.YK11.getr regs3 23); [exact K23 | exact R23]|].
      split; [unfold ACtlCutP.OURb; apply Hbkeep;
              [rewrite A.Prog.SlotModel.OUR_length; intros x Hx; apply HOutF; right; lia | exact HOUR]|].
      split; [unfold ACtlCutP.OUTA in *; exact (Haddrk _ _ HOUTA)|].
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
        split; [unfold ACtlCut.rgv in *;
                transitivity (lib.Reusable.YK11.getr regs3 22); [exact K22 | exact Hc22]
               | unfold ACtlCut.rgv in *;
                 transitivity (lib.Reusable.YK11.getr regs3 25); [exact K25 | exact Hc25]]. }
      exact (Hspk 200 _ ltac:(lia) Hsp200). }
    split; [reflexivity|].
    (* RFb at (R, m') *)
    split.
    { destruct HRF as ((Hb6' & HCUR' & HOUR' & R23' & HIDB & HFGB) & _ & R24' & HFb').
      split.
      { split; [exact Hb6'|].
        split.
        { destruct HCUR' as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
          split; [unfold ACtlCut.rgv in *;
                  transitivity (lib.Reusable.YK11.getr regs3 22); [exact K22 | exact Hc22]
                 | unfold ACtlCut.rgv in *;
                   transitivity (lib.Reusable.YK11.getr regs3 25); [exact K25 | exact Hc25]]. }
        split; [unfold ACtlCutP.OURb in *; apply Hbkeep;
                [rewrite A.Prog.SlotModel.OUR_length; intros x Hx; apply HOutF; right; lia
                | exact HOUR']|].
        split; [unfold ACtlCut.rgv in *;
                transitivity (lib.Reusable.YK11.getr regs3 23); [exact K23 | exact R23']|].
        split.
        { unfold ACtlCutP.IDBr in *. apply Hbkeep; [|exact HIDB].
          assert (LI : length (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 0) = 38%nat) by reflexivity.
          rewrite LI. intros x Hx. apply HOutF; left; lia. }
        unfold ACtlCutP.FGBr in *. apply Hbkeep; [|exact HFGB].
        assert (LF : length (A.Prog.SlotModel.RFG (ACtlCut.c_in cx) 0) = 72%nat) by reflexivity.
        rewrite LF. intros x Hx. apply HOutF; left; lia. }
      split; [exact Hnz|].
      split; [unfold ACtlCut.rgv; exact K24|].
      apply Hbkeep; [|exact HFb']. rewrite ELen. exact HblkW. }
    split; [unfold ACtlCut.rgv; exact K27|].
    split; [unfold ACtlCut.a0v, ACtlCut.rgv; exact K10|].
    split; [unfold ACtlCutP.u32; exact HIq|].
    split; [unfold ACtlCutP.u32; replace (fr + 2532) with (fr + 2528 + 4) by lia; exact HOq|].
    split; [exact (Hspk 216 _ ltac:(lia) Hsp216)|].
    split; [exact (Hspk 8 _ ltac:(lia) Hsp8)|].
    split; [exact (Hspk 0 _ ltac:(lia) Hsp0)|].
    split; [exact (Hspk 112 _ ltac:(lia) Hsp112)|].
    split; [exact (Hspk 128 _ ltac:(lia) Hsp128)|].
    (* PRO at (R, m') *)
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA6 & PIN & PNA &
                        P184 & P256 & P264 & P272 & P32).
      split; [exact (Hspk 40 _ ltac:(lia) P40)|].
      split; [exact (Hspk 120 _ ltac:(lia) P120)|].
      split; [exact (Hspk 136 _ ltac:(lia) P136)|].
      split; [exact (Hspk 160 _ ltac:(lia) P160)|].
      split; [exact (Hspk 168 _ ltac:(lia) P168)|].
      split; [exact (Hspk 176 _ ltac:(lia) P176)|].
      split; [exact (Hspk 208 _ ltac:(lia) P208)|].
      split; [exact (Hspk 248 _ ltac:(lia) P248)|].
      split; [exact (Haddrk _ _ PA6)|].
      split.
      { pose proof HB as (HPRE & _).
        pose proof HPRE as (_ & _ & _ & _ & Hor & Hlenin & _).
        apply Hbkeep; [|exact PIN].
        destruct Hor as [(Hn0 & _) | (Hnpos & HinP)].
        - assert (Hl0 : length (ACtlCut.c_in cx) = 0%nat) by lia.
          rewrite Hl0. intros x Hx. exfalso. cbn [Z.of_nat] in Hx. lia.
        - assert (HinP3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
          { apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact HinP. }
          destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                      HAR HinP3) as (_ & Hp4096 & Hpceil & _).
          assert (Ereq2 : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
          { unfold Reusable.YG00.req_size.
            rewrite (proj2 (Z.eqb_neq (ACtlCut.c_n cx) 0) ltac:(lia)). reflexivity. }
          rewrite Ereq2 in Hpceil.
          pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3
                        (ACtlCut.c_p cx) (ACtlCut.c_n cx) 6 (ACtlCut.c_fpos cx) HAR HinP3 Hin6) as Hsep2.
          unfold Reusable.YG0f.zdisjoint in Hsep2. cbn [fst snd] in Hsep2.
          rewrite Ereq2, Efr3, EFB in Hsep2.
          rewrite <- Hlenin.
          intros x Hx. cbn [Lib.Frame.outside]. split; [lia|]. split; [lia|exact I]. }
      split; [intros Hn; exact (Haddrk _ _ (PNA Hn))|].
      split; [exact (Hspk 184 _ ltac:(lia) P184)|].
      split; [exact (Hspk 256 _ ltac:(lia) P256)|].
      split; [exact (Hspk 264 _ ltac:(lia) P264)|].
      split; [exact (Hspk 272 _ ltac:(lia) P272) | exact (Hspk 32 _ ltac:(lia) P32)]. }
    split; [exact (Hspk 104 _ ltac:(lia) Hsp104)|].
    split; [exact (Hspk 96 _ ltac:(lia) Hsp96)|].
    split; [exact (Hspk 64 _ ltac:(lia) Hsp64)|].
    split; [unfold ACtlCut.rgv in *;
            transitivity (lib.Reusable.YK11.getr regs3 21); [exact K21 | exact R21]|].
    split; [exact (Hspk 144 _ ltac:(lia) Hsp144)|].
    split; [exact (Hspk 192 _ ltac:(lia) Hsp192)|].
    split; [destruct HRWid as (idb & Hc); exists idb;
            exact (Hrwk (fr + 2688) 38%nat idb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hc)|].
    split; [destruct HRWjk as (jk & Hc); exists jk;
            exact (Hrwk (fr + 2768) 72%nat jk ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hc)|].
    split; [exact (Hspk 280 _ ltac:(lia) Hsp280)|].
    split; [exact (Hspk 240 _ ltac:(lia) Hsp240)|].
    split; [destruct HRWjy as (jy & Hc); exists jy;
            exact (Hrwk (fr + 3040) 1%nat jy ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hc)|].
    split; [destruct HRWsc as (sc & Hc); exists sc;
            exact (Hrwk (fr + 3056) 32%nat sc ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hc)|].
    split; [exact (Hspk 152 _ ltac:(lia) Hsp152)|].
    split; [exact (Haddrk _ _ HAD38)|].
    (* RXS at (R, m') *)
    { destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & XA).
      split; [exact (Hspk 48 _ ltac:(lia) X48)|].
      split; [exact (Hspk 56 _ ltac:(lia) X56)|].
      split; [exact (Hspk 88 _ ltac:(lia) X88)|].
      split; [exact (Hspk 80 _ ltac:(lia) X80)|].
      split; [exact (Hspk 72 _ ltac:(lia) X72)|].
      split; [exact (Hspk 8 _ ltac:(lia) X8)|].
      split; [exact (Hspk 0 _ ltac:(lia) X0)|].
      split; [exact (Hspk 200 _ ltac:(lia) X200)|].
      split; [exact (Hspk 216 _ ltac:(lia) X216) | exact (Haddrk _ _ XA)]. }
  - (* ctl_rt_C B ly3 S3 m': the exit cut has the entry's ly3 S3, so the regions are kept (route (i)): asan_cells
       and ro_agree as before; the two shadow regions across the run's write set, which misses the shadow (HSVout) *)
    split; [exact (A.AsanRTFacts.asan_cells_kept [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]
                     mem3 m' HAC MUL HRTdisj)|].
    split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Hcut MUL WML HSVout)|].
    split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Himg MUL WML HSVout)|].
    exact (A.Prog.Seg.R17.r17_ro_keep mem3 m' [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] HRO MUL HROout).
Qed.

End GlueR17.

Print Assumptions glue_seg_R17.
