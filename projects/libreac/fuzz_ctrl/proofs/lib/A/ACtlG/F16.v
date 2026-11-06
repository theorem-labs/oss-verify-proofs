(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 883 of its 974 lines of code are new or changed and 1984 lines of the source are left out. *)
(* lib/A/ACtlG/F16.v -- GLUE for stage seg_F16 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:791-792) (an earlier version, blob a3c6b7b35017, not in this delivery)).  Written by a Theorem Labs lane (claimed in FREE-PIECES.md (a working note, not in this delivery); block owner another lane);
   single writer.  rule 24: no function proved.  proves no function
   (kind: segment lemma).
   Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5, memory-writing run, callee inside,
   section 8: the callee's contract_F premise closed by its CLOSED theorem); shape of lib/A/ACtlG/A5.v, and of
   a Theorem Labs lane's lib/A/ACtlG/F13.v (a working branch 7932c99a28f) for the memory side.

   WHAT IT PROVES
     glue_seg_F16 : forall POST (j : nat), CF POST (ix_cut C_A8229c_at [Z.of_nat j]) -> CF POST (ix_cut C_A821d0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F16.  Segment F16 is 0x821d0 -> 0x8229c (Seg/F16.v:1-30): the byte-sum loop 0x821d0-0x821f4 over the record's
   15-offset window (pll + 5 turns), the sum check 0x82208-0x8220c, the v1.9 tail 0x82210-0x82294 (the have check, the
   inlined joined_byte of FIRST bytes 9 / 10 with their instrumented checks, the 16-bit address compare) and the call
   of reac_identity_ingest at 0x82298, whose return is the exit cut 0x8229c.

   REUSE (rule 24, the three-clause search), proof-index glue_seg_F16 f16_evt_F f16_loop_F seg_F16, index v5 built
   2026-10-29T06:12:16Z from main@c4c03c57ba1 ossv/recipes@e5e7eba2cc0 ossv/candidates@ee89628c997
   b6a0088adcb (a hub release branch), lemma index 05:45:38Z over 10861 working branches:
     glue_seg_F16: 0 named, 0 by address, 0 related, 0 released, 0 in the delivered package, 0 unreleased working-branch hits.
     f16_evt_F / f16_loop_F: 0 released; UNRELEASED only lib/A/Prog/Seg/F16F.v:494 / :91 (a Theorem Labs lane's re-run, on
       this base; used here).
     seg_F16: 0 released; no match in the delivered proofs; UNRELEASED: Seg/F16.v:826 (the
       source), ACtl.v:653 (the statement), image B's lib/B/ACtlW4c.v:288 (a plan, not proved).
   At ossv/recipes c5e779efe8c (2026-10-31), glue_seg_F16, f16_evt_F / f16_loop_F and seg_F16 are defined only in this
   unit (glue_seg_F16 in this file, f16_evt_F / f16_loop_F at lib/A/Prog/Seg/F16F.v:494 / :91, seg_F16 at
   lib/A/Prog/Seg/F16.v:826 and lib/B/Prog/Seg/F16.v:1138, its statements lib/A/ACtl.v:792 and lib/B/ACtl.v:573 and image B's lib/B/ACtlW4c.v:4372, proved).
   At ossv/recipes c5e779efe8c (2026-10-31), this glue has no released counterpart outside this unit; its pieces are the core's (ajournal_exec, frames_bounds, al_blocks,
   sep_block_frame), a Theorem Labs lane's bridge and lifts, the visibility lemmas ProgWorldVis{Win,Heap,Frame}, and the glue
   base's shared kits (Kit.kit_frac_move / kit_wx / kit_segs_low, KitMem.kitmem_frac_munch for FRAC at the exit).

   THE RUN.  Seg/F16F.v's f16_evt_F_on (a Theorem Labs lane's route (C) twin of its mechanical re-run f16_evt_F of
   F16.f16_evt, F16F.v (at head lib/A/Prog/Seg/F16F.v:709; written on a working branch 66e4d6de408), Required, NOT assumed): f16_evt_F's statement
   with the callee premise reac_identity_ingest_contract_F -> _F_on and its `shadow_rw m` premise DROPPED.  The WHOLE
   segment, loop and callee included, as one ExecF.evtF under a footprint RNG.  F16F.v composes it from f16_loop_F
   (the source's own loop induction on the down-counter, branches stepped with lib/Lib/StepF.v) and the five tail
   runs f16_p210_F .. f16_p284_F; the loop is not re-composed here (a Theorem Labs lane 06:2xZ: the in-stage loop of F28a was needed
   only because no loop _F existed there).  Its callee premise, route (C) form reac_identity_ingest_contract_F_on
   (a Theorem Labs lane's reac_identity_ingest_c.v, premise shadow_rw DROPPED), is discharged by the callee's PROVED CLOSED
   theorem A.Prog.reac_identity_ingestF.reac_identity_ingest_F_holds_on (a Theorem Labs lane), NOT by an SRr_at lift.
   The run is lifted ONCE with Reusable.YA0nR.SRr_fevt_hid at RNG := ProgBridge.RNG_W (w_H W3).
   The run's post was checked against the exit cut's body before use: reac_identity_ingest_post keeps ra := 0x8229c,
   sp gp tp s0 s1 (= A) s2-s5 s6 (= phi + 18) s7-s9 s10 (= ASAN_K) s11, gives a0 = ingest_ret .. in {0, 1}, munch of
   the write set W = [(sp - 32, sp); (fr + 2688, fr + 2726)], wmono, stk of the callee window and the identity bytes
   ING (ID1 cx j) FA pb at fr + 2688: every register the exit body pins and every byte it states is in it or kept.

   THE TWO EXACT LOOP RANGES OF f16_evt_F_on AND THEIR VISIBILITY SOURCES (a Theorem Labs lane 06:2xZ check 3)
     (1) the record bytes the loop reads: rng RNG (fragb fr + 15) (Z.of_nat K), K = pll + 5 <= 56, i.e.
         [fr + 2783, fr + 2783 + K) inside the class-6 frame [fr, fr + 4096): ProgWorldVisFrame.frame_vis
         (AR_frames_law) at the journal's owned frame (6, c_fpos cx); bounds 0 <= lo and lo + len <= 2 ^ 64 from
         frames_bounds (fr + 4096 <= alloc_ceiling < 2 ^ 47).
     (2) their shadow bytes: rng RNG (Z.shiftr (fragb fr + 15) 3 + ASAN_K) (Z.shiftr (fragb fr + 15 + K - 1) 3 -
         Z.shiftr (fragb fr + 15) 3 + 1): the same frame_vis, its shadow-word part (the 64-byte hull of the range lies
         in the frame), narrowed to the byte-exact span by f16_sh_vis; the bounds come from that visible word cover.
   The other ranges: the spill cells [A + 104 / 56 / 256 / 48 / 144, +8) and the callee window [sp - 32, sp) by
   ProgWorldVisWin.win_vis (the journal's present stack window [c_sp - 32768, c_sp)); P256 = fr + 256, the 38
   identity bytes at fr + 2688 and the payload [fragb fr + 19, +pll) with their shadow covers by frame_vis; the two
   record bytes X1 / X2 and their shadow bytes by frame_vis (the FIRST body at fr + 2880) or ProgWorldVisHeap.heap_vis
   / heap_sh_vis (the live block (phi, flen cx j)); GOT_CELL_K / CELL_K by ProgBridge.img_vis_W.

   THE PROOF
   G1  the entry cut C_A821d0_at at [Z.of_nat j] (ACtlCutP.v:2342-2371); FRAC is destructed with `& _` (its last
       conjunct, the Batch3 fake-frame trailer word, is not read).
   G2  the premises of f16_evt_F_on from the cut, the journal and ctl_rt_C (its asan_cells conjunct only: the run's
       route (C) form drops shadow_rw, so neither shadow region is read), every bound from VISIBLE state: the frame from
       frames_bounds + the frame law + layout_le's ly_F + the core's frame_facts (fr >= 6332416); FRAC's spill base A
       and sp; the record block phi from al_blocks / sep_block_frame; the stack window from astk_ok; the model side
       (the turn closes a record: FgClose, so 50 <= flen, 14 <= fg_T <= 64, the window sum closes mod 128, FI gives
       have = 1 and the FIRST bytes) from Seg/F16.v's pure lemmas, as Seg/F16.v's seg_F16 derives them.
   G3  the walk moved from the cut's map regs3 to the run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, YA0nR.SRr_fevt_hid (the run writes memory).
   G5  the exit cut C_A8229c_at (ACtlCutP.v:2376-2417) at the run's end map and memory m':
         journal  YCbq.ajournal_exec with Wr := the callee's write set W (its stack window inside the journal's
                  stack window, the identity bytes inside the owned class-6 frame), the hidden bytes from
                  SRr_fevt_hid, mem_grows from munch and the readable post bytes;
         frames, frame law, k bound   unchanged (own6, the same kmax 14 + 2j + 1);
         body     every carried fact crosses W (FRAC's memory part by KitMem.kitmem_frac_munch, the trailer word
                  q64 (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) included: W misses [fr + 4088, fr + 4096);
                  FLSI, LK, F17CARRY, IFS2's record and FSj),
                  a0 = ingest_ret .. in {0, 1}, IFS3's identity of turn S j = the ingest of ID1 cx j (SlotModel's
                  fg_id on the FgClose edge);
         ctl_rt_C asan_cells / ro_agree kept by munch (W misses the runtime cells and the read-only image); the two
                  shadow regions cut_shadow B ly3 S3 and img_shadow kept by ShadowRwOnK.fl_shadow_rw_on (W misses the
                  shadow; the exit cut has the entry's ly3 S3, so the regions do not move).  No new hypothesis.

   SECTION HYPOTHESES (exact text below)
   - LAWS : Reusable.YG0d.AR_laws segs B -- ACtl.v:210's own hypothesis, name and text (YCbq Section a0's).  No other.
   ACtl.v carries seg_F16 as its Hypothesis (at head lib/A/ACtl.v:792); `glue_seg_F16 B MT XM_LIB RLO RHI LAWS` discharges it.

   CLOSURE (the glue closure rule): every Require is qualified and names the directory of the one file it means;
   no statement names a frame-route identifier; Seg/F16.v, Seg/F16F.v, Seg/F13.v, Seg/Tac_b5.v (frame route,
   Required for the run and its pure lemmas) are used proof-internally only.  Every use of a module that exists in
   several copies is written lib.Reusable.<X> / lib.Lib.<X> (core), or through a Module alias to the full path.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified.

   BUILD STATE: see the commit message (route (C) shell on a working branch 1899bed1aee, merged;
   no workspace substitution). *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YK04R YA0n YA0nR YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0f YG0n YG0d YG0s YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ProgBridge RoAdapt MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ProgWorldVisHeap ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan SlotModel RcAsanFPLib ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_identity_ingest_c reac_identity_ingestF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F13 F16 F16F Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit KitMem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcFrag RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK A.ACtlRtC.
Import ListNotations.
Local Open Scope Z_scope.

Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RIL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentLib.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module IIC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingest_c.
Module IIF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingestF.
Module S13 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F13.
Module S16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F16.
Module F16F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F16F.
Module TB5 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.Tac_b5.
Module RGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Module IMB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Proof-internal helpers (Qed, over the core's world and ACtlCutP's transcribed bodies). *)

(* Two 64-bit readings of one register name the same number when the two numbers are less than 2 ^ 64 apart. *)
Lemma f16_rgv_eq : forall regs r a b, ACtlCut.rgv regs r a -> ACtlCut.rgv regs r b ->
  - 2 ^ 64 < a - b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb D. unfold ACtlCut.rgv in *.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by (rewrite <- Ha; exact Hb).
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E.
  revert E D. change (2 ^ 64) with 18446744073709551616. intros E D.
  Z.div_mod_to_equations. lia.
Qed.

(* The ingest call's write set (reac_identity_ingest_c.v:18-19): outside, and its converse by decidability. *)
Lemma f16_W_out : forall S id x, (x < S - 32 \/ S <= x) -> (x < id \/ id + 38 <= x) ->
  FRM.outside (IIC.reac_identity_ingest_W S id) x.
Proof.
  intros S id x H1 H2. unfold IIC.reac_identity_ingest_W, IIC.REAC_IDENTITY_INGEST_FRAME. cbn [FRM.outside].
  split; [lia|]. split; [lia | exact I].
Qed.

Lemma f16_W_in : forall S id x, ~ FRM.outside (IIC.reac_identity_ingest_W S id) x ->
  (S - 32 <= x < S) \/ (id <= x < id + 38).
Proof.
  intros S id x H.
  destruct (Z_le_dec (S - 32) x); destruct (Z_lt_dec x S); [left; lia | | |];
  (destruct (Z_le_dec id x); destruct (Z_lt_dec x (id + 38)); [right; lia | | |]);
  exfalso; apply H; apply f16_W_out; lia.
Qed.

(* No image byte lives at or above 6283264 (RoAdapt.ro_rsegs_low), so a byte the reader returns there is a memory
   byte (a Theorem Labs lane's F13.v f13_mem_of_mrd). *)
Lemma f16_mem_of_mrd : forall (m : word -> option byte) x b, 6283264 <= x < 2 ^ 64 ->
  MEM.mrd rsegs m (MEM.wa x) = Some b -> m (MEM.wa x) = Some b.
Proof.
  intros m x b Hx H. unfold MEM.mrd in H. destruct (m (MEM.wa x)) as [c|] eqn:E; [exact H|].
  exfalso. rewrite A.MemNorm.seg_rom_unmapped in H; [discriminate H|].
  destruct (find_segment rsegs (bv_unsigned (MEM.wa x)) 1) as [s|] eqn:Ef; [|reflexivity].
  exfalso.
  destruct (A.RoAdapt.ro_find_below rsegs 6283264 (bv_unsigned (MEM.wa x)) 1 s A.RoAdapt.ro_rsegs_low Ef
              ltac:(lia)) as [Hlt|Hn]; [|lia].
  rewrite MEM.wa_unsigned in Hlt by lia. lia.
Qed.

(* A range whose bytes the journal shows present is a stk range. *)
Lemma f16_stk_of_present : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) ->
  FRM.stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as (_ & b & Hb).
  split.
  - unfold wview, MEM.wa. rewrite Hb. discriminate.
  - exists b. unfold MEM.mrd, MEM.wa. rewrite Hb. reflexivity.
Qed.

(* The bytes of [lo, lo + len) of an in_app range are app memory. *)
Lemma f16_app_of_in_app : forall {rc : lib.Reusable.YM05.RunCeil} lo len a,
  lib.Reusable.YG0f.in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros rc lo len a H Ha. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C1 C2] _].
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
Qed.

(* The frame's 392 shadow bytes are shadow addresses. *)
Lemma f16_sfr_shadow : forall fr x, (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> ART.app_mem a) ->
  ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> ART.in_shadow x.
Proof.
  intros fr x Happ Hx. unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hx.
  change (3136 / 8) with 392 in Hx.
  assert (Hdiv : (fr + 8 * (x - ACtlCutP.Sfr fr)) / 8 = fr / 8 + (x - ACtlCutP.Sfr fr)).
  { replace (8 * (x - ACtlCutP.Sfr fr)) with ((x - ACtlCutP.Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hin : fr <= fr + 8 * (x - ACtlCutP.Sfr fr) < fr + ACtlCutP.FRAME_BYTES)
    by (unfold ACtlCutP.FRAME_BYTES; lia).
  pose proof (ARF.shadow_of_app (fr + 8 * (x - ACtlCutP.Sfr fr)) (Happ _ Hin)) as His.
  replace (ART.shadow_addr (fr + 8 * (x - ACtlCutP.Sfr fr))) with x in His; [exact His|].
  unfold ART.shadow_addr. rewrite Hdiv. unfold ACtlCutP.Sfr, ART.shadow_addr. lia.
Qed.

(* A visible 8-aligned shadow word cover of [lo, lo + len) makes the byte-exact shadow span of any sub-range
   [a, b] a footprint range of RNG_W. *)
Lemma f16_sh_vis : forall (H : word -> bool) lo len a b,
  0 <= lo -> 0 < len -> lo <= a -> a <= b -> b < lo + len ->
  A.ProgBridge.range_visible H (RGA.sh_al8_lo lo) (RGA.sh_al8_hi lo len - RGA.sh_al8_lo lo) ->
  lib.Lib.ExecF.rng (A.ProgBridge.RNG_W H) (a / 8 + ART.ASAN_K) (b / 8 - a / 8 + 1).
Proof.
  intros H lo len a b H0 Hl Ha Hab Hb V. apply A.ProgBridge.rng_of_visible.
  pose proof (Z.div_pos lo 8 H0 ltac:(lia)) as D0.
  pose proof (Z.div_le_mono lo a 8 ltac:(lia) Ha) as D1.
  pose proof (Z.div_le_mono a b 8 ltac:(lia) Hab) as D2.
  pose proof (Z.div_le_mono b (lo + len - 1) 8 ltac:(lia) ltac:(lia)) as D3.
  unfold RGA.sh_al8_lo, RGA.sh_al8_hi, ART.shadow_addr in V.
  pose proof (Z.mul_div_le (lo / 8 + ART.ASAN_K) 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod ((lo + len - 1) / 8 + ART.ASAN_K) 8 ltac:(lia)) as D5.
  pose proof (Z.mod_pos_bound ((lo + len - 1) / 8 + ART.ASAN_K) 8 ltac:(lia)) as D6.
  eapply A.ProgBridge.range_visible_sub; [exact V | lia | lia | lia].
Qed.

(* The same for one byte. *)
Lemma f16_sh_vis1 : forall (H : word -> bool) lo len a,
  0 <= lo -> 0 < len -> lo <= a < lo + len ->
  A.ProgBridge.range_visible H (RGA.sh_al8_lo lo) (RGA.sh_al8_hi lo len - RGA.sh_al8_lo lo) ->
  lib.Lib.ExecF.rng (A.ProgBridge.RNG_W H) (Z.shiftr a 3 + ART.ASAN_K) 1.
Proof.
  intros H lo len a H0 Hl Ha V.
  pose proof (f16_sh_vis H lo len a a H0 Hl ltac:(lia) ltac:(lia) ltac:(lia) V) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (a / 8 - a / 8 + 1) with 1 in R by lia. exact R.
Qed.

(* The run's canonical start map, unfolded over the core's getr (Regs6ss.v:456-461, by delta). *)
Lemma f16_mkR_of_expand : forall regs, lib.Lib.Regs6ss.mkR_of regs =
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
    (lib.Reusable.YK11.getr regs 31).
Proof. reflexivity. Qed.

Section Loc.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* The class-6 frame lies in the fake stack, 6 MiB into it (the core's frame_facts, YG0s.v:442-447); a Theorem Labs lane's
   F13.v f13_frame_geom. *)
Lemma f16_frame_geom : forall (B : lib.Reusable.YG0f.asyms) ly S rd pos,
  lib.Reusable.YG0n.ARm B ly S rd -> In (6, pos) (lib.Reusable.YG01.frames S) ->
  6332416 <= lib.Reusable.YG0f.frame_addr ly 6 pos.
Proof.
  intros B ly S rd pos M Hin.
  destruct (lib.Reusable.YG0s.frame_facts B ly S rd 6 pos M Hin)
    as (_ & _ & Fapp & _ & _ & Foff1 & Foff2 & _).
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Foff2.
  unfold lib.Reusable.YG0f.in_app in Fapp. unfold lib.Reusable.YG0f.frame_addr.
  unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize in *. lia.
Qed.

End Loc.

(* ---------------------------------------------------------------------------------------------------------
   2. The carried facts of the two cut bodies cross a write set W that misses them (ACtlCutP's transcription of
   SlotInv's bundles; the same steps as Seg/F16.v:1373-1555, over ACtlCutP's names; F13.v's helpers adapted). *)

Lemma f16_q64_keep : forall (m m' : word -> option byte) W a v, ACtlCutP.q64 m a v -> FRM.munch W m m' ->
  (forall x, a <= x < a + 8 -> FRM.outside W x) -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' W a v H MU Ho. unfold ACtlCutP.q64 in *. eapply FPL.fl_bytes; [exact H | exact MU |].
  rewrite MEM.length_le8. exact Ho.
Qed.

Lemma f16_bytes_keep : forall (m m' : word -> option byte) W a bs, MEM.bytes_at segs m a bs -> FRM.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> FRM.outside W x) -> MEM.bytes_at segs m' a bs.
Proof. intros m m' W a bs H MU Ho. exact (FPL.fl_bytes W m m' a bs H MU Ho). Qed.

(* A spill read through s1 = A (Seg/F16.v sl_spill_at, over ACtlCut.rgv). *)
Lemma f16_spill_q64 : forall regs (m : word -> option byte) A off v,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v (A' & H9' & Hq) H9 HA0 HA1 Ho0 Ho1.
  assert (EA : A' = A).
  { pose proof Hq as Hq'. unfold ACtlCutP.q64, MEM.bytes_at in Hq'. rewrite MEM.length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _).
    apply (f16_rgv_eq regs 9 A' A H9' H9). cbn in Hb2. lia. }
  subst A'. exact Hq.
Qed.

Lemma f16_spill_keep : forall regs regs' (m m' : word -> option byte) W A off v,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> FRM.outside W x) -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU Hout.
  pose proof (f16_spill_q64 regs m A off v Hs H9 HA0 HA1 Ho0 Ho1) as Hq.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact H9|].
  exact (f16_q64_keep m m' W (A + off) v Hq MU Hout).
Qed.

(* FSj (Seg/F13.v:352-367). *)
Lemma f16_fsj_keep : forall cx fr j A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.FSj cx fr j regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' -> ARF.meta_kept m m' ->
  (forall x, A + 104 <= x < A + 120 -> FRM.outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> FRM.outside W x) -> ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j A regs regs' m m' W HFS H9 HA0 HA E9 MU MK Ho Hob. unfold ACtlCutP.FSj, ACtlCutP.FSb in *.
  destruct HFS as (S104 & S112 & Hbody & Hadd & HFI).
  split; [eapply f16_spill_keep; [exact S104 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split; [eapply f16_spill_keep; [exact S112 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split.
  { eapply f16_bytes_keep; [exact Hbody | exact MU |].
    pose proof (S13.fs_body_len (ACtlCut.c_in cx) j) as Hl. intros x Hx. apply Hob. lia. }
  split; [eapply ARF.addressable_kept; [exact Hadd | exact MK] | exact HFI].
Qed.

(* PRO (Seg/F13.v:635-667), with the input block's bytes (c_p, c_in). *)
Lemma f16_pro_keep : forall cx fr A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.PRO cx fr regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' -> ARF.meta_kept m m' ->
  (forall x, A + 32 <= x < A + 280 -> FRM.outside W x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> FRM.outside W x) ->
  ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros cx fr A regs regs' m m' W HP H9 HA0 HA E9 MU MK HoA HoIn. unfold ACtlCutP.PRO in *.
  destruct HP as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & Hour & Hin & Hg &
    S184 & S256 & S264 & S272 & S32).
  assert (K : forall off v, 32 <= off -> off + 8 <= 280 -> ACtlCutP.spill regs m off v ->
              ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply f16_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split; [apply K; [lia | lia | exact S40]|].
  split; [apply K; [lia | lia | exact S120]|].
  split; [apply K; [lia | lia | exact S136]|].
  split; [apply K; [lia | lia | exact S160]|].
  split; [apply K; [lia | lia | exact S168]|].
  split; [apply K; [lia | lia | exact S176]|].
  split; [apply K; [lia | lia | exact S208]|].
  split; [apply K; [lia | lia | exact S248]|].
  split; [eapply ARF.addressable_kept; [exact Hour | exact MK]|].
  split; [eapply f16_bytes_keep; [exact Hin | exact MU | exact HoIn]|].
  split.
  { intros Hn. eapply ARF.addressable_kept; [exact (Hg Hn) | exact MK]. }
  split; [apply K; [lia | lia | exact S184]|].
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [apply K; [lia | lia | exact S272]|].
  apply K; [lia | lia | exact S32].
Qed.

(* FLC (Seg/F13.v:690-714). *)
Lemma f16_flc_keep : forall fr A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.FLC fr regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' -> ARF.meta_kept m m' ->
  (forall x, A + 48 <= x < A + 280 -> FRM.outside W x) ->
  ACtlCutP.FLC fr regs' m'.
Proof.
  intros fr A regs regs' m m' W HF H9 HA0 HA E9 MU MK HoA. unfold ACtlCutP.FLC in *.
  destruct HF as (S256 & S184 & S192 & S80 & S88 & S96 & S272 & S264 & Hfa & Hid & S72 & S64 & S56 & S48).
  assert (K : forall off v, 48 <= off -> off + 8 <= 280 -> ACtlCutP.spill regs m off v ->
              ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply f16_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S184]|].
  split; [apply K; [lia | lia | exact S192]|].
  split; [apply K; [lia | lia | exact S80]|].
  split; [apply K; [lia | lia | exact S88]|].
  split; [apply K; [lia | lia | exact S96]|].
  split; [apply K; [lia | lia | exact S272]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [eapply ARF.addressable_kept; [exact Hfa | exact MK]|].
  split; [eapply ARF.addressable_kept; [exact Hid | exact MK]|].
  split; [apply K; [lia | lia | exact S72]|].
  split; [apply K; [lia | lia | exact S64]|].
  split; [apply K; [lia | lia | exact S56] | apply K; [lia | lia | exact S48]].
Qed.

(* FLSI (= FLSH + spills + f1_IN + FLC).  The frame's stk range crosses the write set: outside W unchanged, inside W
   readable afterwards. *)
Lemma f16_flsi_keep : forall cx j fr A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.FLSI cx j fr regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' -> ARF.meta_kept m m' ->
  FRM.wmono rsegs m m' ->
  (forall x, A + 32 <= x < A + 280 -> FRM.outside W x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> FRM.outside W x) ->
  (forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> ~ FRM.outside W x -> exists b, MEM.mrd rsegs m' (MEM.wa x) = Some b) ->
  ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr A regs regs' m m' W HF H9 HA0 HA E9 MU MK WM HoA HoIn Hrd.
  destruct HF as ((HPRO & S128 & Hstk & S144 & Ha17) & S216 & S224 & S248 & (Hin1 & Hin2) & HFLC).
  assert (K : forall off v, 32 <= off -> off + 8 <= 280 -> ACtlCutP.spill regs m off v ->
              ACtlCutP.spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply f16_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split.
  { split; [eapply f16_pro_keep; [exact HPRO | exact H9 | exact HA0 | exact HA | exact E9 | exact MU | exact MK
                                 | exact HoA | exact HoIn]|].
    split; [apply K; [lia | lia | exact S128]|].
    split; [eapply S13.stk_keep; [exact Hstk | exact MU | exact WM | exact Hrd]|].
    split; [apply K; [lia | lia | exact S144]|].
    eapply ARF.addressable_kept; [exact Ha17 | exact MK]. }
  split; [apply K; [lia | lia | exact S216]|].
  split; [apply K; [lia | lia | exact S224]|].
  split; [apply K; [lia | lia | exact S248]|].
  split; [split; [eapply ARF.addressable_kept; [exact Hin1 | exact MK] |
                  eapply f16_bytes_keep; [exact Hin2 | exact MU | exact HoIn]]|].
  eapply f16_flc_keep; [exact HFLC | exact H9 | exact HA0 | exact HA | exact E9 | exact MU | exact MK |].
  intros x Hx. apply HoA. lia.
Qed.

Lemma f16_t_phi_len : forall cx j, Z.of_nat (length (SM.t_phi (ACtlCut.c_in cx) j)) <= ACtlCutP.flen cx j.
Proof.
  intros cx j. unfold ACtlCutP.flen, SM.t_phi, SM.f_phi. rewrite length_firstn.
  pose proof (S13.flen_nonneg (ACtlCut.c_in cx) j) as H. unfold SM.t_len in *. lia.
Qed.

Lemma f16_t8819_big : forall cx j, SM.t_8819 (ACtlCut.c_in cx) j = true -> 50 <= ACtlCutP.flen cx j.
Proof.
  intros cx j H. unfold SM.t_8819 in H. rewrite !andb_true_iff in H.
  destruct H as ((Hb & _) & _). unfold SM.t_big in Hb. apply Z.leb_le in Hb. unfold ACtlCutP.flen. exact Hb.
Qed.

Lemma f16_b8_shadow_keep : forall (m m' : word -> option byte) W p v, FRM.munch W m m' -> ARF.all_app W ->
  ART.app_mem p ->
  ACtlCutP.b8 m (Z.shiftr p 3 + A.ACtlK.ASAN_K) v -> ACtlCutP.b8 m' (Z.shiftr p 3 + A.ACtlK.ASAN_K) v.
Proof.
  intros m m' W p v MU AW Hp H. unfold ACtlCutP.b8 in *. eapply f16_bytes_keep; [exact H | exact MU |].
  cbn [length]. intros x Hx. apply S13.shadow_outside; [exact AW|].
  rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
  replace x with (ART.shadow_addr p) by (unfold ART.shadow_addr, A.ACtlK.ASAN_K in *; lia).
  apply ARF.shadow_of_app. exact Hp.
Qed.

(* F17CARRY (SlotInv.v:2374; Seg/F16.v:1383-1425 and :1491-1531 cross the ingest call with it). *)
Lemma f16_f17carry_keep : forall cx j fr phi A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.F17CARRY cx j fr phi A regs m ->
  FRM.munch W m m' -> ARF.all_app W ->
  ACtlCut.rgv regs 9 A -> 0 <= fr -> fr + ACtlCutP.FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs 18 ->
  lib.Reusable.YK11.getr regs' 20 = lib.Reusable.YK11.getr regs 20 ->
  lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs 22 ->
  lib.Reusable.YK11.getr regs' 23 = lib.Reusable.YK11.getr regs 23 ->
  lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs 24 ->
  (forall x, A + 32 <= x < A + 312 -> FRM.outside W x) ->
  (50 <= ACtlCutP.flen cx j -> forall x, phi <= x < phi + ACtlCutP.flen cx j -> FRM.outside W x) ->
  (forall x, fr + 176 <= x < fr + 200 -> FRM.outside W x) ->
  ACtlCutP.F17CARRY cx j fr phi A regs' m'.
Proof.
  intros cx j fr phi A regs regs' m m' W HC MU AW H9 Hfr0 HfrA HA E9 E18 E20 E22 E23 E24 HoA Hophi Hofr.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (MK : ARF.meta_kept m m') by (apply (ARF.munch_meta W m m' MU AW)).
  unfold ACtlCutP.F17CARRY in *.
  destruct HC as (H23 & H22 & H24 & H18 & H20 & H232 & H192u & H136 & H120 & H176 & H152 & Hw & H50 & H88).
  assert (HA0 : 0 <= A) by lia.
  assert (HqA : forall off v, 32 <= off -> off + 8 <= 312 -> ACtlCutP.q64 m (A + off) v -> ACtlCutP.q64 m' (A + off) v).
  { intros off v Ho1 Ho2 Hq. eapply f16_q64_keep; [exact Hq | exact MU |]. intros x Hx. apply HoA. lia. }
  assert (Hph : 50 <= ACtlCutP.flen cx j -> forall k bs, 0 <= k -> k + Z.of_nat (length bs) <= ACtlCutP.flen cx j ->
            MEM.bytes_at segs m (phi + k) bs -> MEM.bytes_at segs m' (phi + k) bs).
  { intros Hl k bs Hk Hkl Hb. eapply f16_bytes_keep; [exact Hb | exact MU |].
    intros x Hx. apply (Hophi Hl). lia. }
  assert (Hfrb : forall k bs, 176 <= k -> k + Z.of_nat (length bs) <= 200 ->
            MEM.bytes_at segs m (fr + k) bs -> MEM.bytes_at segs m' (fr + k) bs).
  { intros k bs Hk Hkl Hb. eapply f16_bytes_keep; [exact Hb | exact MU |]. intros x Hx. apply Hofr. lia. }
  split; [unfold ACtlCut.rgv in *; rewrite E23; exact H23|].
  split; [unfold ACtlCut.rgv in *; rewrite E22; exact H22|].
  split; [unfold ACtlCut.rgv in *; rewrite E24; exact H24|].
  split; [unfold ACtlCut.rgv in *; rewrite E18; exact H18|].
  split; [unfold ACtlCut.rgv in *; rewrite E20; exact H20|].
  split; [apply HqA; [lia | lia | exact H232]|].
  split; [apply HqA; [lia | lia | exact H192u]|].
  split; [apply HqA; [lia | lia | exact H136]|].
  split; [apply HqA; [lia | lia | exact H120]|].
  split; [apply HqA; [lia | lia | exact H176]|].
  split; [eapply f16_spill_keep; [exact H152 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply HoA; lia|].
  split.
  { destruct Hw as (w240 & H240 & Hwb & Hwt & Hwf).
    exists w240. split; [apply HqA; [lia | lia | exact H240]|].
    split; [exact Hwb|]. split; [exact Hwt | exact Hwf]. }
  split.
  { intros Hl. destruct (H50 Hl) as ((rb & Hrb & Lrb) & Hgb & Hpb & HRI).
    pose proof (f16_t_phi_len cx j) as Hpl.
    split.
    { exists (firstn 38 rb). rewrite length_firstn. split; [|lia].
      rewrite <- (Z.add_0_r phi). apply (Hph Hl); [lia | rewrite length_firstn; lia |].
      rewrite Z.add_0_r. apply S13.bytes_at_firstn; [exact Hrb | lia]. }
    split.
    { rewrite <- (Z.add_0_r phi). apply (Hph Hl);
        [lia | rewrite S13.t_g_length; lia | rewrite Z.add_0_r; exact Hgb]. }
    split.
    { rewrite <- (Z.add_0_r phi). apply (Hph Hl);
        [lia | lia | rewrite Z.add_0_r; exact Hpb]. }
    unfold ACtlCutP.rec_inv0 in *.
    destruct HRI as (Hp0 & Hp50 & Hfl & Htk & Happ & H192 & Hblk & H34 & Hkp & H280).
    split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|].
    split; [exact Happ|].
    split; [apply HqA; [lia | lia | exact H192]|].
    split; [apply (Hph Hl); [lia | rewrite S13.t_blk_length; lia | exact Hblk]|].
    split; [apply (Hph Hl); [lia | rewrite S13.bsl34_length; lia | exact H34]|].
    split; [apply HqA; [lia | lia | exact Hkp] | apply HqA; [lia | lia | exact H280]]. }
  intros Ht. pose proof (f16_t8819_big cx j Ht) as Hl50.
  assert (Happ : forall a, phi <= a < phi + 50 -> ART.app_mem a)
    by (destruct (H50 Hl50) as (_ & _ & _ & (_ & _ & _ & _ & Happ & _)); exact Happ).
  destruct (H88 Ht) as (HRP & (ls & rs & H56 & Hls & Lls & Hrs & Lrs & Hmm & Ha186) &
    (ls2 & rs2 & H48 & Hls2 & Lls2 & Hrs2 & Lrs2 & Hmm2 & Ha180)).
  split.
  { unfold ACtlCutP.rec_parse in *.
    destruct HRP as (f16 & v14 & v15 & v16 & v17 & Hu16 & B14 & B15 & B16 & B17 &
      R14 & R15 & R16 & R17 & S14 & S15 & S16 & S17 & Ef16 & Eif).
    exists f16, v14, v15, v16, v17.
    split; [unfold ACtlCutP.u16 in *; replace (fr + 176 + 20) with (fr + 196) in * by lia;
            apply Hfrb; [lia | rewrite MEM.length_le2; lia | exact Hu16]|].
    unfold ACtlCutP.b8 in B14, B15, B16, B17.
    split; [unfold ACtlCutP.b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B14]|].
    split; [unfold ACtlCutP.b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B15]|].
    split; [unfold ACtlCutP.b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B16]|].
    split; [unfold ACtlCutP.b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B17]|].
    split; [exact R14|]. split; [exact R15|]. split; [exact R16|]. split; [exact R17|].
    split; [apply (f16_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S14]|].
    split; [apply (f16_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S15]|].
    split; [apply (f16_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S16]|].
    split; [apply (f16_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S17]|].
    split; [exact Ef16 | exact Eif]. }
  assert (Lf : forall bs : list byte, (6 <= length bs)%nat -> length (firstn 6 bs) = 6%nat)
    by (intros bs Hb; rewrite length_firstn; lia).
  split.
  { exists (firstn 6 ls), (firstn 6 rs).
    split; [apply HqA; [lia | lia | exact H56]|].
    split; [apply Hfrb; [lia | rewrite (Lf ls Lls); lia | apply S13.bytes_at_firstn; [exact Hls | lia]]|].
    split; [rewrite (Lf ls Lls); lia|].
    split; [rewrite <- (Z.add_0_r phi); apply (Hph Hl50);
            [lia | rewrite (Lf rs Lrs); lia | rewrite Z.add_0_r; apply S13.bytes_at_firstn; [exact Hrs | lia]]|].
    split; [rewrite (Lf rs Lrs); lia|].
    split; [rewrite S13.memcmp_firstn by lia; exact Hmm|].
    eapply ARF.addressable_kept; [exact Ha186 | exact MK]. }
  exists (firstn 6 ls2), (firstn 6 rs2).
  split; [apply HqA; [lia | lia | exact H48]|].
  split; [apply Hfrb; [lia | rewrite (Lf ls2 Lls2); lia | apply S13.bytes_at_firstn; [exact Hls2 | lia]]|].
  split; [rewrite (Lf ls2 Lls2); lia|].
  split; [apply (Hph Hl50); [lia | rewrite (Lf rs2 Lrs2); lia | apply S13.bytes_at_firstn; [exact Hrs2 | lia]]|].
  split; [rewrite (Lf rs2 Lrs2); lia|].
  split; [rewrite S13.memcmp_firstn by lia; exact Hmm2|].
  eapply ARF.addressable_kept; [exact Ha180 | exact MK].
Qed.

Lemma f16_ID1_length : forall cx j, length (ACtlCutP.ID1 cx j) = 38%nat.
Proof.
  intros cx j. change 38%nat with RIM.ID_SIZE. unfold ACtlCutP.ID1.
  apply S13.rp_id_length, S13.t_ID_length.
Qed.

(* Push 12 (Seg/F16.v t_ID_S_ingest, over an input list): on the fragment-ingest edge (t_rf j = 1) the identity of
   turn S j is the ingest of the half-way identity at the fragment's address and payload (SlotModel turn / fg_id). *)
Lemma f16_t_ID_S_ingest : forall inp j, SM.t_rf inp j = 1 ->
  SM.t_ID inp (S j) =
  snd (RIM.ING (SM.rp_id (SM.t_ID inp j) (SM.t_len inp j) (SM.t_g inp j))
         (RFR.fg_addr (SM.t_FG inp j) (SM.t_g inp j)) (SM.f_pl (SM.t_len inp j) (SM.t_FG inp j) (SM.t_g inp j))).
Proof.
  intros inp j H.
  assert (E : SM.t_ID inp (S j) =
              SM.fg_id (SM.rp_id (SM.t_ID inp j) (SM.t_len inp j) (SM.t_g inp j)) (SM.t_len inp j)
                (SM.t_FG inp j) (SM.t_g inp j)).
  { unfold SM.t_ID, SM.t_FG. rewrite SM.fst_at_S. unfold SM.turn.
    destruct (SM.f_opens (SM.t_len inp j) (SM.t_g inp j)); reflexivity. }
  rewrite E. unfold SM.fg_id. unfold SM.t_rf in H. rewrite H. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. The stage. *)

Section GlueF16.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :329-330), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A821d0_at := (ACtlCutP.C_A821d0_at B).
Local Notation C_A8229c_at := (ACtlCutP.C_A8229c_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis), ACtl.v:210's name and text. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F16 : forall POST (j : nat), CF POST (ix_cut C_A8229c_at [Z.of_nat j]) -> CF POST (ix_cut C_A821d0_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* the cut's route (C) runtime conjunct (recipe section 2(c)): asan_cells, the two shadow regions, ro_agree *)
  destruct Hrt as (Hcells & Hcut & Himgsh & Hroag).
  (* ---- G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:234-236; C_A821d0_at, ACtlCutP.v:2342-2371) ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A821d0_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLV & Hrf & R10 & R15 & R11 & R12 & R13 & R14 &
    HbRec & HaRec & HfragOK & HFSj & HU256 & (idb0 & Hidb0 & Lidb0) & HaId & A & R9 & H192 & H256 & H144 &
    HCAR & HIFS2 & R5).
  pose proof HCAR as (R23 & R22 & R24 & R18 & R20 & H232 & H200 & H136 & H120 & H176 & H152 & Hw240 & H50 & H8819).
  pose proof HFLSI as ((HPRO & S128 & Hfstk & S144 & Ha2691) & S216 & S224 & S248 & Hf1in & HFLC).
  pose proof HFLC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S56 & S48).
  pose proof HFSj as (S104 & S112 & Hbody & Hadd35 & HFI).
  pose proof HIFS2 as ((HId1 & HidOK) & HFG1 & HFS1).
  pose proof HHB as (Hphinz & Hphiad).
  (* ---- G2: the journal: AR, the layout's ly_F, the present stack window, astk_ok ---- *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hastk as (_ & _ & Hcl & Hsl & _).
  unfold A.ACfn.LLVMF_STK in Hpres, Hsl.
  pose proof HAR as (M3 & _).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[Hc1 Hc2] _].
  unfold lib.Reusable.YG0f.ASAN_CEIL in Hc1, Hc2.
  (* ---- G2: the frame fr = frame_addr ly3 6 pos, its bounds and its place in the fake stack ---- *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold lib.Reusable.YG0f.frame_addr. rewrite EF.
    reflexivity. }
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfceil & Hfapp).
  rewrite <- Efr in Hfceil, Hfapp. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  pose proof (f16_frame_geom B ly3 S3 _ (ACtlCut.c_fpos cx) M3 Hin6) as Hfr6. rewrite <- Efr in Hfr6.
  assert (Hfrapp : forall a, fr <= a < fr + 4096 -> ART.app_mem a).
  { intros a Ha. exact (f16_app_of_in_app fr 4096 a Hfapp Ha). }
  assert (Hfrapp' : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> ART.app_mem a).
  { intros a Ha. apply Hfrapp. unfold ACtlCutP.FRAME_BYTES in Ha. lia. }
  (* ---- G2: FRAC: the sp pin, the spill base A, the frame below A, the window above c_sp - 4096 ---- *)
  pose proof HFRAC as (A' & sp & F2 & Fsp16 & FspZ & F4 & F8 & F9 & F3 & F19 & F26 & Ffr32 & FA32 & FAc & FspA &
    FfrA & FA416 & Fsp4096 & FcAPP & _).
  unfold ACtlCutP.FRAME_BYTES in FfrA. unfold ART.APPMEM_END in FcAPP.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- FspZ. unfold lib.Reusable.YG0d.spZ. pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)). lia. }
  assert (HA192 : 0 <= A + 192 /\ A + 200 <= 2 ^ 64).
  { pose proof H192 as Hq'. unfold ACtlCutP.q64, MEM.bytes_at in Hq'. rewrite MEM.length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _). cbn in Hb2. lia. }
  assert (EA : A' = A) by (apply (f16_rgv_eq regs3 9 A' A F9 R9); lia).
  subst A'.
  set (csp := ACtlCut.c_sp cx) in *.
  assert (HA0 : 0 <= A) by lia.
  assert (HA416 : A + 416 <= 2 ^ 64) by lia.
  (* ---- G2: the record block phi: in the journal's live list, off the frame, below the allocator ceiling ---- *)
  assert (Hphi_in : In (phi, ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hphi_in)
    as (_ & Hphi4096 & Hphiceil & _).
  pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) 6
                (ACtlCut.c_fpos cx) HAR Hphi_in Hin6) as Hzd.
  unfold lib.Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite <- Efr in Hzd.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hzd.
  pose proof (S13.flen_nonneg (ACtlCut.c_in cx) j) as Hl0. pose proof (S13.flen_small (ACtlCut.c_in cx) j) as Hl1.
  change (SM.t_len (ACtlCut.c_in cx) j) with (ACtlCutP.flen cx j) in Hl0, Hl1.
  pose proof (lib.Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) Hl0) as [Hrq1 Hrq2].
  (* ---- G2: the input block (c_p, c_n) of the core's pre: either empty or a live block off the frame ---- *)
  assert (Hinp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                 (x < fr \/ fr + 4096 <= x) /\ x < lib.Reusable.YM05.alloc_ceiling).
  { intros x Hx. pose proof HB as ((_ & _ & _ & _ & Hpn & Hnlen & _) & _).
    destruct Hpn as [(Hn0 & _) | (_ & Hblk)]; [lia|].
    assert (Hblk3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hblk. }
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hblk3) as (_ & _ & Hpc & _).
    pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hblk3 Hin6)
      as Hz. unfold lib.Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- Efr in Hz.
    change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hz.
    pose proof (lib.Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as [_ Hq]. lia. }
  (* ---- G2: the model side: the turn closes a record (Seg/F16.v:842-853, :904-929) ---- *)
  pose proof (S16.trf1_cls (ACtlCut.c_in cx) j Hrf) as Hcls.
  destruct (S16.cls_close_inv _ _ _ Hcls) as (Hfr & Hkeep & Hclose & _).
  pose proof (S13.t_FG_length (ACtlCut.c_in cx) j) as HLst. pose proof (S13.t_g_length (ACtlCut.c_in cx) j) as HLg.
  pose proof (S16.fr_n _ _ Hfr) as Hgn. pose proof (S16.closeT64 _ _ Hkeep) as HT64.
  pose proof (S16.frT14 _ _ Hclose) as HT14.
  assert (Hlen50 : 50 <= ACtlCutP.flen cx j).
  { unfold RFR.fg_fr in Hfr. rewrite !andb_true_iff in Hfr.
    destruct Hfr as (Hf1 & _). repeat (destruct Hf1 as (Hf1 & _)). apply Z.leb_le in Hf1. unfold ACtlCutP.flen. exact Hf1. }
  destruct (S16.sum_closes (ACtlCut.c_in cx) j Hrf) as (Hsum0 & Hsumb0).
  assert (Hbat6 : RFR.bat (SM.t_FG (ACtlCut.c_in cx) j) 6 = 1).
  { pose proof (S16.keep_hf _ _ Hkeep) as Hhf. unfold RFR.fg_hf in Hhf.
    destruct HfragOK as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
  destruct (HFI Hbat6) as (Hhave1 & Hneq & Hbeq).
  assert (Ebig : SM.t_big (ACtlCut.c_in cx) j = true) by (unfold SM.t_big; apply Z.leb_le; exact Hlen50).
  rewrite Ebig in R22.
  destruct (H50 Hlen50) as ((rb & Hrb & Lrb) & Hgb & Hpb & HRI).
  pose proof HRI as (Hphi0 & Hphi50 & _ & _ & Hphiapp & _).
  set (n := SM.fs_n (SM.fst_at (ACtlCut.c_in cx) j)) in *.
  assert (Hnb : 0 <= n < 256) by (rewrite Hneq; split; [apply S16.bat_nonneg | apply S16.bat_lt]).
  assert (HnT : n <= 63) by (rewrite Hneq; unfold RFR.fg_T, RFR.fg_lf, RFR.fg_n in *; lia).
  assert (Lbody : length (SM.fs_body (SM.fst_at (ACtlCut.c_in cx) j)) = Z.to_nat n).
  { rewrite Hbeq, Hneq. rewrite length_firstn, length_skipn, HLst. rewrite <- Hneq. lia. }
  set (pll := SM.f_pll (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j)) in *.
  assert (Hpll : 1 <= pll <= 51) by (unfold pll, SM.f_pll; lia).
  set (K := Z.to_nat (pll + 5)).
  assert (HKZ : Z.of_nat K = pll + 5) by (unfold K; lia).
  assert (EK : K = Z.to_nat (RFR.fg_T (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j) - 8))
    by (unfold K; f_equal; unfold pll, SM.f_pll; lia).
  (* ---- G2: the spill loads of the tail ---- *)
  pose proof (f16_spill_q64 regs3 mem3 A 104 _ S104 R9 HA0 HA416 ltac:(lia) ltac:(lia)) as H104.
  rewrite Hhave1 in H104.
  pose proof (f16_spill_q64 regs3 mem3 A 56 _ S56 R9 HA0 HA416 ltac:(lia) ltac:(lia)) as H56.
  pose proof (f16_spill_q64 regs3 mem3 A 48 _ S48 R9 HA0 HA416 ltac:(lia) ltac:(lia)) as H48.
  (* ---- G2: the two address bytes of the inlined joined_byte (first, blk, 9 / 10) (Seg/F16.v:931-984) ---- *)
  set (X1 := if 9 <? n then fr + 2889 else phi + 18 + (18 - n)).
  set (X2 := if 10 <? n then fr + 2890 else phi + 18 + (19 - n)).
  assert (HX1b : 0 <= X1 < 2 ^ 64) by (unfold X1; destruct (Z.ltb_spec 9 n); cbv iota; lia).
  assert (HX2b : 0 <= X2 < 2 ^ 64) by (unfold X2; destruct (Z.ltb_spec 10 n); cbv iota; lia).
  assert (HAd1 : ART.addressable mem3 X1 1).
  { unfold X1. destruct (Z.ltb_spec 9 n) as [Hlt|Hge]; cbv iota.
    - replace (fr + 2889) with (fr + 2880 + 9) by lia.
      apply (ARF.addressable_sub mem3 (fr + 2880) 35 9 1 Hadd35); lia.
    - replace (phi + 18 + (18 - n)) with (phi + (36 - n)) by lia.
      apply (ARF.addressable_sub mem3 phi (A.ACtlK.a_size (ACtlCutP.flen cx j)) (36 - n) 1 Hphiad);
        unfold A.ACtlK.a_size; lia. }
  assert (HAd2 : ART.addressable mem3 X2 1).
  { unfold X2. destruct (Z.ltb_spec 10 n) as [Hlt|Hge]; cbv iota.
    - replace (fr + 2890) with (fr + 2880 + 10) by lia.
      apply (ARF.addressable_sub mem3 (fr + 2880) 35 10 1 Hadd35); lia.
    - replace (phi + 18 + (19 - n)) with (phi + (37 - n)) by lia.
      apply (ARF.addressable_sub mem3 phi (A.ACtlK.a_size (ACtlCutP.flen cx j)) (37 - n) 1 Hphiad);
        unfold A.ACtlK.a_size; lia. }
  destruct (TB5.sl_shadow1 mem3 X1 HAd1) as (b1 & RS1 & Hck1 & _).
  destruct (TB5.sl_shadow1 mem3 X2 HAd2) as (b2 & RS2 & Hck2 & _).
  assert (HR1 : exists ch, ov_read_bytes rsegs mem3 (MEM.wa X1) 1 = Some [ch] /\
                  bv_unsigned ch = SM.joined_byte (SM.fst_at (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j) 9).
  { unfold X1, SM.joined_byte. fold n. destruct (Z.ltb_spec 9 n) as [Hlt|Hge].
    - pose proof (MEM.bytes_at_read rsegs mem3 (fr + 2880) (SM.fs_body (SM.fst_at (ACtlCut.c_in cx) j)) 9 1 Hbody
                    ltac:(lia) ltac:(rewrite Lbody; lia)) as RD.
      change (Z.to_nat 9) with 9%nat in RD. rewrite (S16.firstn1_skipn 9 _ ltac:(rewrite Lbody; lia)) in RD.
      replace (fr + 2880 + 9) with (fr + 2889) in RD by lia.
      eexists; split; [exact RD | reflexivity].
    - pose proof (MEM.bytes_at_read rsegs mem3 phi (SM.t_g (ACtlCut.c_in cx) j) (36 - n) 1 Hgb ltac:(lia)
                    ltac:(rewrite HLg; lia)) as RD.
      rewrite (S16.firstn1_skipn (Z.to_nat (36 - n)) _ ltac:(rewrite HLg; lia)) in RD.
      replace (phi + (36 - n)) with (phi + 18 + (18 - n)) in RD by lia.
      eexists; split; [exact RD|]. first [reflexivity | unfold RFR.bat; f_equal; f_equal; lia]. }
  assert (HR2 : exists cl, ov_read_bytes rsegs mem3 (MEM.wa X2) 1 = Some [cl] /\
                  bv_unsigned cl = SM.joined_byte (SM.fst_at (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j) 10).
  { unfold X2, SM.joined_byte. fold n. destruct (Z.ltb_spec 10 n) as [Hlt|Hge].
    - pose proof (MEM.bytes_at_read rsegs mem3 (fr + 2880) (SM.fs_body (SM.fst_at (ACtlCut.c_in cx) j)) 10 1 Hbody
                    ltac:(lia) ltac:(rewrite Lbody; lia)) as RD.
      change (Z.to_nat 10) with 10%nat in RD. rewrite (S16.firstn1_skipn 10 _ ltac:(rewrite Lbody; lia)) in RD.
      replace (fr + 2880 + 10) with (fr + 2890) in RD by lia.
      eexists; split; [exact RD | reflexivity].
    - pose proof (MEM.bytes_at_read rsegs mem3 phi (SM.t_g (ACtlCut.c_in cx) j) (37 - n) 1 Hgb ltac:(lia)
                    ltac:(rewrite HLg; lia)) as RD.
      rewrite (S16.firstn1_skipn (Z.to_nat (37 - n)) _ ltac:(rewrite HLg; lia)) in RD.
      replace (phi + (37 - n)) with (phi + 18 + (19 - n)) in RD by lia.
      eexists; split; [exact RD|]. first [reflexivity | unfold RFR.bat; f_equal; f_equal; lia]. }
  destruct HR1 as (ch & RDh & Ech). destruct HR2 as (cl & RDl & Ecl).
  (* the fragment's address is the joined record's bytes 17 / 18, joined_byte 9 / 10 of the FIRST state *)
  assert (HFAeq : RFR.fg_addr (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j) =
                  256 * bv_unsigned ch + bv_unsigned cl).
  { rewrite Ech, Ecl. unfold RFR.fg_addr.
    rewrite <- (S16.jb_join _ _ _ 9 HLst HLg HFI Hbat6 ltac:(lia) HT64 Hgn).
    rewrite <- (S16.jb_join _ _ _ 10 HLst HLg HFI Hbat6 ltac:(lia) HT64 Hgn).
    reflexivity. }
  assert (HFAb : 0 <= RFR.fg_addr (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j) < 65536).
  { rewrite HFAeq. pose proof (S16.f16_byte_range ch). pose proof (S16.f16_byte_range cl). lia. }
  set (FA := RFR.fg_addr (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j)) in *.
  (* ---- G2: the ingest arguments (Seg/F16.v:986-999) ---- *)
  set (idb := ACtlCutP.ID1 cx j) in *.
  assert (LId : length idb = 38%nat) by exact (f16_ID1_length cx j).
  unfold ACtlCutP.IDBe in HId1.
  assert (Hidcells : STP.rw_cells rsegs mem3 (fr + 2688) [CEL.CB 38 idb]).
  { split.
    - split; [cbn; split; [exact LId | exact I]|].
      cbn [CEL.cells_bytes CEL.cbytes]. rewrite app_nil_r. exact HId1.
    - split; [lia|]. split; [cbn [CEL.cells_size CEL.csize]; lia|].
      intros i Hi. cbn [CEL.cells_size CEL.csize] in Hi.
      destruct Hfstk as (_ & _ & Hfs). exact (proj1 (Hfs (fr + 2688 + i) ltac:(unfold ACtlCutP.FRAME_BYTES; lia))). }
  assert (Lpb : length (firstn (Z.to_nat pll) (skipn 19 (SM.t_FGf (ACtlCut.c_in cx) j))) = Z.to_nat pll).
  { rewrite length_firstn, length_skipn, S16.t_FGf_length. lia. }
  assert (HbRec19 : MEM.bytes_at rsegs mem3 (ACtlCutP.fragb fr + 19)
                      (firstn (Z.to_nat pll) (skipn 19 (SM.t_FGf (ACtlCut.c_in cx) j)))).
  { pose proof HbRec as HB'. rewrite <- (firstn_skipn 19 (SM.t_FGf (ACtlCut.c_in cx) j)) in HB'.
    apply MEM.bytes_at_app in HB'. destruct HB' as (_ & HB').
    rewrite length_firstn, S16.t_FGf_length in HB'. cbn [Nat.min] in HB'.
    change (Z.of_nat 19) with 19 in HB'. apply S16.ba_firstn. exact HB'. }
  set (pb := firstn (Z.to_nat pll) (skipn 19 (SM.t_FGf (ACtlCut.c_in cx) j))) in *.
  (* ---- G2: the footprint, from the cut-time world (ProgWorldVis*.v, PROVED; statements A.ProgWorld.<x>_stmt B of
     a Theorem Labs lane's record text, whose journal is at A.ProgWorld's own instance A.AE2k.tfib_sink_head) ---- *)
  set (RNG := A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)).
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  pose proof (A.ProgWorldVisHeap.heap_vis B LAWS) as HV.
  pose proof (A.ProgWorldVisHeap.heap_sh_vis B LAWS) as HSV.
  pose proof (A.ProgWorldVisFrame.frame_vis B LAWS) as FV.
  assert (Hfv : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
                  A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len /\
                  (0 <= len -> fr <= 64 * (lo / 64) -> 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096 ->
                   len = 0 \/ A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
                                (RGA.sh_al8_lo lo) (RGA.sh_al8_hi lo len - RGA.sh_al8_lo lo))).
  { intros lo len H1 H2.
    pose proof (FV ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len HAR Hin6) as Hx.
    rewrite <- Efr in Hx. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hx. exact (Hx H1 H2). }
  assert (Hfrng : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible. exact (proj1 (Hfv lo len H1 H2)). }
  assert (Hfsh : forall lo len a b, fr + 64 <= lo -> lo + len <= fr + 4032 -> 0 < len -> lo <= a -> a <= b ->
                   b < lo + len -> lib.Lib.ExecF.rng RNG (a / 8 + ART.ASAN_K) (b / 8 - a / 8 + 1)).
  { intros lo len a b H1 H2 H3 Ha Hab Hb.
    assert (D1 : fr <= 64 * (lo / 64)) by (clear - H1; Z.div_mod_to_equations; lia).
    assert (D2 : 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096) by (clear - H2; Z.div_mod_to_equations; lia).
    destruct (proj2 (Hfv lo len ltac:(lia) ltac:(lia)) ltac:(lia) D1 D2) as [E|V]; [lia|].
    exact (f16_sh_vis _ lo len a b ltac:(lia) H3 Ha Hab Hb V). }
  assert (Hwin : forall lo len, csp - 32768 <= lo -> lo + len <= csp -> lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | exact H1 | exact H2]. }
  assert (Hhvis : forall a, phi <= a < phi + 50 -> lib.Lib.ExecF.rng RNG a 1).
  { intros a Ha. apply A.ProgBridge.rng_of_visible.
    exact (HV ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) a 1 HAR Hphi_in ltac:(lia) ltac:(lia)). }
  assert (Hhsh : forall a, phi <= a < phi + 50 -> lib.Lib.ExecF.rng RNG (Z.shiftr a 3 + ART.ASAN_K) 1).
  { intros a Ha.
    destruct (HSV ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) a 1 HAR Hphi_in ltac:(lia) ltac:(lia) ltac:(lia))
      as [E|V]; [lia|].
    exact (f16_sh_vis1 _ a 1 a ltac:(lia) ltac:(lia) ltac:(lia) V). }
  (* the stack range [c_sp - 32768, sp) the callee premises name *)
  assert (Hstk : FRM.stk rsegs mem3 (csp - 32768) (lib.Reusable.YG0d.spZ regs3)).
  { rewrite FspZ. apply (f16_stk_of_present (lib.Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. lia. }
  (* ---- G2: every premise of f16_evt_F, in its order (Seg/F16F.v:494-547) ---- *)
  assert (P02 : Z.of_nat K = pll + 5) by exact HKZ.
  assert (P03 : (1 <= K <= 57)%nat) by (unfold K; lia).
  assert (P04 : 0 <= ACtlCutP.fragb fr) by (unfold ACtlCutP.fragb; lia).
  assert (P05 : ACtlCutP.fragb fr mod 8 = 0) by (unfold ACtlCutP.fragb; clear - Ffr32; Z.div_mod_to_equations; lia).
  assert (P06 : ACtlCutP.fragb fr + 100 < 2 ^ 64) by (unfold ACtlCutP.fragb; lia).
  assert (P10 : RMO.psum (skipn 15 (SM.t_FGf (ACtlCut.c_in cx) j)) K mod 128 = 0) by (rewrite EK; exact Hsum0).
  assert (P11 : RMO.psum (skipn 15 (SM.t_FGf (ACtlCut.c_in cx) j)) K < 2 ^ 64) by (rewrite EK; lia).
  assert (P13 : 0 < 1 < 2 ^ 64) by lia.
  assert (P16 : 0 <= fr + 2889 < 2 ^ 64) by lia.
  assert (P17 : 0 <= fr + 2890 < 2 ^ 64) by lia.
  assert (P18 : 0 <= n < 2 ^ 64) by lia.
  assert (P19 : 0 <= phi + 18) by lia.
  assert (P20 : phi + 18 + 19 < 2 ^ 64) by lia.
  assert (P35 : 0 <= fr + 256 < 2 ^ 64) by lia.
  assert (P39 : 0 <= fr + 2688 < 2 ^ 64) by lia.
  assert (P40 : 0 <= pll < 2 ^ 64) by lia.
  assert (P41 : fr + 2688 <> 0) by lia.
  assert (P42 : fr + 2688 <> 0 -> (fr + 2688) mod 2 = 0 /\ STP.rw_cells rsegs mem3 (fr + 2688) [CEL.CB 38 idb]).
  { intros _. split; [clear - Ffr32; Z.div_mod_to_equations; lia | exact Hidcells]. }
  assert (P44 : 0 < pll -> ACtlCutP.fragb fr + 19 <> 0 -> MEM.bytes_at rsegs mem3 (ACtlCutP.fragb fr + 19) pb)
    by (intros _ _; exact HbRec19).
  assert (P45 : fr + 2688 <> 0 -> 0 < pll -> ACtlCutP.fragb fr + 19 <> 0 ->
                ACtlCutP.fragb fr + 19 + pll <= fr + 2688 \/ fr + 2688 + 38 <= ACtlCutP.fragb fr + 19)
    by (intros _ _ _; right; unfold ACtlCutP.fragb; lia).
  assert (P47 : csp - 32768 + IIC.REAC_IDENTITY_INGEST_FRAME <= lib.Reusable.YG0d.spZ regs3)
    by (unfold IIC.REAC_IDENTITY_INGEST_FRAME; lia).
  assert (P48 : fr + 2688 <> 0 -> fr + 2688 + 38 <= lib.Reusable.YG0d.spZ regs3 - IIC.REAC_IDENTITY_INGEST_FRAME \/
                                  lib.Reusable.YG0d.spZ regs3 <= fr + 2688)
    by (intros _; left; unfold IIC.REAC_IDENTITY_INGEST_FRAME; lia).
  assert (P49 : 0 < pll -> ACtlCutP.fragb fr + 19 <> 0 ->
                ACtlCutP.fragb fr + 19 + pll <= lib.Reusable.YG0d.spZ regs3 - IIC.REAC_IDENTITY_INGEST_FRAME \/
                lib.Reusable.YG0d.spZ regs3 <= ACtlCutP.fragb fr + 19)
    by (intros _ _; left; unfold IIC.REAC_IDENTITY_INGEST_FRAME, ACtlCutP.fragb; lia).
  assert (P53 : 0 < pll -> ACtlCutP.fragb fr + 19 <> 0 -> ART.addressable mem3 (ACtlCutP.fragb fr + 19) pll).
  { intros _ _. apply (ARF.addressable_sub mem3 (ACtlCutP.fragb fr) 72 19 pll HaRec); lia. }
  assert (P54 : forall x, ART.GOT_CELL_K <= x < ART.GOT_CELL_K + 8 \/ ART.CELL_K <= x < ART.CELL_K + 8 \/ ART.in_shadow x ->
                FRM.outside (IIC.reac_identity_ingest_W (lib.Reusable.YG0d.spZ regs3) (fr + 2688)) x).
  { intros x Hx. rewrite FspZ. apply f16_W_out.
    - destruct Hx as [Hg|[Hc|Hs]].
      + left. unfold ART.GOT_CELL_K in Hg. lia.
      + left. unfold ART.CELL_K in Hc. lia.
      + destruct (Z_lt_le_dec x (sp - 32)) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec x sp) as [Hh|Hh]; [|right; exact Hh].
        exfalso. apply (ARF.app_not_shadow x); [|exact Hs].
        unfold ART.app_mem, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia.
    - destruct Hx as [Hg|[Hc|Hs]].
      + left. unfold ART.GOT_CELL_K in Hg. lia.
      + left. unfold ART.CELL_K in Hc. lia.
      + destruct (Z_lt_le_dec x (fr + 2688)) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [Hh|Hh]; [|right; exact Hh].
        exfalso. apply (ARF.app_not_shadow x); [|exact Hs]. apply Hfrapp. lia. }
  (* the footprint ranges *)
  assert (P55 : lib.Lib.ExecF.rng RNG (ACtlCutP.fragb fr + 15) (Z.of_nat K))
    by (apply Hfrng; unfold ACtlCutP.fragb; lia).
  assert (P56 : lib.Lib.ExecF.rng RNG (Z.shiftr (ACtlCutP.fragb fr + 15) 3 + ART.ASAN_K)
                  (Z.shiftr (ACtlCutP.fragb fr + 15 + Z.of_nat K - 1) 3 - Z.shiftr (ACtlCutP.fragb fr + 15) 3 + 1)).
  { rewrite !Z.shiftr_div_pow2 by (unfold ACtlCutP.fragb; lia). change (2 ^ 3) with 8.
    apply (Hfsh (ACtlCutP.fragb fr + 15) (Z.of_nat K)); unfold ACtlCutP.fragb; lia. }
  assert (P57 : lib.Lib.ExecF.rng RNG (A + 104) 8) by (apply Hwin; lia).
  assert (P58 : lib.Lib.ExecF.rng RNG (A + 56) 8) by (apply Hwin; lia).
  assert (P59 : lib.Lib.ExecF.rng RNG (Z.shiftr X1 3 + ART.ASAN_K) 1).
  { unfold X1. destruct (Z.ltb_spec 9 n) as [Hlt|Hge]; cbv iota.
    - pose proof (Hfsh (fr + 2889) 1 (fr + 2889) (fr + 2889) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as R.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      replace ((fr + 2889) / 8 - (fr + 2889) / 8 + 1) with 1 in R by lia. exact R.
    - apply Hhsh. lia. }
  assert (P60 : lib.Lib.ExecF.rng RNG (A + 256) 8) by (apply Hwin; lia).
  assert (P61 : lib.Lib.ExecF.rng RNG (fr + 256) 2) by (apply Hfrng; lia).
  assert (P62 : lib.Lib.ExecF.rng RNG (A + 48) 8) by (apply Hwin; lia).
  assert (P63 : lib.Lib.ExecF.rng RNG (Z.shiftr X2 3 + ART.ASAN_K) 1).
  { unfold X2. destruct (Z.ltb_spec 10 n) as [Hlt|Hge]; cbv iota.
    - pose proof (Hfsh (fr + 2890) 1 (fr + 2890) (fr + 2890) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as R.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      replace ((fr + 2890) / 8 - (fr + 2890) / 8 + 1) with 1 in R by lia. exact R.
    - apply Hhsh. lia. }
  assert (P64 : lib.Lib.ExecF.rng RNG X1 1).
  { unfold X1. destruct (Z.ltb_spec 9 n); cbv iota; [apply Hfrng; lia | apply Hhvis; lia]. }
  assert (P65 : lib.Lib.ExecF.rng RNG X2 1).
  { unfold X2. destruct (Z.ltb_spec 10 n); cbv iota; [apply Hfrng; lia | apply Hhvis; lia]. }
  assert (P66 : lib.Lib.ExecF.rng RNG (A + 144) 8) by (apply Hwin; lia).
  assert (P67 : lib.Lib.ExecF.rng RNG (lib.Reusable.YG0d.spZ regs3 - IIC.REAC_IDENTITY_INGEST_FRAME)
                  IIC.REAC_IDENTITY_INGEST_FRAME)
    by (rewrite FspZ; unfold IIC.REAC_IDENTITY_INGEST_FRAME; apply Hwin; lia).
  assert (Himg : forall lo len, IMB.IMG_LO <= lo -> lo + len <= IMB.IMG_HI -> 0 <= len ->
                   lib.Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible.
    eapply A.ProgBridge.range_visible_sub; [exact (A.ProgBridge.img_vis_W W3) | exact H1 | exact H3 | lia]. }
  assert (P68 : lib.Lib.ExecF.rng RNG ART.GOT_CELL_K 8)
    by (apply Himg; unfold IMB.IMG_LO, IMB.IMG_HI, ART.GOT_CELL_K; lia).
  assert (P69 : lib.Lib.ExecF.rng RNG ART.CELL_K 8)
    by (apply Himg; unfold IMB.IMG_LO, IMB.IMG_HI, ART.CELL_K; lia).
  assert (P70 : fr + 2688 <> 0 -> lib.Lib.ExecF.rng RNG (fr + 2688) 38 /\
                lib.Lib.ExecF.rng RNG ((fr + 2688) / 8 + ART.ASAN_K) ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1)).
  { intros _. split; [apply Hfrng; lia|].
    apply (Hfsh (fr + 2688) 38); lia. }
  assert (P71 : 0 < pll -> ACtlCutP.fragb fr + 19 <> 0 ->
                lib.Lib.ExecF.rng RNG (ACtlCutP.fragb fr + 19) pll /\
                lib.Lib.ExecF.rng RNG ((ACtlCutP.fragb fr + 19) / 8 + ART.ASAN_K)
                  ((ACtlCutP.fragb fr + 19 + pll - 1) / 8 - (ACtlCutP.fragb fr + 19) / 8 + 1)).
  { intros _ _. unfold ACtlCutP.fragb. split; [apply Hfrng; lia|].
    apply (Hfsh (fr + 2768 + 19) pll); lia. }
  (* ---- G3 / G4: the run from the cut's state, the walk moved to mkR_of regs3, the lift ---- *)
  pose proof (F16F.f16_evt_F_on RNG
    (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
    (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 6) (lib.Reusable.YK11.getr regs3 7)
    (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17)
    (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
    (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
    (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 27) (lib.Reusable.YK11.getr regs3 28)
    (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
    A (ACtlCutP.fragb fr) pll FA (fr + 2688) (csp - 32768) 1 n (phi + 18) (fr + 2889) (fr + 2890) (fr + 256) X1 X2
    K (SM.t_FGf (ACtlCut.c_in cx) j) idb pb b1 b2 ch cl
    IIF.reac_identity_ingest_F_holds_on P02 P03 P04 P05 P06 HaRec HbRec (S16.t_FGf_length _ _) P10 P11
    H104 P13 H56 H48 P16 P17 P18 P19 P20 eq_refl eq_refl HX1b HX2b RS1 Hck1 RS2 Hck2 RDh RDl HFAeq HFAb
    H256 HU256 P35 H144 HA0 HA416 P39 P40 P41 P42 Lpb P44 P45 Hstk P47 P48 P49
    Hcells (fun _ => HaId) P53 P54
    P55 P56 P57 P58 P59 P60 P61 P62 P63 P64 P65 P66 P67 P68 P69 P70 P71) as HRUN0.
  lazymatch type of HRUN0 with lib.Lib.ExecF.evtF _ _ _ (lib.Lib.MState.MS ?R0 _ _ _ _ _ _) =>
    assert (EMS : R0 = lib.Lib.Regs6ss.mkR_of regs3) end.
  { rewrite f16_mkR_of_expand. unfold ACtlCut.rgv in R5, R9, R10, R15, R11, R12, R13, R14, R22, F26.
    rewrite R5, R9, R10, R15, R11, R12, R13, R14, R22, F26, <- HKZ. reflexivity. }
  rewrite EMS in HRUN0.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN0) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A821d0_at [Z.of_nat j])) with 0x821d0.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x821d0) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* ---- G5: the continuation at the run's end state ---- *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & MI & ST' & _ & HRW).
  subst ms'.
  change (bv_unsigned (lib.Reusable.YK11.getr regs3 2)) with (lib.Reusable.YG0d.spZ regs3) in MU, ST'.
  rewrite FspZ in MU, ST'.
  rewrite (lib.Lib.MState.ret_pc_even 0x8229c ltac:(lia) eq_refl).
  lazymatch goal with |- lib.Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8229c_at [Z.of_nat j])) RX m' md') (POST cx)).
  (* the exit map's registers *)
  assert (K2 : lib.Reusable.YK11.getr RX 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (K3 : lib.Reusable.YK11.getr RX 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (K4 : lib.Reusable.YK11.getr RX 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (K8 : lib.Reusable.YK11.getr RX 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (K18 : lib.Reusable.YK11.getr RX 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (K19 : lib.Reusable.YK11.getr RX 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (K20 : lib.Reusable.YK11.getr RX 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
  assert (K21 : lib.Reusable.YK11.getr RX 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (K23 : lib.Reusable.YK11.getr RX 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (K24 : lib.Reusable.YK11.getr RX 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (K9a : lib.Reusable.YK11.getr RX 9 = Z_to_bv 64 A) by reflexivity.
  assert (K9 : lib.Reusable.YK11.getr RX 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite K9a; symmetry; exact R9).
  assert (K22 : lib.Reusable.YK11.getr RX 22 = lib.Reusable.YK11.getr regs3 22)
    by (unfold ACtlCut.rgv in R22; rewrite R22; reflexivity).
  assert (K26 : lib.Reusable.YK11.getr RX 26 = lib.Reusable.YK11.getr regs3 26)
    by (unfold ACtlCut.rgv in F26; rewrite F26; reflexivity).
  assert (K10 : lib.Reusable.YK11.getr RX 10 =
                Z_to_bv 64 (IIC.ingest_ret (fr + 2688) FA (ACtlCutP.fragb fr + 19) pll idb pb)) by reflexivity.
  assert (KsP : lib.Reusable.YG0d.spZ RX = sp) by (unfold lib.Reusable.YG0d.spZ; rewrite K2; exact FspZ).
  (* the write set: app memory; what it misses *)
  set (W := IIC.reac_identity_ingest_W sp (fr + 2688)) in *.
  assert (AW : ARF.all_app W).
  { unfold W, IIC.reac_identity_ingest_W, IIC.REAC_IDENTITY_INGEST_FRAME. cbn [ARF.all_app].
    split; [|split; [|exact I]].
    - intros a Ha. unfold ART.app_mem, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia.
    - intros a Ha. apply Hfrapp. lia. }
  assert (MK : ARF.meta_kept mem3 m') by exact (ARF.munch_meta _ mem3 m' MU AW).
  assert (Hout : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2726 <= x) -> FRM.outside W x).
  { intros x H1 H2. unfold W. apply f16_W_out; lia. }
  assert (HoA : forall x, A <= x < A + 416 -> FRM.outside W x) by (intros x Hx; apply Hout; lia).
  assert (Hophi : forall x, phi <= x < phi + ACtlCutP.flen cx j -> FRM.outside W x) by (intros x Hx; apply Hout; lia).
  assert (Hnr : IIC.ingest_refused (fr + 2688) (ACtlCutP.fragb fr + 19) pll = false).
  { unfold IIC.ingest_refused. apply Bool.orb_false_iff. split.
    - apply Z.eqb_neq. lia.
    - apply Bool.andb_false_iff. right. apply Z.eqb_neq. unfold ACtlCutP.fragb. lia. }
  pose proof (HRW Hnr) as HRW'.
  assert (Hidpost : MEM.bytes_at segs m' (fr + 2688) (snd (RIM.ING idb FA pb))).
  { destruct HRW' as ((_ & Hb') & _). cbn [CEL.cells_bytes CEL.cbytes] in Hb'. rewrite app_nil_r in Hb'. exact Hb'. }
  (* every byte the call wrote is readable afterwards *)
  assert (Hrdpost : forall x, 0 <= x < 2 ^ 64 -> ~ FRM.outside W x ->
            exists b, MEM.mrd rsegs m' (MEM.wa x) = Some b).
  { intros x Hx Ho. destruct (f16_W_in sp (fr + 2688) x Ho) as [Hst|Hid].
    - destruct ST' as (_ & _ & HS). destruct (HS x ltac:(lia)) as (_ & b & Hb'). exists b. exact Hb'.
    - apply (S13.ba_rd m' (fr + 2688) (snd (RIM.ING idb FA pb)) x Hidpost).
      rewrite (RIM.ING_length idb FA pb LId). unfold RIM.ID_SIZE. lia. }
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 RX m' md' HB).
  - (* journal: ajournal_exec with the call's write set (YCbq.v:636-643) *)
    eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a : Z => ~ FRM.outside W a).
    + exact HJ.
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict.
      destruct (S13.outside_dec W (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); reflexivity | exfalso; apply Hx; exact Ho].
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict in *.
      destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (S13.outside_dec W (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
      destruct (Hrdpost (bv_unsigned x) Rx Ho) as (b & Hb').
      assert (Hge : 6283264 <= bv_unsigned x) by (destruct (f16_W_in sp (fr + 2688) _ Ho) as [H1|H1]; lia).
      pose proof (f16_mem_of_mrd m' (bv_unsigned x) b ltac:(lia) Hb') as Hm.
      unfold MEM.wa in Hm. rewrite Z_to_bv_bv_unsigned in Hm. rewrite Hm. discriminate.
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
    + intros a Ha. destruct (f16_W_in sp (fr + 2688) a Ha) as [H1|H1].
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr; cbn [fst snd].
        change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096; rewrite <- Efr; lia.
  - (* frames: own6 on both cuts *) exact HF.
  - (* the frame law: own6 on both cuts *) exact HL.
  - (* the event bound: the same kmax 14 + 2j + 1 *) exact Hk.
  - (* the exit body, C_A8229c_at (ACtlCutP.v:2376-2417), at the same index *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8229c_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    pose proof (f16_f17carry_keep cx j fr phi A regs3 RX mem3 m' W HCAR MU AW R9 ltac:(lia)
                  ltac:(unfold ACtlCutP.FRAME_BYTES; lia) HA416 K9 K18 K20 K22 K23 K24
                  ltac:(intros x Hx; apply HoA; lia) ltac:(intros _ x Hx; apply Hophi; exact Hx)
                  ltac:(intros x Hx; apply Hout; lia)) as HCAR'.
    destruct HCAR' as (R23' & R22' & R24' & R18' & R20' & H232' & H200' & H136' & H120' & H176' & H152' & Hw240' &
      H50' & H8819').
    destruct (H50' Hlen50) as ((rb' & Hrb' & Lrb') & Hgb' & Hpb' & HRI').
    assert (HB' : ACtlCutP.HB m' phi (ACtlCutP.flen cx j)).
    { split; [exact Hphinz | eapply ARF.addressable_kept; [exact Hphiad | exact MK]]. }
    exists phi.
    split; [exact HP|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 RX m'); [| exact K2 | exact K3 | exact K4 | exact K8
                                                                 | exact K9 | exact K19 | exact K26].
      (* FRAC's memory part across W, the Batch3 fake-frame trailer word q64 m' (fr + 4088) (flag_addr (c_ly cx) 6
         (c_fpos cx)) included: the base's KitMem.kitmem_frac_munch moves every q64 / bytes_at conjunct by shape.
         The trailer's 8 bytes [fr + 4088, fr + 4096) lie in the class-6 frame above the identity bytes
         [fr + 2688, fr + 2726) and below the callee window [sp - 32, sp) (fr + 4096 <= alloc_ceiling, below the
         journal's stack window), so W misses them and the entry FRAC's trailer is the exit's. *)
      apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' W HFRAC MU).
      - intros x Hx. rewrite FspZ in Hx. apply Hout; lia.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply S13.shadow_outside; [exact AW|]. exact (f16_sfr_shadow fr x Hfrapp' Hx). }
    split; [exact Hn|]. split; [exact Hj|].
    split; [exact HB'|].
    split.
    { eapply f16_flsi_keep; [exact HFLSI | exact R9 | exact HA0 | exact HA416 | exact K9 | exact MU | exact MK
                            | exact WM | | |].
      - intros x Hx. apply HoA. lia.
      - intros x Hx. destruct (Hinp x Hx) as [Hf Hc]. apply Hout; lia.
      - intros x Hx Ho. unfold ACtlCutP.FRAME_BYTES in Hx. apply Hrdpost; [lia | exact Ho]. }
    split.
    { destruct HLK as (Hj' & H21 & HOUR). split; [exact Hj'|].
      split; [unfold ACtlCut.rgv in *; rewrite K21; exact H21|].
      unfold ACtlCutP.OURb in *. eapply f16_bytes_keep; [exact HOUR | exact MU |].
      rewrite SM.OUR_length. intros x Hx. apply Hout; lia. }
    split; [exact R23'|]. split; [exact R22'|].
    split.
    { intros _. split.
      - destruct HB' as (_ & Had').
        pose proof (ARF.addressable_sub m' phi (A.ACtlK.a_size (ACtlCutP.flen cx j)) 0 50 Had' ltac:(lia) ltac:(lia)
                      ltac:(unfold A.ACtlK.a_size; lia)) as Hsub.
        rewrite Z.add_0_r in Hsub. exact Hsub.
      - exists rb'. split; [exact Hrb' | exact Lrb']. }
    split.
    { exists (IIC.ingest_ret (fr + 2688) FA (ACtlCutP.fragb fr + 19) pll idb pb).
      split; [unfold ACtlCut.rgv; exact K10|].
      unfold IIC.ingest_ret. rewrite Hnr. cbv iota.
      destruct (RIM.ING_ret idb FA pb) as [E0|E1]; rewrite ?E0, ?E1; lia. }
    split.
    { exists A.
      split; [unfold ACtlCut.rgv; exact K9a|].
      split; [exact H232'|]. split; [exact H200'|]. split; [exact H136'|]. split; [exact H120'|].
      split; [exact H176'|].
      split; [intros a Ha; unfold ART.HIGHMEM_BEG, ART.APPMEM_END; lia|].
      split; [exact Hw240'|].
      split; [exact R24'|].
      split.
      { intros _. split; [exact HRI'|].
        split; [rewrite KsP; left; unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia|].
        left; lia. }
      exact H8819'. }
    split; [exact R18'|].
    split; [intros _; split; [exact Hgb'|]; split; [exact Hpb' | exact (f16_t_phi_len cx j)]|].
    split; [exact H152'|].
    split.
    { pose proof HRI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H280').
      exists A. split; [unfold ACtlCut.rgv; exact K9a | exact H280']. }
    split; [|exact R20'].
    (* IFS3 at 0x8229c: the identity of turn S j is the ingest of ID1 cx j at the fragment's address and payload
       (f16_t_ID_S_ingest); the fragment record of turn S j and FSj are outside the call's write set *)
    unfold ACtlCutP.IFS3. split; [|split].
    + unfold ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe.
      rewrite (f16_t_ID_S_ingest (ACtlCut.c_in cx) j Hrf).
      split; [exact Hidpost | apply RIL.ING_id_ok; [exact LId | exact HidOK]].
    + unfold ACtlCutP.FGj, ACtlCutP.FGb, ACtlCutP.FGBe in HFG1 |- *. destruct HFG1 as (HG1 & HGok). split; [|exact HGok].
      eapply f16_bytes_keep; [exact HG1 | exact MU |].
      rewrite S13.t_FG_length. intros x Hx. apply Hout; lia.
    + eapply f16_fsj_keep; [exact HFS1 | exact R9 | exact HA0 | exact HA416 | exact K9 | exact MU | exact MK | |].
      * intros x Hx. apply HoA. lia.
      * intros x Hx. apply Hout; lia.
  - (* ctl_rt_C: kept across the write set, which misses the runtime cells, the shadow and the read-only image; the
       exit cut has the entry's ly3 S3, so both shadow regions are the entry's (recipe section 2(d), keep) *)
    split; [|split; [|split]].
    + apply (FPL.fl_asan_cells W mem3 m' Hcells MU).
      intros x Hx. apply Hout; unfold ART.RT_LO, ART.RT_HI in Hx; lia.
    + apply (A.ShadowRwOnK.fl_shadow_rw_on _ W mem3 m' Hcut MU WM).
      intros x Hx. exact (S13.shadow_outside W x AW Hx).
    + apply (A.ShadowRwOnK.fl_shadow_rw_on _ W mem3 m' Himgsh MU WM).
      intros x Hx. exact (S13.shadow_outside W x AW Hx).
    + apply (A.RoAdapt.ro_agree_munch W mem3 m' Hroag MU).
      intros x Hx. apply A.RoAdapt.ro_addr_false_w. destruct (f16_W_in sp (fr + 2688) _ Hx) as [H1|H1]; lia.
Qed.

End GlueF16.

