(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* lib/A/ACtlG/F13.v -- GLUE for stage seg_F13 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:782).  Written by a Theorem Labs lane (block of a Theorem Labs lane 03:48Z); single writer.
   rule 24: no function proved.  proves no function (kind: segment lemma).
   Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5, memory-writing run, callee inside).

   WHAT IT PROVES
     glue_seg_F13 : forall POST (j : nat),
       CF POST (ix_cut C_A82154_at [Z.of_nat j]) -> CF POST (ix_cut C_A82138_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F13.  Segment F13 is 0x82138 -> 0x82154: three register moves, three spill loads
   [A+256] / [A+264] / [A+272] and the call of reac_ctrl_identity_fragment at 0x82150, whose return lands at the
   exit cut 0x82154 with a0 = fg_ret of the fragment class (Seg/F13.v:755-819).

   THE RUN.  Seg/F13F.v's f13_evt_ro_F_on (a Theorem Labs lane's route (C) twin of f13_evt_ro_F, a working branch
   13c92b75539): the WHOLE segment, callee included, as one ExecF.evtF under a footprint RNG.  Its callee premise
   reac_ctrl_identity_fragment_contract_F_on is discharged by the callee's PROVED CLOSED theorem
   A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed (a Theorem Labs lane,
   a working branch 6db4ffd630a), NOT by an SRr_at.  No split: the run is lifted ONCE with
   Reusable.YA0nR.SRr_fevt_hid at RNG := ProgBridge.RNG_W (w_H W3).

   THE PROOF
   G1  the entry cut C_A82138_at at [Z.of_nat j] (ACtlCutP.v:2231-2261): phi, FRAC, HB, FLSI, LK, the spill base A,
       the cells the call reads, F16CARRY, IFS1.
   G2  premises of f13_evt_ro_F from the cut: registers s1 = A, s9 = fragb fr, s7 = phi, s2 = flen (the body's rgv
       facts and F17CARRY's); placement from VISIBLE state only: the frame from the journal (frames_bounds, the
       core's frame_facts: fr >= 6332416, the frame inside the fake stack), the record block phi from the AR block
       law (al_blocks, sep_block_frame, and the chunk placement chunk_facts: a block lies in the primary reserve or
       a secondary map, both apart from the fake stack, so phi + 50 <= fr or fr + 4096 <= phi), the spill base and
       the callee window from FRAC and the journal's astk_ok.  Each footprint (rng) premise from a range_visible
       fact (section 4 of the pattern): the spill cells [A+256, A+280) and the callee window [sp - 4656, sp) by
       ProgWorldVisWin.win_vis (the journal's stack window [c_sp - 32768, c_sp)); the window's shadow word span
       (the `sh_word_rng RNG (sp - K) K` premise of the contract text of record d393c5dde09) by
       ProgWorldVisWin.win_sh_vis; the image range by ProgBridge.img_vis_W; the GUARDED ranges kept guarded as the
       contract states them: the fragment bytes frg = phi (50) and their shadow cover under 50 <= len by
       ProgWorldVisHeap.heap_vis / heap_sh_vis, the record f = fragb fr (72), pa (2), pp (8), pn (8) and their
       shadow covers under the five pointers <> 0 by ProgWorldVisFrame.frame_vis; rng_bytes by
       ProgBridge.rng_bytes_RNG_W.  ROUTE (C), a working branch 1899bed1aee: the cut gives ctl_rt_C B ly3 S3 mem3; the run's
       asan_cells / ro_agree are its 1st / 4th parts, and its shadow premise shadow_rw_on (f13_evt_ro_shadow_R ..)
       comes from ctl_rt_C's cut_shadow by shadow_rw_on_mono and f13g_R_cover (record pieces in the owned frame's
       shadow, (F); fragment pieces in the live block phi's shadow-word cover, (L)).
   G3  the walk moved from the cut's map regs3 to the run's canonical map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, YA0nR.SRr_fevt_hid (the run writes memory).
   G5  the exit cut C_A82154_at (ACtlCutP.v:2265-2293) at the run's end map and memory m':
         journal  YCbq.ajournal_exec with Wr := the call's write set fg_fp K f pa pp pn sp c (the record and the
                  three out cells, all frame bytes of the owned class-6 frame, and the callee window, inside the
                  journal's stack window), the hidden bytes from SRr_fevt_hid, mem_grows from munch and the
                  readable post bytes;
         frames, frame law, k bound   unchanged (own6, same kmax);
         body     every carried fact crosses the write set (fl_bytes / addressable_kept / stk_keep /
                  rw_cells_transport), the record's post bytes frrec from the callee's fg_mem, IFS2 by
                  t_FG_S / frrec = t_FGf, a0 = fg_ret (frcl ..) from the run's post;
         ctl_rt_C the run's post: asan_cells, ro_agree, and both regions (cut_shadow B ly3 S3, img_shadow) by its
                  forall-P shadow conjunct (same state ly3 S3).

   SECTION HYPOTHESES (exact text below)
   - LAWS : Reusable.YG0d.AR_laws segs B -- ACtl.v:183's own hypothesis (YCbq Section a0's).
   No other: Kit's kit_wx / kit_segs_low / kit_frac_move are Required from lib/A/ACtlG/Kit.v (it builds on glue
   base 46eb24cd4b3), never copied.
   No bound is a Section hypothesis: every bound is discharged at its use site from visible state.

   CLOSURE (the glue closure rule): every Require is qualified (no Import / Export of a project module); no
   statement names a frame-route identifier; Seg/F13.v, Seg/F13F.v (frame route, Required for the run) are used
   proof-internally only, qualified.  The six twin modules YI04 YI16 YK11 YK1b YM05 YO09 are written
   lib.Reusable.<X> (the core copy), per the porter's rule of 04:24Z.  SHADOWED NAMES: getr / mkst / seg_rom /
   cfg_at are lib.Reusable.YK11 / Reusable.YG0d-qualified.

   BUILD STATE: see the commit message (TYPE-CHECK ONLY on the planning core: port_core_refused_<hex> stood in by
   their literal in the build workspace only; values do not count). *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YK04R YA0n YA0nR YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0f YG0n YG0d YG0s YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ProgBridge RoAdapt MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ProgWorldVisHeap ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan SlotModel RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F13 F13F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.Prog.reac_ctrl_identity_fragment_F_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on A.Prog.asan_memcpy_c_on A.Prog.bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss RngBytes Mem Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcFragLib RcIdentModel.
Import ListNotations.
Local Open Scope Z_scope.

Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RFL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFragLib.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module FGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.
Module S13 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F13.
Module F13F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F13F.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   1. Proof-internal helpers (Qed, over the core's world and ACtlCutP's transcribed bodies). *)

(* No image byte lives at or above 6283264 (RoAdapt.ro_rsegs_low), so a byte the reader returns there is a memory
   byte. *)
Lemma f13_mem_of_mrd : forall (m : word -> option byte) x b, 6283264 <= x < 2 ^ 64 ->
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

(* An address off the five FgClose intervals is outside the call's write set in every class (constructive;
   Seg/F13.v's fp_outside_of goes through Classical_Prop.classic). *)
Lemma f13_fp_out : forall K f pa pp pn S c x,
  ~ (f <= x < f + 72) -> ~ (pa <= x < pa + 2) -> ~ (pp <= x < pp + 8) -> ~ (pn <= x < pn + 8) -> ~ (S - K <= x < S) ->
  FRM.outside (RFR.fg_fp K f pa pp pn S c) x.
Proof. intros K f pa pp pn S c x H1 H2 H3 H4 H5. destruct c; cbn [RFR.fg_fp FRM.outside]; repeat split; assumption. Qed.

(* Its converse, by decidability of the five range tests (Seg/F13.v's fp_in closes it by tauto, classically). *)
Lemma f13_fp_in : forall K f pa pp pn S c x,
  ~ FRM.outside (RFR.fg_fp K f pa pp pn S c) x ->
  (f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S).
Proof.
  intros K f pa pp pn S c x H.
  assert (D : forall lo hi, {lo <= x < hi} + {~ (lo <= x < hi)}).
  { intros lo hi. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); [left; lia | right; lia | right; lia | right; lia]. }
  destruct (D f (f + 72)) as [d1|d1]; [left; exact d1|].
  destruct (D pa (pa + 2)) as [d2|d2]; [right; left; exact d2|].
  destruct (D pp (pp + 8)) as [d3|d3]; [right; right; left; exact d3|].
  destruct (D pn (pn + 8)) as [d4|d4]; [right; right; right; left; exact d4|].
  destruct (D (S - K) S) as [d5|d5]; [right; right; right; right; exact d5|].
  exfalso. apply H. exact (f13_fp_out K f pa pp pn S c x d1 d2 d3 d4 d5).
Qed.

(* Route (C): the callee's region at the 0x82150 call (F13F.f13_evt_ro_shadow_R = reac_ctrl_identity_fragment_shadow_R
   at f := fragb fr = fr + 2768, frg := phi, the out cells pa / pp / pn in the frame) lies in ctl_rt_C's cut_shadow:
   every record piece in the owned class-6 frame's shadow ((F) disjunct), every fragment piece in the live block phi's
   8-aligned shadow-word cover ((L) disjunct).  The bounds come from the region's own guard fg_fr (50 <= len,
   1 <= fg_n g <= 22) and, on the keep arm, fg_keep (fg_lf st + fg_n g <= 64). *)
Lemma f13g_R_cover : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) pos fr phi len st g a,
  In (6, pos) (Reusable.YG01.frames S) -> fr = Reusable.YG0f.frame_addr ly 6 pos ->
  In (phi, len) (Reusable.YG0d.ablocks B ly S) ->
  0 <= fr -> fr + 4096 <= 2 ^ 64 -> 0 <= phi -> phi + len <= 2 ^ 64 ->
  F13F.f13_evt_ro_shadow_R (fr + 2768) phi len (fr + 256) (fr + 272) (fr + 304) st g a ->
  A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S pos fr phi len st g a Hin6 Efr Hphi Hf0 Hf1 Hp0 Hp1 H.
  unfold F13F.f13_evt_ro_shadow_R, FGA.reac_ctrl_identity_fragment_shadow_R in H.
  destruct H as (_ & _ & _ & _ & _ & Hfr & Hpath).
  unfold RFR.fg_fr in Hfr. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le, !Z.eqb_eq in Hfr.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  (* a record piece: the shadow words of [q, q + k) inside [fr + 64, fr + 4032) *)
  assert (FR6 : forall q k, fr + 64 <= q -> q + k <= fr + 4032 -> A.Prog.sh_word_on.sh_word_on q k a ->
                  A.ACtlRtC.cut_shadow B ly S a).
  { intros q k Hq1 Hq2 Hs. left. exists 6, pos. split; [exact Hin6|]. rewrite <- Efr.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096.
    unfold A.Prog.sh_word_on.sh_word_on, A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Hs.
    destruct Hs as (Hk & Hs1 & Hs2).
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in *.
    clear - Hq1 Hq2 Hs1 Hs2 Hf0. Z.div_mod_to_equations. lia. }
  (* a fragment piece: the shadow words of [q, q + k) inside the live block [phi, phi + len) *)
  assert (PH : forall q k, phi <= q -> q + k <= phi + len -> A.Prog.sh_word_on.sh_word_on q k a ->
                 A.ACtlRtC.cut_shadow B ly S a).
  { intros q k Hq1 Hq2 Hs. right; left. exists phi, len. split; [exact Hphi|].
    assert (Hl0 : 0 <= len) by lia.
    pose proof (Reusable.YCbq.req_size_pos len Hl0) as [_ Hrq].
    unfold A.Prog.sh_word_on.sh_word_on, A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Hs.
    destruct Hs as (Hk & Hs1 & Hs2).
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in *.
    clear - Hq1 Hq2 Hk Hs1 Hs2 Hrq Hp0. Z.div_mod_to_equations. lia. }
  (* the memcpy region over literals *)
  assert (MC : forall d s n, 0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
                 A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a ->
                 A.Prog.sh_word_on.sh_word_on s n a \/ A.Prog.sh_word_on.sh_word_on d n a).
  { intros d s n Hd Hs Hn Hm. unfold A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Hm.
    rewrite !Z_to_bv_unsigned in Hm. unfold bv_wrap, bv_modulus in Hm. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hm.
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  assert (Hlf : 0 <= RFR.fg_lf st).
  { unfold RFR.fg_lf, RFR.bat. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as Hr. lia. }
  destruct Hpath as [(_ & [Hm | Hm]) | (_ & _ & [Hb | (Hk & Hm)])].
  - destruct (MC (fr + 2768) (phi + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) Hm) as [Hs | Hs];
      [apply (PH (phi + 6) 6) | apply (FR6 (fr + 2768) 6)]; try lia; exact Hs.
  - destruct (MC (fr + 2768 + 8) (phi + 27) (RFR.fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) Hm) as [Hs | Hs];
      [apply (PH (phi + 27) (RFR.fg_n g)) | apply (FR6 (fr + 2768 + 8) (RFR.fg_n g))]; try lia; exact Hs.
  - unfold A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R in Hb. destruct Hb as [Hs | Hs];
      [apply (FR6 (fr + 2768) 6) | apply (PH (phi + 6) 6)]; try lia; exact Hs.
  - unfold RFR.fg_keep in Hk. rewrite !Bool.andb_true_iff, Z.leb_le in Hk. destruct Hk as (_ & HT).
    unfold RFR.fg_T in HT.
    destruct (MC (fr + 2768 + 8 + RFR.fg_lf st) (phi + 27) (RFR.fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) Hm)
      as [Hs | Hs];
      [apply (PH (phi + 27) (RFR.fg_n g)) | apply (FR6 (fr + 2768 + 8 + RFR.fg_lf st) (RFR.fg_n g))];
      try lia; exact Hs.
Qed.

(* A range whose bytes the journal shows present is a stk range. *)
Lemma f13_stk_of_present : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) ->
  FRM.stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as (_ & b & Hb).
  split.
  - unfold wview, MEM.wa. rewrite Hb. discriminate.
  - exists b. unfold MEM.mrd, MEM.wa. rewrite Hb. reflexivity.
Qed.

(* A sub-range of a stk range is writable. *)
Lemma f13_wr_of_stk : forall (m : word -> option byte) lo hi a n,
  FRM.stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> MEM.wr_at segs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma f13_pw_cross : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  Reusable.YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 x y H Hx Hy; [destruct Hx|].
  cbn [app Reusable.YG0f.pairwise] in H. destruct H as [Ha Hp].
  destruct Hx as [<-|Hx].
  - rewrite Forall_forall in Ha. apply Ha. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y Hp Hx Hy).
Qed.

(* The bytes of [lo, lo + len) of an in_app range are app memory. *)
Lemma f13_app_of_in_app : forall {rc : lib.Reusable.YM05.RunCeil} lo len a,
  Reusable.YG0f.in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros rc lo len a H Ha. pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [[C1 C2] _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in H.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
Qed.

(* The frame's 392 shadow bytes are shadow addresses (Seg/F13.v:1307-1314). *)
Lemma f13_sfr_shadow : forall fr x, (forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> ART.app_mem a) ->
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

(* Two 64-bit register readings of one register name the same in-range number. *)
Lemma f13_rgv_eq : forall regs r a b, ACtlCut.rgv regs r a -> ACtlCut.rgv regs r b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb. unfold ACtlCut.rgv in *.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by (rewrite <- Ha; exact Hb).
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !lib.Lib.MState.unsigned_lit in E by lia. exact E.
Qed.

Section Loc.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* The class-6 frame lies in the fake stack, 6 MiB into it (the core's frame_facts, YG0s.v:442-447). *)
Lemma f13_frame_geom : forall (B : Reusable.YG0f.asyms) ly S rd pos,
  Reusable.YG0n.ARm B ly S rd -> In (6, pos) (Reusable.YG01.frames S) ->
  6332416 <= Reusable.YG0f.frame_addr ly 6 pos /\
  Reusable.YG0f.ly_F ly + 50 <= Reusable.YG0f.frame_addr ly 6 pos /\
  Reusable.YG0f.frame_addr ly 6 pos + 4096 <= Reusable.YG0f.ly_F ly + Reusable.YG0f.kFakeStackSize.
Proof.
  intros B ly S rd pos M Hin.
  destruct (Reusable.YG0s.frame_facts B ly S rd 6 pos M Hin)
    as (_ & _ & Fapp & _ & _ & Foff1 & Foff2 & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Foff2.
  unfold Reusable.YG0f.in_app in Fapp. unfold Reusable.YG0f.frame_addr.
  unfold Reusable.YG0f.kFakeFramesOff, Reusable.YG0f.kFakeStackSize in *. lia.
Qed.

(* A live block's first 50 bytes stay off the class-6 frame: the block lies in the primary reserve or in a
   secondary map (chunk_facts, YG0s.v:226-240), both apart from the fake stack (layout_ok lo_disj, sec_placed). *)
Lemma f13_blk_frame : forall (B : Reusable.YG0f.asyms) ly S rd p n pos,
  Reusable.YG0n.ARm B ly S rd -> In (p, n) (Reusable.YG0d.ablocks B ly S) -> In (6, pos) (Reusable.YG01.frames S) ->
  p + 50 <= Reusable.YG0f.frame_addr ly 6 pos \/ Reusable.YG0f.frame_addr ly 6 pos + 4096 <= p.
Proof.
  intros B ly S rd p n pos M Hin Hf.
  destruct (f13_frame_geom B ly S rd pos M Hf) as (G1 & G2 & G3).
  apply (Reusable.YG0s.In_ablocks B ly S p n) in Hin as (k & Hk & _ & Hu & Hn).
  pose proof (Reusable.YG0s.chunk_facts B ly S rd k M Hk) as (_ & _ & _ & C4 & C5 & _ & C7 & C8 & CG).
  pose proof (Reusable.YCbq.req_size_pos (Reusable.YG00.ck_req k) ltac:(lia)) as [Q1 _].
  pose proof (Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  assert (HE : exists lo len, lo <= p < lo + len /\
             (lo + len <= Reusable.YG0f.ly_F ly \/ Reusable.YG0f.ly_F ly + Reusable.YG0f.kFakeStackSize <= lo)).
  { destruct (Reusable.YG00.ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct CG].
    - cbv zeta in CG.
      destruct CG as (Hc & _ & _ & Hext & Hbase & Hx0 & _ & Hxs & Ha1 & Ha2).
      destruct (Reusable.YG0s.region_in_prim ly (Reusable.YG00.prim_class off) LO ltac:(lia)) as (R1 & R2 & _).
      pose proof (Reusable.YG0f.lo_disj _ LO) as D.
      unfold Reusable.YG0f.static_extents, Reusable.YG0f.owned_extents in D.
      cbn [app Reusable.YG0f.pairwise] in D. destruct D as (D1 & _).
      rewrite Forall_forall in D1.
      specialize (D1 (Reusable.YG0f.ly_F ly, Reusable.YG0f.kFakeStackSize) ltac:(cbn; right; right; left; reflexivity)).
      unfold Reusable.YG0f.zdisjoint in D1. cbn [fst snd] in D1.
      exists (Reusable.YG0f.ly_prim ly), Reusable.YG0f.kPrimResvSize. split; [|exact D1].
      rewrite <- Hu, C4. lia.
    - destruct CG as (Ho & _ & Hbase & Hext & Hsec & _).
      destruct (Reusable.YG0n.am_placed _ _ _ _ M) as [_ PD].
      assert (HinF : In (Reusable.YG0f.ly_F ly, Reusable.YG0f.kFakeStackSize) (Reusable.YG0f.static_extents ly)).
      { unfold Reusable.YG0f.static_extents, Reusable.YG0f.owned_extents. cbn. right; right; right; left.
        reflexivity. }
      pose proof (f13_pw_cross _ _ _ _ _ PD Hsec HinF) as D1.
      unfold Reusable.YG0f.zdisjoint in D1. cbn [fst snd] in D1.
      exists (Reusable.YG0f.ly_sec ly r), (Reusable.YG00.sec_map_size (Reusable.YG00.ck_req k)).
      split; [|exact D1].
      rewrite <- Hu, C4. unfold Reusable.YG00.kPage in *. lia. }
  destruct HE as (lo & len & Hp & [Hb|Ha]); [left | right]; lia.
Qed.

End Loc.

(* ---------------------------------------------------------------------------------------------------------
   2. The carried facts of the two cut bodies cross a write set W that misses them (ACtlCutP's transcription of
   SlotInv's bundles; the same steps as Seg/F13.v:267-724, over ACtlCutP's names). *)

Lemma f13_q64_keep : forall (m m' : word -> option byte) W a v, ACtlCutP.q64 m a v -> FRM.munch W m m' ->
  (forall x, a <= x < a + 8 -> FRM.outside W x) -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' W a v H MU Ho. unfold ACtlCutP.q64 in *. eapply FPL.fl_bytes; [exact H | exact MU |].
  rewrite MEM.length_le8. exact Ho.
Qed.

Lemma f13_bytes_keep : forall (m m' : word -> option byte) W a bs, MEM.bytes_at segs m a bs -> FRM.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> FRM.outside W x) -> MEM.bytes_at segs m' a bs.
Proof. intros m m' W a bs H MU Ho. exact (FPL.fl_bytes W m m' a bs H MU Ho). Qed.

Lemma f13_spill_keep : forall regs regs' (m m' : word -> option byte) W A off v,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> FRM.outside W x) -> ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v (A' & H9' & Hq) H9 HA0 HA1 Ho0 Ho1 E9 MU Hout.
  assert (EA : A' = A).
  { unfold ACtlCut.rgv in *.
    assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- H9'; exact H9).
    pose proof Hq as Hq'. unfold ACtlCutP.q64, MEM.bytes_at in Hq'. rewrite MEM.length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _).
    apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 64) with (2 ^ 64) in E.
    revert E Hb1 Hb2 HA0 HA1 Ho0 Ho1. change (2 ^ 64) with 18446744073709551616. intros.
    Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact H9|].
  exact (f13_q64_keep m m' W (A + off) v Hq MU Hout).
Qed.

Lemma f13_spill_r9 : forall regs regs' (m : word -> option byte) off v,
  ACtlCutP.spill regs m off v -> lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 ->
  ACtlCutP.spill regs' m off v.
Proof.
  intros regs regs' m off v (A & H9 & Hq) E9. exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact H9 | exact Hq].
Qed.

(* FSj (Seg/F13.v:352-367). *)
Lemma f13_fsj_keep : forall cx fr j A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.FSj cx fr j regs m ->
  ACtlCut.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs 9 -> FRM.munch W m m' -> ARF.meta_kept m m' ->
  (forall x, A + 104 <= x < A + 120 -> FRM.outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> FRM.outside W x) -> ACtlCutP.FSj cx fr j regs' m'.
Proof.
  intros cx fr j A regs regs' m m' W HFS H9 HA0 HA E9 MU MK Ho Hob. unfold ACtlCutP.FSj, ACtlCutP.FSb in *.
  destruct HFS as (S104 & S112 & Hbody & Hadd & HFI).
  split; [eapply f13_spill_keep; [exact S104 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split; [eapply f13_spill_keep; [exact S112 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split.
  { eapply f13_bytes_keep; [exact Hbody | exact MU |].
    pose proof (S13.fs_body_len (ACtlCut.c_in cx) j) as Hl. intros x Hx. apply Hob. lia. }
  split; [eapply ARF.addressable_kept; [exact Hadd | exact MK] | exact HFI].
Qed.

(* PRO (Seg/F13.v:635-667), with the input block's bytes (c_p, c_in). *)
Lemma f13_pro_keep : forall cx fr A regs regs' (m m' : word -> option byte) W,
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
    eapply f13_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
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
  split; [eapply f13_bytes_keep; [exact Hin | exact MU | exact HoIn]|].
  split.
  { intros Hn. eapply ARF.addressable_kept; [exact (Hg Hn) | exact MK]. }
  split; [apply K; [lia | lia | exact S184]|].
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [apply K; [lia | lia | exact S272]|].
  apply K; [lia | lia | exact S32].
Qed.

(* FLC (Seg/F13.v:690-714). *)
Lemma f13_flc_keep : forall fr A regs regs' (m m' : word -> option byte) W,
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
    eapply f13_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
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

(* FLSI (= FLSH + spills + f1_IN + FLC).  The frame's stk range crosses the write set: outside W unchanged,
   inside W readable afterwards (Seg/F13.v:1453-1456). *)
Lemma f13_flsi_keep : forall cx j fr A regs regs' (m m' : word -> option byte) W,
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
    eapply f13_spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split.
  { split; [eapply f13_pro_keep; [exact HPRO | exact H9 | exact HA0 | exact HA | exact E9 | exact MU | exact MK
                                 | exact HoA | exact HoIn]|].
    split; [apply K; [lia | lia | exact S128]|].
    split; [eapply S13.stk_keep; [exact Hstk | exact MU | exact WM | exact Hrd]|].
    split; [apply K; [lia | lia | exact S144]|].
    eapply ARF.addressable_kept; [exact Ha17 | exact MK]. }
  split; [apply K; [lia | lia | exact S216]|].
  split; [apply K; [lia | lia | exact S224]|].
  split; [apply K; [lia | lia | exact S248]|].
  split; [split; [eapply ARF.addressable_kept; [exact Hin1 | exact MK] |
                  eapply f13_bytes_keep; [exact Hin2 | exact MU | exact HoIn]]|].
  eapply f13_flc_keep; [exact HFLC | exact H9 | exact HA0 | exact HA | exact E9 | exact MU | exact MK |].
  intros x Hx. apply HoA. lia.
Qed.

Lemma f13_t_phi_len : forall cx j, Z.of_nat (length (SM.t_phi (ACtlCut.c_in cx) j)) <= ACtlCutP.flen cx j.
Proof.
  intros cx j. unfold ACtlCutP.flen, SM.t_phi, SM.f_phi. rewrite length_firstn.
  pose proof (S13.flen_nonneg (ACtlCut.c_in cx) j) as H. unfold SM.t_len in *. lia.
Qed.

Lemma f13_t8819_big : forall cx j, SM.t_8819 (ACtlCut.c_in cx) j = true -> 50 <= ACtlCutP.flen cx j.
Proof.
  intros cx j H. unfold SM.t_8819 in H. rewrite !andb_true_iff in H.
  destruct H as ((Hb & _) & _). unfold SM.t_big in Hb. apply Z.leb_le in Hb. unfold ACtlCutP.flen. exact Hb.
Qed.

Lemma f13_b8_shadow_keep : forall (m m' : word -> option byte) W p v, FRM.munch W m m' -> ARF.all_app W -> ART.app_mem p ->
  ACtlCutP.b8 m (Z.shiftr p 3 + A.ACtlK.ASAN_K) v -> ACtlCutP.b8 m' (Z.shiftr p 3 + A.ACtlK.ASAN_K) v.
Proof.
  intros m m' W p v MU AW Hp H. unfold ACtlCutP.b8 in *. eapply f13_bytes_keep; [exact H | exact MU |].
  cbn [length]. intros x Hx. apply S13.shadow_outside; [exact AW|].
  rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
  replace x with (ART.shadow_addr p) by (unfold ART.shadow_addr, A.ACtlK.ASAN_K in *; lia).
  apply ARF.shadow_of_app. exact Hp.
Qed.

(* F16CARRY (Seg/F13.v:373-496). *)
Lemma f13_f16carry_keep : forall cx j fr phi A regs regs' (m m' : word -> option byte) W,
  ACtlCutP.F16CARRY cx j fr phi A regs m ->
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
  (forall x, fr + 2688 <= x < fr + 2726 -> FRM.outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> FRM.outside W x) ->
  ACtlCutP.F16CARRY cx j fr phi A regs' m'.
Proof.
  intros cx j fr phi A regs regs' m m' W HC MU AW H9 Hfr0 HfrA HA E9 E18 E20 E22 E23 E24 HoA Hophi Hofr Hoid Hobody.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (MK : ARF.meta_kept m m') by (apply (ARF.munch_meta W m m' MU AW)).
  unfold ACtlCutP.F16CARRY, ACtlCutP.F17CARRY in *.
  destruct HC as (Hfok & HFS & (idb & Hidb & Lidb) & Haid & H144 &
    H23 & H22 & H24 & H18 & H20 & H232 & H192u & H136 & H120 & H176 & H152 & Hw & H50 & H88).
  assert (HA0 : 0 <= A) by lia.
  assert (HqA : forall off v, 32 <= off -> off + 8 <= 312 -> ACtlCutP.q64 m (A + off) v -> ACtlCutP.q64 m' (A + off) v).
  { intros off v Ho1 Ho2 Hq. eapply f13_q64_keep; [exact Hq | exact MU |]. intros x Hx. apply HoA. lia. }
  assert (Hph : 50 <= ACtlCutP.flen cx j -> forall k bs, 0 <= k -> k + Z.of_nat (length bs) <= ACtlCutP.flen cx j ->
            MEM.bytes_at segs m (phi + k) bs -> MEM.bytes_at segs m' (phi + k) bs).
  { intros Hl k bs Hk Hkl Hb. eapply f13_bytes_keep; [exact Hb | exact MU |].
    intros x Hx. apply (Hophi Hl). lia. }
  assert (Hfrb : forall k bs, 176 <= k -> k + Z.of_nat (length bs) <= 200 ->
            MEM.bytes_at segs m (fr + k) bs -> MEM.bytes_at segs m' (fr + k) bs).
  { intros k bs Hk Hkl Hb. eapply f13_bytes_keep; [exact Hb | exact MU |]. intros x Hx. apply Hofr. lia. }
  split; [exact Hfok|].
  split.
  { eapply f13_fsj_keep; [exact HFS | exact H9 | lia | lia | exact E9 | exact MU | exact MK | |].
    - intros x Hx. apply HoA. lia.
    - exact Hobody. }
  split.
  { exists idb. split; [|exact Lidb]. eapply f13_bytes_keep; [exact Hidb | exact MU |].
    rewrite Lidb. intros x Hx. apply Hoid. lia. }
  split; [eapply ARF.addressable_kept; [exact Haid | exact MK]|].
  split; [apply HqA; [lia | lia | exact H144]|].
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
  split; [eapply f13_spill_keep; [exact H152 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply HoA; lia|].
  split.
  { destruct Hw as (w240 & H240 & Hwb & Hwt & Hwf).
    exists w240. split; [apply HqA; [lia | lia | exact H240]|].
    split; [exact Hwb|]. split; [exact Hwt | exact Hwf]. }
  split.
  { intros Hl. destruct (H50 Hl) as ((rb & Hrb & Lrb) & Hgb & Hpb & HRI).
    pose proof (f13_t_phi_len cx j) as Hpl.
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
  intros Ht. pose proof (f13_t8819_big cx j Ht) as Hl50.
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
    split; [apply (f13_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S14]|].
    split; [apply (f13_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S15]|].
    split; [apply (f13_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S16]|].
    split; [apply (f13_b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S17]|].
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

(* FRAC's memory part (today: the spills [A+304] / [A+24] / [A+16], the frame header words, the frame's shadow
   bytes and the saved caller registers at [c_sp - 104, c_sp)) crosses a write set that misses them.  The proof
   walks FRAC's conjuncts instead of naming them, so a conjunct appended at the end (a Theorem Labs lane's announced Batch3
   trailer word `q64 m (fr + 4088) ..`, inside the frame range of the fourth premise) is kept by the same step. *)
Lemma f13_frac_mem_keep : forall B cx fr sel regs (m m' : word -> option byte) W A,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> FRM.munch W m m' ->
  (forall x, A + 16 <= x < A + 312 -> FRM.outside W x) ->
  (forall x, fr <= x < fr + 256 \/ fr + 2840 <= x < fr + 4096 -> FRM.outside W x) ->
  (forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW -> FRM.outside W x) ->
  (forall x, ACtlCut.c_sp cx - 104 <= x < ACtlCut.c_sp cx -> FRM.outside W x) ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros B cx fr sel regs m m' W A HF H9 HAb MU HoA Hofr Hosh Hosv.
  destruct HF as (A' & sp & HF).
  (* every conjunct into the context; q64 / bytes_at / exists conjuncts are not syntactic conjunctions *)
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hsp0 : 0 <= sp).
  { match goal with H : Reusable.YG0d.spZ regs = sp |- _ => rewrite <- H end.
    unfold Reusable.YG0d.spZ. pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)). lia. }
  unfold ART.APPMEM_END in *.
  assert (EA : A' = A).
  { match goal with H : ACtlCut.rgv regs 9 A' |- _ => apply (f13_rgv_eq regs 9 A' A H H9) end; lia. }
  subst A'.
  assert (Ls : length (ACtlCutP.saved_bytes cx) = 104%nat).
  { unfold ACtlCutP.saved_bytes. rewrite !length_app, !MEM.length_le8. reflexivity. }
  exists A, sp.
  repeat match goal with |- _ /\ _ => split end.
  all: first
    [ assumption
    | unfold ART.APPMEM_END; assumption
    | lazymatch goal with
      | H : ACtlCutP.q64 ?m0 ?a ?v |- ACtlCutP.q64 ?m1 ?a ?v =>
          eapply f13_q64_keep; [exact H | exact MU |]; intros x Hx;
          first [apply HoA; lia | apply Hofr; lia | apply Hosv; lia]
      | H : MEM.bytes_at _ ?m0 ?a ?bs |- MEM.bytes_at _ ?m1 ?a ?bs =>
          eapply f13_bytes_keep; [exact H | exact MU |]; rewrite ?Ls, ?MEM.length_le8; intros x Hx;
          first [apply HoA; lia | apply Hofr; lia | apply Hosv; lia]
      | H : exists _, MEM.bytes_at _ ?m0 ?a _ /\ _ |- exists _, _ =>
          let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Lsh := fresh "Lsh" in
          destruct H as (sh & Hsh & Lsh); exists sh; split; [|exact Lsh];
          eapply f13_bytes_keep; [exact Hsh | exact MU |];
          rewrite Lsh; intros x Hx; apply Hosh; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in *;
          change (Z.of_nat (Z.to_nat (3136 / 8))) with 392 in Hx; change (3136 / 8) with 392; lia
      end ].
Qed.

(* The record's post bytes (Seg/F13.v:198-213) over ACtlCutP's frcl / frrec. *)
Lemma f13_frrec_FGf : forall cx j fr phi, ACtlCutP.fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  ACtlCutP.frrec cx j fr phi = SM.t_FGf (ACtlCut.c_in cx) j.
Proof.
  intros cx j fr phi H1 H2 H3 H4 H5. unfold ACtlCutP.frrec, SM.t_FGf, SM.fg_st, ACtlCutP.frcl, SM.fcls.
  rewrite (RFL.rf_class_nn (ACtlCutP.fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite (RFL.rf_class_nn 1 1 1 1 1) by lia. unfold ACtlCutP.flen. reflexivity.
Qed.

Lemma f13_ID1_length : forall cx j, length (ACtlCutP.ID1 cx j) = 38%nat.
Proof.
  intros cx j. change 38%nat with RIM.ID_SIZE. unfold ACtlCutP.ID1.
  apply S13.rp_id_length, S13.t_ID_length.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. The stage. *)

Section GlueF13.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :281-282), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82138_at := (ACtlCutP.C_A82138_at B).
Local Notation C_A82154_at := (ACtlCutP.C_A82154_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F13 : forall POST (j : nat), CF POST (ix_cut C_A82154_at [Z.of_nat j]) -> CF POST (ix_cut C_A82138_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A82138_at, ACtlCutP.v:2231-2261). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82138_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & A & v280 & R9 & R25 & HAb & Hvb & Hvs &
    Hc256 & Hrwf & Haf & Hapa & Happ8 & Hapn & HB1 & HB2 & HB3 & HB4 & HB5 &
    H184 & H192 & H280 & HbL & HaL & H80 & H88 & H96 & H272 & H264 & HCAR & HIFS1).
  pose proof HCAR as (HfokC & HFSjC & HidbC & HaidC & H144C & H23 & H22 & H24 & H18 & H20 & H232 & H200 &
    H136 & H120 & H176 & H152 & Hw240 & H50 & H8819).
  pose proof HFLSI as ((HPRO & S128 & Hfstk & S144 & Ha2691) & S216 & S224 & S248 & Hf1in & HFLC).
  destruct HHB as (Hphinz & Hphiad).
  (* G2: the journal: AR, the layout equations, the present stack window, astk_ok. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ESL & ESH & _).
  destruct Hastk as (_ & _ & Hcl & Hsl & Hshi & _).
  unfold A.ACfn.LLVMF_STK in Hpres, Hsl.
  pose proof HAR as (M3 & _).
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold Reusable.YG0f.ASAN_CEIL in Hc1, Hc2.
  (* G2: the frame fr = frame_addr ly3 6 pos, its bounds and its place in the fake stack. *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold Reusable.YG0f.frame_addr. rewrite EF.
    reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfceil & Hfapp).
  rewrite <- Efr in Hfceil, Hfapp. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  destruct (f13_frame_geom B ly3 S3 _ (ACtlCut.c_fpos cx) M3 Hin6) as (Hfr6 & _ & _). rewrite <- Efr in Hfr6.
  assert (Hfrapp : forall a, fr <= a < fr + ACtlCutP.FRAME_BYTES -> ART.app_mem a).
  { intros a Ha. apply (f13_app_of_in_app fr 4096 a Hfapp). unfold ACtlCutP.FRAME_BYTES in Ha. lia. }
  (* G2: FRAC: the sp pin, the spill base A, the frame below A, the window above c_sp - 4096. *)
  pose proof HFRAC as (A' & sp & F2 & Fsp16 & FspZ & F4 & F8 & F9 & F3 & F19 & F26 & Ffr32 & FA32 & FAc & FspA &
    FfrA & FA416 & Fsp4096 & FcAPP & _).
  unfold ACtlCutP.FRAME_BYTES in FfrA. unfold ART.APPMEM_END in FcAPP.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- FspZ. unfold Reusable.YG0d.spZ. pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs3 2)). lia. }
  assert (EA : A' = A) by (apply (f13_rgv_eq regs3 9); [exact F9 | exact R9 | lia | exact HAb]).
  subst A'.
  set (csp := ACtlCut.c_sp cx) in *.
  (* G2: the record block phi: in the journal's live list, off the frame, below the allocator ceiling. *)
  assert (Hphi_in : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hphi_in)
    as (_ & Hphi4096 & Hphiceil & _).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) 6
                (ACtlCut.c_fpos cx) HAR Hphi_in Hin6) as Hzd.
  unfold Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite <- Efr in Hzd.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hzd.
  pose proof (f13_blk_frame B ly3 S3 _ phi (ACtlCutP.flen cx j) (ACtlCut.c_fpos cx) M3 Hphi_in Hin6) as Hpf.
  rewrite <- Efr in Hpf.
  pose proof (S13.flen_nonneg (ACtlCut.c_in cx) j) as Hl0. pose proof (S13.flen_small (ACtlCut.c_in cx) j) as Hl1.
  change (SM.t_len (ACtlCut.c_in cx) j) with (ACtlCutP.flen cx j) in Hl0, Hl1.
  pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx j) Hl0) as [Hrq1 Hrq2].
  (* G2: the input block (c_p, c_n) of the core's pre: either empty or a live block off the frame. *)
  assert (Hinp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                 (x < fr \/ fr + 4096 <= x) /\ x < lib.Reusable.YM05.alloc_ceiling).
  { intros x Hx. pose proof HB as ((_ & _ & _ & _ & Hpn & Hnlen & _) & _).
    destruct Hpn as [(Hn0 & _) | (_ & Hblk)]; [lia|].
    assert (Hblk3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hblk. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hblk3) as (_ & _ & Hpc & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hblk3 Hin6)
      as Hz. unfold Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- Efr in Hz.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hz.
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as [_ Hq]. lia. }
  (* G2: the callee contract, by its proved closed theorem (route C: a Theorem Labs lane, 6db4ffd630a). *)
  pose proof A.Prog.reac_ctrl_identity_fragment_F_on.reac_ctrl_identity_fragment_F_holds_on_closed as HFRAG.
  (* The footprint lemmas of the cut-time world (ProgWorldVis*.v, PROVED). *)
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  pose proof (A.ProgWorldVisWin.win_sh_vis B LAWS) as WSV.
  pose proof (A.ProgWorldVisHeap.heap_vis B LAWS) as HV.
  pose proof (A.ProgWorldVisHeap.heap_sh_vis B LAWS) as HSV.
  pose proof (A.ProgWorldVisFrame.frame_vis B LAWS) as FV.
  assert (Hfv : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
                  A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) lo len /\
                  (0 <= len -> fr <= 64 * (lo / 64) -> 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096 ->
                   len = 0 \/ A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                                (A.Prog.rng_asan.sh_al8_lo lo)
                                (A.Prog.rng_asan.sh_al8_hi lo len - A.Prog.rng_asan.sh_al8_lo lo))).
  { intros lo len H1 H2.
    pose proof (FV ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len HAR Hin6) as Hx.
    rewrite <- Efr in Hx. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hx. exact (Hx H1 H2). }
  assert (Hfsh : forall lo len, fr + 64 <= lo -> lo + len <= fr + 3136 -> 0 < len ->
                   lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                     (ART.shadow_addr lo / 8 * 8) (ART.shadow_addr (lo + len - 1) / 8 * 8 + 8 - ART.shadow_addr lo / 8 * 8)).
  { intros lo len H1 H2 H3.
    assert (D1 : fr <= 64 * (lo / 64)) by (Z.div_mod_to_equations; lia).
    assert (D2 : 64 * ((lo + len - 1) / 64) + 64 <= fr + 4096) by (Z.div_mod_to_equations; lia).
    destruct (proj2 (Hfv lo len ltac:(lia) ltac:(lia)) ltac:(lia) D1 D2) as [E|V]; [lia|].
    apply A.ProgBridge.rng_of_visible. exact V. }
  assert (Hwin : forall lo len, csp - 32768 <= lo -> lo + len <= csp ->
                   lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible.
    eapply WV; [exact HJ | exact H1 | exact H2]. }
  (* G3 / G4: the run, the lift. *)
  eassert (HRUN : lib.Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
    (lib.Lib.MState.MS (lib.Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82138)
       lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
  { unfold lib.Lib.Regs6ss.mkR_of.
    eapply F13F.f13_evt_ro_F_on with (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (m := mem3) (A := A)
      (f := ACtlCutP.fragb fr) (frg := phi) (len := ACtlCutP.flen cx j) (pa := fr + 256) (pp := fr + 272)
      (pn := fr + 304) (st := SM.t_FG (ACtlCut.c_in cx) j) (gfrag := SM.t_g (ACtlCut.c_in cx) j).
    all: try (match goal with |- context [bv_unsigned ?t] =>
                change (bv_unsigned t) with (Reusable.YG0d.spZ regs3) end); rewrite ?FspZ.
    all: try unfold FGA.REAC_CTRL_IDENTITY_FRAGMENT_K; try unfold ACtlCutP.fragb.
    - (* the callee contract *) exact HFRAG.
    - exact R9.
    - exact R25.
    - exact H23.
    - exact H18.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hc256.
    - exact Fsp16.
    - apply (f13_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |]. intros a Ha. apply Hpres. lia.
    - apply S13.t_g_length.
    - apply S13.t_FG_length.
    - intros _ _ _ _ _ Hl. destruct (H50 Hl) as (_ & Hgb & _). exact Hgb.
    - intros _ _ _ _ _.
      split; [exact Hrwf|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (f13_wr_of_stk mem3 fr (fr + ACtlCutP.FRAME_BYTES)); [exact Hfstk | lia | unfold ACtlCutP.FRAME_BYTES; lia | lia]|].
      split; [apply (f13_wr_of_stk mem3 fr (fr + ACtlCutP.FRAME_BYTES)); [exact Hfstk | lia | unfold ACtlCutP.FRAME_BYTES; lia | lia]|].
      split; [apply (f13_wr_of_stk mem3 fr (fr + ACtlCutP.FRAME_BYTES)); [exact Hfstk | lia | unfold ACtlCutP.FRAME_BYTES; lia | lia]|].
      cbn [RFR.all_dj RFR.dj_from]. repeat split; lia.
    - (* ro_agree: ctl_rt_C's 4th part *) exact (proj2 (proj2 (proj2 Hrt))).
    - (* asan_cells: ctl_rt_C's 1st part *) exact (proj1 Hrt).
    - (* the callee's region at the call, inside ctl_rt_C's cut_shadow (f13g_R_cover) *)
      refine (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 _ (proj1 (proj2 Hrt))). intros a Ha.
      exact (f13g_R_cover B ly3 S3 (ACtlCut.c_fpos cx) fr phi (ACtlCutP.flen cx j) _ _ a Hin6 Efr Hphi_in
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha).
    - unfold ART.HIGHMEM_BEG. lia.
    - unfold ART.APPMEM_END. lia.
    - intros _ _ _ _ _ Hl. rewrite <- (Z.add_0_r phi).
      apply (ARF.addressable_sub _ _ _ 0 50 Hphiad); unfold A.ACtlK.a_size; lia.
    - intros _ _ _ _ _.
      split; [exact Haf|]. split; [exact Hapa|]. split; [exact Happ8|]. split; [exact Hapn|].
      split; [apply Hfrapp; unfold ACtlCutP.FRAME_BYTES; lia|].
      unfold ART.RT_LO, ART.RT_HI. cbn [RFR.dj_from]. repeat split; try lia; exact I.
    - exact HB1.
    - exact HB2.
    - exact HB3.
    - exact HB4.
    - exact HB5.
    - (* the spill cells [A+256, A+280) *) apply Hwin; lia.
    - exact (A.ProgBridge.rng_bytes_RNG_W _).
    - exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
    - (* the callee window *) apply Hwin; lia.
    - (* its shadow word span *)
      destruct (WSV ly3 S3 W3 mem3 md3 (sp - 4656) 4656 HAR ltac:(rewrite ESL; lia) ltac:(rewrite ESH; lia)
                  ltac:(lia)) as [E|V]; [left; exact E | right; exact (A.ProgBridge.rng_of_visible _ _ _ V)].
    - (* the fragment bytes, under 50 <= len *)
      intros _ _ _ _ _ Hl. apply A.ProgBridge.rng_of_visible.
      exact (HV ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 50 HAR Hphi_in ltac:(lia) ltac:(lia)).
    - intros _ _ _ _ _ Hl.
      destruct (HSV ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 50 HAR Hphi_in ltac:(lia) ltac:(lia) ltac:(lia))
        as [E|V]; [lia|].
      apply A.ProgBridge.rng_of_visible.
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in V. replace (phi + 50 - 1) with (phi + 49) in V by lia.
      exact V.
    - (* the record and the three out cells, under the five pointers <> 0 *)
      intros _ _ _ _ _. apply A.ProgBridge.rng_of_visible. exact (proj1 (Hfv (fr + 2768) 72 ltac:(lia) ltac:(lia))).
    - intros _ _ _ _ _. pose proof (Hfsh (fr + 2768) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as Hs.
      replace (fr + 2768 + 72 - 1) with (fr + 2768 + 71) in Hs by lia. exact Hs.
    - intros _ _ _ _ _. apply A.ProgBridge.rng_of_visible. exact (proj1 (Hfv (fr + 256) 2 ltac:(lia) ltac:(lia))).
    - intros _ _ _ _ _. pose proof (Hfsh (fr + 256) 2 ltac:(lia) ltac:(lia) ltac:(lia)) as Hs.
      replace (fr + 256 + 2 - 1) with (fr + 256 + 1) in Hs by lia. exact Hs.
    - intros _ _ _ _ _. apply A.ProgBridge.rng_of_visible. exact (proj1 (Hfv (fr + 272) 8 ltac:(lia) ltac:(lia))).
    - intros _ _ _ _ _. pose proof (Hfsh (fr + 272) 8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hs.
      replace (fr + 272 + 8 - 1) with (fr + 272 + 7) in Hs by lia. exact Hs.
    - intros _ _ _ _ _. apply A.ProgBridge.rng_of_visible. exact (proj1 (Hfv (fr + 304) 8 ltac:(lia) ltac:(lia))).
    - intros _ _ _ _ _. pose proof (Hfsh (fr + 304) 8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hs.
      replace (fr + 304 + 8 - 1) with (fr + 304 + 7) in Hs by lia. exact Hs. }
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82138_at [Z.of_nat j])) with 0x82138.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82138) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the continuation at the run's end state. *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & RO' & ST' & FGM & AC' & SW').
  subst ms'.
  match type of ST' with context [bv_unsigned ?t] =>
    change (bv_unsigned t) with (Reusable.YG0d.spZ regs3) in MU, ST' end.
  rewrite FspZ in MU, ST'.
  fold (ACtlCutP.frcl cx j fr phi) in MU, FGM.
  unfold FGA.REAC_CTRL_IDENTITY_FRAGMENT_K in MU, ST'.
  lazymatch goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (RX := R) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82154_at [Z.of_nat j])) RX m' md') (POST cx)).
  (* the exit map's registers *)
  assert (K2 : lib.Reusable.YK11.getr RX 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (K3 : lib.Reusable.YK11.getr RX 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (K4 : lib.Reusable.YK11.getr RX 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (K8 : lib.Reusable.YK11.getr RX 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (K18 : lib.Reusable.YK11.getr RX 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (K19 : lib.Reusable.YK11.getr RX 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (K20 : lib.Reusable.YK11.getr RX 20 = lib.Reusable.YK11.getr regs3 20) by reflexivity.
  assert (K21 : lib.Reusable.YK11.getr RX 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (K22 : lib.Reusable.YK11.getr RX 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (K23 : lib.Reusable.YK11.getr RX 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (K24 : lib.Reusable.YK11.getr RX 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (K26 : lib.Reusable.YK11.getr RX 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (K9a : lib.Reusable.YK11.getr RX 9 = Z_to_bv 64 A) by reflexivity.
  assert (K9 : lib.Reusable.YK11.getr RX 9 = lib.Reusable.YK11.getr regs3 9)
    by (rewrite K9a; symmetry; exact R9).
  assert (K10 : lib.Reusable.YK11.getr RX 10 = Z_to_bv 64 (RFR.fg_ret (ACtlCutP.frcl cx j fr phi))) by reflexivity.
  assert (KsP : Reusable.YG0d.spZ RX = sp) by (unfold Reusable.YG0d.spZ; rewrite K2; exact FspZ).
  (* the write set: app memory; what it misses *)
  assert (AW : ARF.all_app (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                              (ACtlCutP.frcl cx j fr phi))).
  { apply S13.all_app_fp; intros a Ha; unfold ACtlCutP.fragb in *.
    - apply Hfrapp. unfold ACtlCutP.FRAME_BYTES. lia.
    - apply Hfrapp. unfold ACtlCutP.FRAME_BYTES. lia.
    - apply Hfrapp. unfold ACtlCutP.FRAME_BYTES. lia.
    - apply Hfrapp. unfold ACtlCutP.FRAME_BYTES. lia.
    - unfold ART.app_mem, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  assert (MK : ARF.meta_kept mem3 m') by exact (ARF.munch_meta _ mem3 m' MU AW).
  assert (Hout : forall x, (x < fr \/ fr + 2840 <= x \/ (fr + 258 <= x < fr + 272) \/ (fr + 280 <= x < fr + 304) \/
                              (fr + 312 <= x < fr + 2768) \/ x < fr + 256) ->
                 (x < sp - 4656 \/ sp <= x) ->
                 FRM.outside (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                                (ACtlCutP.frcl cx j fr phi)) x).
  { intros x H1 H2. apply f13_fp_out; unfold ACtlCutP.fragb; lia. }
  assert (HoA : forall x, A <= x < A + 416 ->
                FRM.outside (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                               (ACtlCutP.frcl cx j fr phi)) x)
    by (intros x Hx; apply Hout; lia).
  (* the record's post bytes (Seg/F13.v:1184-1200) *)
  assert (Hrec : MEM.bytes_at segs m' (ACtlCutP.fragb fr) (ACtlCutP.frrec cx j fr phi)).
  { unfold ACtlCutP.frrec, ACtlCutP.frcl in *.
    rewrite (RFL.rf_class_nn (ACtlCutP.fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (ACtlCutP.flen cx j)
               (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j)) in *
      by (unfold ACtlCutP.fragb; lia).
    destruct (RFR.fg_fr (ACtlCutP.flen cx j) (SM.t_g (ACtlCut.c_in cx) j)) eqn:FR; cbn [negb] in *.
    - destruct (RFR.bat (SM.t_g (ACtlCut.c_in cx) j) 19 =? 1); cbn [FGA.fg_mem SM.fg_next] in *; [exact FGM|].
      destruct (RFR.fg_keep (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j)); cbn [negb] in *;
        [|cbn [FGA.fg_mem SM.fg_next] in *; exact FGM].
      destruct (RFR.fg_close (SM.t_FG (ACtlCut.c_in cx) j) (SM.t_g (ACtlCut.c_in cx) j));
        cbn [negb FGA.fg_mem SM.fg_next] in *; [exact (proj1 FGM) | exact FGM].
    - cbn [FGA.fg_mem SM.fg_next] in *.
      destruct Hrwf as ((_ & Hbf) & _).
      cbn [CEL.cells_bytes CEL.cbytes] in Hbf. rewrite app_nil_r in Hbf.
      eapply f13_bytes_keep; [exact Hbf | exact MU |].
      rewrite S13.t_FG_length. intros x' Hx'. cbn [RFR.fg_fp FRM.outside].
      split; [unfold ACtlCutP.fragb in *; lia | exact I]. }
  (* every byte the call wrote is readable afterwards (Seg/F13.v:1202-1226) *)
  assert (Hrdpost : forall x, 0 <= x < 2 ^ 64 ->
            ~ FRM.outside (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                             (ACtlCutP.frcl cx j fr phi)) x ->
            exists b, MEM.mrd rsegs m' (MEM.wa x) = Some b).
  { intros x Hx Ho. destruct (f13_fp_in _ _ _ _ _ _ _ x Ho) as [Hf|[Hpa|[Hpp|[Hpn|Hstk]]]].
    - apply (S13.ba_rd m' (ACtlCutP.fragb fr) (ACtlCutP.frrec cx j fr phi) x Hrec).
      unfold ACtlCutP.frrec, ACtlCutP.frcl.
      rewrite S13.fg_next_length by (apply S13.t_FG_length || apply S13.t_g_length). lia.
    - destruct (S13.fg_case_eq_dec (ACtlCutP.frcl cx j fr phi) RFR.FgClose) as [HC|HC].
      + rewrite HC in FGM. cbn [FGA.fg_mem] in FGM. destruct FGM as (_ & Hpa2 & _ & _).
        apply (S13.ba_rd m' (fr + 256) _ x Hpa2). rewrite MEM.length_le2. lia.
      + exfalso. apply Ho. destruct (ACtlCutP.frcl cx j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
          cbn [RFR.fg_fp FRM.outside]; repeat split; unfold ACtlCutP.fragb in *; try lia; exact I.
    - destruct (S13.fg_case_eq_dec (ACtlCutP.frcl cx j fr phi) RFR.FgClose) as [HC|HC].
      + rewrite HC in FGM. cbn [FGA.fg_mem] in FGM. destruct FGM as (_ & _ & Hpp2 & _).
        apply (S13.ba_rd m' (fr + 272) _ x Hpp2). rewrite MEM.length_le8. lia.
      + exfalso. apply Ho. destruct (ACtlCutP.frcl cx j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
          cbn [RFR.fg_fp FRM.outside]; repeat split; unfold ACtlCutP.fragb in *; try lia; exact I.
    - destruct (S13.fg_case_eq_dec (ACtlCutP.frcl cx j fr phi) RFR.FgClose) as [HC|HC].
      + rewrite HC in FGM. cbn [FGA.fg_mem] in FGM. destruct FGM as (_ & _ & _ & Hpn2).
        apply (S13.ba_rd m' (fr + 304) _ x Hpn2). rewrite MEM.length_le8. lia.
      + exfalso. apply Ho. destruct (ACtlCutP.frcl cx j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
          cbn [RFR.fg_fp FRM.outside]; repeat split; unfold ACtlCutP.fragb in *; try lia; exact I.
    - destruct ST' as (_ & _ & HS). destruct (HS x ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 RX m' md' HB).
  - (* journal: ajournal_exec with the call's write set (YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a : Z => ~ FRM.outside (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                                               (ACtlCutP.frcl cx j fr phi)) a).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (S13.outside_dec (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                                   (ACtlCutP.frcl cx j fr phi)) (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); reflexivity | exfalso; apply Hx; exact Ho].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (S13.outside_dec (RFR.fg_fp 4656 (ACtlCutP.fragb fr) (fr + 256) (fr + 272) (fr + 304) sp
                                   (ACtlCutP.frcl cx j fr phi)) (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
      destruct (Hrdpost (bv_unsigned x) Rx Ho) as (b & Hb).
      assert (Hge : 6283264 <= bv_unsigned x).
      { destruct (f13_fp_in _ _ _ _ _ _ _ _ Ho) as [H1|[H1|[H1|[H1|H1]]]]; unfold ACtlCutP.fragb in *; lia. }
      pose proof (f13_mem_of_mrd m' (bv_unsigned x) b ltac:(lia) Hb) as Hm.
      unfold MEM.wa in Hm. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm. rewrite Hm. discriminate.
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
    + intros a Ha. destruct (f13_fp_in _ _ _ _ _ _ _ a Ha) as [H1|[H1|[H1|[H1|H1]]]].
      5: { left. unfold A.ACfn.LLVMF_STK. lia. }
      all: right; right; right; exists 6, (ACtlCut.c_fpos cx); split; [left; reflexivity|]; left;
        unfold Reusable.YG0n.in_zr; cbn [fst snd];
        change (Reusable.YG00.fs_frame_bytes 6) with 4096; rewrite <- Efr; unfold ACtlCutP.fragb in *; lia.
  - (* frames: own6 on both cuts *) exact HF.
  - (* the frame law: own6 on both cuts *) exact HL.
  - (* the event bound: the same kmax *) exact Hk.
  - (* the exit body, C_A82154_at (ACtlCutP.v:2265-2293), at the same index *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82154_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 RX m'); [| exact K2 | exact K3 | exact K4 | exact K8
                                                                 | exact K9 | exact K19 | exact K26].
      apply (f13_frac_mem_keep B cx fr fr regs3 mem3 m' _ A HFRAC R9 HAb MU).
      - intros x Hx. apply HoA. lia.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply S13.shadow_outside; [exact AW|]. exact (f13_sfr_shadow fr x Hfrapp Hx).
      - intros x Hx. apply Hout; lia. }
    split; [exact Hn|]. split; [exact Hj|].
    split; [split; [exact Hphinz | eapply ARF.addressable_kept; [exact Hphiad | exact MK]]|].
    split.
    { eapply f13_flsi_keep; [exact HFLSI | exact R9 | lia | lia | exact K9 | exact MU | exact MK | exact WM | | |].
      - intros x Hx. apply HoA. lia.
      - intros x Hx. destruct (Hinp x Hx) as [Hf Hc]. apply Hout; lia.
      - intros x Hx Ho. unfold ACtlCutP.FRAME_BYTES in Hx. apply Hrdpost; [lia | exact Ho]. }
    split.
    { destruct HLK as (Hj' & H21 & HOUR). split; [exact Hj'|].
      split; [unfold ACtlCut.rgv in *; rewrite K21; exact H21|].
      unfold ACtlCutP.OURb in *. eapply f13_bytes_keep; [exact HOUR | exact MU |].
      rewrite SM.OUR_length. intros x Hx. apply Hout; lia. }
    exists A, v280.
    split; [exact K9a|].
    split; [unfold ACtlCut.rgv; exact K10|].
    split; [exact HAb|]. split; [exact Hvb|]. split; [exact Hvs|].
    split; [unfold ACtlCutP.FRAME_BYTES; lia|].
    split; [rewrite KsP; left; unfold FGA.REAC_CTRL_IDENTITY_FRAGMENT_K; lia|].
    split; [eapply f13_q64_keep; [exact H184 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H192 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H280 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_bytes_keep; [exact HbL | exact MU |]; rewrite S13.t_FG_length; intros x Hx; apply Hout; lia|].
    split; [eapply ARF.addressable_kept; [exact HaL | exact MK]|].
    split; [exact Hrec|].
    split; [eapply ARF.addressable_kept; [exact Haf | exact MK]|].
    split; [eapply f13_bytes_keep; [exact HB1 | exact MU |]; rewrite MEM.length_le8; intros x Hx; apply Hout;
            unfold A.Prog.bcmp_wrap_c.REAL_BCMP in *; lia|].
    split; [eapply f13_bytes_keep; [exact HB2 | exact MU |]; rewrite MEM.length_le8; intros x Hx; apply Hout;
            unfold A.Prog.bcmp_wrap_c.REAL_MEMCMP in *; lia|].
    split; [eapply f13_bytes_keep; [exact HB3 | exact MU |]; rewrite MEM.length_le8; intros x Hx; apply Hout;
            unfold A.Prog.bcmp_wrap_c.GOT_CF in *; lia|].
    split; [eapply f13_bytes_keep; [exact HB4 | exact MU |]; cbn [length]; intros x Hx; apply Hout;
            unfold A.Prog.bcmp_wrap_c.CF in *; lia|].
    split; [eapply f13_bytes_keep; [exact HB5 | exact MU |]; cbn [length]; intros x Hx; apply Hout;
            unfold A.Prog.bcmp_wrap_c.CF in *; lia|].
    split.
    { eapply FRM.rw_cells_transport; [exact Hc256 | exact MU | exact WM |].
      change (Z.of_nat (CEL.cells_size [CEL.C8 (Z_to_bv 64 (fr + 256)); CEL.C8 (Z_to_bv 64 (fr + 304));
                                         CEL.C8 (Z_to_bv 64 (fr + 272))])) with 24.
      unfold ACtlCutP.fragb in *.
      destruct (ACtlCutP.frcl cx j fr phi); cbn [RFR.fg_fp FRM.disjoint_from]; repeat split; first [right; lia | exact I]. }
    split; [eapply f13_q64_keep; [exact H80 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H88 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H96 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H272 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [eapply f13_q64_keep; [exact H264 | exact MU |]; intros x Hx; apply HoA; lia|].
    split; [exact FGM|].
    split.
    { eapply f13_f16carry_keep; [exact HCAR | exact MU | exact AW | exact R9 | lia | unfold ACtlCutP.FRAME_BYTES; lia
                                | lia | exact K9 | exact K18 | exact K20 | exact K22 | exact K23 | exact K24 | | | | |].
      - intros x Hx. apply HoA. lia.
      - intros Hl x Hx. apply Hout; lia.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply Hout; lia. }
    (* IFS2 at 0x82154: the identity record kept, the fragment record of turn S j = the call's post bytes *)
    unfold ACtlCutP.IFS1, ACtlCutP.IDb1, ACtlCutP.FGj, ACtlCutP.FGb in HIFS1.
    destruct HIFS1 as ((HId1 & HidOK) & (_ & HfOK) & HFSj).
    unfold ACtlCutP.IFS2, ACtlCutP.IDb1, ACtlCutP.FGj, ACtlCutP.FGb.
    split; [split; [|exact HidOK]|].
    { unfold ACtlCutP.IDBe in *. eapply f13_bytes_keep; [exact HId1 | exact MU |].
      rewrite f13_ID1_length. intros x Hx. apply Hout; lia. }
    rewrite S13.t_FG_S.
    split; [split|].
    { unfold ACtlCutP.FGBe. rewrite <- (f13_frrec_FGf cx j fr phi) by (unfold ACtlCutP.fragb; lia).
      exact Hrec. }
    { unfold SM.t_FGf. apply S13.frag_ok_fg_st; [exact HfOK | apply S13.t_FG_length | apply S13.t_g_length]. }
    eapply f13_fsj_keep; [exact HFSj | exact R9 | lia | lia | exact K9 | exact MU | exact MK | |].
    + intros x Hx. apply HoA. lia.
    + intros x Hx. apply Hout; lia.
  - (* ctl_rt_C B ly3 S3 m': the run's post (same state): asan_cells, both regions by its forall-P conjunct,
       ro_agree *)
    split; [exact AC'|]. split; [exact (SW' _ (proj1 (proj2 Hrt)))|].
    split; [exact (SW' _ (proj1 (proj2 (proj2 Hrt)))) | exact RO'].
Qed.

End GlueF13.

Print Assumptions glue_seg_F13.
