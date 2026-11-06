(* lib/A/ACtlG/F29.v -- GLUE for stage seg_F29 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   `Hypothesis seg_F29`, :643 at a working branch 5f2b9fab28a).  Written by a Theorem Labs lane, one
   writer.  Pattern: glue-pattern.md steps G1-G5 (a working note, not in this delivery) (its section 4 form for a run
   that writes memory), worked example lib/A/ACtlG/A5.v.  rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F29 : forall POST (j : nat),
       CF POST (ix_cut C_A8275c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F29.  ENTRY cut C_A82750_at (pc 0x82750, ACtlCutP.v:2693-2703), EXIT cut C_A8275c_at (pc 0x8275c,
   ACtlCutP.v:2708-2718); the two bodies have the same text.  Segment F29 (Seg/F29.v:1-25) is three one-byte stores
   of s11's low byte to the frame's shadow bytes S(fr)+16, S(fr)+17, S(fr)+20 (s3 = S(fr)); no register changes.

   THE RUN: A.Prog.Seg.F29F.f29_evt_F (Seg/F29F.v:47-77), the footprint re-run of Seg/F29.v's f29_evt (:527), lifted
   at RNG := ProgBridge.RNG_W (w_H W3).  F29.sl_run_lib (:566) concludes SR, not evt: it is the slot engine's
   evt -> SR bridge and has no _F; the cgif walk replaces it by a Theorem Labs lane's lift (SRr_fevt_hid), as the pattern says.

   THE PROOF (glue-pattern.md G1-G5)
   G1  the entry cut at index [Z.of_nat j]: ix_cut's index equation, then C_A82750_at's body (Permutation of the live
       list, FRAC, c_n < 2^26, j <= 255, HB, FLSI, LK, FLS, LT).
   G2  the run's premises: s3 = S(fr) (FRAC's rgv regs 19), the 5 shadow bytes present (FRAC's 392 frame-shadow
       bytes) and writable (ctl_rt_C's shadow_rw_on cut_shadow: the (F) disjunct, the owned class-6 frame's shadow
       [S(fr), S(fr) + 512)), the rng premise from the frame-shadow visibility of the core's
       AR_frames_law (al_frames, YG0d.v:447-455) at the journal's AR; the frame base fr = frame_addr ly3 6 pos by the
       shell's frame law and layout_le's ly_F.
   G3  ProgBridge.cfg_at_MS, then the walk moved to the run's canonical map Regs6ss.mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, the lift YA0nR.SRr_fevt_hid (the run writes memory).
   G5  the walk moved back to regs3 (no register changes), then the exit cut at the same cx fr k ly3 S3 W3 regs3,
       the run's memory m' and the materialized model md':
         journal  YCbq.ajournal_exec with Wr = [S(fr)+16, S(fr)+21): every written byte is the owned class-6 frame's
                  shadow (awr_byte's in_frames case, YCbq.v:346-349, :460-464); memory equal outside Wr (munch); the
                  restricted memory grows (the written bytes are present, and no shadow byte is an image byte:
                  ProgBridge.rsegs_spans); the hidden bytes from SRr_fevt_hid; same_but_materialized from the lift;
         frames, frame law, k bound  unchanged (exact: own6 and the same kmax on both cuts);
         body     the live list unchanged; every other conjunct reads application bytes (the spill block above sp,
                  the frame outside [fr+448, fr+536), the machine stack, the input block, the turn's block) or the
                  shadow of bytes outside [fr+128, fr+536) - none is written (the keep lemmas below, f_safe);
                  FRAC's 392 frame-shadow bytes are re-read at m' (present outside the window, written inside);
         ctl_rt_C asan_cells kept (AsanRTFacts.asan_cells_kept: the window is far above RT_HI), the two shadow_rw_on
                  regions (cut_shadow B ly3 S3 and img_shadow, the same state ly3 S3: writable by wmono, present by
                  munch / the written cells), ro_agree (every read-only byte is below 0x5fe000).

   SECTION HYPOTHESES: only LAWS, the core's AR law record (YCbq Section a0's hypothesis, YCbq.v:207), as ACtl.v's
   Section Ctl carries it (ACtl.v:183).  No run hypothesis: the run is Required from Seg/F29F.v.

   CITED BY NAME (all proved): A.Prog.Seg.F29F.f29_evt_F; Reusable.YA0nR.SRr_fevt_hid / SRr_xregs_eqv (a Theorem Labs lane);
   A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / RNG_W / rng_of_visible / fp_avoids_RNG_W / rsegs_spans
   (a Theorem Labs lane); Reusable.YCbq.ajournal_exec / sep_block_frame / asan_consts, Reusable.YG0d.al_frames / al_blocks,
   Reusable.YK04.find_segment_some_spec (the core); A.Prog.Seg.F29's addr_keep / stk_tr / spill_keep / ba_sub /
   ba_some / ba_present / sh_frame / sh_frame_of / ro_lo / t_g_length / tID_len / tFG_len / fs_body_len (Seg/F29.v,
   already in Seg/F29F.v's closure); A.Prog.RcAsanFPLib.fl_bytes; A.AsanRTFacts' app_not_shadow / shadow_of_app /
   addressable_app / asan_cells_kept / in_shadow_range; A.Prog.SlotModel.OUR_length.  From the shared kit
   lib/A/ACtlG/Kit.v (Required qualified, never copied): kit_wx and kit_segs_low.

   KEEP LAYER (sections 2-3 below): the write-set keep lemmas k_* (any write set W with `f_safe fr W`: W misses every
   application byte outside [fr+448, fr+536) and the shadow of every byte outside [fr+128, fr+536)) and the ONE
   transfer relation ktr with its bundle lemmas kt_*, which lib/A/ACtlG/F30.v reuses across F30's stores and callee.

   CLOSURE (glue closure rule, glue-pattern.md section 1): every project Require below is qualified; the closure is
   Seg/F29F.v's (Seg/F29.v, Tac_slot, Tac_fs, SlotInv, AsanRTInv, Contract, FrameAPI, MemNorm, ...) plus the walk's
   files; no lib/AZ/AsanW, no W6, no cut-free file is Required here.  EVERY Require names the FULL directory in its
   From clause, and every lib/Reusable, lib/Lib and lib/Prog module this file names is bound by full path in the
   alias modules Reusable / Lib / Prog below (a Theorem Labs lane 05:28Z: 160 of lib/Reusable's modules and 15 of lib/Lib's
   exist a second time under lib/A, lib/B, lib/U, lib/AZ, so a partial `Reusable.X` / `Lib.X` can bind the wrong copy).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only full-path YK11 / Reusable.YG0d (the local notations getrC /
   fpR / fpC / romC / romA below are bound to full paths).

   BUILD STATE: route (C) L3 switch (a Theorem Labs lane, recipe L3-recipe.md section 2 (a working note, not in this delivery)): the
   entry cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ctl_from on a working branch); the three stores' write permission is read
   from its cut_shadow region and the exit re-supplies both regions at the same state.  Built on
   a working branch by cbrec v7 (build of record, .prov under (internal path)).  Batch3's
   FRAC trailer word is produced by kt_frac below.  Print Assumptions glue_seg_F29 = the Rocq primitives and
   functional_extensionality_dep. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YA0nR YG0f YG00 YG01 YG0d YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F29 F29F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The lib/Reusable, lib/Lib and lib/Prog modules this file names, bound by full path: every `Reusable.X.n`,
   `Lib.X.n` and `Prog.X.n` below resolves to these aliases, never to a same-named copy elsewhere. *)
Module Reusable.
  Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
  Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
  Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
  Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
  Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
  Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
  Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
  Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
  Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
  Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
  Module YI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
End Reusable.
Module Lib.
  Module ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
  Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
  Module Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
  Module Mem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
  Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
  Module Cells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
  Module Step := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
  Module PropExec := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
End Lib.
Module Prog.
  Module RcIdentModel := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
End Prog.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
(* Full-path names of the core's YK11 (one of the six doubled modules) and ctrl's lib/A/Reusable YK11 copy. *)
Local Notation getrC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation fpR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs.
Local Notation fpC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr.
Local Notation romC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
Local Notation romA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom.
(* LPS's register read (Riscv/Sem.v:301), the one Regs6ss.mkR_of is written with. *)
Local Notation reg_get := LinuxProcessSemantics.Riscv.Sem.reg_get.

(* ---------------------------------------------------------------------------------------------------------
   1. Address facts. *)

(* The core's shadow map (YG0f.shadow_addr) is ctrl's (AsanRT.shadow_addr): both are a / 8 + 0x7fff8000. *)
Lemma f29_sa_eq : forall a, Reusable.YG0f.shadow_addr a = A.AsanRT.shadow_addr a.
Proof.
  intros a. unfold Reusable.YG0f.shadow_addr, A.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.ASAN_K. lia.
Qed.

(* No byte at or above the image top 0x5fe000 is a segment byte (ProgBridge.rsegs_spans). *)
Lemma f29_seg_none : forall a, 0x5fe000 <= a -> find_segment A.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment A.Img0.rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  destruct (Reusable.YK04.find_segment_some_spec _ _ _ _ E) as (Hin & H1 & H2).
  pose proof (in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0))) _ _ Hin) as Hm.
  rewrite A.ProgBridge.rsegs_spans in Hm. cbn [In] in Hm.
  repeat (destruct Hm as [Hm | Hm]; [injection Hm as E1 E2; lia |]). destruct Hm.
Qed.

(* So a byte at or above 0x5fe000 that reads Some through lib/Lib's mrd is a byte of the memory itself. *)
Lemma f29_mrd_high : forall (m : word -> option byte) (x : word) b,
  0x5fe000 <= bv_unsigned x -> Lib.Mem.mrd segs m x = Some b -> m x <> None.
Proof.
  intros m x b Hx Hb Hn. unfold Lib.Mem.mrd in Hb. rewrite Hn in Hb.
  unfold Lib.PropExec.seg_rom, memory_read in Hb. change (Z.of_N 1) with 1 in Hb.
  pose proof (f29_seg_none (bv_unsigned x) Hx) as Hn0. rewrite <- A.ProgBridge.tfibsegs_rsegs in Hn0.
  rewrite Hn0 in Hb. discriminate Hb.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. A write set that misses the stage bundles (F29's three shadow stores, F30's six shadow stores and its event
   cell): no application byte outside [fr + 448, fr + 536), no shadow byte of an address outside [fr + 128, fr + 536). *)
Definition f_safe (fr : Z) (W : list Lib.Frame.ivl) : Prop :=
  (forall x, A.AsanRT.app_mem x -> ~ (fr + 448 <= x < fr + 536) -> Lib.Frame.outside W x) /\
  (forall y, 0 <= y < A.AsanRT.APPMEM_END -> ~ (fr + 128 <= y < fr + 536) ->
     Lib.Frame.outside W (A.AsanRT.shadow_addr y)).

Section Keep.
Variables (W : list Lib.Frame.ivl) (fr : Z) (m m' : word -> option byte).
Hypothesis MU : Lib.Frame.munch W m m'.
Hypothesis FS : f_safe fr W.

Lemma k_bytes : forall a bs, Lib.Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> A.AsanRT.app_mem x /\ ~ (fr + 448 <= x < fr + 536)) ->
  Lib.Mem.bytes_at segs m' a bs.
Proof.
  intros a bs H Hx. exact (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs H MU
    (fun x Hr => proj1 FS x (proj1 (Hx x Hr)) (proj2 (Hx x Hr)))).
Qed.

Lemma k_addr : forall p n, A.AsanRT.addressable m p n ->
  (forall y, p <= y < p + n -> ~ (fr + 128 <= y < fr + 536)) -> A.AsanRT.addressable m' p n.
Proof.
  intros p n H Hy. pose proof H as (H0 & Hn & Hend & _).
  apply (A.Prog.Seg.F29.addr_keep W m m' p n H MU). intros i Hi.
  apply (proj2 FS); [split; lia | apply Hy; lia].
Qed.

(* A spill [Ab + off] moves when the spill base Ab (register 9) is high application memory above the frame. *)
Lemma k_spill : forall (regs regs' : bvmap 5 word) Ab off v, ACtlCutP.spill regs m off v ->
  ACtlCut.rgv regs 9 Ab -> getrC regs' 9 = getrC regs 9 ->
  A.AsanRT.HIGHMEM_BEG <= Ab -> Ab + 416 <= A.AsanRT.APPMEM_END -> fr + 536 <= Ab -> 0 <= off <= 400 ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' Ab off v Hs HA E9 Hhi Htop Hfr Hoff.
  assert (Hx : forall x, Ab <= x < Ab + 416 -> Lib.Frame.outside W x).
  { intros x Hx. apply (proj1 FS); [|lia].
    unfold A.AsanRT.app_mem. right. unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia. }
  unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *.
  exact (A.Prog.Seg.F29.spill_keep regs regs' m m' W Ab off v Hs MU E9 HA ltac:(lia) ltac:(lia) Hoff Hx).
Qed.

(* HB: the turn's block, apart from the frame window. *)
Lemma k_hb : forall phi len,
  (forall y, phi <= y < phi + A.ACtlK.a_size len -> ~ (fr + 128 <= y < fr + 536)) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof. intros phi len Hy (H0 & Had). split; [exact H0|]. exact (k_addr phi _ Had Hy). Qed.
End Keep.

(* ---------------------------------------------------------------------------------------------------------
   3. What the frame-loop bundles (ACtlCutP.v:466-725) and FRAC (:980-994) read, as ONE transfer relation from a
   memory m with map regs to a memory m' with map regs': the frame's bytes outside [fr + 448, fr + 536) and the
   spill / saved-register block [Ab, c_sp), the frame's shadow outside [fr + 128, fr + 536), the spills through
   register 9, the input block's bytes and addressability, the frame's readable-writable range.  F29 establishes it
   across its stores (ktr_of_munch); F30 across its stores and then across the callee's kept view, and composes the
   two (ktr_trans). *)
Definition ktr (fr Ab : Z) (cx : ACtlCut.ctlcx) (regs regs' : bvmap 5 word) (m m' : word -> option byte) : Prop :=
  (forall a bs, Lib.Mem.bytes_at segs m a bs ->
     (forall x, a <= x < a + Z.of_nat (length bs) ->
        (fr <= x < fr + 4096 /\ ~ (fr + 448 <= x < fr + 536)) \/ (Ab <= x < ACtlCut.c_sp cx)) ->
     Lib.Mem.bytes_at segs m' a bs) /\
  (forall p n, A.AsanRT.addressable m p n ->
     (forall y, p <= y < p + n -> fr <= y < fr + 4096 /\ ~ (fr + 128 <= y < fr + 536)) ->
     A.AsanRT.addressable m' p n) /\
  (forall off v, 0 <= off <= 400 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v) /\
  (Lib.Mem.bytes_at segs m (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
     Lib.Mem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)) /\
  (A.AsanRT.addressable m (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
     A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) /\
  (Lib.Frame.stk segs m fr (fr + 3136) -> Lib.Frame.stk segs m' fr (fr + 3136)).

Lemma ktr_trans : forall fr Ab cx r1 r2 r3 m1 m2 m3,
  ktr fr Ab cx r1 r2 m1 m2 -> ktr fr Ab cx r2 r3 m2 m3 -> ktr fr Ab cx r1 r3 m1 m3.
Proof.
  intros fr Ab cx r1 r2 r3 m1 m2 m3 (A1 & B1 & C1 & D1 & E1 & F1) (A2 & B2 & C2 & D2 & E2 & F2).
  split; [intros a bs H Hx; exact (A2 a bs (A1 a bs H Hx) Hx)|].
  split; [intros p n H Hy; exact (B2 p n (B1 p n H Hy) Hy)|].
  split; [intros off v Ho H; exact (C2 off v Ho (C1 off v Ho H))|].
  split; [intros H; exact (D2 (D1 H))|].
  split; [intros H; exact (E2 (E1 H)) | intros H; exact (F2 (F1 H))].
Qed.

(* The facts a munch-run transfer takes: the frame and the input block are application memory, the input block
   misses the frame, the spill base Ab (register 9) is high application memory above the frame, register 9 kept. *)
Definition kenv (W : list Lib.Frame.ivl) (fr : Z) (m m' : word -> option byte) (cx : ACtlCut.ctlcx)
    (regs regs' : bvmap 5 word) (Ab : Z) : Prop :=
  Lib.Frame.munch W m m' /\ f_safe fr W /\
  (forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y) /\
  (forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
     A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)) /\
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx /\
  ACtlCut.rgv regs 9 Ab /\ getrC regs' 9 = getrC regs 9 /\
  A.AsanRT.HIGHMEM_BEG <= Ab /\ Ab + 416 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END /\
  fr + 536 <= Ab.

Lemma ktr_of_munch : forall W fr m m' cx regs regs' Ab, kenv W fr m m' cx regs regs' Ab ->
  Lib.Frame.wmono segs m m' ->
  (forall x, fr + 448 <= x < fr + 536 ->
     Lib.Frame.outside W x \/ exists b, Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Some b) ->
  ktr fr Ab cx regs regs' m m'.
Proof.
  intros W fr m m' cx regs regs' Ab (MU & FS & HFAPP & HCP & HLEN & R9 & E9 & HAHI & HAc & HcAPP & HAFR) WM HNW.
  split.
  { intros a bs H Hx. apply (k_bytes W fr m m' MU FS a bs H). intros x Hr.
    destruct (Hx x Hr) as [(H1 & H2) | H1].
    - split; [apply HFAPP; lia | exact H2].
    - split; [|lia]. unfold A.AsanRT.app_mem. right. unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia. }
  split.
  { intros p n H Hy. apply (k_addr W fr m m' MU FS p n H). intros y Hr. exact (proj2 (Hy y Hr)). }
  split.
  { intros off v Ho Hs. exact (k_spill W fr m m' MU FS regs regs' Ab off v Hs R9 E9 HAHI ltac:(lia) HAFR Ho). }
  split.
  { intros H. apply (k_bytes W fr m m' MU FS _ _ H). intros x Hr. rewrite HLEN in Hr.
    destruct (HCP x Hr) as (Ha & Hn). split; [exact Ha | lia]. }
  split.
  { intros H. apply (k_addr W fr m m' MU FS _ _ H). intros y Hr. destruct (HCP y Hr) as (_ & Hn). lia. }
  intros Hstk. apply (A.Prog.Seg.F29.stk_tr W m m' fr (fr + 3136) Hstk MU WM). intros x Hx.
  destruct (Z_lt_le_dec x (fr + 448)) as [Hlo|Hlo]; [left; apply (proj1 FS); [apply HFAPP; lia | lia]|].
  destruct (Z_lt_le_dec x (fr + 536)) as [Hhi|Hhi]; [apply HNW; lia|].
  left; apply (proj1 FS); [apply HFAPP; lia | lia].
Qed.

(* a byte range of the frame at offsets >= 536 *)
Lemma kt_frb : forall fr Ab cx a n x, fr + 536 <= a -> a + n <= fr + 4096 -> a <= x < a + n ->
  (fr <= x < fr + 4096 /\ ~ (fr + 448 <= x < fr + 536)) \/ (Ab <= x < ACtlCut.c_sp cx).
Proof. intros. left. lia. Qed.

Section Bundles.
Variables (fr Ab : Z) (cx : ACtlCut.ctlcx) (regs regs' : bvmap 5 word) (m m' : word -> option byte).
Hypothesis HT : ktr fr Ab cx regs regs' m m'.

Let TB := proj1 HT.
Let TA := proj1 (proj2 HT).
Let SP := proj1 (proj2 (proj2 HT)).
Let TCB := proj1 (proj2 (proj2 (proj2 HT))).
Let TCA := proj1 (proj2 (proj2 (proj2 (proj2 HT)))).
Let TSTK := proj2 (proj2 (proj2 (proj2 (proj2 HT)))).

Lemma kt_pro : ACtlCutP.PRO cx fr regs m -> ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros (H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248 & Had & Hby & Hin & H184 & H256 & H264 & H272 & H32).
  split; [apply SP; [lia | exact H40]|]. split; [apply SP; [lia | exact H120]|].
  split; [apply SP; [lia | exact H136]|]. split; [apply SP; [lia | exact H160]|].
  split; [apply SP; [lia | exact H168]|]. split; [apply SP; [lia | exact H176]|].
  split; [apply SP; [lia | exact H208]|]. split; [apply SP; [lia | exact H248]|].
  split; [apply TA; [exact Had | intros y Hy; lia]|].
  split; [exact (TCB Hby)|].
  split; [intros Hn0; exact (TCA (Hin Hn0))|].
  split; [apply SP; [lia | exact H184]|]. split; [apply SP; [lia | exact H256]|].
  split; [apply SP; [lia | exact H264]|]. split; [apply SP; [lia | exact H272] | apply SP; [lia | exact H32]].
Qed.

Lemma kt_flsh : forall j, ACtlCutP.FLSH cx j fr regs m -> ACtlCutP.FLSH cx j fr regs' m'.
Proof.
  intros j (HP & H128 & Hstk & H144 & Had17).
  split; [exact (kt_pro HP)|]. split; [apply SP; [lia | exact H128]|].
  split; [unfold ACtlCutP.FRAME_BYTES in *; exact (TSTK Hstk)|].
  split; [apply SP; [lia | exact H144]|].
  apply TA; [exact Had17 | intros y Hy; lia].
Qed.

Lemma kt_flc : ACtlCutP.FLC fr regs m -> ACtlCutP.FLC fr regs' m'.
Proof.
  intros (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cra & C72 & C64 & C56 & C48).
  split; [apply SP; [lia | exact C256]|]. split; [apply SP; [lia | exact C184]|].
  split; [apply SP; [lia | exact C192]|]. split; [apply SP; [lia | exact C80]|].
  split; [apply SP; [lia | exact C88]|]. split; [apply SP; [lia | exact C96]|].
  split; [apply SP; [lia | exact C272]|]. split; [apply SP; [lia | exact C264]|].
  split; [apply TA; [exact Cfa | unfold ACtlCutP.fragb; intros y Hy; lia]|].
  split; [apply TA; [exact Cra | intros y Hy; lia]|].
  split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
  split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]].
Qed.

Lemma kt_flsi : forall j, ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros j (HH & H216 & H224 & H248 & (Had & Hby) & HC).
  split; [exact (kt_flsh j HH)|].
  split; [apply SP; [lia | exact H216]|]. split; [apply SP; [lia | exact H224]|].
  split; [apply SP; [lia | exact H248]|].
  split; [split; [exact (TCA Had) | exact (TCB Hby)] | exact (kt_flc HC)].
Qed.

Lemma kt_lk : forall j, getrC regs' 21 = getrC regs 21 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros j E21 (Hj & H21 & HOUR).
  split; [exact Hj|]. split; [exact (eq_trans E21 H21)|].
  unfold ACtlCutP.OURb in *. apply TB; [exact HOUR|].
  rewrite A.Prog.SlotModel.OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx.
  apply (kt_frb fr Ab cx (fr + 2624) 6); lia.
Qed.

Lemma kt_lt : forall j, ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros j HLT.
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb,
    ACtlCutP.FGBe, ACtlCutP.FSj, ACtlCutP.FSb in *.
  destruct HLT as ((HIDB & Hok1) & (HFGB & Hok2) & (H104 & H112 & Hbody & Had & HFI)).
  split; [split; [|exact Hok1]|split; [split; [|exact Hok2]|]].
  - apply TB; [exact HIDB|]. rewrite A.Prog.Seg.F29.tID_len. intros x Hx.
    change (Z.of_nat OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.ID_SIZE) with 38 in Hx.
    apply (kt_frb fr Ab cx (fr + 2688) 38); lia.
  - apply TB; [exact HFGB|]. rewrite A.Prog.Seg.F29.tFG_len. intros x Hx.
    change (Z.of_nat 72) with 72 in Hx.
    apply (kt_frb fr Ab cx (fr + 2768) 72); lia.
  - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
    split.
    + apply TB; [exact Hbody|]. intros x Hx.
      pose proof (A.Prog.Seg.F29.fs_body_len (ACtlCut.c_in cx) (S j)) as Hl.
      apply (kt_frb fr Ab cx (fr + 2880) 23); lia.
    + split; [apply TA; [exact Had | intros y Hy; lia] | exact HFI].
Qed.

Lemma kt_fls : forall j phi,
  getrC regs' 18 = getrC regs 18 -> getrC regs' 22 = getrC regs 22 -> getrC regs' 23 = getrC regs 23 ->
  getrC regs' 24 = getrC regs 24 -> getrC regs' 25 = getrC regs 25 ->
  (forall bs, Z.of_nat (length bs) <= ACtlCutP.flen cx j ->
     Lib.Mem.bytes_at segs m phi bs -> Lib.Mem.bytes_at segs m' phi bs) ->
  ACtlCutP.FLS cx j phi fr regs m -> ACtlCutP.FLS cx j phi fr regs' m'.
Proof.
  intros j phi E18 E22 E23 E24 E25 TPH (HI & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280).
  split; [exact (kt_flsi j HI)|].
  split; [exact (eq_trans E18 H18)|]. split; [exact (eq_trans E22 H22)|].
  split; [exact (eq_trans E23 H23)|]. split; [exact (eq_trans E24 H24)|].
  split; [exact (eq_trans E25 H25)|].
  split.
  { intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [apply TPH; [rewrite A.Prog.Seg.F29.t_g_length; change (Z.of_nat 50) with 50; lia | exact Hg]|].
    split; [apply TPH; [exact Hpl | exact Hpb] | exact Hpl]. }
  split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]].
Qed.

(* FRAC at the new map and memory, its spill base being Ab; the 392 frame-shadow bytes re-read at m'; the fake-frame
   trailer word [fr + 4088, fr + 4096) (FRAC's last conjunct, Batch3) is a frame byte range outside the window
   [fr + 448, fr + 536), so ktr's byte clause keeps it like the header words. *)
Lemma kt_frac : forall B sel,
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab < 2 ^ 64 ->
  getrC regs' 2 = getrC regs 2 -> getrC regs' 3 = getrC regs 3 -> getrC regs' 4 = getrC regs 4 ->
  getrC regs' 8 = getrC regs 8 -> getrC regs' 9 = getrC regs 9 -> getrC regs' 19 = getrC regs 19 ->
  getrC regs' 26 = getrC regs 26 ->
  (exists sh, Lib.Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros B sel RAb HAb E2 E3 E4 E8 E9 E19 E26 Hsh'
    (A1 & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
     HfrA & HA416 & Hspc & HcAPP & Q304 & Q24 & Q16 & Qhdr & Qhdr16 & _ & Hsaved & Qtr).
  pose proof HfrA as HfrA'. unfold ACtlCutP.FRAME_BYTES in HfrA'.
  assert (Hsp0 : 0 <= sp < 2 ^ 64).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (getrC regs 2)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
  assert (EA : A1 = Ab).
  { apply (A.Prog.Seg.F29.reg_eq regs 9 A1 Ab R9 RAb); [unfold A.AsanRT.APPMEM_END in HcAPP; lia | exact HAb]. }
  subst A1.
  exists Ab, sp.
  split; [exact (eq_trans E2 R2)|]. split; [exact Hsp16|].
  split; [unfold Reusable.YG0d.spZ in *; rewrite <- HspZ; exact (f_equal (@bv_unsigned 64) E2)|].
  split; [exact (eq_trans E4 R4)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact (eq_trans E3 R3)|]. split; [exact (eq_trans E19 R19)|]. split; [exact (eq_trans E26 R26)|].
  split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAc|]. split; [exact HspA|]. split; [exact HfrA|].
  split; [exact HA416|]. split; [exact Hspc|]. split; [exact HcAPP|].
  unfold ACtlCutP.q64 in *.
  split.
  { apply TB; [exact Q304|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Q24|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Q16|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Qhdr|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    left. lia. }
  split.
  { apply TB; [exact Qhdr16|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    left. lia. }
  split; [exact Hsh'|].
  split.
  { apply TB; [exact Hsaved|].
    assert (Hsl : length (ACtlCutP.saved_bytes cx) = 104%nat).
    { unfold ACtlCutP.saved_bytes. rewrite !length_app, !Lib.Mem.length_le8. reflexivity. }
    rewrite Hsl. intros x Hx. change (Z.of_nat 104) with 104 in Hx. right. lia. }
  apply TB; [exact Qtr|]. rewrite Lib.Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  left. lia.
Qed.
End Bundles.

(* ---------------------------------------------------------------------------------------------------------
   4. The stage. *)
Section GlueF29.

(* ACtl.v's Section shape (ACtl.v:170-194), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:189, :193-194), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82750_at := (ACtlCutP.C_A82750_at B).
Local Notation C_A8275c_at := (ACtlCutP.C_A8275c_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F29 : forall POST (j : nat),
  CF POST (ix_cut C_A8275c_at [Z.of_nat j]) -> CF POST (ix_cut C_A82750_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82750_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hcn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
  (* G2: the frame, the blocks, the spill base, from visible state *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _ & Hastk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstkhi & _).
  pose proof Reusable.YCbq.asan_consts as (Hceil & _).
  unfold A.ACfn.LLVMF_STK in Hstkhi.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (E4096 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfapp & _ & Hfsh).
  rewrite Efr3, E4096 in Hfapp. rewrite Efr3, E4096 in Hfsh. change (4096 / 8) with 512 in Hfsh.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  assert (HFAPP : forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y).
  { intros y Hy. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hfapp as (H1 & [H2 | (H2 & H3)]); [left | right]; lia. }
  pose proof HFRAC as (Ab & sp & _ & _ & HspZ & _ & _ & R9 & _ & R19 & _ & Hfr32 & _ & HAc & HspA & HfrA & HA416 &
    Hspc & HcAPP & _ & _ & _ & _ & _ & (sh & Hsh & Hshl) & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hfr0 : 0 <= fr) by (destruct Hfapp; lia).
  assert (Hcsp : A.AsanRT.HIGHMEM_BEG + 4096 <= ACtlCut.c_sp cx)
    by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HAHI : A.AsanRT.HIGHMEM_BEG <= Ab) by (unfold A.AsanRT.HIGHMEM_BEG in *; lia).
  assert (HcAPP' : ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) by lia.
  assert (HAFR : fr + 536 <= Ab) by lia.
  assert (HAb64 : 0 <= Ab < 2 ^ 64) by (unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *; lia).
  (* the turn's block phi: live at this cut, apart from the frame *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi _ HAR Hinphi) as (_ & _ & _ & _ & _ & _ & Hfl).
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hinphi Hin6)
    as Hdphi.
  rewrite Efr3, E4096 in Hdphi. unfold Reusable.YG0f.zdisjoint in Hdphi. cbn [fst snd] in Hdphi.
  pose proof HHB as (_ & HphA).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HphA) as HphApp.
  assert (HPH : forall y, phi <= y < phi + A.ACtlK.a_size (ACtlCutP.flen cx j) ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HphApp; lia|].
    unfold A.ACtlK.a_size, Reusable.YG00.req_size in *.
    destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  (* the input block: live at entry, still live (FP = []), apart from the frame *)
  pose proof Hbase as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
  pose proof HFLSI as (_ & _ & _ & _ & (HinA & _) & _).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HinA) as HinApp.
  assert (HCP : forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HinApp; lia|].
    destruct Hpn as [(Hn0 & _) | (Hn0 & Hinp)]; [lia|].
    assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x0 y0; decide equality; apply Z.eq_dec).
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { destruct (in_dec Hdec (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)) as [Hi|Hni];
        [exact Hi|].
      exfalso. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil (ACtlCut.c_p cx + 0)).
      apply (Hgone _ _ 0 Hinp Hni). unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hinp3 Hin6)
      as Hdin.
    rewrite Efr3, E4096 in Hdin. unfold Reusable.YG0f.zdisjoint in Hdin. cbn [fst snd] in Hdin.
    unfold Reusable.YG00.req_size in Hdin. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (HLEN : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hlen).
  (* the run's premises *)
  set (Sh := ACtlCutP.Sfr fr) in *.
  assert (ESh : Sh = A.AsanRT.shadow_addr fr) by reflexivity.
  assert (HshA : forall i, 0 <= i < 512 -> Sh + i = A.AsanRT.shadow_addr (fr + 8 * i)).
  { intros i Hi. rewrite ESh. rewrite A.Prog.Seg.F29.sh_frame_of by lia. reflexivity. }
  assert (HinSh : forall i, 0 <= i < 512 -> A.AsanRT.in_shadow (Sh + i)).
  { intros i Hi. rewrite (HshA i Hi). apply A.AsanRTFacts.shadow_of_app. apply HFAPP. lia. }
  pose proof (A.AsanRTFacts.in_shadow_range _ (HinSh 0 ltac:(lia))) as HSb0.
  pose proof (A.AsanRTFacts.in_shadow_range _ (HinSh 511 ltac:(lia))) as HSb1.
  assert (HSlo : A.AsanRT.LOWMEM_END <= Sh).
  { pose proof (HinSh 0 ltac:(lia)) as H0. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
      A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *. lia. }
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  destruct Hrt as (Hac & Hcut & Himg & Hro).
  pose proof (A.Prog.Seg.F29.ba_sub mem3 Sh sh 16 5 Hsh ltac:(lia)) as Hsh5.
  change (Z.of_nat 16) with 16 in Hsh5.
  (* the five stored bytes are the owned class-6 frame's shadow: ctl_rt_C's (F) disjunct *)
  assert (HF5 : forall i, 0 <= i < 5 -> A.ACtlRtC.cut_shadow B ly3 S3 (Sh + (16 + i))).
  { intros i Hi. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efr3, E4096, f29_sa_eq, <- ESh. change (4096 / 8) with 512. lia. }
  assert (Hwr5 : Lib.Mem.wr_at A.Img0.rsegs mem3 (Sh + 16) 5).
  { split; [lia|]. split; [lia|]. intros i Hi.
    replace (Sh + 16 + i) with (Sh + (16 + i)) by lia.
    exact (proj1 (Hcut _ (HF5 i Hi) (HinSh (16 + i) ltac:(lia)))). }
  assert (HRW : Lib.Step.rw_cells A.Img0.rsegs mem3 (Sh + 16) [Lib.Cells.CB 5 (firstn 5 (skipn 16 sh))]).
  { split; [split|].
    - cbn [Lib.Cells.cells_wf Lib.Cells.cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [Lib.Cells.cells_bytes Lib.Cells.cbytes]. rewrite app_nil_r. exact Hsh5.
    - cbn [Lib.Cells.cells_size Lib.Cells.csize Nat.add]. exact Hwr5. }
  assert (Hrng : Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (Sh + 16) 5).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfsh (a - Sh) ltac:(lia)) as ((Hv & _) & _).
    rewrite f29_sa_eq, <- ESh in Hv. replace (Sh + (a - Sh)) with a in Hv by lia. exact Hv. }
  assert (E19 : reg_get regs3 19 = Z_to_bv 64 Sh) by exact R19.
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82750_at [Z.of_nat j])) with 0x82750.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 fpR (Z_to_bv 64 0x82750) fpC None
           mem3 (romC segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the lift *)
  pose proof (A.Prog.Seg.F29F.f29_evt_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11)
    (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
    (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21)
    (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26)
    (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    fpR fpC mem3 Sh (firstn 5 (skipn 16 sh)) E19 HRW ltac:(lia) ltac:(lia) Hrng)
    as HRUN.
  change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (m' & Ems & MU & WM & cs & Hcs & Hcsl). subst ms'.
  change (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
  (* G5: back to the cut's own map (the run writes no register), then the exit cut *)
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 regs3 (Lib.Regs6ss.mkR_of regs3) fpR (Z_to_bv 64 0x8275c) fpC None
           m' (romC segs) md' (POST cx)); [| exact (Lib.Regs6ss.mkR_of_eqv regs3)].
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8275c_at [Z.of_nat j])) regs3 m' md') (POST cx)).
  (* what the three stores write, and what they miss *)
  assert (Hnew : forall x, Sh + 16 <= x < Sh + 21 -> exists b, Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Some b).
  { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
    pose proof (Lib.Cells.cells_bytes_length cs Hwf) as Hcl.
    replace x with (Sh + 16 + (x - (Sh + 16))) by lia.
    apply (A.Prog.Seg.F29.ba_some m' (Sh + 16) (Lib.Cells.cells_bytes cs)); [exact Hba|].
    rewrite Hcl, Hcsl. cbn. lia. }
  assert (FS : f_safe fr [(Sh + 16, Sh + 21)]).
  { split.
    - intros x Hx _. cbn [Lib.Frame.outside]. split; [|exact I]. intros Hin.
      apply (A.AsanRTFacts.app_not_shadow x Hx).
      replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia.
    - intros y Hy Hny. cbn [Lib.Frame.outside]. split; [|exact I]. intros Hin. apply Hny.
      pose proof (A.Prog.Seg.F29.sh_frame fr y (A.AsanRT.shadow_addr y - Sh) Hfr0 Hfr8 ltac:(lia)
                    ltac:(rewrite <- ESh; lia)) as Hz.
      lia. }
  assert (HE : kenv [(Sh + 16, Sh + 21)] fr mem3 m' cx regs3 regs3 Ab).
  { split; [exact MU|]. split; [exact FS|]. split; [exact HFAPP|]. split; [exact HCP|].
    split; [exact HLEN|]. split; [exact R9|]. split; [reflexivity|]. split; [exact HAHI|].
    split; [exact HA416|]. split; [exact HcAPP' | exact HAFR]. }
  assert (HNW : forall x, fr + 448 <= x < fr + 536 ->
            Lib.Frame.outside [(Sh + 16, Sh + 21)] x \/ exists b, Lib.Mem.mrd segs m' (Lib.Mem.wa x) = Some b).
  { intros x Hx. left. cbn [Lib.Frame.outside]. split; [|exact I]. intros Hin.
    apply (A.AsanRTFacts.app_not_shadow x (HFAPP x ltac:(lia))).
    replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia. }
  pose proof (ktr_of_munch _ _ _ _ _ _ _ _ HE WM HNW) as HT.
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 regs3 m' md' Hbase).
  - (* journal: the three bytes are the owned frame's shadow (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => Sh + 16 <= a < Sh + 21).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict. destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [Lib.Frame.outside]. split; [exact Hx | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (Z_le_gt_dec (Sh + 16) (bv_unsigned x)) as [H1|H1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (Sh + 21)) as [H2|H2]|].
      * destruct (Hnew (bv_unsigned x) ltac:(lia)) as (b & Hb).
        unfold Lib.Mem.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
        apply (f29_mrd_high m' x b); [unfold A.AsanRT.LOWMEM_END in HSlo; lia | exact Hb].
      * rewrite MU; [exact Hx|]. cbn [Lib.Frame.outside]. split; [lia | exact I].
      * rewrite MU; [exact Hx|]. cbn [Lib.Frame.outside]. split; [lia | exact I].
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames. right. right. right.
      exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      rewrite Efr3, E4096, f29_sa_eq, <- ESh. unfold Reusable.YG0n.in_zr. cbn [fst snd].
      change (4096 / 8) with 512. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax on both cuts *)
    exact Hk.
  - (* the exit body, C_A8275c_at (ACtlCutP.v:2708-2718), at the same index *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8275c_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact Hperm|].
    split.
    { apply (kt_frac fr Ab cx regs3 regs3 mem3 m' HT B fr R9 HAb64 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
               eq_refl); [|exact HFRAC].
      assert (Hpres : forall i, (i < 392)%nat ->
                exists b, Lib.Mem.mrd A.Img0.rsegs m' (Lib.Mem.wa (Sh + Z.of_nat i)) = Some b).
      { intros i Hi.
        destruct (Z_le_gt_dec 16 (Z.of_nat i)) as [H1|H1];
          [destruct (Z_lt_ge_dec (Z.of_nat i) 21) as [H2|H2]|].
        - apply Hnew. lia.
        - destruct (A.Prog.Seg.F29.ba_some mem3 Sh sh (Z.of_nat i) Hsh ltac:(rewrite Hshl'; lia)) as (b & Hb).
          exists b. unfold Lib.Mem.mrd in *. rewrite MU; [exact Hb|].
          rewrite Lib.Mem.wa_unsigned by lia. cbn [Lib.Frame.outside]. split; [lia | exact I].
        - destruct (A.Prog.Seg.F29.ba_some mem3 Sh sh (Z.of_nat i) Hsh ltac:(rewrite Hshl'; lia)) as (b & Hb).
          exists b. unfold Lib.Mem.mrd in *. rewrite MU; [exact Hb|].
          rewrite Lib.Mem.wa_unsigned by lia. cbn [Lib.Frame.outside]. split; [lia | exact I]. }
      destruct (A.Prog.Seg.F29.ba_present m' 392 Sh ltac:(lia) ltac:(lia) Hpres) as (sh' & Hb' & Hl').
      exists sh'. split; [exact Hb' | rewrite Hl'; reflexivity]. }
    split; [exact Hcn|]. split; [exact Hj|].
    split.
    { apply (k_hb [(Sh + 16, Sh + 21)] fr mem3 m' MU FS); [|exact HHB].
      intros y Hy. destruct (HPH y Hy) as (_ & Hn). lia. }
    split; [exact (kt_flsi fr Ab cx regs3 regs3 mem3 m' HT j HFLSI)|].
    split; [exact (kt_lk fr Ab cx regs3 regs3 mem3 m' HT j eq_refl HLK)|].
    split.
    { apply (kt_fls fr Ab cx regs3 regs3 mem3 m' HT j phi eq_refl eq_refl eq_refl eq_refl eq_refl); [|exact HFLS].
      intros bs Hbs Hb. apply (k_bytes [(Sh + 16, Sh + 21)] fr mem3 m' MU FS _ _ Hb).
      intros x Hx. destruct (HPH x ltac:(unfold A.ACtlK.a_size; lia)) as (Ha & Hn). split; [exact Ha | lia]. }
    exact (kt_lt fr Ab cx regs3 regs3 mem3 m' HT j HLT).
  - (* ctl_rt_C at the same state ly3 S3: asan_cells (the window is far above RT_HI), the two shadow_rw_on regions
       (any region P is kept: writable by wmono, present by munch / the written cells), ro_agree *)
    assert (Hkeep : forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m').
    { intros P HP a Hp Ha.
      destruct (HP a Hp Ha) as (Hw & b & Hb). split; [apply WM; exact Hw|].
      pose proof (A.AsanRTFacts.in_shadow_range a Ha) as Hab.
      destruct (Z_le_gt_dec (Sh + 16) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 21)) as [H2|H2]|].
      - apply Hnew. lia.
      - exists b. unfold Lib.Mem.mrd in *. rewrite MU; [exact Hb|].
        rewrite Lib.Mem.wa_unsigned by lia. cbn [Lib.Frame.outside]. split; [lia | exact I].
      - exists b. unfold Lib.Mem.mrd in *. rewrite MU; [exact Hb|].
        rewrite Lib.Mem.wa_unsigned by lia. cbn [Lib.Frame.outside]. split; [lia | exact I]. }
    split; [|split; [|split]].
    + apply (A.AsanRTFacts.asan_cells_kept _ mem3 m' Hac MU). cbn [Lib.Frame.disjoint_from].
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. unfold A.AsanRT.LOWMEM_END in HSlo.
      split; [left; lia | exact I].
    + exact (Hkeep _ Hcut).
    + exact (Hkeep _ Himg).
    + unfold A.ACtlK.ro_agree_at in *. intros a Ha.
      pose proof (A.Prog.Seg.F29.ro_lo a Ha) as Hlo.
      unfold Lib.Mem.mrd in *. rewrite MU; [exact (Hro a Ha)|].
      cbn [Lib.Frame.outside]. split; [unfold A.AsanRT.LOWMEM_END in HSlo; lia | exact I].
Qed.

End GlueF29.
