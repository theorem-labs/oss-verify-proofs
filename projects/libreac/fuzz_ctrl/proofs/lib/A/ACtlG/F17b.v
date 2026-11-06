(* lib/A/ACtlG/F17b.v -- GLUE for stage seg_F17b of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   Hypothesis seg_F17b, ACtl.v (at head lib/A/ACtl.v:803) (an earlier version, blob 84ef756918c, not in this delivery)).  Written by a Theorem Labs lane after the pattern of
   lib/A/ACtlG/A5.v (glue-pattern.md (a working note, not in this delivery)); single writer.  rule 24: no
   function proved (stage glue of a walk).
   proves no function (kind: segment lemma).
   REUSE SEARCH (FREE-PIECES rule 17; `proof-index glue_seg_F17b seg_F17b`, index built 2026-10-29T07:26:27Z, run 07:34Z,
   output reuse-F17b.txt): glue_seg_F17b: 0 named, 0 by address,
   0 related, 0 released, the delivered package 0; declared only on this branch (a working branch). seg_F17b: 0 released, the delivered package 0;
   its hits are the stage hypothesis (ACtl.v) and source lemma (Seg/F17.v, image B twin) this file builds on.  Written new.
   At ossv/recipes c5e779efe8c (2026-10-31), glue_seg_F17b and seg_F17b are defined only in this unit (glue_seg_F17b
   in this file; seg_F17b at the stage hypotheses lib/A/ACtl.v:803 and lib/B/ACtl.v:580, the source lemmas lib/A/Prog/Seg/F17.v:1383 and
   lib/B/Prog/Seg/F17b.v:706, and image B's lib/B/ACtlW4d.v:811).

   WHAT IT PROVES
     glue_seg_F17b : forall POST (j : nat),
       CF POST (ix_cut C_A823e8_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's seg_F17b.  The ENTRY
   is C_A822a0_at at turn j, the EXIT C_A823e8_at at the same turn.  Segment F17b is the opens_record body
   0x822a0 -> 0x823e8 of a Theorem Labs lane's v1.9 proof (Seg/F17.v seg_F17b :1383-2001 at db985828094, blob 2530d1eeed7 (the blob this tree had at release c5e779efe8c)):
   the length / sum guard, nine instrumented record-byte checks, and, when they all pass, the copy of the first
   fragment's body into the frame object first.sroa.7 by `jal __asan_memcpy` (0x823d4) and the two spill stores
   [A+104] = 1, [A+112] = gg[26]; every arm leaves through the join `ld s9,176(s1)` to 0x823e8.

   THE RUN.  lib/A/Prog/Seg/F17bFs.v (this lane, on a working branch since c8dd30be050): since the route (C)
   switch, PF.seg_F17b_run_F_on, the route (C) twin of PF.seg_F17b_run_F (the footprint extraction of seg_F17b's
   inline run; the tail composed from a Theorem Labs lane's F17F.v stretches and PF.f17_mc_F_on), whose callee premise
   asan_memcpy_contract_F_on is discharged here by a Theorem Labs lane's proved closed
   A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on (the same route as before with the region form: a Theorem Labs lane's
   split-rule correction, 04:39Z via a Theorem Labs lane: a LIFTED callee's contract_F premise is discharged by its proved closed
   theorem, no split, the run consumed whole).  So Seg/F17.v:486's plain Hypothesis HMC is used by nothing and NO callee
   hypothesis stays open.  F17bFs.v's source tie seg_F17b_src (`type of @F17.seg_F17b`) is the pin of the extraction
   (of seg_F17b_run_F, whose script seg_F17b_run_F_on repeats with the call's region premise).

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at [Z.of_nat j]: ix_cut's index equation, then C_A822a0_at's body (ACtlCutP.v:2409-2449).
   G2  the run's premises from the body, FRAC, the journal and the AR laws: registers sp, s1 = A, s4, s7 = phi, s10;
       the spills [A+232], [A+176], [A+200], [A+32] (PRO); on a long frame the record (bytes, addressable 50, the
       sum flag) and its distance from the frame (YCbq.sep_block_frame) and from the callee window (the body's
       BCMP_WRAP_K clause, 4560 >= ASAN_MEMCPY_K = 2224); first.sroa.7 addressable 35 (IFS3) and the frame
       byte-backed (FLSH); IMG_TOP = 0x5fe000 <= fr from YG0s.frame_facts, moved to the run's Contract.GT by the one
       bridge equation f17bg_GT; the spill window writable and the callee
       window byte-backed from the journal's presence conjunct; the cut's A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 for
       ro_agree / asan_cells and the run's one shadow premise, shadow_rw_on (PF.f17b_run_shadow_R ..), the callee's
       region at the call under its guard (the record opens): the source span sh_word_on (phi + 27) gg[26] lies in the
       record block's shadow-word cover (cut_shadow's (L) disjunct, phi live in ablocks with req_size >= 50 > 27 + 22),
       the destination span sh_word_on (fr + 2880) gg[26] in the owned class-6 frame's shadow ((F) disjunct), both by
       ShadowRwOn.shadow_rw_on_mono from the cut's cut_shadow part.
       Footprint RNG := ProgBridge.RNG_W (w_H W3); every rng premise from a Theorem Labs lane's proved visibility rows
       (ProgWorldVisWin.win_vis / win_sh_vis, ProgWorldVisFrame.frame_vis, ProgWorldVisHeap.heap_vis / heap_sh_vis,
       ProgBridge.img_vis_W) through ProgBridge.rng_of_visible.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from regs3 to mkR_of regs3.
   G4  lift: ProgBridge.fevt_of_evtF and YA0nR.SRr_fevt_hid (the run writes memory on the opening arm).
   G5  the continuation at 0x823e8 with the run's end map R: the write set W is [] on the eight arms that do not
       open the record, and [(fr+2880, fr+2880+gg[26]); (sp-2224, sp); (A+104, A+120)] on the one that does (the
       copy, the callee's scratch, the two stores; as F17.v :1747-1757).  Journal by ajournal_exec with Wr := ~
       outside W (awr_byte: the own class-6 frame, or the stack window [c_sp - LLVMF_STK, c_sp)); frames, frame
       law, k bound unchanged; every body fact kept by its distance from W (Lib.Frame.munch / RcAsanFPLib.fl_bytes,
       AsanRTFacts.addressable_kept through munch_meta, the spill keep below, FRAC through Kit.kit_frac_move);
       LT = IFS (S j): F17.v's own f17_idfg_keep / f17_fsj_false / f17_fsj_true / F18.rec_inv0_kept /
       F17.f17_rec_parse_kept, read on a ghost whose g_in is c_in cx (SlotInv's predicates and ACtlCutP's
       transcriptions of them agree by conversion); ctl_rt_C B ly3 S3 mem' at the same ly3 / S3 (the exit cut is
       applied at the entry's layout and state): asan_cells_kept, both shadow regions (cut_shadow, img_shadow) by
       ShadowRwOnT.shadow_rw_on_kept (meta_kept: W misses the shadow; wmono), and ro_agree from the run
       (RoAdapt.ro_agree_munch).

   SECTION HYPOTHESES.  The pattern's template over ACtl.v's Section Ctl names: Context {fx rc LS}, B, MT, XM_LIB,
   RLO, RHI, and LAWS (the core's AR law record, YCbq.v:207; ACtl.v:185's own Hypothesis LAWS).  No other open
   hypothesis: the run is Required, its callee contract is the proved asan_memcpy_holds_F_on.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here but the two
   bridge equations names a frame-route identifier (proof-internal uses only: the ghost of SlotInv, F17.v / F18.v
   lemmas, Contract via the run).  The run's two frame-route constants are bridged by one equation each to the
   core's names: f17bg_GT (Contract.GT = YImgTop.IMG_TOP) and f17bg_FB (SlotInv.FRAME_BYTES =
   ACtlCutP.FRAME_BYTES).  The six twin modules
   are Required by their full logical path and cited as lib.Reusable.<X> (core) or through the module alias CK
   (porter 04:24Z / 04:33Z).  Measured closure and frame-route blobs: commit message.

   BUILD STATE: type-check only, WITH WORKSPACE STAND-INS (gbuild.sh (internal path) on a build machine, FACTS ed6b6b7b0ab +
   PAU pau-libreac-v190; the planning core's port_core_refused_<hex> names patched to numerals in the workspace
   only; of the stand-in files this file's closure reaches lib/A/AE2k.v alone, through ACtlCut) - provisional. *)

From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six twin modules (core copy) by their full logical path (porter a Theorem Labs lane, 04:33Z). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YK04 Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes Regs6ss Mem Frame MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.AsanRTFacts A.MemNorm A.RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNormTr A.BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.SlotInv A.Prog.RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.asan_memcpy_c A.Prog.asan_memcpyF_on.
(* Route (C): the cut's runtime form, the region predicate and its transports, the call's region. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlRtC A.ShadowRwOn A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on A.Prog.asan_memcpy_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.bcmp_wrap_c A.Contract.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.Tac_f17b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F17 A.Prog.Seg.F18 A.Prog.Seg.F17bFs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcFrag Prog.RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
(* The core's YK11 (getr, fp_regs, fp_csr, seg_rom) under one short alias, by its full path. *)
Module CK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotInv.
Module FL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.

(* ---- Helpers over ACtlCutP's vocabulary (proof-internal). ---- *)

(* The run's two frame-route constants, each bridged to the core's name by ONE equation (pattern section 1 rule
   6): ctrl's image top Contract.GT (seg_F17b_run_F's premise `AC.GT <= fr`) and SlotInv's FRAME_BYTES (the frame
   size in its premises; the cut layer's own name is ACtlCutP.FRAME_BYTES). *)
Lemma f17bg_GT : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof. reflexivity. Qed.

Lemma f17bg_FB : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotInv.FRAME_BYTES = ACtlCutP.FRAME_BYTES.
Proof. reflexivity. Qed.

(* A spill word at the spill base A that register 9 holds (the spill's own base is A modulo 2^64, and the word's
   bounds put it in range). *)
Lemma f17bg_spill_q : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> 0 <= off ->
  A + off + 8 <= 2 ^ 64 -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HAr Hoff Htop.
  pose proof Hq as (H0 & H1 & _). rewrite MEM.length_le8 in H1. change (Z.of_nat 8) with 8 in H1.
  unfold ACtlCut.rgv in HA, HA'. rewrite HA in HA'.
  apply (f_equal (@bv_unsigned 64)) in HA'.
  rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'. change (bv_modulus 64) with (2 ^ 64) in HA'.
  rewrite (Z.mod_small A) in HA' by lia.
  assert (E : A' = A) by (Z.div_mod_to_equations; lia).
  subst A'. exact Hq.
Qed.

Lemma f17bg_q64_keep : forall (m m' : word -> option byte) (W : list (Z * Z)) (a v : Z),
  ACtlCutP.q64 m a v -> FRM.munch W m m' -> (forall x, a <= x < a + 8 -> FRM.outside W x) ->
  ACtlCutP.q64 m' a v.
Proof.
  intros m m' W a v H MU HW. unfold ACtlCutP.q64 in *.
  eapply FL.fl_bytes; [exact H | exact MU |]. rewrite MEM.length_le8. exact HW.
Qed.

Lemma f17bg_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z))
    (off v A : Z),
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 64 -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  CK.getr regs' 9 = CK.getr regs 9 -> FRM.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> FRM.outside W x) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A Hs HA HAr Hoff Htop E9 MU HW.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  exact (f17bg_q64_keep m m' W (A + off) v (f17bg_spill_q regs m off v A Hs HA HAr Hoff Htop) MU HW).
Qed.

(* A byte the write view sees, above the image, is a byte of the memory itself (no segment lies there). *)
Lemma f17bg_raw_of_wview : forall (m : word -> option byte) (a : Z), IB.IMG_HI <= a < 2 ^ 64 ->
  wview A.Img0.rsegs m (MEM.wa a) <> None -> m (MEM.wa a) <> None.
Proof.
  intros m a Ha H. unfold wview in H. destruct (m (MEM.wa a)) as [b|] eqn:E; [discriminate|].
  exfalso. apply H. destruct (find_segment A.Img0.rsegs (bv_unsigned (MEM.wa a)) 1) as [s|] eqn:F; [|reflexivity].
  exfalso. rewrite (MEM.wa_unsigned a ltac:(unfold IB.IMG_HI in Ha; lia)) in F.
  destruct (A.BzBridge.find_segment_below A.Img0.rsegs IB.IMG_HI a 1 s A.MemNormTr.rsegs_below_img F
              ltac:(lia)) as [L|L]; lia.
Qed.

(* A present byte (the journal's presence conjunct) is writable and readable in the memory itself. *)
Lemma f17bg_wview_of_some : forall (m : word -> option byte) (a : Z) (b : byte),
  m (Z_to_bv 64 a) = Some b -> wview A.Img0.rsegs m (MEM.wa a) <> None.
Proof. intros m a b H. unfold wview, MEM.wa. rewrite H. discriminate. Qed.

Lemma f17bg_mrd_of_some : forall (m : word -> option byte) (a : Z) (b : byte),
  m (Z_to_bv 64 a) = Some b -> MEM.mrd A.Img0.rsegs m (MEM.wa a) = Some b.
Proof. intros m a b H. unfold MEM.mrd, MEM.wa. rewrite H. reflexivity. Qed.

(* Route (C): what the guard of the run's region (F17bFs.PF.f17b_run_shadow_R: the record opens) gives the region
   proof: the frame is long (fg_fr's first test) and gg[26] = fg_n is 1 .. 22 (F18.f18_fr_fg_n). *)
Lemma f17bg_opens_facts : forall (L : Z) (G : list byte),
  SM.f_opens L G = true -> 50 <= L /\ 1 <= RF.bat G 26 <= 22.
Proof.
  intros L G H. unfold SM.f_opens in H. apply andb_prop in H as (H & _).
  split; [|exact (A.Prog.Seg.F18.f18_fr_fg_n _ _ H)].
  unfold RF.fg_fr in H. repeat (apply andb_prop in H as (H & _)). apply Z.leb_le in H. exact H.
Qed.

(* Route (C): a span sh_word_on s n (its aligned shadow words, rng_asan's sh_al8_lo / sh_al8_hi) inside a live block
   [p, p + rq) lies in that block's 8-aligned shadow-word cover, cut_shadow's (L) disjunct (ACtlRtC.v:29-31). *)
Lemma f17bg_sh_L : forall (p rq s n a : Z), p <= s -> s + n <= p + rq ->
  A.Prog.rng_asan.sh_al8_lo s <= a < A.Prog.rng_asan.sh_al8_hi s n ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= a < Reusable.YG0f.shadow_addr (p + rq - 1) / 8 * 8 + 8.
Proof.
  intros p rq s n a H1 H2 Ha.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, ART.shadow_addr, ART.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* Route (C): a span sh_word_on s n at least 56 bytes into a 4096-byte frame f and ending 96 bytes before its end lies
   in the frame's shadow [shadow_addr f, shadow_addr f + 4096 / 8), cut_shadow's (F) disjunct (ACtlRtC.v:26-28). *)
Lemma f17bg_sh_F : forall (f s n a : Z), f + 56 <= s -> s + n <= f + 4000 ->
  A.Prog.rng_asan.sh_al8_lo s <= a < A.Prog.rng_asan.sh_al8_hi s n ->
  Reusable.YG0f.shadow_addr f <= a < Reusable.YG0f.shadow_addr f + 4096 / 8.
Proof.
  intros f s n a H1 H2 Ha.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, ART.shadow_addr, ART.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* One FRAC conjunct at the run's end memory, for glue_seg_F17b's FRAC walk, dispatched on the conjunct's shape: a
   q64 cell is kept off the write set (Hq64k: its three disjointness side conditions by lia); the frame shadow
   (HshK) and the saved words (HsvK) likewise; any other conjunct (registers, arithmetic) is the entry's own.  The
   trailer word a Theorem Labs lane's batch appends to FRAC (`q64 m (fr + 4088) ..`, a Theorem Labs lane 05:53Z) is a q64 cell in the
   class-6 frame's tail [fr + 3136, fr + 4096), below alloc_ceiling and so below the callee window and the spill
   stores: the q64 case keeps it. *)
Ltac f17bg_frac_keep1 H Hq64k HshK HsvK :=
  lazymatch goal with
  | |- ACtlCutP.q64 _ _ _ => apply Hq64k; [lia .. | exact H]
  | |- exists _, _ =>
      let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hshl := fresh "Hshl" in
      destruct H as (sh & Hsh & Hshl); exists sh; exact (conj (HshK sh Hsh Hshl) Hshl)
  | |- context [ACtlCutP.saved_bytes _] => exact (HsvK H)
  | |- _ => exact H
  end.

Section GlueF17b.

(* ACtl.v's Section Ctl shape (ACtl.v:170-174, :183), restricted to what this stage uses (pattern section 2). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :287-288), verbatim for the names this stage uses. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A822a0_at := (ACtlCutP.C_A822a0_at B).
Local Notation C_A823e8_at := (ACtlCutP.C_A823e8_at B).

Lemma glue_seg_F17b : forall POST (j : nat), CF POST (ix_cut C_A823e8_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* the cut's runtime fact, route (C) form (ACtlRtC.ctl_rt_C): asan cells, the cut's own shadow regions, the image's
     shadow, ro_agree *)
  destruct Hrt as (Hcells & Hcut & Himg & Hroag).
  (* ---- G1: the entry cut at index [Z.of_nat j] (ix_cut; C_A822a0_at, ACtlCutP.v:2409-2449). ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A822a0_at] in Hb.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & R23 & R22 & H50a & HAx & R18 & H50b &
    S152 & S280 & HIFS3 & R20).
  destruct HAx as (A & R9 & Q232 & Q200 & Q136 & Q120 & Q176 & Happ & Hw240 & R24 & H50c & H8819).
  pose proof (eq_refl : ACtlCutP.FRAME_BYTES = 3136) as HFB.
  pose proof f17bg_FB as HFB'.
  pose proof (eq_refl : ACPY.ASAN_MEMCPY_K = 2224) as HKv.
  pose proof (eq_refl : ART.HIGHMEM_BEG = 0x10007fff8000) as HHMv.
  pose proof (eq_refl : ART.APPMEM_END = 0x800000000000) as HAEv.
  pose proof (eq_refl : A.ACfn.LLVMF_STK = 32768) as HSTKv.
  pose proof (eq_refl : IB.IMG_HI = 0x5fe000) as HIMGv.
  pose proof (eq_refl : A.Prog.bcmp_wrap_c.BCMP_WRAP_K = 4560) as HBKv.
  pose proof Reusable.YCbq.asan_consts as (Hceil & _).
  (* the spill base A *)
  assert (HA88 : ART.HIGHMEM_BEG <= A + 88) by exact (proj1 (Happ (A + 88) ltac:(lia))).
  assert (HA120 : A + 120 <= ART.APPMEM_END) by (pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia).
  assert (HAr : 0 <= A < 2 ^ 64) by lia.
  (* FRAC (ACtlCutP.v:980-994): sp, the frame's placement under A, the frame header and shadow, the saved words *)
  pose proof HFRAC as (A' & sp & HFC).
  pose proof HFC as (E2 & Hsp16 & EspZ & E4 & R8 & R9' & E3 & R19 & R26 & Hfr32 & HA32 & HAcsp &
    HspA & HfrA & HA416 & Hcsp4096 & HcspE & _).
  (* the journal: its AR, layout, stack anchor and the presence of the stack window *)
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hastk & F5 & HQT).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  pose proof Hastk as (_ & _ & Hceil_lo & Hlo_sp & Hsp_hi & H47 & _).
  assert (EA : A' = A).
  { unfold ACtlCut.rgv in R9, R9'. rewrite R9 in R9'.
    apply (f_equal (@bv_unsigned 64)) in R9'. rewrite !Z_to_bv_unsigned in R9'.
    unfold bv_wrap in R9'. change (bv_modulus 64) with (2 ^ 64) in R9'.
    rewrite (Z.mod_small A) in R9' by lia. rewrite Z.mod_small in R9' by lia. lia. }
  subst A'.
  (* the frame: fr is frame_addr ly3 6 (c_fpos cx), at or above GT = 0x5fe000, below alloc_ceiling *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 _ HAR Hin6) as (Hf4096 & Hfceil & Hfapp).
  rewrite Efr3 in Hf4096, Hfceil, Hfapp.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  pose proof HAR as (HM & _).
  destruct (Reusable.YG0s.frame_facts B ly3 S3 _ 6 (ACtlCut.c_fpos cx) HM Hin6)
    as (_ & Hpos & HFapp & _ & _ & Hfoff & _).
  assert (HGT : Reusable.YImgTop.IMG_TOP <= fr).
  { rewrite <- Efr3. unfold Reusable.YG0f.frame_addr. unfold Reusable.YG0f.in_app in HFapp.
    unfold Reusable.YG0f.kFakeFramesOff in Hfoff. lia. }
  assert (HGTr : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.GT <= fr) by (rewrite f17bg_GT; exact HGT).
  (* the stack: sp is above alloc_ceiling by more than the callee's window *)
  assert (Hsplo : lib.Reusable.YM05.alloc_ceiling + 28672 < sp) by lia.
  (* the record block (phi, flen) and the frame are live in AR *)
  assert (Hphi_in : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  (* every heap byte is below alloc_ceiling and apart from the frame *)
  assert (Hblk : forall p n x, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= x < p + Reusable.YG00.req_size n ->
            x < lib.Reusable.YM05.alloc_ceiling /\ (x < fr \/ fr + 4096 <= x)).
  { intros p n x Hpn Hx.
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR Hpn) as (_ & _ & Hpc & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 p n 6 _ HAR Hpn Hin6) as Hsep.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efr3 in Hsep.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep. lia. }
  (* ---- G2: the run's premises. ---- *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  assert (VIS : forall lo len, ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= lo -> lo + len <= ACtlCut.c_sp cx ->
            Lib.ExecF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | exact H1 | exact H2]. }
  pose proof (A.ProgWorldVisWin.win_sh_vis B) as WSV. unfold A.ProgWorld.win_sh_vis_stmt in WSV.
  pose proof (A.ProgWorldVisFrame.frame_vis B) as FV. unfold A.ProgWorld.frame_vis_stmt in FV.
  pose proof (A.ProgWorldVisHeap.heap_vis B) as HV. unfold A.ProgWorld.heap_vis_stmt in HV.
  pose proof (A.ProgWorldVisHeap.heap_sh_vis B) as HSV. unfold A.ProgWorld.heap_sh_vis_stmt in HSV.
  (* the spills and the callee's window *)
  assert (G232 : Lib.ExecF.rng RNG (A + 232) 8) by (apply VIS; lia).
  assert (G176 : Lib.ExecF.rng RNG (A + 176) 8) by (apply VIS; lia).
  assert (G200 : Lib.ExecF.rng RNG (A + 200) 8) by (apply VIS; lia).
  assert (G32 : Lib.ExecF.rng RNG (A + 32) 8) by (apply VIS; lia).
  assert (G88 : Lib.ExecF.rng RNG (A + 88) 32) by (apply VIS; lia).
  assert (GSTK : Lib.ExecF.rng RNG (sp - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K) by (apply VIS; lia).
  assert (GSSTK : A.Prog.rng_asan.sh_word_rng RNG (sp - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K).
  { destruct (WSV LAWS ly3 S3 W3 mem3 md3 (sp - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K HAR
                ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as [E|V];
      [left; exact E | right; apply A.ProgBridge.rng_of_visible; exact V]. }
  (* the frame object first.sroa.7, at its largest copy *)
  destruct (FV LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2880) 22 HAR Hin6
              ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia))
    as (VD & VSD).
  assert (GD : Lib.ExecF.rng RNG (fr + 2880) 22) by (apply A.ProgBridge.rng_of_visible; exact VD).
  assert (GSD : A.Prog.rng_asan.sh_word_rng RNG (fr + 2880) 22).
  { destruct (VSD ltac:(lia) ltac:(rewrite Efr3; Z.div_mod_to_equations; lia)
                ltac:(rewrite Efr3; change (Reusable.YG00.fs_frame_bytes 6) with 4096; Z.div_mod_to_equations; lia))
      as [E|V]; [left; exact E | right; apply A.ProgBridge.rng_of_visible; exact V]. }
  (* the image and the footprint's own shape *)
  assert (GIMG : Lib.ExecF.rng RNG IB.IMG_LO (IB.IMG_HI - IB.IMG_LO))
    by (apply A.ProgBridge.rng_of_visible; exact (A.ProgBridge.img_vis_W W3)).
  assert (GRB : Lib.RngBytes.rng_bytes RNG) by apply A.ProgBridge.rng_bytes_RNG_W.
  (* the record, on a long frame *)
  assert (GLONG : 50 <= ACtlCutP.flen cx jj ->
            Lib.ExecF.rng RNG phi 50 /\ A.Prog.rng_asan.sh_word_rng RNG phi 50).
  { intros HfL.
    assert (Hrq : 50 <= Reusable.YG00.req_size (ACtlCutP.flen cx jj))
      by (pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx jj) ltac:(lia)); lia).
    split.
    - apply A.ProgBridge.rng_of_visible.
      exact (HV LAWS ly3 S3 W3 mem3 md3 phi _ phi 50 HAR Hphi_in ltac:(lia) ltac:(lia)).
    - destruct (HSV LAWS ly3 S3 W3 mem3 md3 phi _ phi 50 HAR Hphi_in ltac:(lia) ltac:(lia) ltac:(lia)) as [E|V];
        [left; exact E | right; apply A.ProgBridge.rng_of_visible; exact V]. }
  (* the memory facts the run reads *)
  assert (Q32 : ACtlCutP.q64 mem3 (A + 32) (fr + 2880)).
  { destruct HFLSI as ((HPRO & _) & _).
    destruct HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P32).
    exact (f17bg_spill_q regs3 mem3 32 (fr + 2880) A P32 R9 HAr ltac:(lia) ltac:(lia)). }
  assert (Had35 : ART.addressable mem3 (fr + 2880) 35) by (destruct HIFS3 as (_ & _ & (_ & _ & _ & H & _)); exact H).
  assert (Hstkfr : FRM.stk A.Img0.rsegs mem3 fr (fr + ACtlCutP.FRAME_BYTES))
    by (destruct HFLSI as ((_ & _ & H & _) & _); exact H).
  assert (Hwr : MEM.wr_at A.Img0.rsegs mem3 (A + 88) 32).
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Hpres (A + 88 + i) ltac:(lia)) as (_ & b & Hb).
    exact (f17bg_wview_of_some mem3 (A + 88 + i) b Hb). }
  assert (HSTK : FRM.stk A.Img0.rsegs mem3 (sp - ACPY.ASAN_MEMCPY_K) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as (_ & b & Hb).
    split; [exact (f17bg_wview_of_some mem3 a b Hb) | exists b; exact (f17bg_mrd_of_some mem3 a b Hb)]. }
  assert (HLONG : 50 <= ACtlCutP.flen cx jj ->
     SM.t_sum_ok (ACtlCut.c_in cx) jj = (Prog.RcModel.blocksum (skipn 18 (SM.t_g (ACtlCut.c_in cx) jj)) =? 0) /\
     length (SM.t_g (ACtlCut.c_in cx) jj) = 50%nat /\
     MEM.bytes_at A.Img0.rsegs mem3 phi (SM.t_g (ACtlCut.c_in cx) jj) /\ ART.addressable mem3 phi 50 /\
     (phi + 50 <= fr \/ fr + SI.FRAME_BYTES <= phi) /\
     (phi + 50 <= sp - ACPY.ASAN_MEMCPY_K \/ sp <= phi)).
  { intros HfL.
    assert (Ebig : SM.t_big (ACtlCut.c_in cx) jj = true)
      by (unfold SM.t_big; apply Z.leb_le; unfold ACtlCutP.flen in HfL; exact HfL).
    destruct (H50a HfL) as (Haddr & _). destruct (H50b HfL) as (Hrbb & _ & _).
    destruct (H50c HfL) as (_ & Hsd & _).
    assert (Hrq : 50 <= Reusable.YG00.req_size (ACtlCutP.flen cx jj))
      by (pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx jj) ltac:(lia)); lia).
    split; [symmetry; exact (A.Prog.Seg.F17.f17_sumok_bs (ACtlCut.c_in cx) jj Ebig)|].
    split; [apply A.Prog.Seg.F18.f18_t_g_length|].
    split; [exact Hrbb|]. split; [exact Haddr|].
    split.
    { destruct (Z_le_gt_dec (phi + 50) fr) as [D1|D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (fr + SI.FRAME_BYTES) phi) as [D2|D2]; [right; exact D2|].
      exfalso. destruct (Hblk phi _ (Z.max phi fr) Hphi_in ltac:(lia)) as (_ & Hnf). lia. }
    rewrite EspZ in Hsd. lia. }
  (* route (C): the run's one shadow premise (PF.f17b_run_shadow_R: the call's region under its guard, the record
     opens) from the cut's cut_shadow part: the source span sh_word_on (phi + 27) gg[26] in the record block's
     shadow-word cover ((L): phi live in ablocks, req_size flen >= 50 > 27 + 22), the destination span
     sh_word_on (fr + 2880) gg[26] in the owned class-6 frame's shadow ((F): (6, c_fpos cx) in frames S3,
     frame_addr ly3 6 (c_fpos cx) = fr, 4096 / 8 shadow bytes) *)
  assert (HSWR : A.ShadowRwOn.shadow_rw_on
            (A.Prog.Seg.F17bFs.PF.f17b_run_shadow_R (ACtlCutP.flen cx jj) (SM.t_g (ACtlCut.c_in cx) jj) phi fr) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3) _ mem3); [|exact Hcut].
    intros a (Hop & Ha).
    destruct (f17bg_opens_facts _ _ Hop) as (HfL & Hng).
    destruct (H50a HfL) as (Haddr & _). pose proof Haddr as (Hp0 & _ & HpE & _).
    assert (Hrq : 50 <= Reusable.YG00.req_size (ACtlCutP.flen cx jj))
      by (pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx jj) ltac:(lia)); lia).
    assert (ITv : Reusable.YImgTop.IMG_TOP = 0x5fe000) by reflexivity.
    assert (ES : bv_unsigned (Z_to_bv 64 (phi + 27)) = phi + 27)
      by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
    assert (ED : bv_unsigned (Z_to_bv 64 (fr + 2880)) = fr + 2880)
      by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 (RF.bat (SM.t_g (ACtlCut.c_in cx) jj) 26))
                 = RF.bat (SM.t_g (ACtlCut.c_in cx) jj) 26)
      by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
    unfold A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Ha. rewrite ES, ED, EN in Ha.
    destruct Ha as [(_ & Ha) | (_ & Ha)].
    - right; left. exists phi, (ACtlCutP.flen cx jj). split; [exact Hphi_in|].
      exact (f17bg_sh_L phi (Reusable.YG00.req_size (ACtlCutP.flen cx jj)) (phi + 27)
               (RF.bat (SM.t_g (ACtlCut.c_in cx) jj) 26) a ltac:(lia) ltac:(lia) Ha).
    - left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
      rewrite Efr3. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
      exact (f17bg_sh_F fr (fr + 2880) (RF.bat (SM.t_g (ACtlCut.c_in cx) jj) 26) a ltac:(lia) ltac:(lia) Ha). }
  (* ---- G3 / G4: the walk moved to the run's canonical map, and the run lifted. ---- *)
  pose proof (A.Prog.Seg.F17bFs.PF.seg_F17b_run_F_on RNG A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on regs3
                CK.fp_regs CK.fp_csr mem3 A phi fr (ACtlCutP.flen cx jj) sp (sp - ACPY.ASAN_MEMCPY_K)
                (SM.t_g (ACtlCut.c_in cx) jj) (SM.t_sum_ok (ACtlCut.c_in cx) jj)
                E2 R9 R20 R23 R26 Happ Q232 Q176 Q200 Q32 HLONG Had35 Hstkfr HGTr HfrA HspA
                ltac:(left; lia) Hwr HSTK ltac:(lia) ltac:(lia)
                Hroag Hcells HSWR
                G232 G176 G200 G32 G88 GLONG GRB GIMG GSTK GSSTK GD GSD) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A822a0_at [Z.of_nat j])) with 0x822a0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 CK.fp_regs
           (Z_to_bv 64 0x822a0) CK.fp_csr None mem3 (CK.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* ---- G5: the continuation at 0x823e8 with the run's end map R. ---- *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & pc' & mem' & Ems & Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K21 & K23 & K24 & K22 & K18 &
    K25 & Hmem).
  subst ms' pc'.
  assert (Hhid' : forall x, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) by exact Hhid.
  clear Hhid.
  assert (K2c : CK.getr R 2 = CK.getr regs3 2) by exact K2.
  assert (K9c : CK.getr R 9 = CK.getr regs3 9) by exact K9.
  assert (ESP : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ in *; rewrite K2c; exact EspZ).
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A823e8_at [Z.of_nat j])) R mem' md') (POST cx)).
  (* the write set of the run, on every arm *)
  assert (COM : exists Wm : list (Z * Z),
     FRM.munch Wm mem3 mem' /\ FRM.wmono A.Img0.rsegs mem3 mem' /\ ARF.all_app Wm /\
     (forall x, ~ FRM.outside Wm x ->
        (fr + 2880 <= x < fr + 2902) \/ (sp - ACPY.ASAN_MEMCPY_K <= x < sp) \/ (A + 104 <= x < A + 120)) /\
     (forall x : word, ~ FRM.outside Wm (bv_unsigned x) -> mem' x <> None) /\
     FRM.disjoint_from Wm ART.RT_LO (ART.RT_HI - ART.RT_LO) /\
     FRM.stk A.Img0.rsegs mem' fr (fr + ACtlCutP.FRAME_BYTES) /\
     A.MemNorm.ro_agree A.Img0.rsegs mem' /\
     ACtlCutP.FSj cx fr (S jj) R mem').
  { destruct Hmem as [(-> & Hopf) | (Hopt & mc & MUc & WMc & ROc & STc & BSc & ->)].
    - (* the record does not open: memory unchanged, the first-fragment state is turn j's *)
      exists []. split; [apply FRM.munch_refl|]. split; [apply FRM.wmono_refl|]. split; [exact I|].
      split; [intros x Hx; exfalso; apply Hx; exact I|].
      split; [intros x Hx; exfalso; apply Hx; exact I|].
      split; [exact I|]. split; [exact Hstkfr|]. split; [exact Hroag|].
      destruct HIFS3 as (_ & _ & HFSj).
      set (GH := SI.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
      exact (A.Prog.Seg.F17.f17_fsj_regs GH fr (S jj) regs3 R mem3
               (A.Prog.Seg.F17.f17_fsj_false GH fr jj regs3 mem3 Hopf HFSj) K9).
    - (* the record opens: the copy into first.sroa.7, the callee's scratch, the two spill stores *)
      set (n := RF.bat (SM.t_g (ACtlCut.c_in cx) jj) 26) in *.
      assert (Hn26 : 1 <= n <= 22).
      { pose proof Hopt as Ho. unfold SM.f_opens in Ho. apply andb_prop in Ho as (Ho1 & _).
        exact (A.Prog.Seg.F18.f18_fr_fg_n _ _ Ho1). }
      assert (Hrbl : length (SM.t_g (ACtlCut.c_in cx) jj) = 50%nat) by apply A.Prog.Seg.F18.f18_t_g_length.
      assert (BSl : length (firstn (Z.to_nat n) (skipn 27 (SM.t_g (ACtlCut.c_in cx) jj))) = Z.to_nat n)
        by (rewrite length_firstn, length_skipn, Hrbl; lia).
      assert (MU2 : FRM.munch [(A + 104, A + 120)] mc
                      (write_to_mem (write_to_mem mc (MEM.wa (A + 104)) (MEM.le8 (Z_to_bv 64 1)))
                         (MEM.wa (A + 112)) (MEM.le8 (Z_to_bv 64 n)))).
      { apply FRM.munch_write; [ apply FRM.munch_write; [ apply FRM.munch_refl | | | ] | | | ];
          try (rewrite MEM.length_le8); try (cbn [FRM.inside]; left); lia. }
      assert (WM2 : FRM.wmono A.Img0.rsegs mc
                      (write_to_mem (write_to_mem mc (MEM.wa (A + 104)) (MEM.le8 (Z_to_bv 64 1)))
                         (MEM.wa (A + 112)) (MEM.le8 (Z_to_bv 64 n))))
        by (repeat apply FRM.wmono_write; apply FRM.wmono_refl).
      set (mem' := write_to_mem (write_to_mem mc (MEM.wa (A + 104)) (MEM.le8 (Z_to_bv 64 1)))
                     (MEM.wa (A + 112)) (MEM.le8 (Z_to_bv 64 n))) in *.
      assert (MU : FRM.munch [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp); (A + 104, A + 120)]
                     mem3 mem').
      { apply (FRM.munch_trans _ mem3 mc).
        - apply (FRM.munch_weaken [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp)]); [|exact MUc].
          intros x Hx. cbn [FRM.outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
          split; [exact H1|]. split; [exact H2 | exact I].
        - apply (FRM.munch_weaken [(A + 104, A + 120)]); [|exact MU2].
          intros x Hx. cbn [FRM.outside] in Hx |- *. destruct Hx as (_ & _ & H3 & _).
          split; [exact H3 | exact I]. }
      (* the frame stays byte-backed: the copy's bytes are readable, the stores are above it *)
      assert (HSTKc : FRM.stk A.Img0.rsegs mc fr (fr + ACtlCutP.FRAME_BYTES)).
      { apply (A.Prog.Seg.Tac_f17b.f17m_stk_keep _ mem3 mc fr (fr + ACtlCutP.FRAME_BYTES) Hstkfr MUc WMc).
        intros q Hq Hno. apply (A.Prog.Seg.F17.f17_ba_rd mc (fr + 2880) _ q BSc). rewrite BSl.
        cbn [FRM.outside] in Hno. lia. }
      assert (HSTKm : FRM.stk A.Img0.rsegs mem' fr (fr + ACtlCutP.FRAME_BYTES)).
      { apply (FRM.stk_transport A.Img0.rsegs [(A + 104, A + 120)] mc _ fr (fr + ACtlCutP.FRAME_BYTES) HSTKc MU2 WM2).
        intros x Hx. left. cbn [FRM.outside]. split; [lia | exact I]. }
      assert (HSTKs : FRM.stk A.Img0.rsegs mem' (sp - ACPY.ASAN_MEMCPY_K) sp).
      { apply (FRM.stk_transport A.Img0.rsegs [(A + 104, A + 120)] mc _ (sp - ACPY.ASAN_MEMCPY_K) sp STc MU2 WM2).
        intros x Hx. left. cbn [FRM.outside]. split; [lia | exact I]. }
      assert (WM : FRM.wmono A.Img0.rsegs mem3 mem') by exact (FRM.wmono_trans _ _ _ _ WMc WM2).
      assert (Hwr' : MEM.wr_at A.Img0.rsegs mem' (A + 88) 32) by exact (FRM.wr_at_transport _ _ _ _ _ Hwr WM).
      exists [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp); (A + 104, A + 120)].
      split; [exact MU|]. split; [exact WM|].
      split.
      { cbn [ARF.all_app]. split.
        { intros a Ha. pose proof Had35 as (_ & _ & _ & Hab). destruct (Hab (a - (fr + 2880)) ltac:(lia)) as (Hap & _).
          replace (fr + 2880 + (a - (fr + 2880))) with a in Hap by lia. exact Hap. }
        split; [intros a Ha; unfold ART.app_mem; right; lia|].
        split; [intros a Ha; unfold ART.app_mem; right; apply Happ; lia | exact I]. }
      split.
      { intros x Hx. destruct (A.Prog.Seg.F17.f17_in3 _ _ _ _ _ _ x Hx) as [Hw|[Hw|Hw]];
          [left | right; left | right; right]; lia. }
      split.
      { intros x Hx. pose proof (bv_unsigned_in_range _ x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
        assert (Ex : MEM.wa (bv_unsigned x) = x)
          by (unfold MEM.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
        rewrite <- Ex.
        destruct (A.Prog.Seg.F17.f17_in3 _ _ _ _ _ _ _ Hx) as [Hw|[Hw|Hw]];
          (apply f17bg_raw_of_wview; [lia|]).
        - exact (proj1 (proj2 (proj2 HSTKm) (bv_unsigned x) ltac:(lia))).
        - exact (proj1 (proj2 (proj2 HSTKs) (bv_unsigned x) ltac:(lia))).
        - pose proof Hwr' as (_ & _ & Hw').
          specialize (Hw' (bv_unsigned x - (A + 88)) ltac:(lia)).
          replace (A + 88 + (bv_unsigned x - (A + 88))) with (bv_unsigned x) in Hw' by lia. exact Hw'. }
      split.
      { cbn [FRM.disjoint_from]. unfold ART.RT_LO, ART.RT_HI. repeat split; lia. }
      split; [exact HSTKm|].
      split.
      { apply (A.RoAdapt.ro_agree_munch [(A + 104, A + 120)] mc mem' ROc MU2).
        intros x Hx. cbn [FRM.outside] in Hx.
        pose proof (bv_unsigned_in_range _ x) as Hxr. change (bv_modulus 64) with (2 ^ 64) in Hxr.
        assert (Ex : MEM.wa (bv_unsigned x) = x)
          by (unfold MEM.wa; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
        rewrite <- Ex. apply A.MemNormTr.ro_addr_above_img. lia. }
      (* the first-fragment state of turn S j: [A + 104] = 1, [A + 112] = gg[26], the copied body at fr + 2880 *)
      set (GH := SI.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
      apply (A.Prog.Seg.F17.f17_fsj_true GH fr jj R mem' Hopt).
      + exists A. split; [unfold SI.rg; rewrite K9; exact R9|]. apply A.Prog.Seg.F17.f17_q64_ba.
        apply A.Prog.Seg.F17.f17_w8_other; [apply A.Prog.Seg.F17.f17_w8_same | | | ]; lia.
      + exists A. split; [unfold SI.rg; rewrite K9; exact R9|]. apply A.Prog.Seg.F17.f17_q64_ba.
        apply A.Prog.Seg.F17.f17_w8_same; lia.
      + refine (FL.fl_bytes [(A + 104, A + 120)] mc mem' (fr + 2880) _ BSc MU2 _). rewrite BSl. intros x Hx.
        cbn [FRM.outside]. split; [lia | exact I].
      + refine (ARF.addressable_kept mem3 mem' (fr + 2880) 35 Had35 (ARF.munch_meta _ mem3 mem' MU _)).
        cbn [ARF.all_app]. split.
        { intros a Ha. pose proof Had35 as (_ & _ & _ & Hab).
          destruct (Hab (a - (fr + 2880)) ltac:(lia)) as (Hap & _).
          replace (fr + 2880 + (a - (fr + 2880))) with a in Hap by lia. exact Hap. }
        split; [intros a Ha; unfold ART.app_mem; right; lia|].
        split; [intros a Ha; unfold ART.app_mem; right; apply Happ; lia | exact I]. }
  destruct COM as (Wm & MU & WM & HAW & HWin & HSome & HDRT & HSTK' & HRO' & HFSj').
  assert (HWout : forall x, (x < fr + 2880 \/ fr + 2902 <= x) -> (x < sp - ACPY.ASAN_MEMCPY_K \/ sp <= x) ->
                    (x < A + 104 \/ A + 120 <= x) -> FRM.outside Wm x).
  { intros x H1 H2 H3. destruct (A.Prog.Seg.Tac_f17b.f17m_outside_dec Wm x) as [Ho|Ho]; [exact Ho|].
    exfalso. destruct (HWin x Ho) as [Hw|[Hw|Hw]]; lia. }
  assert (HWsh : forall x, ART.in_shadow x -> FRM.outside Wm x).
  { intros x Hx. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
    unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Hx.
    apply HWout; lia. }
  assert (MK : ARF.meta_kept mem3 mem') by exact (ARF.munch_meta Wm mem3 mem' MU HAW).
  assert (Hspk : forall off v, 0 <= off -> off + 8 <= 104 \/ 120 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R mem' off v).
  { intros off v H0 H1 H2 Hs.
    apply (f17bg_spill_keep regs3 R mem3 mem' Wm off v A Hs R9 HAr H0 ltac:(lia) K9c MU).
    intros x Hx. apply HWout; lia. }
  assert (Hq64k : forall a v, (a + 8 <= fr + 2880 \/ fr + 2902 <= a) -> (a + 8 <= sp - ACPY.ASAN_MEMCPY_K \/ sp <= a) ->
            (a + 8 <= A + 104 \/ A + 120 <= a) -> ACtlCutP.q64 mem3 a v -> ACtlCutP.q64 mem' a v).
  { intros a v H1 H2 H3 Hq. apply (f17bg_q64_keep mem3 mem' Wm a v Hq MU). intros x Hx. apply HWout; lia. }
  (* every byte of a live heap block is off W *)
  assert (Hblkout : forall p n x, In (p, n) (Reusable.YG0d.ablocks B ly3 S3) -> p <= x < p + Reusable.YG00.req_size n ->
            FRM.outside Wm x).
  { intros p n x Hpn Hx. destruct (Hblk p n x Hpn Hx) as (Hc & Hnf). apply HWout; lia. }
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem' md' HB).
  - (* the journal across the run (ajournal_exec, YCbq.v:636-643): W's bytes are the own frame's and the stack
       window's *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => ~ FRM.outside Wm a).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (A.Prog.Seg.Tac_f17b.f17m_outside_dec Wm (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); reflexivity | exfalso; exact (Hx Ho)].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
      destruct (A.Prog.Seg.Tac_f17b.f17m_outside_dec Wm (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx | exact (HSome x Ho)].
    + exact Hhid'.
    + exact Hsbm.
    + intros a Ha. destruct (HWin a Ha) as [Hw|[Hw|Hw]].
      * do 3 right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
        left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      * left. lia.
      * left. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body C_A823e8_at (ACtlCutP.v:2453-2490) at the same turn *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A823e8_at].
    split; [reflexivity|].
    fold jj.
    exists phi.
    split; [exact HP|].
    (* FRAC: its memory facts are off W, its registers kept by the run *)
    split.
    { (* FRAC at the end memory, walked conjunct by conjunct (f17bg_frac_keep1), so that a conjunct appended to
         FRAC later is kept by the same cases *)
      assert (HshK : forall sh, MEM.bytes_at segs mem3 (ACtlCutP.Sfr fr) sh ->
                length sh = Z.to_nat ACtlCutP.FRAME_SHADOW -> MEM.bytes_at segs mem' (ACtlCutP.Sfr fr) sh).
      { intros sh Hsh Hshl.
        eapply FL.fl_bytes; [exact Hsh | exact MU |]. intros x Hx. apply HWsh.
        unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in Hx. rewrite Hshl in Hx.
        unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hx.
        unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
        unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG.
        change (Z.of_nat (Z.to_nat (3136 / 8))) with 392 in Hx. Z.div_mod_to_equations. lia. }
      assert (HsvK : MEM.bytes_at segs mem3 (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx) ->
                MEM.bytes_at segs mem' (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
      { intros Hsv. eapply FL.fl_bytes; [exact Hsv | exact MU |].
        assert (Hsl : length (ACtlCutP.saved_bytes cx) = 104%nat)
          by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !MEM.length_le8; reflexivity).
        rewrite Hsl. intros x Hx. apply HWout; lia. }
      assert (HFRACm : ACtlCutP.FRAC B cx fr fr regs3 mem').
      { exists A, sp. pose proof HFC as HC.
        repeat lazymatch goal with
          | |- _ /\ _ =>
              let H1 := fresh "HC1" in destruct HC as [H1 HC]; split; [f17bg_frac_keep1 H1 Hq64k HshK HsvK|]
          end.
        f17bg_frac_keep1 HC Hq64k HshK HsvK. }
      exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem' HFRACm K2 K3 K4 K8 K9 K19 K26). }
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hpnz & Hadp). split; [exact Hpnz | exact (ARF.addressable_kept mem3 mem' _ _ Hadp MK)]. }
    (* FLSI *)
    split.
    { destruct HFLSI as ((HPRO & S128 & HstkF & S144 & Had2691) & S216 & S224 & S248 & (Hadin & Hbin) & HFLC).
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Had2624 & Hbin' & Hadin' & P184 &
        P256 & P264 & P272 & P32).
      destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Hadfg & Had2688 & C72 & C64 & C56 & C48).
      (* the input block (c_p, c_n) is a live heap block of the entry when it is not empty *)
      assert (HinOut : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                FRM.outside Wm x).
      { intros x Hx. destruct HB as (Hpre & _).
        destruct Hpre as (_ & _ & _ & _ & Hpn & Hnlen & _).
        destruct Hpn as [(Hn0 & _) | (Hnpos & Hpin)]; [lia|].
        assert (Hpin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
        { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hpin. }
        apply (Hblkout _ _ x Hpin3).
        pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)). lia. }
      assert (Hf1 : ACtlCutP.f1_IN cx mem').
      { split; [exact (ARF.addressable_kept mem3 mem' _ _ Hadin MK)|].
        eapply FL.fl_bytes; [exact Hbin | exact MU | exact HinOut]. }
      split.
      { split.
        { split; [apply Hspk; [lia .. | exact P40]|].
          split; [apply Hspk; [lia .. | exact P120]|].
          split; [apply Hspk; [lia .. | exact P136]|].
          split; [apply Hspk; [lia .. | exact P160]|].
          split; [apply Hspk; [lia .. | exact P168]|].
          split; [apply Hspk; [lia .. | exact P176]|].
          split; [apply Hspk; [lia .. | exact P208]|].
          split; [apply Hspk; [lia .. | exact P248]|].
          split; [exact (ARF.addressable_kept mem3 mem' _ _ Had2624 MK)|].
          split; [eapply FL.fl_bytes; [exact Hbin' | exact MU | exact HinOut]|].
          split; [intros Hc; exact (ARF.addressable_kept mem3 mem' _ _ (Hadin' Hc) MK)|].
          split; [apply Hspk; [lia .. | exact P184]|].
          split; [apply Hspk; [lia .. | exact P256]|].
          split; [apply Hspk; [lia .. | exact P264]|].
          split; [apply Hspk; [lia .. | exact P272]|].
          apply Hspk; [lia .. | exact P32]. }
        split; [apply Hspk; [lia .. | exact S128]|].
        split; [exact HSTK'|].
        split; [apply Hspk; [lia .. | exact S144]|].
        exact (ARF.addressable_kept mem3 mem' _ _ Had2691 MK). }
      split; [apply Hspk; [lia .. | exact S216]|].
      split; [apply Hspk; [lia .. | exact S224]|].
      split; [apply Hspk; [lia .. | exact S248]|].
      split; [exact Hf1|].
      split; [apply Hspk; [lia .. | exact C256]|].
      split; [apply Hspk; [lia .. | exact C184]|].
      split; [apply Hspk; [lia .. | exact C192]|].
      split; [apply Hspk; [lia .. | exact C80]|].
      split; [apply Hspk; [lia .. | exact C88]|].
      split; [apply Hspk; [lia .. | exact C96]|].
      split; [apply Hspk; [lia .. | exact C272]|].
      split; [apply Hspk; [lia .. | exact C264]|].
      split; [exact (ARF.addressable_kept mem3 mem' _ _ Hadfg MK)|].
      split; [exact (ARF.addressable_kept mem3 mem' _ _ Had2688 MK)|].
      split; [apply Hspk; [lia .. | exact C72]|].
      split; [apply Hspk; [lia .. | exact C64]|].
      split; [apply Hspk; [lia .. | exact C56]|].
      apply Hspk; [lia .. | exact C48]. }
    (* LK *)
    split.
    { destruct HLK as (HLj & HL21 & HLour). split; [exact HLj|]. split; [exact (eq_trans K21 HL21)|].
      unfold ACtlCutP.OURb in *. eapply FL.fl_bytes; [exact HLour | exact MU |]. rewrite SM.OUR_length.
      intros x Hx. apply HWout; lia. }
    (* the spill / record / compare conjunct *)
    split.
    { destruct Hw240 as (w240 & Q240 & Hw240r & Hw240t & Hw240f).
      exists A, w240.
      split; [exact (eq_trans K9 R9)|]. split; [exact HAr|]. split; [rewrite ESP; exact HspA|].
      split; [exact (eq_trans K23 R23)|]. split; [exact (eq_trans K24 R24)|]. split; [exact (eq_trans K22 R22)|].
      set (GH := SI.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
      assert (Hblk50 : 50 <= ACtlCutP.flen cx jj -> forall x, phi <= x < phi + 50 -> FRM.outside Wm x).
      { intros HfL x Hx. apply (Hblkout _ _ x Hphi_in).
        pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx jj) ltac:(lia)). lia. }
      split.
      { intros HfL. destruct (H50c HfL) as (HRI & _ & _).
        exact (A.Prog.Seg.F18.rec_inv0_kept GH jj fr phi A mem3 mem' Wm HRI MU (Hblk50 HfL)
                 ltac:(intros x Hx; apply HWout; lia)). }
      split; [apply Hq64k; [lia .. | exact Q136]|].
      split; [apply Hq64k; [lia .. | exact Q120]|].
      split; [apply Hq64k; [lia .. | exact Q176]|].
      split; [apply Hq64k; [lia .. | exact Q240]|].
      split; [exact Hw240r|]. split; [exact Hw240f|].
      intros E8819.
      assert (HfL : 50 <= ACtlCutP.flen cx jj).
      { pose proof E8819 as E0. unfold SM.t_8819, SM.t_big in E0. apply andb_prop in E0 as [E1 _].
        apply andb_prop in E1 as [E1' _]. apply Z.leb_le in E1'. unfold ACtlCutP.flen. exact E1'. }
      destruct (H50a HfL) as (Haddr & _).
      destruct (H50c HfL) as (HRI0 & Hphiw & _).
      destruct (H8819 E8819) as (HRP & (ls & rs & HLq & HLb & HLl & HRb & HRl & HLm & HLad) &
        (ls2 & rs2 & HL2q & HL2b & HL2l & HR2b & HR2l & HL2m & HL2ad)).
      destruct (A.Prog.Seg.F18.ba_first6 mem3 (fr + 186) ls HLb HLl) as (HLb6 & HLl6).
      destruct (A.Prog.Seg.F18.ba_first6 mem3 phi rs HRb HRl) as (HRb6 & HRl6).
      destruct (A.Prog.Seg.F18.ba_first6 mem3 (fr + 180) ls2 HL2b HL2l) as (HL2b6 & HL2l6).
      destruct (A.Prog.Seg.F18.ba_first6 mem3 (phi + 6) rs2 HR2b HR2l) as (HR2b6 & HR2l6).
      split; [exact (Hw240t E8819)|].
      split.
      { destruct HRI0 as (_ & _ & _ & _ & Hpap & _).
        exact (A.Prog.Seg.F17.f17_rec_parse_kept GH jj fr phi mem3 mem' Wm HRP Hpap MU (Hblk50 HfL) HWsh
                 ltac:(intros x Hx; apply HWout; lia)). }
      exists (firstn 6 ls), (firstn 6 rs), (firstn 6 ls2), (firstn 6 rs2).
      split; [apply Hq64k; [lia .. | exact HLq]|].
      split; [eapply FL.fl_bytes; [exact HLb6 | exact MU |]; rewrite HLl6; intros x Hx; apply HWout; lia|].
      split; [rewrite HLl6; lia|].
      split; [eapply FL.fl_bytes; [exact HRb6 | exact MU |]; rewrite HRl6; intros x Hx; apply (Hblk50 HfL); lia|].
      split; [rewrite HRl6; lia|].
      split; [rewrite A.Prog.Seg.F18.memcmp_firstn; exact HLm|].
      split; [exact (ARF.addressable_kept mem3 mem' (fr + 186) 6 HLad MK)|].
      split.
      { pose proof (ARF.addressable_sub mem3 phi 50 0 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) as Had6.
        rewrite Z.add_0_r in Had6. exact (ARF.addressable_kept mem3 mem' phi 6 Had6 MK). }
      split; [rewrite ESP; rewrite EspZ in Hphiw; exact Hphiw|].
      split; [apply Hq64k; [lia .. | exact HL2q]|].
      split; [eapply FL.fl_bytes; [exact HL2b6 | exact MU |]; rewrite HL2l6; intros x Hx; apply HWout; lia|].
      split; [rewrite HL2l6; lia|].
      split; [eapply FL.fl_bytes; [exact HR2b6 | exact MU |]; rewrite HR2l6; intros x Hx; apply (Hblk50 HfL); lia|].
      split; [rewrite HR2l6; lia|].
      split; [rewrite A.Prog.Seg.F18.memcmp_firstn; exact HL2m|].
      split; [exact (ARF.addressable_kept mem3 mem' (fr + 180) 6 HL2ad MK)|].
      exact (ARF.addressable_kept mem3 mem' (phi + 6) 6
               (ARF.addressable_sub mem3 phi 50 6 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) MK). }
    split; [exact (eq_trans K18 R18)|].
    split; [exact K25|].
    split.
    { intros HfL. destruct (H50b HfL) as (Hbg & Hbp & Hlp).
      assert (Hrq : ACtlCutP.flen cx jj <= Reusable.YG00.req_size (ACtlCutP.flen cx jj))
        by (pose proof (Reusable.YCbq.req_size_pos (ACtlCutP.flen cx jj) ltac:(lia)); lia).
      split; [eapply FL.fl_bytes; [exact Hbg | exact MU |]; rewrite A.Prog.Seg.F18.f18_t_g_length;
              intros x Hx; apply (Hblkout _ _ x Hphi_in); lia|].
      split; [eapply FL.fl_bytes; [exact Hbp | exact MU |]; intros x Hx; apply (Hblkout _ _ x Hphi_in); lia
             | exact Hlp]. }
    split; [apply Hspk; [lia | right; lia | lia | exact S152]|].
    split; [apply Hspk; [lia | right; lia | lia | exact S280]|].
    (* LT = IFS (S j): the two frame records are off W, the first-fragment state is COM's *)
    destruct HIFS3 as (HID & HFG & _).
    set (GH := SI.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
    destruct (A.Prog.Seg.F17.f17_idfg_keep GH fr jj mem3 mem' Wm HID HFG MU
                ltac:(intros x Hx; apply HWout; lia)) as (HID' & HFG').
    split; [exact HID'|]. split; [exact HFG'|]. exact HFSj'.
  - (* ctl_rt_C B ly3 S3 mem': the exit cut is at the entry's ly3 / S3, so the regions are the entry's: the runtime
       cells are off W (asan_cells_kept), the two shadow regions are kept by ShadowRwOnT.shadow_rw_on_kept (meta_kept
       MK: W misses the shadow; wmono WM), ro_agree from the run *)
    split; [exact (ARF.asan_cells_kept Wm mem3 mem' Hcells MU HDRT)|].
    split; [exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 mem' Hcut MK WM)|].
    split; [exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 mem' Himg MK WM) | exact HRO'].
Qed.

End GlueF17b.
