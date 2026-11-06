(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module names changed; 426 of its 465 lines of code are new or changed and 927 lines of the source are left out. *)
(* lib/A/ACtlG/R8.v -- GLUE for stage seg_R8 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:678).
   Written by a Theorem Labs lane (piece W2a); single writer.  rule 24: no function proved (stage glue
   of a walk; proves no function, kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R8 : forall POST (b : nat), CF POST (ix_cut C_A81658_at [Z.of_nat b]) -> CF POST (ix_cut C_A81640_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R8.  Segment R8 is 0x81640 -> 0x81658 (Seg/R8.v:1-21): bnez a0 (the malloc result phi <> 0), mv s8,a0,
   ld a1,128(s1) (the source pointer fr + 544), mv a2,s2 (the count n_b), and the call of checked_memcpy at 0x81654,
   which copies the n_b bytes rt_F of the frame's out[] into the fresh block [phi, phi + n_b).

   THE RUN.  Route (C): Seg/R8F_on.v r8_evt_F_on (this lane's twin of a Theorem Labs lane's Seg/R8F.v (not in this delivery) r8_evt_F, consent
   12:55Z; Required qualified): R8.r8_evt under a footprint RNG, with the callee's footprint contract
   asan_memcpy_contract_F_on as a premise, the shadow premise narrowed to r8_evt_shadow_R (memcpy's region at the
   call) and the post's shadow conjunct `forall P, shadow_rw_on P mem3 -> shadow_rw_on P m'`.  NO SPLIT (ruling 2,
   04:01Z): memcpy's _F_on is PROVED, so the premise is DISCHARGED by a Theorem Labs lane's
   A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on and the whole run is lifted once.

   THE PROOF (glue-pattern.md section 3, a run that writes memory)
   G1  the entry cut at index [Z.of_nat b]: ix_cut's index equation, C_A81640_at's body (ACtlCutP.v:1325-1347).
   G2  r8_evt_F's premises: the registers from FRAC / the body (sp, s1 = A, a0 = phi, s2 = n_b); n_b in
       [124, 1492] and length rt_F = n_b (Seg/R8.v r8_rtn); the block (phi, n_b) is a live block of the journal's
       AR (the body's Permutation), so AR_blocks_law gives its placement, presence (hence rw_cells), pairwise
       separation, and AR_client_img_law puts it off the image (hence no read-only byte and apart from
       [RT_LO, RT_HI)); the frame's bytes / bounds from AR_frames_law + the frame law (KitMem own6); the
       callee window [sp - 2224, sp) lies in the journal's present stack window [c_sp - LLVMF_STK, c_sp) (FRAC:
       c_sp - 4096 < sp <= A <= c_sp); asan_cells / ro_agree from ctl_rt_C, and the run's shadow region (the aligned
       shadow words of the source [fr + 544, + n_b) and of the block) from ctl_rt_C's cut_shadow: the source's from the
       owned class-6 frame's (F) disjunct (r8g_src_shadow), the block's from the live-block (L) disjunct
       (r8g_blk_shadow).  Every rng premise at
       RNG := ProgBridge.RNG_W (w_H W3): the spill [A + 128, + 8) and the callee window by ProgWorldVisWin.win_vis,
       the image by ProgBridge.img_vis_W, the block by ProgWorldVisHeap.heap_vis, the source bytes by
       ProgWorldVisFrame.frame_vis; the three shadow word spans by heap_sh_vis, frame_vis (64-byte hull inside the
       4096-byte frame) and win_sh_vis; rng_bytes by ProgBridge.rng_bytes_RNG_W.
   G3  cfg_at_MS, then the walk moved from regs3 to the run's canonical map (YA0nR.SRr_xregs_eqv).
   G4  the lift: ProgBridge.fevt_of_evtF, then YA0nR.SRr_fsteps (its continuation keeps the fsteps run, which
       ProgWorld.ajournal_of_fsteps takes).
   G5  the exit cut at the run's end map R and memory m' (munch [(phi, phi + n_b); (sp - 2224, sp)] mem3 m'):
         journal  ProgWorld.ajournal_of_fsteps (PROVED, a Theorem Labs lane's ProgWorld head 26edf006f53 on this branch),
                  every written byte awr_byte: the callee window by the stack case (it lies in
                  [c_sp - LLVMF_STK, c_sp)), the block by in_tmp_block (phi, n_b) is in the cut's ablocks and NOT an
                  entry block: the Permutation would list it twice, against AR_blocks_law's pairwise separation;
         body     every memory conjunct off the write set: the frame [fr, fr + 4096) (sep_block_frame, and below
                  alloc_ceiling <= c_sp - LLVMF_STK < sp - 2224), the save area [A, A + 416) (at or above sp), the
                  shadow (the write set is application memory), the input block (an entry block: separated from
                  (phi, n_b) as above, and below alloc_ceiling); the copied bytes at phi = rt_F and the source kept
                  from the run's post; registers through the run's kept registers; FRAC RE-ESTABLISHED at m' (the
                  one place this file rebuilds FRAC) by KitMem frac_munch, which moves FRAC by shape, including the
                  announced trailer word q64 (fr + 4088) (a Theorem Labs lane 05:3xZ): every range it reads off FRAC lies in
                  the class-6 frame [fr, fr + 4096), at or above sp, or in the frame's shadow, all outside the write
                  set; then Kit.kit_frac_move for the registers;
         ctl_rt_C asan_cells m' and ro_agree m' from the run's post; the regions cut_shadow B ly3 S3 and img_shadow
                  carried across the run by its forall-P post (the exit keeps ly3 S3).

   SECTION HYPOTHESES (exact text below)
   - LAWS: the core's AR law record (YCbq.v:207), as A5.v.  ACtl.v has it (ACtl.v:183).
   No other.  The seven shared memory helpers are the PROVED lemmas of lib/A/ACtlG/KitMem.v (a Theorem Labs lane, on this
   branch by path from a working branch 4a56e997c0f, blob 19bfb2e48a9), cited by name:
   kitmem_in_img, kitmem_ro_img, kitmem_own6, kitmem_stk_of_present, kitmem_addr_munch, kitmem_spill_munch,
   kitmem_frac_munch.
   CITED BY NAME (proved on this branch): Seg/R8F_on.r8_evt_F_on, asan_memcpyF_on.asan_memcpy_holds_F_on,
   ShadowRwOn.shadow_rw_on_mono, Seg/R8.v's
   r8_rtn / r8_rec_len / r8_ro8 / r8_rw_CB / r8_wr_stk / r8_rwcb_keep (outside its Section), RcAsanFPLib.fl_bytes,
   AsanRTFacts.addressable_sub / app_not_shadow, YA0nR.SRr_fsteps / SRr_xregs_eqv, ProgBridge, ProgWorldVis*,
   ProgWorld.ajournal_of_fsteps, YCbq.frames_bounds / sep_block_frame, YG0d.al_blocks / al_client_img, Kit, KitMem.
   READS NO PLANNING-CORE VALUE that differs from the record (ts_zsh / am_const / owned_static / const_shadow /
   TFIB_GP / pc_wrap_* / pc_stack_malloc / AB01): gp passes through FRAC symbolically; every shadow fact comes from
   the block, frame or stack-zero-shadow laws of AR.
   NOT USED: the frame-route RT conjuncts (segment-F-premises-A.tsv R8 row "frame_route AsanRTInv.RT"): the runtime
   facts the run needs come from the cut's ctl_rt_C.

   CLOSURE: every project Require is qualified (no Import / Export); the six twin modules (YI04 YI16 YK11 YK1b YM05
   YO09) and lib/Lib are named absolutely (ruling 1).  No statement here names a frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only through the absolute core YK11 alias CK11 / Reusable.YG0d.

   BUILD STATE: see the commit message and the lane's build of record (route (C), on a working branch, no workspace
   substitution).  Print Assumptions glue_seg_R8 (below): Rocq primitives (PrimInt63 / PrimString / PrimArray) and
   functional_extensionality_dep only.  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memcpy_c A.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R8 A.Prog.Seg.R8F_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SR8 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R8.
Module SR8Fo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R8F_on.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it; ctrl's runs' list (= segs by reflexivity,
   ProgBridge.tfibsegs_rsegs). *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local list facts (proof-internal, no memory vocabulary). *)

(* pairwise separation of block extents is kept by a permutation (zdisjoint is symmetric) *)
Lemma r8g_pairwise_perm : forall l l' : list (Z * Z),
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint l -> Permutation l l' ->
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint l'.
Proof.
  intros l l' Hp HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2].
  - exact I.
  - destruct Hp as [Hf Hp]. split; [|exact (IH Hp)].
    apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hf).
    exact (Permutation_in _ (Permutation_sym HP) Hz).
  - destruct Hp as [Hfy [Hfx Hp]]. inversion Hfy as [|u v Hyx Hyl]; subst.
    split; [constructor; [unfold Reusable.YG0f.zdisjoint in *; lia | exact Hfx] | split; [exact Hyl | exact Hp]].
  - exact (IH2 (IH1 Hp)).
Qed.

(* a list whose extents are pairwise separated, listed as e1 ++ y :: e2 ++ [x] up to permutation, separates y
   from x *)
Lemma r8g_perm_sep : forall (l e1 e2 : list (Z * Z)) (y x : Z * Z),
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint (map (fun b => (fst b, Reusable.YG00.req_size (snd b))) l) ->
  Permutation l ((e1 ++ y :: e2) ++ [x]) ->
  Reusable.YG0f.zdisjoint (fst y, Reusable.YG00.req_size (snd y)) (fst x, Reusable.YG00.req_size (snd x)).
Proof.
  intros l e1 e2 y x Hp HP.
  pose proof (r8g_pairwise_perm _ _ Hp (Permutation_map (fun b => (fst b, Reusable.YG00.req_size (snd b))) HP))
    as H.
  rewrite map_app, map_app in H. cbn [map] in H. rewrite <- app_assoc in H. cbn [app] in H.
  exact (Reusable.YCbq.pairwise_In2 Reusable.YG0f.zdisjoint _ _ _ _ _ [] H eq_refl).
Qed.

(* a spill whose base register 9 holds A reads its word at A + off *)
Lemma r8g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  A.ACtlCutP.spill regs m off v -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  A.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A1 & HA1 & Hq) HA H0 Hoff Hhi.
  assert (EA : A1 = A).
  { unfold A.ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* Route (C): the run's shadow region (SR8Fo.r8_evt_shadow_R) inside the cut's own shadow.  The source span
   [fr + 544, + n) of the owned class-6 frame: its aligned shadow words lie in the frame's shadow, cut_shadow's (F). *)
Lemma r8g_src_shadow : forall fr n a, 0 <= fr -> 0 < n <= 1492 ->
  A.Prog.sh_word_on.sh_word_on (fr + 544) n a ->
  Reusable.YG0f.shadow_addr fr <= a < Reusable.YG0f.shadow_addr fr + 4096 / 8.
Proof.
  intros fr n a Hfr Hn (_ & Ha). unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The block's span [p, p + n): the same aligned shadow-word cover as cut_shadow's (L) disjunct. *)
Lemma r8g_blk_shadow : forall p n a, A.Prog.sh_word_on.sh_word_on p n a ->
  Reusable.YG0f.shadow_addr p / 8 * 8 <= a < Reusable.YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8.
Proof.
  intros p n a (_ & Ha). unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueR8.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :235-236), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81640_at := (ACtlCutP.C_A81640_at B).
Local Notation C_A81658_at := (ACtlCutP.C_A81658_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R8 : forall POST (b : nat), CF POST (ix_cut C_A81658_at [Z.of_nat b]) -> CF POST (ix_cut C_A81640_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A81640_at, ACtlCutP.v:1325-1347). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81640_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & (Hcn & Hb6 & Hnz & Ha0 & HHB & R18 & S128 & HADs & Hsrcx & R23 & HOUR &
    HOUTA & HCUR & S112 & HPRO & S104 & S96 & S64 & S144 & S192 & RW38 & RW72 & S280 & S240 & RW1 & RW32 & S152 &
    R21 & HAD38) & (HID & HFG & HF544 & HRXS)).
  pose proof HFRAC as (A & sp & R2 & Hs16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  destruct Hrt as (HAC & Hcut & HimgS & HRO).
  (* G2: the numbers.  n_b in [124, 1492], rt_F has n_b bytes, the turn-b records have 38 / 72 bytes. *)
  destruct (SR8.r8_rtn (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & HNr & HLF).
  change (SM.rt_n (ACtlCut.c_in cx) (Z.of_nat b)) with (ACtlCutP.rnb cx b) in HNr, HLF.
  destruct (SR8.r8_rec_len (ACtlCut.c_in cx) b Hb6) as (HLID & HLFG).
  assert (HreqN : Reusable.YG00.req_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b)
    by (unfold Reusable.YG00.req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
  assert (HaN : A.ACtlK.a_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b) by (unfold A.ACtlK.a_size; lia).
  assert (HK : MCC.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hceil0 Hceil1] _].
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* the journal: AR, the layout, the stack window's presence and bounds *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hstklo & Hstk0 & Hstkhi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ely_lo & Ely_hi & _).
  (* the owned frame *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr6 & Hfr4096 & Hfr32 & Hfrceil & Hceilsp).
  rewrite HFB in Hfrceil. rewrite HSTKv in Hceilsp, Hstk0, Hpres.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Happfr).
  rewrite Efr6, HFB in Happfr.
  assert (Happ_fr : forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x).
  { intros x Hx. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happfr.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  (* the fresh block (phi, n_b): a live block of the cut's AR, not an entry block *)
  assert (Hin_blk : In (phi, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) HAR Hin_blk)
    as (_ & Hphi4096 & Hphiceil & Happ_in & Hpres_blk & Hpw & _).
  rewrite HreqN in Hphiceil, Happ_in, Hpres_blk.
  assert (Happ_blk : forall x, phi <= x < phi + ACtlCutP.rnb cx b -> A.AsanRT.app_mem x).
  { intros x Hx. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happ_in.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (Hblk_img : forall x, phi <= x < phi + ACtlCutP.rnb cx b -> ~ Reusable.YG0d.in_img segs x).
  { intros x Hx. refine (proj2 (Reusable.YG0d.al_client_img segs B LAWS ly3 S3 W3 mem3 md3 x HAR _)).
    left. exists phi, (ACtlCutP.rnb cx b). rewrite HreqN. split; [exact Hin_blk | exact Hx]. }
  assert (Hnew : ~ In (phi, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx))).
  { intros Hin. destruct (in_split _ _ Hin) as (e1 & e2 & Ee). rewrite Ee in HP.
    pose proof (r8g_perm_sep _ e1 e2 _ _ Hpw HP) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqN in Hd. lia. }
  (* the block is apart from the frame *)
  pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) 6
                (ACtlCut.c_fpos cx) HAR Hin_blk Hin6) as Hsepf.
  unfold Reusable.YG0f.zdisjoint in Hsepf. cbn [fst snd] in Hsepf. rewrite HreqN, Efr6, HFB in Hsepf.
  (* the input block: an entry block (the core's pre), so apart from the fresh block *)
  pose proof Hbase as ((_ & _ & _ & _ & Hpn & Hlenin & _) & _).
  assert (Hinp : 0 < ACtlCut.c_n cx -> ACtlCut.c_p cx + ACtlCut.c_n cx <= phi \/
                   phi + ACtlCutP.rnb cx b <= ACtlCut.c_p cx).
  { intros Hn0. destruct Hpn as [(Hn & _) | (_ & Hinp)]; [lia|].
    destruct (in_split _ _ Hinp) as (e1 & e2 & Ee). rewrite Ee in HP.
    pose proof (r8g_perm_sep _ e1 e2 _ _ Hpw HP) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    assert (Hrq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
      by (unfold Reusable.YG00.req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
    rewrite HreqN, Hrq in Hd. lia. }
  assert (Hinp_ceil : 0 < ACtlCut.c_n cx -> ACtlCut.c_p cx + ACtlCut.c_n cx <= CM05.alloc_ceiling).
  { intros Hn0. destruct Hpn as [(Hn & _) | (_ & Hinp0)]; [lia|].
    assert (Hin' : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinp0. }
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin') as (_ & _ & Hc & _).
    assert (Hrq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx)
      by (unfold Reusable.YG00.req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
    rewrite Hrq in Hc. exact Hc. }
  (* the write set of the run and what lies outside it *)
  set (WR := [(phi, phi + ACtlCutP.rnb cx b); (sp - MCC.ASAN_MEMCPY_K, sp)]).
  assert (Hout : forall x, ~ (phi <= x < phi + ACtlCutP.rnb cx b) -> ~ (sp - MCC.ASAN_MEMCPY_K <= x < sp) ->
            LFrame.outside WR x).
  { intros x H1 H2. cbn [LFrame.outside WR]. split; [exact H1 | split; [exact H2 | exact I]]. }
  assert (Hnapp_out : forall x, ~ A.AsanRT.app_mem x -> LFrame.outside WR x).
  { intros x Hx. apply Hout.
    - intros Hin. exact (Hx (Happ_blk x Hin)).
    - intros Hin. apply Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. right. lia. }
  assert (Hsh_out : forall x, A.AsanRT.in_shadow x -> LFrame.outside WR x).
  { intros x Hx. apply Hnapp_out. intros Ha. exact (A.AsanRTFacts.app_not_shadow x Ha Hx). }
  assert (Hfrout : forall x, fr <= x < fr + 4096 -> LFrame.outside WR x).
  { intros x Hx. apply Hout; lia. }
  assert (HAout : forall x, A <= x < A + 416 -> LFrame.outside WR x).
  { intros x Hx. apply Hout; lia. }
  assert (Hspout : forall x, sp <= x -> LFrame.outside WR x).
  { intros x Hx. apply Hout; lia. }
  assert (Hinout : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
            LFrame.outside WR x).
  { intros x Hx. rewrite <- Hlenin in Hx. specialize (Hinp ltac:(lia)). specialize (Hinp_ceil ltac:(lia)).
    apply Hout; lia. }
  (* G2: the run's premises *)
  set (lo := ACtlCut.c_sp cx - A.ACfn.LLVMF_STK).
  assert (Hlo : lo = ACtlCut.c_sp cx - 32768) by (unfold lo; rewrite HSTKv; reflexivity).
  assert (RO : LStep.ro_cells rsegs mem3 (A + 128) [LCells.C8 (Z_to_bv 64 (fr + 544))]).
  { apply SR8.r8_ro8. exact (r8g_spill_q64 regs3 mem3 128 (fr + 544) A S128 R9 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Hstk_blk : LFrame.stk rsegs mem3 phi (phi + ACtlCutP.rnb cx b)).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. exact (proj1 (Hpres_blk a Ha)). }
  destruct (LFrame.stk_bytes rsegs mem3 phi (phi + ACtlCutP.rnb cx b) Hstk_blk ltac:(lia)) as (junk & Hjl & Hjb).
  assert (RWd : LStep.rw_cells rsegs mem3 phi [LCells.CB (Z.to_nat (ACtlCutP.rnb cx b)) junk]).
  { replace (Z.to_nat (ACtlCutP.rnb cx b)) with (length junk) by lia. apply SR8.r8_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length junk)) with (phi + ACtlCutP.rnb cx b - phi) by lia.
    exact (SR8.r8_wr_stk mem3 _ _ Hstk_blk). }
  assert (HAL : phi = fr + 544 \/ fr + 544 + ACtlCutP.rnb cx b <= phi \/ phi + ACtlCutP.rnb cx b <= fr + 544)
    by lia.
  destruct HHB as (Hphi_nz & HADphi). rewrite HaN in HADphi.
  assert (AD : A.AsanRT.addressable mem3 phi (ACtlCutP.rnb cx b)).
  { replace phi with (phi + 0) at 1 by lia.
    exact (A.AsanRTFacts.addressable_sub mem3 phi (ACtlCutP.rnb cx b) 0 (ACtlCutP.rnb cx b) HADphi
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (ES : A.AsanRT.end_in_app (fr + 544) (ACtlCutP.rnb cx b)) by (right; apply Happ_fr; lia).
  assert (ED : A.AsanRT.end_in_app phi (ACtlCutP.rnb cx b)).
  { right. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happ_in.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (APP : ACtlCutP.rnb cx b = 0 \/ A.AsanRT.app_mem (fr + 544 + 7) /\ A.AsanRT.app_mem (phi + 7))
    by (right; split; [apply Happ_fr; lia | apply Happ_blk; lia]).
  assert (HRTd : phi + ACtlCutP.rnb cx b <= A.AsanRT.RT_LO \/ A.AsanRT.RT_HI <= phi).
  { destruct (Z_le_gt_dec (phi + ACtlCutP.rnb cx b) A.AsanRT.RT_LO) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec A.AsanRT.RT_HI phi) as [H2|H2]; [right; exact H2|].
    exfalso. apply (Hblk_img (Z.max phi A.AsanRT.RT_LO)); [lia|].
    apply A.ACtlG.KitMem.kitmem_in_img.
    unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in *.
    lia. }
  assert (HSEPd : phi + ACtlCutP.rnb cx b <= sp - MCC.ASAN_MEMCPY_K \/ sp <= phi) by (left; lia).
  assert (HSEPs : fr + 544 + ACtlCutP.rnb cx b <= sp - MCC.ASAN_MEMCPY_K \/ sp <= fr + 544) by (left; lia).
  assert (ST : LFrame.stk rsegs mem3 lo sp).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. apply Hpres. lia. }
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= lo) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HROphi : forall i, 0 <= i < ACtlCutP.rnb cx b ->
             LMem.ro_addr rsegs (LMem.wa (phi + i)) = false).
  { intros i Hi. destruct (LMem.ro_addr rsegs (LMem.wa (phi + i))) eqn:E; [exfalso | reflexivity].
    pose proof (A.ACtlG.KitMem.kitmem_ro_img _ E) as Himg. rewrite LMem.wa_unsigned in Himg by lia.
    exact (Hblk_img (phi + i) ltac:(lia) Himg). }
  (* the footprint RNG_W (w_H W3) and its ranges *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Rld : LExecF.rng RNG (A + 128) 8).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 128) 8 HJ ltac:(lia) ltac:(lia)). }
  assert (Rimg : LExecF.rng RNG A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO))
    by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  assert (Rstk : LExecF.rng RNG (sp - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K HJ
             ltac:(lia) ltac:(lia)). }
  assert (RngD : LExecF.rng RNG phi (ACtlCutP.rnb cx b)).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) phi (ACtlCutP.rnb cx b)
             HAR Hin_blk ltac:(lia) ltac:(lia)). }
  pose proof (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 544)
                (ACtlCutP.rnb cx b) HAR Hin6) as Hfv.
  rewrite Efr6, HFB in Hfv. destruct (Hfv ltac:(lia) ltac:(lia)) as (Hfv1 & Hfv2).
  assert (RngS : LExecF.rng RNG (fr + 544) (ACtlCutP.rnb cx b)) by exact (A.ProgBridge.rng_of_visible _ _ _ Hfv1).
  assert (RngDs : A.Prog.rng_asan.sh_word_rng RNG phi (ACtlCutP.rnb cx b)).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.rnb cx b) phi
                (ACtlCutP.rnb cx b) HAR Hin_blk ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | HV];
      [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ HV)]. }
  assert (RngSs : A.Prog.rng_asan.sh_word_rng RNG (fr + 544) (ACtlCutP.rnb cx b)).
  { destruct (Hfv2 ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as [E0 | HV];
      [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ HV)]. }
  assert (RngKs : A.Prog.rng_asan.sh_word_rng RNG (sp - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - MCC.ASAN_MEMCPY_K) MCC.ASAN_MEMCPY_K
                HAR ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | HV];
      [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ HV)]. }
  (* route (C): the run's shadow region lies in the cut's own shadow (cut_shadow's (F) and (L) disjuncts) *)
  assert (HSWR : A.ShadowRwOn.shadow_rw_on (SR8Fo.r8_evt_shadow_R (fr + 544) phi (ACtlCutP.rnb cx b)) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
    intros a [Ha | Ha].
    - (* the source bytes [fr + 544, + n_b) of the owned class-6 frame: (F) *)
      left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. rewrite Efr6, HFB.
      exact (r8g_src_shadow fr (ACtlCutP.rnb cx b) a ltac:(lia) ltac:(lia) Ha).
    - (* the fresh block (phi, n_b), a live block of the cut: (L) *)
      right; left. exists phi, (ACtlCutP.rnb cx b). split; [exact Hin_blk|]. rewrite HreqN.
      exact (r8g_blk_shadow phi (ACtlCutP.rnb cx b) a Ha). }
  (* the run, its memcpy premise discharged by a Theorem Labs lane's proof *)
  pose proof (SR8Fo.r8_evt_F_on RNG A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 sp A (fr + 544) (ACtlCutP.rnb cx b) phi lo
    (SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b)) junk
    R2 R9 Ha0 R18 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    RO HF544 HLF RWd HAL ltac:(lia) HADs AD ES ED APP HRTd HSEPd HSEPs ST ltac:(lia) HHM
    ltac:(unfold A.AsanRT.APPMEM_END; lia)
    HAC HSWR HRO HROphi Rld (A.ProgBridge.rng_bytes_RNG_W _) Rimg Rstk RngD RngS RngDs RngSs RngKs) as HRUN.
  match type of HRUN with LExecF.evtF _ _ _ ?s => set (ms0 := s) in HRUN end.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms1 & Hrun & HQ).
  rewrite <- A.ProgBridge.tfibsegs_rsegs in Hrun.
  assert (Hfp : Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W3) RNG) by exact (A.ProgBridge.fp_avoids_RNG_W _).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81640_at [Z.of_nat b])) with 0x81640.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81640) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the lift (YA0nR.SRr_fsteps keeps the run for ajournal_of_fsteps). *)
  change (Reusable.YA0n.SRr segs W3 (mkCfg ms0 md3) (POST cx)).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 ms0 ms1 md3 RNG (POST cx) Hrun Hfp).
  intros md' Hsbm.
  (* G5: the continuation at the run's end state *)
  destruct HQ as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K10 & K24 & K18 &
    MU & WM & RO' & ST' & AC' & SW' & RW' & BS').
  assert (E2 : CK11.getr R 2 = CK11.getr regs3 2) by exact K2.
  assert (E3 : CK11.getr R 3 = CK11.getr regs3 3) by exact K3.
  assert (E4 : CK11.getr R 4 = CK11.getr regs3 4) by exact K4.
  assert (E8 : CK11.getr R 8 = CK11.getr regs3 8) by exact K8.
  assert (E9 : CK11.getr R 9 = CK11.getr regs3 9) by exact K9.
  assert (E19 : CK11.getr R 19 = CK11.getr regs3 19) by exact K19.
  assert (E21 : CK11.getr R 21 = CK11.getr regs3 21) by exact K21.
  assert (E22 : CK11.getr R 22 = CK11.getr regs3 22) by exact K22.
  assert (E23 : CK11.getr R 23 = CK11.getr regs3 23) by exact K23.
  assert (E25 : CK11.getr R 25 = CK11.getr regs3 25) by exact K25.
  assert (E26 : CK11.getr R 26 = CK11.getr regs3 26) by exact K26.
  assert (MU0 : LFrame.munch WR mem3 m') by exact MU.
  (* the journal across the run (ProgWorld.ajournal_of_fsteps) *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFrame.outside WR a ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3)
              ly3 (ACtlCut.own6 cx) a).
  { intros a Ha Hno.
    destruct (Z_le_gt_dec phi a) as [H1|H1]; [destruct (Z_lt_ge_dec a (phi + ACtlCutP.rnb cx b)) as [H2|H2]|].
    - right; right; left. exists phi, (ACtlCutP.rnb cx b). rewrite HreqN.
      split; [exact Hin_blk|]. split; [exact Hnew | lia].
    - left. rewrite HSTKv. destruct (Z_le_gt_dec (sp - MCC.ASAN_MEMCPY_K) a) as [H3|H3];
        [destruct (Z_lt_ge_dec a sp) as [H4|H4]|]; [lia | (exfalso; apply Hno; apply Hout; lia) ..].
    - left. rewrite HSTKv. destruct (Z_le_gt_dec (sp - MCC.ASAN_MEMCPY_K) a) as [H3|H3];
        [destruct (Z_lt_ge_dec a sp) as [H4|H4]|]; [lia | (exfalso; apply Hno; apply Hout; lia) ..]. }
  assert (MU1 : LFrame.munch WR (ms_mem ms0) (ms_mem ms1)) by (rewrite Ems; exact MU0).
  pose proof (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
    ly3 S3 W3 ms0 ms1 md3 md' k RNG WR HJ Hrun Hfp MU1 Hsbm Hawr) as HJ'.
  rewrite Ems in HJ'. rewrite Ems.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81658_at [Z.of_nat b]))
            R m' md') (POST cx)).
  (* the keep facts *)
  assert (KSP : forall off v, 0 <= off -> off + 8 <= 416 -> ACtlCutP.spill regs3 mem3 off v ->
            ACtlCutP.spill R m' off v).
  { intros off v Ho1 Ho2 Hs.
    exact (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' off v A Hs R9 ltac:(lia) Ho1 ltac:(lia) MU0 E9
             (fun x Hx => HAout x ltac:(lia))). }
  assert (KFR : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 Hb. exact (A.Prog.RcAsanFPLib.fl_bytes WR mem3 m' a bs Hb MU0 (fun x Hx => Hfrout x ltac:(lia))). }
  assert (KAD : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Hadr; exact (A.ACtlG.KitMem.kitmem_addr_munch WR mem3 m' p n Hadr MU0 Hsh_out)).
  assert (KRW : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + 4096 ->
            LStep.rw_cells segs mem3 a [LCells.CB n bs] -> LStep.rw_cells segs m' a [LCells.CB n bs]).
  { intros a n bs H1 H2 Hc. exact (SR8.r8_rwcb_keep WR mem3 m' a n bs Hc MU0 WM (fun x Hx => Hfrout x ltac:(lia))). }
  assert (KIN : LMem.bytes_at segs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
            LMem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx))
    by (intros Hb; exact (A.Prog.RcAsanFPLib.fl_bytes WR mem3 m' _ _ Hb MU0 Hinout)).
  apply (HX cx [Z.of_nat b] fr k ly3 S3 W3 R m' md' Hbase).
  - (* journal *)
    exact HJ'.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law *)
    exact HL.
  - (* the event bound: 2b + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81658_at (ACtlCutP.v:1352-1370), at the same index *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81658_at ACtlCutP.ixn nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact E2 | exact E3 | exact E4 | exact E8 |
        exact E9 | exact E19 | exact E26].
      apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' WR HFRAC MU0).
      - intros x Hx. apply Hspout. rewrite HspZ in Hx. exact Hx.
      - intros x Hx. apply Hfrout. lia.
      - intros x Hx. apply Hnapp_out.
        unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES, A.AsanRT.shadow_addr,
          A.AsanRT.ASAN_K in Hx.
        unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
        Z.div_mod_to_equations. lia. }
    split.
    { split; [exact Hcn|]. split; [exact Hb6|].
      split; [split; [exact Hphi_nz | rewrite HaN; exact (KAD _ _ HADphi)]|].
      split; [unfold ACtlCut.rgv; rewrite E23; exact R23|].
      split; [unfold ACtlCutP.OURb in *; apply KFR; [lia | rewrite SM.OUR_length; lia | exact HOUR]|].
      split; [unfold ACtlCutP.OUTA in *; exact (KAD _ _ HOUTA)|].
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
        split; [unfold ACtlCut.rgv in *; rewrite E22; exact Hc22 | unfold ACtlCut.rgv in *; rewrite E25; exact Hc25]. }
      split; [exact (KSP 112 _ ltac:(lia) ltac:(lia) S112)|].
      split; [exact (KSP 128 _ ltac:(lia) ltac:(lia) S128)|].
      split.
      { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA6 & PIN & PINB &
          P184 & P256 & P264 & P272 & P32).
        split; [exact (KSP 40 _ ltac:(lia) ltac:(lia) P40)|].
        split; [exact (KSP 120 _ ltac:(lia) ltac:(lia) P120)|].
        split; [exact (KSP 136 _ ltac:(lia) ltac:(lia) P136)|].
        split; [exact (KSP 160 _ ltac:(lia) ltac:(lia) P160)|].
        split; [exact (KSP 168 _ ltac:(lia) ltac:(lia) P168)|].
        split; [exact (KSP 176 _ ltac:(lia) ltac:(lia) P176)|].
        split; [exact (KSP 208 _ ltac:(lia) ltac:(lia) P208)|].
        split; [exact (KSP 248 _ ltac:(lia) ltac:(lia) P248)|].
        split; [exact (KAD _ _ PA6)|].
        split; [exact (KIN PIN)|].
        split; [intros Hn0; exact (KAD _ _ (PINB Hn0))|].
        split; [exact (KSP 184 _ ltac:(lia) ltac:(lia) P184)|].
        split; [exact (KSP 256 _ ltac:(lia) ltac:(lia) P256)|].
        split; [exact (KSP 264 _ ltac:(lia) ltac:(lia) P264)|].
        split; [exact (KSP 272 _ ltac:(lia) ltac:(lia) P272)|].
        exact (KSP 32 _ ltac:(lia) ltac:(lia) P32). }
      split; [exact (KSP 104 _ ltac:(lia) ltac:(lia) S104)|].
      split; [exact (KSP 96 _ ltac:(lia) ltac:(lia) S96)|].
      split; [exact (KSP 64 _ ltac:(lia) ltac:(lia) S64)|].
      split; [exact (KSP 144 _ ltac:(lia) ltac:(lia) S144)|].
      split; [exact (KSP 192 _ ltac:(lia) ltac:(lia) S192)|].
      split; [destruct RW38 as (idb & Hc); exists idb; apply KRW; [lia | lia | exact Hc]|].
      split; [destruct RW72 as (jk & Hc); exists jk; apply KRW; [lia | lia | exact Hc]|].
      split; [exact (KSP 280 _ ltac:(lia) ltac:(lia) S280)|].
      split; [exact (KSP 240 _ ltac:(lia) ltac:(lia) S240)|].
      split; [destruct RW1 as (jy & Hc); exists jy; apply KRW; [lia | lia | exact Hc]|].
      split; [destruct RW32 as (jk & Hc); exists jk; apply KRW; [lia | lia | exact Hc]|].
      split; [exact (KSP 152 _ ltac:(lia) ltac:(lia) S152)|].
      split; [unfold ACtlCut.rgv; rewrite E21; exact R21|].
      exact (KAD _ _ HAD38). }
    (* X81658: RF (the turn-b records kept, s8 = phi, phi's bytes = rt_F, s2 = n_b) and RXS *)
    unfold ACtlCutP.X81658, ACtlCutP.RF, ACtlCutP.RFx, ACtlCutP.RFb, ACtlCutP.RB.
    split.
    { split; [|exact K18].
      split.
      - split; [exact Hb6|].
        split.
        { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
          split; [unfold ACtlCut.rgv in *; rewrite E22; exact Hc22 | unfold ACtlCut.rgv in *; rewrite E25; exact Hc25]. }
        split; [unfold ACtlCutP.OURb in *; apply KFR; [lia | rewrite SM.OUR_length; lia | exact HOUR]|].
        split; [unfold ACtlCut.rgv; rewrite E23; exact R23|].
        split; [unfold ACtlCutP.IDBr in *; apply KFR; [lia | rewrite HLID; lia | exact HID]|].
        unfold ACtlCutP.FGBr in *; apply KFR; [lia | rewrite HLFG; lia | exact HFG].
      - split; [exact Hnz|]. split; [exact K24|].
        destruct RW' as ((_ & Hbq) & _). cbn [LCells.cells_bytes LCells.cbytes] in Hbq. rewrite app_nil_r in Hbq.
        exact Hbq. }
    destruct HRXS as (S48 & S56 & S88 & S80 & S72 & S8 & S0 & S200 & S216 & HA72).
    split; [exact (KSP 48 _ ltac:(lia) ltac:(lia) S48)|].
    split; [exact (KSP 56 _ ltac:(lia) ltac:(lia) S56)|].
    split; [exact (KSP 88 _ ltac:(lia) ltac:(lia) S88)|].
    split; [exact (KSP 80 _ ltac:(lia) ltac:(lia) S80)|].
    split; [exact (KSP 72 _ ltac:(lia) ltac:(lia) S72)|].
    split; [exact (KSP 8 _ ltac:(lia) ltac:(lia) S8)|].
    split; [exact (KSP 0 _ ltac:(lia) ltac:(lia) S0)|].
    split; [exact (KSP 200 _ ltac:(lia) ltac:(lia) S200)|].
    split; [exact (KSP 216 _ ltac:(lia) ltac:(lia) S216)|].
    exact (KAD _ _ HA72).
  - (* ctl_rt_C: asan_cells / ro_agree from the run's post; the two regions carried by its forall-P post *)
    split; [exact AC'|]. split; [exact (SW' _ Hcut)|]. split; [exact (SW' _ HimgS) | exact RO'].
Qed.

End GlueR8.

Print Assumptions glue_seg_R8.

(* Gate check (a Theorem Labs lane 07:18Z): the Section's classes are the CORE copies of the twin modules (lib/Reusable). *)
Locate CM05.RunCeil.
Locate CO09.lib_shape.
Locate CK11.FPState.
