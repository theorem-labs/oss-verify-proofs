(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the route (C) shadow premise of the narrowed
   _F files, `shadow_rw_on (C_ON.reac_box_model_block_shadow_R Sp (ly_F ly) p b o row nb) (normalize rsegs mem)`, at
   ANY AR state of the cgif world, for a Theorem Labs lane's TMB glue (lib/A/Prog/reac_box_model_block_glue.v).  The proof
   uses NO universal shadow fact: not A.ProgWorld.AR_states_vis0_shadow (false at an AR state), and no shell that
   contains shadow_rw.  rule 24: no function is proved here (a program-world fact over the core's AR).
   Writer: a Theorem Labs lane; a working branch.

   The disjuncts of R (lib/A/Prog/reac_box_model_block_c_on.v 552ee645503 (the blob this tree had at release c5e779efe8c)) and the world fact that covers each.
   sh_word_on x n is the shadow of the 64-aligned app blocks around [x, x + n) (8-aligned shadow WORDS), so each cover
   needs a region whose app range is 64-aligned at both ends:
     window  sh_word_on (Sp - K) K      cut_shadow (Z), the machine stack's zero_shadow range
                                        (YG0n.v:188-189; page-aligned ends: layout_ok lo_top, YG0f.v:322-324)
     FS      asan_stack_malloc_shadow_R (ly_F ly) 0
                                        cut_shadow (A), the fake stack's frames area (aareas, YG0n.v:139)
     o       sh_word_on o 32            tbmb_o_home: on the machine stack, cut_shadow (Z) as the window; in a frame
                                        (cid, pos) of frames S, cut_shadow (F), the frame's shadow (al_frames,
                                        YG0d.v:447-455); the frame is 64-aligned (ly_F page-aligned, 0 <= cid by
                                        Wf's wfs_live, YG01.v:313)
     JOIN    sh_word_on JOIN_0013/4 32  img_shadow, from img_shadow_vis (CtrlRo.v:44-46): both are image constants
     row     sh_word_on p 296           img_shadow, from img_shadow_vis and the row's image bounds
     name    sh_word_on (rname row) n   img_shadow, from img_shadow_vis and the name's in_roP bytes
   The covers are A.ACtlCutC.cut_shadow_of_AR (AR_laws) and sr_img_of_vis (img_shadow_vis); MemNormTr's argument moves
   the region to `normalize rsegs mem` (shadow_rw_on_normalize).

   STOP (reported to a Theorem Labs lane, 2026-10-29 ~20:00Z).  The statement as first sent (premises up to the o premise)
   does NOT give the row and the name: globs_marked gives block_shadow q sz (YG0v.v:37-40), the shadow of the
   glob's OWN granules, while sh_word_on reaches the shadow words of the granules before q and after q + sz; no
   premise covers those (img_shadow_vis needs the app address in [IMG_LO, IMG_HI), and AR's ahs_pres,
   YG0n.v:442-444, leaves visible vis0 bytes not present).  a Theorem Labs lane DECIDED (20:04Z) to append three premises:
   ROW (the text of C_reac_box_model_block.v:152 under p <> 0), NAME (the in_roP conjunct of :162-163 under the name
   guards), RELRO (pb_reac_box_model_block_stmt's RELRO, :185).  reac_box_model_block_sr_on_img below is that
   statement.  The first form is NOT proved here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcSynthLib.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt A.ProgWorldOwnedRo
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.memset A.Prog.asan_memcpyF A.Prog.build_dt1_singleF
  A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi A.Prog.reac_box_model_block_epiF.
(* route (C): the region leaf and the VIS0-free covers *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ACtlCutC A.Prog.sh_word_on
  A.Prog.asan_stack_malloc_c_on A.Prog.reac_box_model_block_c_on.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

Module BmbGlueSR.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- 1. Arithmetic covers: which app range each sh_word_on region's shadow words lie in. ---- *)

(* The shadow words of [x, x + n) lie in the shadow of [lo, lo + len) when both ends of that range are 64-aligned. *)
Lemma hull_cover : forall lo len x n a,
  lo mod 64 = 0 -> len mod 64 = 0 -> lo <= x -> x + n <= lo + len -> 0 <= n ->
  A.Prog.sh_word_on.sh_word_on x n a ->
  lib.Reusable.YG0f.SHADOW_OFF + lo / 8 <= a < lib.Reusable.YG0f.SHADOW_OFF + lo / 8 + len / 8.
Proof.
  intros lo len x n a Hlo Hlen H1 H2 Hn0 (Hn & Ha1 & Ha2).
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* The image's shadow: a range inside [IMG_LO, IMG_HI) (both ends 64-aligned) has its shadow words in img_shadow. *)
Lemma img_cover : forall x n a, 0 <= n -> A.Prog.CtrlRo.IMG_LO <= x -> x + n <= A.Prog.CtrlRo.IMG_HI ->
  A.Prog.sh_word_on.sh_word_on x n a -> A.ACtlRtC.img_shadow a.
Proof.
  intros x n a Hn0 H1 H2 Ha.
  assert (Hc : lib.Reusable.YG0f.SHADOW_OFF + A.Prog.CtrlRo.IMG_LO / 8 <= a <
               lib.Reusable.YG0f.SHADOW_OFF + A.Prog.CtrlRo.IMG_LO / 8 +
               (A.Prog.CtrlRo.IMG_HI - A.Prog.CtrlRo.IMG_LO) / 8).
  { apply (hull_cover A.Prog.CtrlRo.IMG_LO (A.Prog.CtrlRo.IMG_HI - A.Prog.CtrlRo.IMG_LO) x n a);
      [reflexivity | reflexivity | lia | lia | lia | exact Ha]. }
  exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)).
  unfold lib.Reusable.YG0f.shadow_addr.
  rewrite (Z.mul_comm 8 (a - lib.Reusable.YG0f.SHADOW_OFF)), Z.div_mul by lia.
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The class-0 block of the fake stack lies in its frames area. *)
Lemma fs0_cover : forall F a, A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R F 0%nat a ->
  lib.Reusable.YG0f.shadow_addr (F + lib.Reusable.YG0f.kFakeFramesOff) <= a <
  lib.Reusable.YG0f.shadow_addr (F + lib.Reusable.YG0f.kFakeStackSize).
Proof.
  intros F a Ha. unfold A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R in Ha.
  assert (E : A.Prog.asan_stack_malloc_c.fs_frame F 0%nat 0 = F + 36864).
  { unfold A.Prog.asan_stack_malloc_c.fs_frame. rewrite Nat2Z.inj_0, !Z.mul_0_l, !Z.add_0_r. reflexivity. }
  rewrite E in Ha. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG0f.kFakeStackSize.
  Z.div_mod_to_equations. lia.
Qed.

(* A fake-stack frame of a class cid >= 0 is 64-aligned and its size is a multiple of 64. *)
Lemma frame_al64 : forall ly cid pos, lib.Reusable.YG0f.ly_F ly mod 4096 = 0 -> 0 <= cid ->
  lib.Reusable.YG0f.frame_addr ly cid pos mod 64 = 0 /\ lib.Reusable.YG00.fs_frame_bytes cid mod 64 = 0.
Proof.
  intros ly cid pos HF Hc.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG00.fs_frame_bytes,
    lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG00.kStackSizeLog.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (1 * 2 ^ 20) with 1048576.
  set (t := 2 ^ cid).
  replace (pos * (64 * t)) with (64 * (pos * t)) by ring.
  set (w := pos * t). clearbody w t.
  split; Z.div_mod_to_equations; lia.
Qed.

(* Every segment of the image lies in [IMG_LO, IMG_HI) (A.MemNormTr's vm_computed bounds of rsegs = tfibsegs). *)
Lemma img_bounds_of_in_img : forall x, in_img AB1v.tfibsegs x ->
  A.Prog.CtrlRo.IMG_LO <= x < A.Prog.CtrlRo.IMG_HI.
Proof.
  intros x (sg & Hin & H1 & H2).
  assert (Hin' : In sg A.Img0.rsegs) by exact Hin.
  pose proof (proj1 (forallb_forall _ _) A.MemNormTr.rsegs_below_img sg Hin') as Hhi.
  pose proof (proj1 (forallb_forall _ _) A.MemNormTr.rsegs_above_img_lo sg Hin') as Hlo.
  cbv beta in Hhi, Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
  unfold A.Prog.ImgBounds.IMG_HI, A.Prog.ImgBounds.IMG_LO in *.
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI. lia.
Qed.

(* NAME's conversion (a Theorem Labs lane 20:04Z): bytes in in_roP (C_reac_box_model_block.v:163) under RELRO lie in the image,
   so the name's shadow words are in img_shadow.  The one lemma that reads the NAME premise's form. *)
Lemma name_cover_of_roP : forall RLO RHI q n a,
  (forall a, RLO <= a < RHI -> in_img AB1v.tfibsegs a) ->
  (forall x, q <= x < q + n -> in_roP AB1v.tfibsegs RLO RHI x) ->
  0 <= n -> A.Prog.sh_word_on.sh_word_on q n a -> A.ACtlRtC.img_shadow a.
Proof.
  intros RLO RHI q n a RELRO Hro Hn0 Ha.
  assert (Hn : 0 < n) by (destruct Ha as [Hn _]; lia).
  assert (Himg : forall x, q <= x < q + n -> A.Prog.CtrlRo.IMG_LO <= x < A.Prog.CtrlRo.IMG_HI).
  { intros x Hx. apply img_bounds_of_in_img.
    destruct (Hro x Hx) as [(s & Hs & _ & Hb) | Hr].
    - exists s. split; [exact Hs | exact Hb].
    - exact (RELRO x Hr). }
  pose proof (Himg q ltac:(lia)) as [Hq _]. pose proof (Himg (q + n - 1) ltac:(lia)) as [_ Hqn].
  apply (img_cover q n a); [lia | lia | lia | exact Ha].
Qed.

(* ---- 2. The memory step: a region of the world memory holds on its normalized memory (A.MemNormTr's
   shadow_rw_normalize, restricted to P: a shadow address is above every segment, so it is not read-only). ---- *)
Lemma shadow_rw_on_normalize : forall (P : Z -> Prop) (m : word -> option byte), ro_agree rsegs m ->
  A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P (normalize rsegs m).
Proof.
  intros P m RO H a Hp Ha. pose proof (mem_rel_normalize rsegs m RO) as REL.
  destruct (H a Hp Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false).
  { apply ro_addr_above_img.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Ha.
    unfold A.Prog.ImgBounds.IMG_HI. lia. }
  split; [rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ REL E); exact Hv|].
  exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ REL). exact Hb.
Qed.

(* ---- 3. The world covers, one lemma per disjunct of R, at the world memory of ANY AR state. ---- *)
Section Covers.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.

(* (I) the image's shadow, from img_shadow_vis (CtrlRo.v:44-46). *)
Lemma sr_img_of_vis : A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md -> A.ShadowRwOn.shadow_rw_on A.ACtlRtC.img_shadow mem.
Proof.
  intros HV ly S W mem md HAR a (x & Hx & ->) _.
  apply A.ShadowRwOn.srw_byte_of_mem.
  apply (A.ProgWorldCtlRt.mem_some_of_aview_high W mem).
  - unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, A.Prog.CtrlRo.IMG_LO,
      A.Prog.CtrlRo.IMG_HI in *.
    Z.div_mod_to_equations. lia.
  - exact (HV ly S W mem md x HAR Hx).
Qed.

(* The machine stack's ends are page-aligned (layout_ok, YG0f.v:322-324, by AR's am_layout). *)
Lemma stk_al64 : forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  ly_stk_lo ly mod 64 = 0 /\ (ly_stk_hi ly - ly_stk_lo ly) mod 64 = 0.
Proof.
  intros ly S W mem md HAR.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR)) as Hly.
  apply lib.Reusable.YG0f.lo_top in Hly. destruct Hly as (_ & _ & _ & _ & Hal & Hah & _).
  unfold lib.Reusable.YG0f.page_aligned in Hal, Hah.
  split; Z.div_mod_to_equations; lia.
Qed.

(* A range on the machine stack: its shadow words are in cut_shadow (Z), the stack's zero_shadow range. *)
Lemma sr_stack_range : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md x n,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  0 <= n -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on x n) mem.
Proof.
  intros LAWS ly S W mem md x n HAR Hn0 H1 H2.
  apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly S));
    [|exact (A.ACtlCutC.cut_shadow_of_AR B LAWS ly S W mem md HAR)].
  intros a Ha. destruct (stk_al64 ly S W mem md HAR) as [Hlo Hlen].
  right. right. left. exists (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly). split.
  - unfold lib.Reusable.YG0n.zero_shadow_ranges. left. reflexivity.
  - cbn [fst snd]. unfold lib.Reusable.YG0v.shadow_of_addr.
    apply (hull_cover (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) x n a Hlo Hlen H1 ltac:(lia) Hn0 Ha).
Qed.

(* window: the call window [Sp - K, Sp) on the machine stack. *)
Lemma sr_window : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md Sp,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  ly_stk_lo ly <= Sp - REAC_BOX_MODEL_BLOCK_K -> Sp <= ly_stk_hi ly ->
  A.ShadowRwOn.shadow_rw_on
    (A.Prog.sh_word_on.sh_word_on (Sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K) mem.
Proof.
  intros LAWS ly S W mem md Sp HAR H1 H2.
  apply (sr_stack_range LAWS ly S W mem md _ _ HAR); unfold REAC_BOX_MODEL_BLOCK_K in *; lia.
Qed.

(* FS band: the class-0 block of the fake stack, in cut_shadow (A), the frames area (aareas, YG0n.v:139). *)
Lemma sr_fs0 : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R (ly_F ly) 0%nat) mem.
Proof.
  intros LAWS ly S W mem md HAR.
  apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly S));
    [|exact (A.ACtlCutC.cut_shadow_of_AR B LAWS ly S W mem md HAR)].
  intros a Ha. right. right. right. exact (fs0_cover (ly_F ly) a Ha).
Qed.

(* o on the machine stack (tbmb_o_home's second disjunct). *)
Lemma sr_o_stack : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md o,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  ly_stk_lo ly <= o -> o + 32 < ly_stk_hi ly ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on o 32) mem.
Proof.
  intros LAWS ly S W mem md o HAR H1 H2.
  apply (sr_stack_range LAWS ly S W mem md _ _ HAR); lia.
Qed.

(* o in a frame (cid, pos) of frames S (tbmb_o_home's first disjunct): cut_shadow (F), the frame's shadow. *)
Lemma sr_o_frame : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md o cid pos,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  In (cid, pos) (lib.Reusable.YG01.frames S) ->
  (forall x, o <= x < o + 32 -> lib.Reusable.YG0n.in_zr x (lib.Reusable.YCbq.frame_rng ly (cid, pos))) ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on o 32) mem.
Proof.
  intros LAWS ly S W mem md o cid pos HAR Hin Hx.
  apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly S));
    [|exact (A.ACtlCutC.cut_shadow_of_AR B LAWS ly S W mem md HAR)].
  intros a Ha. left. exists cid, pos. split; [exact Hin|].
  pose proof (lib.Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR)) as Hwf.
  apply lib.Reusable.YG01.wf_fakestack in Hwf. apply lib.Reusable.YG01.wfs_live in Hwf.
  rewrite Forall_forall in Hwf. destruct (Hwf (cid, pos) Hin) as [[Hc0 _] _]. cbn [fst] in Hc0.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR)) as Hly.
  apply lib.Reusable.YG0f.lo_F_al in Hly. unfold lib.Reusable.YG0f.page_aligned in Hly.
  destruct (frame_al64 ly cid pos Hly Hc0) as [Hfa Hfb].
  pose proof (Hx o ltac:(lia)) as H1. pose proof (Hx (o + 31) ltac:(lia)) as H2.
  unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in H1, H2. cbn [fst snd] in H1, H2.
  pose proof (hull_cover _ _ o 32 a Hfa Hfb ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hc.
  unfold lib.Reusable.YG0f.shadow_addr. lia.
Qed.

(* o, either home (tbmb_o_home, C_reac_box_model_block.v:116-118). *)
Lemma sr_o : lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md o,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  C_reac_box_model_block.tbmb_o_home ly S o ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on o 32) mem.
Proof.
  intros LAWS ly S W mem md o HAR [(cid & pos & Hin & _ & Hx) | (H1 & H2)].
  - exact (sr_o_frame LAWS ly S W mem md o cid pos HAR Hin Hx).
  - exact (sr_o_stack LAWS ly S W mem md o HAR H1 H2).
Qed.

(* JOIN_0013 (b = 2) and JOIN_0014 (b = 1): image constants, img_shadow. *)
Lemma sr_join13 : A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on JOIN_0013 32) mem.
Proof.
  intros HV ly S W mem md HAR.
  apply (A.ShadowRwOn.shadow_rw_on_mono A.ACtlRtC.img_shadow); [|exact (sr_img_of_vis HV ly S W mem md HAR)].
  intros a Ha. apply (img_cover JOIN_0013 32 a); [lia | | | exact Ha];
    unfold JOIN_0013, A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI; lia.
Qed.

Lemma sr_join14 : A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on JOIN_0014 32) mem.
Proof.
  intros HV ly S W mem md HAR.
  apply (A.ShadowRwOn.shadow_rw_on_mono A.ACtlRtC.img_shadow); [|exact (sr_img_of_vis HV ly S W mem md HAR)].
  intros a Ha. apply (img_cover JOIN_0014 32 a); [lia | | | exact Ha];
    unfold JOIN_0014, A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI; lia.
Qed.

(* row: the 296 bytes at p, inside the image by ROW (C_reac_box_model_block.v:152). *)
Lemma sr_row : A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md p,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  A.Prog.CtrlRo.IMG_LO + 64 <= p -> p + 296 + 64 <= A.Prog.CtrlRo.IMG_HI ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on p 296) mem.
Proof.
  intros HV ly S W mem md p HAR H1 H2.
  apply (A.ShadowRwOn.shadow_rw_on_mono A.ACtlRtC.img_shadow); [|exact (sr_img_of_vis HV ly S W mem md HAR)].
  intros a Ha. apply (img_cover p 296 a); [lia | lia | lia | exact Ha].
Qed.

(* name: the n bytes at q, in in_roP (C_reac_box_model_block.v:163) under RELRO. *)
Lemma sr_name : A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md RLO RHI q n,
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  (forall a, RLO <= a < RHI -> in_img AB1v.tfibsegs a) ->
  (forall x, q <= x < q + n -> in_roP AB1v.tfibsegs RLO RHI x) -> 0 <= n ->
  A.ShadowRwOn.shadow_rw_on (A.Prog.sh_word_on.sh_word_on q n) mem.
Proof.
  intros HV ly S W mem md RLO RHI q n HAR RELRO Hro Hn0.
  apply (A.ShadowRwOn.shadow_rw_on_mono A.ACtlRtC.img_shadow); [|exact (sr_img_of_vis HV ly S W mem md HAR)].
  intros a Ha. exact (name_cover_of_roP RLO RHI q n a RELRO Hro Hn0 Ha).
Qed.

End Covers.

(* ---- 4. The statement the TMB glue cites (a Theorem Labs lane's text of ~19:58Z, sr_on-statement.md (a working note, not in this delivery), with the three
   premises a Theorem Labs lane appended at 20:04Z: ROW, NAME, RELRO, after the binders RLO RHI). ---- *)
Lemma reac_box_model_block_sr_on_img :
  forall {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}
         (B : asyms) (GLOBS : list (Z * Z)),
  A.AF0m.CtrlTSyms B ->
  lib.Reusable.YG0d.AR_laws AB1v.tfibsegs B ->
  A.Prog.CtrlRo.globs_marked AB1v.tfibsegs B GLOBS ->
  A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  in_zs B JOIN_0013 32 -> in_zs B JOIN_0014 32 ->
  forall ly S (W : lib.Reusable.YA0n.world AB1v.tfibsegs) (mem : word -> option byte) md (Sp p b o : Z) (row nb : list byte),
  lib.Reusable.YG0n.AR AB1v.tfibsegs B ly S W mem md ->
  ro_agree rsegs mem ->
  ly_stk_lo ly <= Sp - REAC_BOX_MODEL_BLOCK_K -> Sp <= ly_stk_hi ly ->
  (p <> 0 -> exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) ->
  (p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
     exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\ RcSynth.rname row + Z.of_nat (length nb) <= q + sz) ->
  (o <> 0 -> C_reac_box_model_block.tbmb_o_home ly S o /\ (forall x, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x)) ->
  forall (RLO RHI : Z),
  (p <> 0 -> IMG_LO + 64 <= p /\ p + 296 + 64 <= IMG_HI) ->
  (p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
     forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) -> in_roP AB1v.tfibsegs RLO RHI x) ->
  (forall a, RLO <= a < RHI -> in_img AB1v.tfibsegs a) ->
  A.ShadowRwOn.shadow_rw_on (C_ON.reac_box_model_block_shadow_R Sp (ly_F ly) p b o row nb) (normalize rsegs mem).
Proof.
  intros fx rc SK B GLOBS _ LAWS _ HV _ _ ly S W mem md Sp p b o row nb HAR Hro Hlo Hhi _ _ HO RLO RHI HROW HNAME
    RELRO.
  apply shadow_rw_on_normalize; [exact Hro|].
  intros a HR Hsh. unfold C_ON.reac_box_model_block_shadow_R in HR.
  destruct HR as [Ha | [Ha | [(Hp & Ha) | [(Hp & Hb & Hh & Hn & Ha) | [(Ho & Ha) | [(_ & Ha) | (_ & Ha)]]]]]].
  - exact (sr_window B LAWS ly S W mem md Sp HAR Hlo Hhi a Ha Hsh).
  - exact (sr_fs0 B LAWS ly S W mem md HAR a Ha Hsh).
  - destruct (HROW Hp) as [H1 H2].
    exact (sr_row B HV ly S W mem md p HAR H1 H2 a Ha Hsh).
  - exact (sr_name B HV ly S W mem md RLO RHI _ _ HAR RELRO (HNAME Hp Hb Hh Hn) (Nat2Z.is_nonneg _) a Ha Hsh).
  - destruct (HO Ho) as [Hhome _].
    exact (sr_o B LAWS ly S W mem md o HAR Hhome a Ha Hsh).
  - exact (sr_join14 B HV ly S W mem md HAR a Ha Hsh).
  - exact (sr_join13 B HV ly S W mem md HAR a Ha Hsh).
Qed.

End BmbGlueSR.
