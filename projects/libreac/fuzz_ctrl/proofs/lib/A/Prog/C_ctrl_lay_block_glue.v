(* ctrl_lay_block (0x855f4) on fuzz_ctrl's ASan build, image A: the cgif glue over the eight proved `_F` stretches
   of ctrl's proved run, re-based at the three cuts.  A Theorem Labs lane.  rule 24: no function proved.

   STATUS: Part C of lane-layglue.md (a working note, not in this delivery).  `Theorem pb_ctrl_lay_block` (section 8)
   proves C_ctrl_lay_block.v's tctrl_lay_block_spec at BASE + AF_ctrl_lay_block = 0x855f4 under the Section
   hypotheses below (the callee contract, a Theorem Labs lane's route (C) footprint contracts, the cgif core rules, a Theorem Labs lane's
   stack_malloc_classes, and image facts).  Regions: R1 lay_to_ret (s.4), R2 lay_r2_lift (s.5), the box call lay_box
   (s.6), R3 lay_r3_lift (s.7), R4 in the theorem (s.8); what the call keeps: C_ctrl_lay_block_kept.lay_tcj_final.

   ROUTE (C) (L3 recipe L3-recipe.md (a working note, not in this delivery)): at every cut the shadow facts are
   read from A.ACtlRtC.ctl_rt_C, supplied at the cut's AR by A.ProgWorldCtlRtC.ctl_rt_C_of_AR (LayBase.rt_facts_C);
   the region runs R2 / R3 / R4 are a Theorem Labs lane's _on twins, whose shadow premise shadow_rw_on (lay_F_R{2,3}_shadow_R)
   lies in cut_shadow's fake-stack-frames disjunct (lay_on_R_cut).  No AR_states_vis0_shadow, AR_states_owned_ro or
   universal shadow fact is taken.

   PLAN OF RECORD: ctrl_lay_block-rebase.md (a working note, not in this delivery) (regions R1..R4, the
   premises at each base memory and their sources).  The re-base is the instantiation of each stretch lemma with
   Section L's memory m := MemNorm.normalize rsegs m_R (m_R the region's base memory); the run on the normalized
   memory is carried back to the real memory by MemNormF.evtF_normalize_ro; the four region files
   ctrl_lay_block_F_R{1..4}.v add the boundary steps and the exact write sets the journal steps need.
   The lift pattern (SRr_fevt_hid on the normalized memory, the journal step after it, the allocator event through
   cgif's astack_malloc_realizes) is a Theorem Labs lane's, reac_box_model_block_glue.v (a working branch
   3ba915a90d1) SRr_evtF_norm :144-166 and bmb_to_ret :600-723; the same shape here keeps the two glues one audit.

   CLOSURE (glue closure rule, a Theorem Labs lane 23:38Z, accepted by a Theorem Labs lane): the `_F` files and their closure are Required
   QUALIFIED, never Imported or Exported; no lib/AZ/AsanW (not in this delivery), no W6, no SegCF / *_cfw / Cf* file; the statement of
   pb_ctrl_lay_block names only C_ctrl_lay_block's contract.  The lib.Lib family is Required from its own directory
   and named lib.Lib.X (a Theorem Labs lane 05:20Z).

   OVERLAP WITH fuzz_grant's proved walk (a working branch 5aae1e8a0ce,
   proofs/libreac/fuzz_grant/lib/A/Prog/CtrlLayBlock.v): cited at each shared stretch below (prologue, the
   fake-stack frame at 0x85668, the memset, the epilogue and the class-1 release); nothing of fuzz_grant is
   Required. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist twice (core lib/Reusable/<X> and ctrl's lib/A/Reusable/<X>: YI04 YI16 YK11 YK1b YM05
   YO09; porter a Theorem Labs lane 04:03Z) are Required, never Imported, and every name of theirs is written
   lib.Reusable.<X>.<name>: they are the CORE copies (the cgif world, the PA layer, ProgWorld). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block CtrlImg C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import YC85 CtrlFrame.
(* the world-walk kit and the bridges (lemmas only) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04R YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld ProgWorldVisWin ProgWorldVisFrame
  ProgWorldShadow ProgWorld_Fs ProgWorldAstack MemNorm MemNormF MemNormTr AF0m.
(* route (C): the cut facts ctl_rt_C (a Theorem Labs lane's form, A.ACtlRtC) from AR by a Theorem Labs lane's A.ProgWorldCtlRtC.ctl_rt_C_of_AR
   (no VIS0, no OWNED_RO), and the region form A.ShadowRwOn.shadow_rw_on with its normalize transport.  Loaded BEFORE
   ctrl_lay_block: ShadowRwOnT loads MemMono, whose `Ltac footprint_after_store ::=` (MemMono.v:207) is not Local and
   would replace ctrl_lay_block.v:215's if it loaded after it (a Theorem Labs lane's files keep the same order). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT ACtlRtC ProgWorldCtlRtC.
(* ProgWorld statements proved by a Theorem Labs lane (a working branch 87fcd8d0b28): fp_tls_apart_stmt,
   ctl_block_apart_fs_stmt *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldTlsApart ProgWorldBlkApart.
(* the _F closure, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c ctrl_lay_block_c ctrl_lay_block
  ctrl_lay_block_F_R1.
(* route (C) twins of the region runs (a working branch 5a39ad33995) and a Theorem Labs lane's
   route (C) footprint contracts they take *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_R2_on ctrl_lay_block_F_R3_on
  ctrl_lay_block_F_R4_on asan_memset_cF_on asan_memcpy_cF_on asan_stack_malloc_c_on sh_word_on rng_asan.
(* the final tcj_kept composition (lay_tcj_final) and the val_mem / aview bridge (val_mem1_of_aview) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_ctrl_lay_block_kept YC88.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcLay RcLayLib RcSynthLib.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.
(* The walk's segments (C_ctrl_lay_block.v:81); = A.Img0.rsegs by conversion (ProgBridge.tfibsegs_rsegs). *)
#[local] Notation SEGS := AB1v.tfibsegs.

(* ================================================================================================================
   1. The lift of one stretch (lib.Lib level): a footprint run on the normalized memory is a silent prefix of a world
   walk from the real memory, for a footprint that avoids the world's hidden bytes; the continuation gets the run,
   the post carried back through ms_rel, and the hidden bytes kept.  a Theorem Labs lane's SRr_evtF_norm
   (reac_box_model_block_glue.v:144-166), same proof.
   ================================================================================================================ *)
Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma lay_SRr_norm : lib.Reusable.YK04.wx_segs_nowrap A.Img0.rsegs ->
  forall (W : world A.Img0.rsegs) (RNG : lib.Lib.ExecF.footprint) (model : Model) (R F : bvmap 5 word) (pc : word)
         (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (K : world A.Img0.rsegs -> config -> Prop),
  lib.Reusable.YK04R.fp_avoids (w_H W) RNG ->
  A.MemNorm.ro_agree A.Img0.rsegs m ->
  lib.Lib.ExecF.evtF A.Img0.rsegs RNG Q
    (lib.Lib.MState.MS R F pc fc None (A.MemNorm.normalize A.Img0.rsegs m) (lib.Lib.PropExec.seg_rom A.Img0.rsegs)) ->
  (forall ms' model',
     lib.Reusable.YK04R.fsteps A.Img0.rsegs RNG
       (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom A.Img0.rsegs)) ms' ->
     (exists s0, Q s0 /\ A.MemNorm.ms_rel A.Img0.rsegs ms' s0 /\ A.MemNorm.ro_same A.Img0.rsegs m (ms_mem ms')) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> SRr A.Img0.rsegs W (mkCfg ms' model') K) ->
  SRr A.Img0.rsegs W
    (mkCfg (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom A.Img0.rsegs)) model) K.
Proof.
  intros Hwx W RNG model R F pc fc m Q K Hfp Hro HN Hk.
  destruct (A.MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Hro HN) as (ms' & Hrun & HP).
  pose proof (A.ProgBridge.fsteps_of_mstepsF _ _ _ Hrun) as Hf.
  apply (YA0nR.SRr_fevt_hid A.Img0.rsegs Hwx W
           (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom A.Img0.rsegs)) model RNG
           (fun s => lib.Reusable.YK04R.fsteps A.Img0.rsegs RNG
                       (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom A.Img0.rsegs)) s /\
                     exists s0, Q s0 /\ A.MemNorm.ms_rel A.Img0.rsegs s s0 /\
                                A.MemNorm.ro_same A.Img0.rsegs m (ms_mem s))).
  - exists ms'. split; [exact Hf | split; [exact Hf | exact HP]].
  - exact Hfp.
  - intros ms1 model1 [Hf1 HP1] Hhid Hs. exact (Hk ms1 model1 Hf1 HP1 Hhid Hs).
Qed.
End Lift.

(* Byte-level glue between the core's view and ctrl's raw-memory facts: a Theorem Labs lane's lemmas
   (reac_box_model_block_glue.v:486-535), same proofs; the lib.Lib layer is Imported inside this module only. *)
Module LayLib.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs, bytes_at A.Img0.rsegs m a bs ->
  (forall i, (i < length bs)%nat -> m' (wa (a + Z.of_nat i)) = m (wa (a + Z.of_nat i))) ->
  bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold mrd in *. rewrite (E i Hi). exact H.
Qed.

Lemma wr_at_agree : forall (m m' : word -> option byte) a n, wr_at A.Img0.rsegs m a n ->
  (forall i, 0 <= i < n -> m' (wa (a + i)) = m (wa (a + i))) -> wr_at A.Img0.rsegs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (E i Hi). exact H.
Qed.

Lemma rw_cells_agree : forall (m m' : word -> option byte) a cs, rw_cells A.Img0.rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (a + i)) = m (wa (a + i))) ->
  rw_cells A.Img0.rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] Hw] E. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m); [exact Hb|]. intros i Hi. apply E.
    rewrite (cells_bytes_length cs Hwf) in Hi. lia.
  - exact (wr_at_agree m m' a _ Hw E).
Qed.

(* At a visible address outside the segments the view determines the raw byte. *)
Lemma raw_of_aview : forall {fx : lib.Reusable.YK11.FPState} (W : world AB1v.tfibsegs)
    (mem mem' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> w_H W (Z_to_bv 64 a) = false -> ~ in_img AB1v.tfibsegs a ->
  aview AB1v.tfibsegs (w_H W) mem' a = aview AB1v.tfibsegs (w_H W) mem a ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros fx W mem mem' a Ha Hh Hni E.
  rewrite !(A.ProgWorld.aview_vis_mrd W _ a Hh) in E.
  assert (Hs : seg_rom A.Img0.rsegs (Z_to_bv 64 a) = None).
  { apply (A.MemNorm.seg_rom_unmapped A.Img0.rsegs). rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact (find_segment_none AB1v.tfibsegs a Hni). }
  unfold mrd in E. rewrite Hs in E.
  destruct (mem' (Z_to_bv 64 a)) as [b'|], (mem (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* Addresses at or above the allocation ceiling are outside the segments. *)
Lemma above_ceil_not_img : forall {rc : lib.Reusable.YM05.RunCeil} a, lib.Reusable.YM05.alloc_ceiling <= a ->
  ~ in_img AB1v.tfibsegs a.
Proof.
  intros rc a Ha Hi. pose proof (A.ProgWorld.pws_segs_low a Hi) as H.
  pose proof asan_consts as (C1 & _). unfold kLowMemEnd in H. lia.
Qed.
End LayLib.

(* ================================================================================================================
   The Section facts of a stretch at the normalized memory of a cut, from the cut's world (AR).  rt_facts_C, win_facts,
   asan_tls_cells_normalize and fp_normalize are a Theorem Labs lane's (reac_box_model_block_glue.v at
   a working branch cc9af1fcb2e, :733-795), same proofs; lay_fp0_facts is a Theorem Labs lane's fp0_facts (:801-883)
   for ctrl_lay_block's class set [0; 1] and its write / data ranges; lay_tls0_facts takes ProgWorld's
   fp_tls_apart_stmt (owner a Theorem Labs lane; proved: A.ProgWorldTlsApart.fp_tls_apart).
   ================================================================================================================ *)
Module LayBase.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.ctrl_lay_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.

Section Base.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Hypothesis TSY : A.AF0m.CtrlTSyms B.

(* The cut facts at the normalized memory, route (C): A.ProgWorldCtlRtC.ctl_rt_C_of_AR (a Theorem Labs lane, needs neither
   AR_states_vis0_shadow nor AR_states_owned_ro) gives asan_cells, ro_agree and the cut's shadow region
   (A.ACtlRtC.cut_shadow), carried to normalize m by asan_cells_normalize / A.ShadowRwOnT.shadow_rw_on_normalize. *)
Lemma rt_facts_C : forall RLO RHI ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  A.Prog.CtrlBase.arodata_okP AB1v.tfibsegs RLO RHI B (aview AB1v.tfibsegs (YA0n.w_H W) m) ->
  ro_agree rsegs m /\ asan_cells (normalize rsegs m) /\
  A.ShadowRwOn.shadow_rw_on (A.ACtlRtC.cut_shadow B ly S) (normalize rsegs m).
Proof.
  intros RLO RHI ly S W m md HAR HRO.
  destruct (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TSY LAWS RLO RHI ly S W m md HAR HRO) as (AC & SC & _ & RO).
  assert (Hro : ro_agree rsegs m) by exact RO.
  split; [exact Hro|]. split; [exact (asan_cells_normalize m Hro AC) |].
  exact (A.ShadowRwOnT.shadow_rw_on_normalize _ m Hro SC).
Qed.

Lemma win_facts : forall ly S (W : YA0n.world AB1v.tfibsegs) m md lo hi,
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (YA0n.w_H W) m a) ->
  stk rsegs (normalize rsegs m) lo hi /\ addressable (normalize rsegs m) lo (hi - lo) /\
  HIGHMEM_BEG <= lo /\ hi <= APPMEM_END /\ lib.Reusable.YM05.alloc_ceiling <= lo.
Proof.
  intros ly S W m md lo hi HAR Hro Hlo Hle Hhi Hp.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_stk_ceil _ LO) as SC. pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold ASAN_CEIL in SC.
  split; [|split; [|split; [|split]]].
  - apply stk_normalize_ro; [exact Hro | unfold ImgBounds.IMG_HI; lia |].
    apply (A.ProgWorld_Fs.pw_stk_of_present W); [lia | unfold kHighMemEnd in T4; lia | exact Hp].
  - apply addressable_normalize; [exact Hro|].
    exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS ly S W m md lo (hi - lo) HAR Hlo ltac:(lia) ltac:(lia)).
  - unfold HIGHMEM_BEG. lia.
  - unfold APPMEM_END. unfold kHighMemEnd in T4. lia.
  - lia.
Qed.

(* The side-stack premise fp moved to the normalized memory (the side stack is above the image). *)
Lemma asan_tls_cells_normalize : forall m TP DT TS C T DB k, ro_agree rsegs m ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells (normalize rsegs m) TP DT TS C T DB k.
Proof.
  intros m TP DT TS C T DB k Hro H. unfold asan_tls_cells in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 &
                 H17 & H18 & H19).
  repeat (split; [first [apply bytes_at_normalize; [exact Hro | assumption] | assumption] |]).
  split; [exists tb, te; apply bytes_at_normalize; [exact Hro | assumption]|].
  repeat (split; [first [apply bytes_at_normalize; [exact Hro | assumption] | assumption] |]).
  apply bytes_at_normalize; [exact Hro | assumption].
Qed.

(* The converse direction (the cells read at the normalized memory are the real memory's), for ctrl_lay_block_tls. *)
Lemma asan_tls_cells_unnormalize : forall m TP DT TS C T DB k, ro_agree rsegs m ->
  asan_tls_cells (normalize rsegs m) TP DT TS C T DB k -> asan_tls_cells m TP DT TS C T DB k.
Proof.
  intros m TP DT TS C T DB k Hro H. pose proof (mem_rel_normalize rsegs m Hro) as REL.
  unfold asan_tls_cells in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 &
                 H17 & H18 & H19).
  repeat (split; [first [apply (proj2 (bytes_at_rel rsegs _ _ _ _ REL)); assumption | assumption] |]).
  split; [exists tb, te; apply (proj2 (bytes_at_rel rsegs _ _ _ _ REL)); assumption|].
  repeat (split; [first [apply (proj2 (bytes_at_rel rsegs _ _ _ _ REL)); assumption | assumption] |]).
  apply (proj2 (bytes_at_rel rsegs _ _ _ _ REL)); assumption.
Qed.

Lemma fp_normalize : forall cs m TP FS lo hi Wr D, ro_agree rsegs m ->
  fp cs m TP FS lo hi Wr D -> fp cs (normalize rsegs m) TP FS lo hi Wr D.
Proof.
  intros cs m TP FS lo hi Wr D Hro (DT & TS & C & T & DB & k & HT & HTP & HPl & H88 & H96 & HC & Hlo & Happ & HdW & HdD).
  pose proof HPl as (P1 & P2 & P3 & P4 & P5).
  exists DT, TS, C, T, DB, k.
  split; [exact (asan_tls_cells_normalize _ _ _ _ _ _ _ _ Hro HT)|].
  split; [apply bytes_at_normalize; assumption|].
  split.
  { split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    apply stk_normalize_ro; [exact Hro | unfold ImgBounds.IMG_HI; unfold ASAN_GT in P3; lia | exact P5]. }
  split; [apply bytes_at_normalize; assumption|].
  split; [apply bytes_at_normalize; assumption|].
  split; [|exact (conj Hlo (conj Happ (conj HdW HdD)))].
  eapply Forall_impl; [|exact HC]. intros c (Hc6 & h & flags & Hh & Hf & Hl & Hb).
  split; [exact Hc6|]. exists h, flags.
  split; [apply bytes_at_normalize; assumption|]. split; [apply bytes_at_normalize; assumption|]. split; assumption.
Qed.

(* FP0 of ctrl_lay_block at the normalized memory of a cut: ctl_fp_of_AR (ProgWorld_Fs.v, proved) with cs = [0; 1],
   the window [sp - 4512, sp) and ctrl_lay_block_W / ctrl_lay_block_D (ctrl_lay_block_c.v:19-20): the window is in
   the stack (above the ceiling, so above every allocator extent), f in the image (below the side stack), the
   32-byte block in a live frame of class >= 2 (C_ctrl_lay_block.v tfr_hull: past the class-0 and class-1 areas,
   apart from the other allocator extents by layout_ok's lo_disj). *)
Lemma lay_fp0_facts : forall ly S (W : YA0n.world AB1v.tfibsegs) m md (sp p f : Z),
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  lib.Reusable.YM05.alloc_ceiling <= sp - 4512 -> sp <= APPMEM_END ->
  0 <= f -> f + 24 <= ASAN_GT ->
  (exists cid pos, In (cid, pos) (frames S) /\ 2 <= cid /\
     forall x, p + 18 <= x < p + 50 -> in_zr x (frame_rng ly (cid, pos))) ->
  fp [0%nat; 1%nat] (normalize rsegs m) RT_TP (ly_F ly) (sp - 4512) sp
    (ctrl_lay_block_W p sp) (ctrl_lay_block_D p f).
Proof.
  intros ly S W m md sp p f HAR Hro Hc Hsp Hf0 Hf1 (cid & pos & Hin & Hcid & Hx).
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR) as HGT. unfold ASAN_GT in HGT.
  assert (EXT : forall e, In e (owned_extents ly) -> 4096 <= fst e /\ fst e + snd e <= lib.Reusable.YM05.alloc_ceiling).
  { intros e He. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [E0 E1].
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in E1. lia. }
  destruct (EXT (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F0 F1].
  destruct (EXT (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [T0 T1].
  destruct (EXT (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as [CC0 CC1].
  destruct (EXT (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as [D0 D1].
  cbn [fst snd] in F0, F1, T0, T1, CC0, CC1, D0, D1.
  pose proof (lo_disj _ LO) as LD.
  assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize))
    by exact (pairwise_In2 zdisjoint _ _ _ [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv)] []
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
                 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize)]
                [(ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)]
                [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  unfold zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  assert (Etsd : ly_tsd ly = 0x5fcbb8) by (rewrite (am_tsd _ _ _ _ M), (A.AF0m.ts_tsd B TSY); reflexivity).
  assert (ET : bv_unsigned (Z_to_bv 64 (ly_T ly)) = ly_T ly)
    by (apply A.ProgWorld_Fs.pw_u64; unfold kThreadObjSize in T1; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ly_D ly)) = ly_D ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (ly_C ly)) = ly_C ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 0x5fcbb8) = 0x5fcbb8) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (apply A.ProgWorld_Fs.pw_u64; unfold RT_TP; lia).
  (* the block's range: inside the fake stack, past the class-0 and class-1 frame areas *)
  assert (OB : ly_F ly + kFakeFramesOff + 2 * 2 ^ 20 <= p + 18 /\ p + 50 <= ly_F ly + kFakeStackSize).
  { destruct (YG0s.frame_facts B ly S _ cid pos M Hin) as (Q1 & Q2 & _ & _ & _ & Q6 & Q7 & _).
    pose proof (Hx (p + 18) ltac:(lia)) as X0. pose proof (Hx (p + 49) ltac:(lia)) as X1.
    unfold in_zr, frame_rng, frame_addr in X0, X1. cbn [fst snd] in X0, X1.
    assert (cid * 2 ^ 20 >= 2 * 2 ^ 20) by nia. lia. }
  apply fp_normalize; [exact Hro|].
  apply (A.ProgWorld_Fs.ctl_fp_of_AR B TSY LAWS ly S W m md [0%nat; 1%nat] (sp - 4512) sp _ _ HAR).
  - repeat constructor.
  - unfold FS_SIZE, kFakeStackSize in *. lia.
  - intros a Ha. unfold app_mem, HIGHMEM_BEG. right. lia.
  - unfold fp_dj, ctrl_lay_block_W, fp_tls, CTRL_LAY_BLOCK_K.
    rewrite Etsd. rewrite ?ET, ?ED, ?EC, ?ETS, ?EDT.
    unfold TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF,
      RT_TP.
    assert (EF00 : fs_frame (ly_F ly) 0%nat 0 = ly_F ly + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    rewrite EF00. unfold kFakeFramesOff, kFakeStackSize, kThreadObjSize in *.
    cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd]; lia.
  - unfold fp_dj, ctrl_lay_block_D, fp_w, fp_w1. cbn [flat_map app].
    unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat].
    unfold shadow_addr, ASAN_K, kFakeFramesOff, kFakeStackSize in *.
    destruct (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize)
                ltac:(unfold owned_extents; cbn; tauto)) as [FA0 FA1].
    cbn [fst snd] in FA1. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in FA1.
    unfold ASAN_GT in Hf1.
    cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
    all: Z.div_mod_to_equations; lia.
Qed.

(* TLS0 of ctrl_lay_block at the normalized memory: the cells read there are the real memory's
   (asan_tls_cells_unnormalize), apart from the side stack's class bytes and the window's shadow by ProgWorld's
   fp_tls_apart_stmt (proved: A.ProgWorldTlsApart.fp_tls_apart). *)
Lemma lay_tls0_facts : A.ProgWorld.fp_tls_apart_stmt B ->
  forall ly S (W : YA0n.world AB1v.tfibsegs) m md lo hi,
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  ctrl_lay_block_tls (normalize rsegs m) RT_TP (ly_F ly) lo hi.
Proof.
  intros TLSAP ly S W m md lo hi HAR Hro Hlo Hhi DT TS C T DB k HT.
  exact (TLSAP TSY LAWS ly S W m md [0%nat; 1%nat] lo hi HAR ltac:(repeat constructor) Hlo Hhi DT TS C T DB k
           (asan_tls_cells_unnormalize m _ _ _ _ _ _ _ Hro HT)).
Qed.
End Base.
End LayBase.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Context {LS : lib.Reusable.YO09.lib_shape}.

Section d.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).

Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.
(* cgif YC20.v:56, exactly this name (brief, rule for a walk that carries arodata_okS across a call) *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.

(* ---- cgif core rules and the bundle (owner: the core / the composition) ---- *)
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis TLF : PALibF B.
(* the composition fixes B := CtrlB with CtrlB_syms (A/AD2l.v:72); ProgWorld's AR statements take it *)
Hypothesis CTS : A.AF0m.CtrlTSyms B.
Hypothesis HWX : wx_segs_nowrap SEGS.

(* ---- a Theorem Labs lane's named top-level statement still carried (a Theorem Labs lane 14:08Z; a Theorem Labs lane's four realizations pending) ---- *)
Hypothesis stack_malloc_classes : A.ProgWorld.stack_malloc_classes B.

(* ---- the class-1 release law over the generic SK is a theorem: A.ProgWorldAstack.ctl_release_of_free_law
   (lib/A/ProgWorldAstack.v:333, Section Fs with {SK} at :158; a working branch 170335f992e). ---- *)

(* ---- the callee (a Theorem Labs lane), exactly its type ---- *)
Hypothesis TMB : treac_box_model_block_spec (SK := SK) B GLOBS (BASE + AF_reac_box_model_block) RLO RHI.

(* ---- a Theorem Labs lane's route (C) footprint contracts, applied INSIDE the region runs R2 / R3, exactly their types ---- *)
Hypothesis MEMSF : asan_memset_cF_on.asan_memset_contract_F_on.
Hypothesis MEMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.

(* ---- facts of the image alone (discharged from the image by vm_compute; none reads a start-up table value) ---- *)
(* the registered globals' shadow encoding (CtrlRo.v:116), as a Theorem Labs lane's TMB contract takes it *)
Hypothesis HGM : globs_marked SEGS B GLOBS.
(* ProgWorld's thread-cell apartness and heap-block apartness are theorems (A.ProgWorldTlsApart.fp_tls_apart,
   A.ProgWorldBlkApart.ctl_block_apart_fs; a working branch 87fcd8d0b28). *)
(* CTRL_FRAMES (object 21, 11 rows of 24 bytes) and BOX_CATALOGUE (object 17, 11 rows of 296 bytes): registered
   globals, in the image, read-only (in_roP: PT_GNU_RELRO), not owned, not errno; the rows' bytes are the image's. *)
Hypothesis HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS.
Hypothesis HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS.
Hypothesis HFR_rng : A.Prog.ImgBounds.IMG_LO <= VAL (A_OBJ A_FRAMES) /\
  VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES <= A.Prog.ImgBounds.IMG_HI /\ VAL (A_OBJ A_FRAMES) mod 8 = 0.
(* the catalogue's rows lie 64 bytes inside the image on both sides (TMB's row premise, C_reac_box_model_block.v:152) *)
Hypothesis HCAT_rng : A.Prog.ImgBounds.IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\
  VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= A.Prog.ImgBounds.IMG_HI /\ VAL (A_OBJ A_CAT) mod 8 = 0.
Hypothesis HFR_ro : forall x, VAL (A_OBJ A_FRAMES) <= x < VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Hypothesis HCAT_ro : forall x, VAL (A_OBJ A_CAT) <= x < VAL (A_OBJ A_CAT) + 11 * CAT_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
(* row r of CTRL_FRAMES, for the rows the contract allows (3 <= r <= 9): its 24 image bytes, kind byte r *)
Hypothesis HFR_rom : forall r, 3 <= r <= 9 -> exists fr : list byte,
  length fr = 24%nat /\ RcLay.ly_k fr = r /\
  forall i, (i < 24)%nat -> exists b, nth_error fr i = Some b /\
    lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)) = Some b.

Lemma lay_K_val : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512.
Proof. reflexivity. Qed.

Lemma lay_TLAY_val : TLAY_STK = 4512.
Proof. reflexivity. Qed.

Lemma pc_sm1 : pc_stack_malloc (as_code B) 1 = 0x3d72c.
Proof. rewrite <- (palf_sm1 B TLF). vm_compute. reflexivity. Qed.

(* ================================================================================================================
   Image and view helpers: the read-only window carried across the run, the registered globals' bytes and shadow.
   ================================================================================================================ *)
Lemma lay_img_below : forall a, in_img SEGS a -> a < A.Prog.ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hin & Hb). pose proof A.MemNormTr.rsegs_below_img as H.
  unfold A.MemNormTr.seg_ends_below in H. rewrite forallb_forall in H. specialize (H sg Hin).
  apply Z.leb_le in H. lia.
Qed.

(* arodata_okS of a later view: the view is kept at every image byte that is not owned and not errno (the image
   clause of acall_kept / tcj_kept, YCbq.v:829-830, CtrlCallerJ.v:46-47; a stretch writes above the image); RELRO_IMG
   puts the relro window in the image. *)
Lemma lay_arodata_kept : forall (rd rd' : Z -> option Z),
  YE01.arodata_okS SEGS B RLO RHI rd ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rd' a = rd a) ->
  YE01.arodata_okS SEGS B RLO RHI rd'.
Proof.
  intros rd rd' H Hk a Ha Ho He. rewrite (Hk a); [exact (H a Ha Ho He) | | exact Ho | exact He].
  destruct Ha as [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)].
Qed.

(* A view kept across a write set that lies above the image. *)
Lemma lay_view_img_munch : forall (W : world SEGS) m m' (WR : list lib.Lib.Frame.ivl),
  lib.Lib.Frame.munch WR m m' ->
  (forall a, a < A.Prog.ImgBounds.IMG_HI -> lib.Lib.Frame.outside WR a) ->
  forall a, in_img SEGS a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
  intros W m m' WR HM HO a Ha. pose proof (lay_img_below a Ha) as Hb. pose proof (A.ProgWorld.pws_segs_low a Ha) as Hl.
  apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  unfold kLowMemEnd in Hl. rewrite Z.mod_small by lia. exact (HO a Hb).
Qed.

Lemma lay_le_byte1 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 (le_byte v 1 0)) = v.
Proof.
  intros v Hv.
  assert (E : le_byte v 1 0 = v).
  { unfold le_byte. rewrite Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
    rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia.
    apply Z.mod_small. lia. }
  rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

Lemma lay_garr8_view : forall (H : word -> bool) (m : word -> option byte) base (l : list Z) j,
  garr8 SEGS (mrestrict H m) base l -> (j < length l)%nat ->
  aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H m base l j G Hj. destruct (G j Hj) as (V & R).
  specialize (V 0%nat ltac:(lia)). replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in V by lia.
  unfold aview. rewrite V. cbn [option_map]. f_equal. exact (lay_le_byte1 _ R).
Qed.

Lemma lay_bytes_of_view : forall (W : world SEGS) (m : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, (j < length bs)%nat -> aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j (bmb_z bs) 0)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs.
Proof.
  intros W m a bs H0 H1 Hv. apply (A.ProgWorld_Fs.pw_bytes_of_view W m a bs H0 H1).
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  exists b. split; [reflexivity|]. rewrite (Hv i Hi). f_equal. unfold bmb_z.
  rewrite (nth_indep (map _ bs) 0 (bv_unsigned b)) by (rewrite length_map; exact Hi).
  rewrite map_nth. rewrite (nth_error_nth bs i b E). reflexivity.
Qed.

(* Bytes given by garr8 at one view, read at a later memory whose view agrees on them. *)
Lemma lay_view_kept_bytes : forall (W W' : world SEGS) m m' a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a (bmb_z bs) ->
  (forall j, (j < length bs)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros W W' m m' a bs H0 H1 G K. apply (lay_bytes_of_view W' m' a bs H0 H1).
  intros j Hj. rewrite (K j Hj). apply lay_garr8_view; [exact G | unfold bmb_z; rewrite length_map; exact Hj].
Qed.

(* Row r of CTRL_FRAMES at any memory whose view satisfies the read-only premise. *)
Lemma lay_row_bytes : forall (W : world SEGS) m r fr,
  YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) m) -> 3 <= r <= 9 -> length fr = 24%nat ->
  (forall i, (i < 24)%nat -> exists b, nth_error fr i = Some b /\
     lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)) = Some b) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) fr.
Proof.
  intros W m r fr HRO Hr Hl Hb. destruct HFR_rng as (R1 & R2 & R3). unfold ROW_BYTES in *.
  unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in R1, R2.
  apply (A.ProgWorld_Fs.pw_bytes_of_view W m); [lia | rewrite Hl; lia |].
  intros i Hi. rewrite Hl in Hi. destruct (Hb i Hi) as (b & E & Hs). exists b. split; [exact E|].
  assert (Hi' : 0 <= Z.of_nat i < 24) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hi; exact Hi]).
  assert (Hx : VAL (A_OBJ A_FRAMES) <= VAL (A_OBJ A_FRAMES) + 24 * r + Z.of_nat i <
               VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES) by (unfold ROW_BYTES; split; nia).
  destruct (HFR_ro (VAL (A_OBJ A_FRAMES) + 24 * r + Z.of_nat i) Hx) as (H1 & H2 & H3).
  rewrite (HRO _ H1 H2 H3). rewrite Hs. reflexivity.
Qed.

(* A registered global's body is addressable (its shadow encoding, globs_marked; as ProgWorldShadow's
   ctl_block_shadow_of_AR reads a block's). *)
Lemma lay_glob_addressable : forall ly S (W : world SEGS) m md q sz lo len,
  AR SEGS B ly S W m md -> In (q, sz) GLOBS -> 0 <= lo ->
  q <= lo -> 0 <= len -> lo + len <= q + sz -> lo + len <= A.AsanRT.LOWMEM_END ->
  A.AsanRT.addressable m lo len.
Proof.
  intros ly S W m md q sz lo len HAR Hin Hq0 Hlo Hlen Hhi Hlow.
  destruct (HGM ly S W m md q sz Hin HAR) as (Hq8 & Hsz & Hsh).
  unfold A.AsanRT.addressable. split; [lia|]. split; [exact Hlen|].
  split; [unfold A.AsanRT.APPMEM_END, A.AsanRT.LOWMEM_END in *; lia|].
  intros i Hi. unfold A.AsanRT.addr_byte. split.
  - unfold A.AsanRT.app_mem. left. lia.
  - assert (Hj : 0 <= (lo + i - q) / 8 < (sz + 7) / 8) by (clear Hsh; Z.div_mod_to_equations; lia).
    specialize (Hsh _ Hj). rewrite (A.ProgWorldShadow.pwsh_shadow_eq q (lo + i) Hq8) in Hsh.
    destruct (A.ProgWorldShadow.pwsh_view_mrd W m _ _ Hsh) as (b & Hb & Hbu).
    exists b. split; [exact Hb|].
    assert (Hsm : bv_unsigned b < 128) by (rewrite Hbu; destruct (_ <? _); [lia | clear Hsh; Z.div_mod_to_equations; lia]).
    unfold A.AsanRT.shadow_ok. rewrite (A.ProgWorldShadow.pwsh_byte_signed_small b Hsm), Hbu.
    destruct (Z.ltb_spec ((lo + i - q) / 8) (sz / 8)) as [Hl | Hl].
    + left. reflexivity.
    + right. clear Hsh. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). Z.div_mod_to_equations; lia.
Qed.

(* The shadow bytes of n whole granules of a registered global are visible. *)
Lemma lay_glob_shvis : forall ly S (W : world SEGS) m md q sz lo n,
  AR SEGS B ly S W m md -> In (q, sz) GLOBS -> 0 <= lo -> q <= lo -> lo mod 8 = 0 -> 0 <= n ->
  lo + 8 * n <= q + sz -> lo + 8 * n <= A.AsanRT.LOWMEM_END ->
  A.ProgBridge.range_visible (w_H W) (A.AsanRT.shadow_addr lo) n.
Proof.
  intros ly S W m md q sz lo n HAR Hin Hq0 Hlo Hl8 Hn Hhi Hlow.
  destruct (HGM ly S W m md q sz Hin HAR) as (Hq8 & Hsz & Hsh).
  unfold A.AsanRT.LOWMEM_END in Hlow.
  unfold A.ProgBridge.range_visible, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  split; [clear Hsh; Z.div_mod_to_equations; lia|]. split; [clear Hsh; Z.div_mod_to_equations; lia|]. intros a Ha.
  assert (Hj : 0 <= (lo - q) / 8 + (a - (lo / 8 + 2147450880)) < (sz + 7) / 8) by (clear Hsh; Z.div_mod_to_equations; lia).
  specialize (Hsh _ Hj).
  replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF q + ((lo - q) / 8 + (a - (lo / 8 + 2147450880))))
    with a in Hsh.
  - apply (A.ProgWorldVisFrame.vis_of_aview SEGS W m a). rewrite Hsh. discriminate.
  - unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF. clear Hsh. Z.div_mod_to_equations; lia.
Qed.

(* ================================================================================================================
   3. The allocator event at 0x3d72c (class 1), as YC85.aj_stack_malloc_atS (YC85.v:291-375) with the same proof, whose
   post hands on, in place of YC85's journal of the call alone (YC85.v:308), what A.ProgWorldAstack.ctl_fs_of_astack takes from astack_malloc_realizes: ecall_pre at the
   call, AR at the new state, the realizes post's frame condition (YG0d.v:298-299) and the window presence
   (YG0d.v:300).
   fuzz_grant overlap: the fake-stack frame at 0x85668 is the twin of grant's CtrlLayBlock.v class-1 frame
   (a working branch 5aae1e8a0ce).
   ================================================================================================================ *)
Lemma lay_stack_malloc_atS : forall cid, astack_malloc_realizes SEGS B cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  rget regsT 3 = w64 (as_gp B) -> rget regsT 4 = w64 (as_tp B) ->
  rget regsT 1 = raw -> lib.Reusable.YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr SEGS W (mkCfg (rmkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (lib.Reusable.YK11.seg_rom SEGS))
                    mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
      c2 = mkCfg (rmkst regs2 raw mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
      ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
      aregs_preserved regsT regs2 /\ rget regs2 10 = w64 (frame_addr lyc cid pos) /\
      ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
      st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
      zero_shadow (aview SEGS (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
      rdword (aview SEGS (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) =
        Some (flag_addr lyc cid pos) /\
      acall_kept SEGS B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
      (exists f, S2 = set_fs f Sc) /\
      (* what ctl_fs_of_astack takes *)
      ecall_pre SEGS B lyc Sc W regsT memT mdc /\ AR SEGS B lyc S2 W mem2 md2 /\
      (forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) mem2 a) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a ->
         ~ (spZ regsT - ESTACK <= a < spZ regsT) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
  intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
    HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
  pose proof (pal_env B TL) as errno_low.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5
    & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
  assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
  { unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
    all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
  assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
  { split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
    split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
    split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
  pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
  destruct (SMP Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
  pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
  destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
  destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
  eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
  cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr
    & Hpres2).
  assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
  assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
  assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
  assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
  assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
  assert (HJ1 : ajournal (SK := SK) SEGS B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
  { eapply (call_effect_journal SEGS B LAWS A.ProgWorld.pws_segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W
              mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
      [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2
      | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
    - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
    - intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
    - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
  split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned;
          reflexivity|].
  split.
  { rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
    eapply (ajournal_sub SEGS B LAWS A.ProgWorld.pws_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
  split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
  split.
  { rewrite Hsp' in HJ1. eapply (acall_kept_of_journal SEGS B A.ProgWorld.pws_segs_low);
      [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
    intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
  split; [exists f; exact ES2|].
  split; [exact HPRE|]. split; [exact HAR2|]. split; [exact Hpres2 | exact Hfr].
Qed.

(* ================================================================================================================
   4. Region R1 and the allocator event: from the entry (cfg_at 0x855f4) to the return of __asan_stack_malloc_1 at
   0x8566c.  lay_F_R1_run (ctrl_lay_block_F_R1.v: stretch k = 1 + the jal) on the normalized entry memory, the
   journal step with its write set [(S - K, S)] (all window bytes), then the allocator (section 3) and
   A.ProgWorldAstack.ctl_fs_of_astack for the class-1 frame's bytes.  a Theorem Labs lane's bmb_to_ret
   (reac_box_model_block_glue.v:983-1121) takes the first three of these steps for class 0 (the run on the normalized entry memory, the journal step with write set [(S - 4272, S)], the allocator); in place of ctl_fs_of_astack it hands the allocator's zero_shadow and flag facts to its continuation, and bmb_frame_facts (:1394) derives the class-0 frame facts.
   fuzz_grant overlap: grant's proved prologue (CtrlLayBlock.v at a working branch 5aae1e8a0ce) is the twin of
   stretch k = 1 (same listing offsets).
   ================================================================================================================ *)
(* What a call keeps (acall_kept), after a stretch that wrote only a window of the machine stack: a Theorem Labs lane's
   acall_kept_after_munch (reac_box_model_block_glue.v:551-585), same proof. *)
Lemma lay_acall_kept_after_munch : forall lyc Sc (W : world SEGS) (memc mem1 mem2 : word -> option byte)
    md (lo hi lo1 hi1 lo2 hi2 : Z) (E : Z -> Prop),
  AR SEGS B lyc Sc W memc md ->
  lib.Reusable.YM05.alloc_ceiling <= lo -> lo2 <= lo -> hi <= hi2 -> lo2 <= lo1 -> hi1 <= hi2 ->
  lib.Lib.Frame.munch [(lo, hi)] memc mem1 ->
  acall_kept SEGS B lyc Sc W mem1 W mem2 lo1 hi1 E ->
  (forall a, lo2 <= a < hi2 -> apresent (w_H W) mem2 a) ->
  acall_kept SEGS B lyc Sc W memc W mem2 lo2 hi2 E.
Proof.
  intros lyc Sc W memc mem1 mem2 md lo hi lo1 hi1 lo2 hi2 E HAR Hc H1 H2 H3 H4 HM (K1 & K2 & K3 & K4 & K5 & K6) Hp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
            aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hn. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn. rewrite (K1 a Ha ltac:(lia)). apply EQ; lia.
  - intros b0 m0 i Hin Hi HE. rewrite (K2 b0 m0 i Hin Hi HE).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HAR Hin) as (_ & Hb0 & Hb1 & _). apply EQ; lia.
  - intros a Hi Hs He. rewrite (K3 a Hi Hs He). pose proof (A.ProgWorld.pws_segs_low a Hi) as HL.
    unfold kLowMemEnd in HL. apply EQ; lia.
  - intros cid pos a Hin Hr HE. rewrite (K4 cid pos a Hin Hr HE).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + apply EQ; lia.
    + unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hr. pose proof asan_consts as (D1 & _).
      apply EQ; Z.div_mod_to_equations; lia.
  - intros a Ha Hn Hpr. apply (K5 a Ha ltac:(lia)).
    destruct Hpr as [Hh (bb & Hb)]. split; [exact Hh|]. exists bb. rewrite (HM (Z_to_bv 64 a)); [exact Hb|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
  - exact Hp.
Qed.

(* The callee-saved registers after the allocator returns: the values k = 1 left in them (lay_F_R1_post). *)
Definition lay_ret_regs (regs regs2 : bvmap 5 word) (A p f md : Z) : Prop :=
  rget regs2 2 = w64 A /\ rget regs2 3 = rget regs 3 /\ rget regs2 4 = rget regs 4 /\
  rget regs2 8 = rget regs 2 /\ rget regs2 9 = w64 A /\ rget regs2 18 = rget regs 18 /\
  rget regs2 19 = w64 0 /\ rget regs2 20 = w64 f /\ rget regs2 21 = rget regs 21 /\
  rget regs2 22 = w64 md /\ rget regs2 23 = w64 p /\ rget regs2 24 = rget regs 24 /\
  rget regs2 25 = rget regs 25 /\ rget regs2 26 = w64 A.AsanRT.ASAN_K /\ rget regs2 27 = rget regs 27.

(* ctl_fs_of_astack's conclusion for the class-1 frame (ProgWorld.v:465-480 at cid = 1), on the memory after the
   allocator; lo := S - K, the bottom of the window (rebase plan, R2 table, FK row). *)
Definition lay_fs1 (FS pos lo S2sp : Z) (a0 : word) (mem' : word -> option byte) : Prop :=
  let fr := asan_stack_malloc_c.fs_frame FS 1 pos in
  let n := asan_stack_malloc_c.fs_B 1 in
  0 <= pos < asan_stack_malloc_c.fs_M 1 /\
  a0 = Z_to_bv 64 fr /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (asan_stack_malloc_c.fs_flag FS 1 pos) (Z_to_bv 8 1 :: nil) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (fr + n - 8) (lib.Lib.Mem.le8 (Z_to_bv 64 (asan_stack_malloc_c.fs_flag FS 1 pos))) /\
  lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (A.AsanRT.shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))) /\
  A.AsanRT.addressable mem' fr (lib.Reusable.YG00.fs_frame_bytes 1) /\
  lib.Lib.Frame.stk A.Img0.rsegs mem' fr (fr + n) /\
  (forall a, fr <= a < fr + n -> A.AsanRT.app_mem a) /\
  fr mod 64 = 0 /\ FS <= fr /\ fr + n <= FS + asan_stack_malloc_c.FS_SIZE /\
  asan_stack_malloc_c.ASAN_GT <= fr /\
  lib.Lib.Frame.stk A.Img0.rsegs mem' lo S2sp.

Lemma lay_to_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (p f md : Z) (Q : world SEGS -> config -> Prop),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  lib.Reusable.YK0s.ret_ok (rget regs 1) -> rget regs 3 = w64 (as_gp B) -> rget regs 4 = w64 (as_tp B) ->
  rget regs 10 = w64 p -> rget regs 11 = w64 f -> rget regs 12 = w64 md -> rget regs 13 = w64 0 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 ->
  A.MemNorm.ro_agree A.Img0.rsegs memc ->
  A.AsanRT.asan_cells (A.MemNorm.normalize A.Img0.rsegs memc) ->
  (forall S2 regs2 mem2 md2 pos,
     ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
     frames S2 = (1, pos) :: frames Sc -> ~ In (1, pos) (frames Sc) -> ablocks B lyc S2 = ablocks B lyc Sc ->
     (exists fS, S2 = set_fs fS Sc) ->
     AR SEGS B lyc S2 W mem2 md2 ->
     rget regs2 10 = w64 (frame_addr lyc 1 pos) ->
     lay_ret_regs regs regs2 ((spZ regs - 128) / 32 * 32) p f md ->
     lay_fs1 (ly_F lyc) pos (spZ regs - 4512) ((spZ regs - 128) / 32 * 32) (rget regs2 10) mem2 ->
     acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - TLAY_STK) (spZ regs) (fun _ => False) ->
     lib.Lib.Step.rw_cells A.Img0.rsegs mem2 (spZ regs - 96)
       (ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18) (rget regs 19) (rget regs 20)
          (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25) (rget regs 26)) ->
     SRr SEGS W (mkCfg (rmkst regs2 (w64 0x8566c) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (cfg_at SEGS 0x855f4 regs memc mdc) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p f md Q HJ Hra Hgp Htp Ha0 Ha1 Ha2 Ha3
    Hal Hlo Hhi Hroom Hro AC0 K.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5
    & HQT).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite lay_TLAY_val in Hlo.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR)) as LO.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  set (A := (spZ regs - 128) / 32 * 32) in *.
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  (* the window [S - K, S): visible, present; stk on the normalized memory *)
  assert (RWIN : lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (w_H W)) (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
                   ctrl_lay_block_c.CTRL_LAY_BLOCK_K).
  { rewrite lay_K_val. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (STKc : lib.Lib.Frame.stk A.Img0.rsegs memc (spZ regs - 4512) (spZ regs)).
  { apply (A.ProgWorld_Fs.pw_stk_of_present W); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  assert (ST0 : lib.Lib.Frame.stk A.Img0.rsegs (A.MemNorm.normalize A.Img0.rsegs memc)
                  (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs)).
  { rewrite lay_K_val. apply A.MemNormTr.stk_normalize_ro; [exact Hro | | exact STKc].
    unfold A.Prog.ImgBounds.IMG_HI. lia. }
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
    by (unfold A.AsanRT.HIGHMEM_BEG; rewrite lay_K_val; lia).
  assert (HAE : spZ regs <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  pose proof (A.ProgBridge.img_vis_W W) as VIMG.
  assert (RIMG : forall lo len, A.Prog.ImgBounds.IMG_LO <= lo -> 0 <= len -> lo + len <= A.Prog.ImgBounds.IMG_HI ->
                   lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (w_H W)) lo len).
  { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ VIMG); lia. }
  change (rget regs 10) with (reg_get regs 10) in Ha0.
  change (rget regs 11) with (reg_get regs 11) in Ha1.
  change (rget regs 12) with (reg_get regs 12) in Ha2.
  change (rget regs 13) with (reg_get regs 13) in Ha3.
  rewrite (A.ProgBridge.cfg_at_MS SEGS).
  apply (YA0nR.SRr_xregs_eqv SEGS W (lib.Lib.Regs6ss.mkR_of regs) regs);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs))].
  unfold lib.Lib.Regs6ss.mkR_of. rewrite Ha0, Ha1, Ha2, Ha3.
  refine (lay_SRr_norm HWX W (A.ProgBridge.RNG_W (w_H W)) mdc _ lib.Reusable.YK11.fp_regs _ lib.Reusable.YK11.fp_csr
            memc
            (ctrl_lay_block_F_R1.lay_F_R1_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
               (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
               (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
               (A.MemNorm.normalize A.Img0.rsegs memc) p f md 0)
            Q (A.ProgBridge.fp_avoids_RNG_W _) Hro _ _).
  { apply (ctrl_lay_block_F_R1.lay_F_R1_run (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
             (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
             (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
             (A.MemNorm.normalize A.Img0.rsegs memc) p f md 0
             ST0 (A.MemNorm.mem_inv_normalize A.Img0.rsegs memc) AC0 HHM HAE).
    - exact RWIN.
    - apply RIMG; unfold A.AsanRT.GOT_CELL_K, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia.
    - apply RIMG; unfold A.AsanRT.CELL_K, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia.
    - apply RIMG; unfold A.AsanRT.GOT_UAR, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia.
    - apply RIMG; unfold A.AsanRT.UAR, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  intros ms1 model1 Hrun1 (s1' & HP1 & HREL1 & HROS1) Hhid1 Hsame1.
  destruct HP1 as (t0' & t1' & t2' & a1' & a2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mg & Es1 & MU & WM & RM
    & MI & FR).
  subst s1'.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL1) as [Ems1 HMR1].
  assert (HMU1 : lib.Lib.Frame.munch [(spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K, spZ regs)] memc (ms_mem ms1))
    by exact (A.MemNorm.munch_rel A.Img0.rsegs _ memc (A.MemNorm.normalize A.Img0.rsegs memc) (ms_mem ms1) mg
               (A.MemNorm.mem_rel_normalize A.Img0.rsegs memc Hro) HMR1 HROS1 MU).
  assert (HJ1 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) model1 k).
  { lazymatch type of Hrun1 with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS HWX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W ms0 ms1 mdc model1 k
                _ _ HJ Hrun1
                (A.ProgBridge.fp_avoids_RNG_W _) HMU1 Hsame1 _) end.
    intros a Ha Hout. left. cbn [lib.Lib.Frame.outside] in Hout. rewrite lay_K_val in Hout. lia. }
  rewrite Ems1. clear Ems1.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  rewrite lay_K_val in HMU1.
  (* the allocator event, class 1 (section 3) *)
  lazymatch goal with |- SRr _ _ {| cfg_ms := lib.Lib.MState.MS ?R _ _ _ _ ?mm _; cfg_model := _ |} _ =>
    set (regsT := R) in *; set (mem1 := mm) in * end.
  replace (Z_to_bv 64 asan_stack_malloc_c.ASAN_STACK_MALLOC_1) with (Z_to_bv 64 (pc_stack_malloc (as_code B) 1))
    by (rewrite pc_sm1; reflexivity).
  change (SRr SEGS W (mkCfg (rmkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) 1)) mem1
            (lib.Reusable.YK11.seg_rom SEGS)) model1) Q).
  change (rget regs 3) with (reg_get regs 3) in Hgp. change (rget regs 4) with (reg_get regs 4) in Htp.
  assert (EspT : spZ regsT = A).
  { unfold spZ. change (rget regsT 2) with (Z_to_bv 64 A). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  eapply SRr_bind.
  { refine (lay_stack_malloc_atS 1 (stack_malloc_classes 1 (or_intror (or_introl eq_refl))) ltac:(lia) W regsT mem1
              STK sp0 FP ly S W0 mem0 md0 own lyc Sc model1 k (A - sp0) (Z_to_bv 64 0x8566c) HJ1 _ _ _ _ _ _
              eq_refl _ Hroom).
    - rewrite EspT. lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - unfold ESTACK. lia.
    - exact Hgp.
    - exact Htp.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha02 & Eab & Hfrs2 & Hnin & Hnev2 &
    Hbb2 & Hz & Hflag & HK & HfS & HPRE & HAR2 & Hpres2 & Hfr).
  replace (sp0 + (A - sp0) - ESTACK) with (A - 4096) in HK by (unfold ESTACK; lia).
  replace (sp0 + (A - sp0)) with A in HK by lia.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ2 & _).
  rewrite EspT in Hpres2, Hfr.
  (* the class-1 frame's bytes: A.ProgWorldAstack.ctl_fs_of_astack at cid = 1, lo := S - K *)
  assert (HFS : lay_fs1 (ly_F lyc) pos (spZ regs - 4512) A (rget regs2 10) mem2).
  { pose proof (A.ProgWorldAstack.ctl_fs_of_astack B 1 A.ProgWorld.ctl_fs_geom LAWS ltac:(lia) lyc Sc S2 W regsT regs2
                  mem1 mem2 model1 md2 pos (spZ regs - 4512) (lib.Reusable.YG00.fs_frame_bytes 1) HPRE) as H.
    rewrite EspT in H.
    unfold lay_fs1. apply H; clear H.
    - rewrite Eslo. lia.
    - unfold ESTACK. lia.
    - intros a Ha. apply Hpres1. unfold ESTACK in Ha. lia.
    - exact Hfrs2.
    - exact Hnin.
    - exact HAR2.
    - exact Ha02.
    - exact Hz.
    - exact Hflag.
    - exact Hpres2.
    - exact Hfr.
    - split; [vm_compute; discriminate | lia]. }
  apply (K S2 regs2 mem2 md2 pos HJ2 Hfrs2 Hnin Eab HfS HAR2 Ha02).
  - unfold lay_ret_regs.
    assert (P : forall r, acallee_saved r -> rget regs2 (Z_to_bv 5 r) = rget regsT (Z_to_bv 5 r)) by exact HP2.
    repeat split.
    all: lazymatch goal with
         | |- rget _ ?n = _ =>
             let z := eval vm_compute in (bv_unsigned n) in
             transitivity (rget regsT (Z_to_bv 5 z)); [exact (P z ltac:(unfold acallee_saved; lia)) | reflexivity]
         end.
  - exact HFS.
  - rewrite lay_TLAY_val.
    apply (lay_acall_kept_after_munch lyc Sc W memc mem1 mem2 mdc (spZ regs - 4512) (spZ regs) (A - 4096) A
             (spZ regs - 4512) (spZ regs) (fun _ => False) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             HMU1 HK).
    intros a Ha. apply HpresJ2. lia.
  - apply (LayLib.rw_cells_agree mem1).
    + exact (A.MemNormTr.rw_cells_of_rel _ _ _ _ HMR1 FR).
    + intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_block.SAVES] in Hi.
      pose proof (proj1 (HpresJ2 (spZ regs - 96 + i) ltac:(lia))) as Hv.
      apply (LayLib.raw_of_aview W mem1 mem2); [lia | exact Hv | apply LayLib.above_ceil_not_img; lia |].
      pose proof HK as (K1 & _). apply K1; lia.
Qed.

(* ================================================================================================================
   5. Region R2 (0x8566c, the return of __asan_stack_malloc_1, -> the entry of reac_box_model_block 0x85b44 with
   ra = 0x85828): a Theorem Labs lane's route (C) twin lay_F_R2_run_on (ctrl_lay_block_F_R2_on.v: re-based k2 + stretch k3 + the
   jal) on the normalized memory of the cut, its shadow region lay_F_R2_shadow_R from the cut's ctl_rt_C (lay_on_R_cut),
   the journal step with k2's exact write set (window, the class-1 frame's first 24 bytes and 12 of its
   shadow bytes, the 32-byte block: all awr), then the continuation at the callee entry.
   fuzz_grant overlap: the memset at 0x856f4 in k2 is the twin of grant's proved memset in CtrlLayBlock.v
   (a working branch 5aae1e8a0ce).
   ================================================================================================================ *)

(* Route (C): the shadow region the region runs R2 / R3 take (a Theorem Labs lane's lay_F_R2_shadow_R = lay_F_R3_shadow_R: the
   shadow of the class-1 block of the fake stack and the 8-aligned shadow-word cover of the 32-byte output block)
   lies in the fake-stack frames area, the (FA) disjunct of A.ACtlRtC.cut_shadow at any state of the layout.  The
   block is in a frame of class >= 2 (tfr_hull, via lay_blk_range), so past the class-1 area; the fake stack is
   page-aligned (lo_F_al), so the word cover of a byte below its end stays below its end. *)
Lemma lay_on_R_cut : forall ly S p a,
  ly_F ly mod 4096 = 0 ->
  ly_F ly + 36864 + 2097152 <= p + 18 -> p + 50 <= ly_F ly + 11571200 ->
  (asan_stack_malloc_c_on.asan_stack_malloc_shadow_R (ly_F ly) 1%nat a \/ sh_word_on.sh_word_on (p + 18) 32 a) ->
  A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S p a Hal H1 H2 Ha. right; right; right.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG0f.kFakeStackSize.
  set (FS := ly_F ly) in *. clearbody FS.
  destruct Ha as [Ha | (_ & Ha)].
  - unfold asan_stack_malloc_c_on.asan_stack_malloc_shadow_R, asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B,
      A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    cbn [Z.of_nat Pos.of_succ_nat] in Ha. change (2 ^ 20) with 1048576 in Ha. change (2 ^ 1) with 2 in Ha.
    clear - Ha. Z.div_mod_to_equations. lia.
  - unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    clear - Ha Hal H1 H2. Z.div_mod_to_equations. lia.
Qed.

(* Where the fake stack and the block lie (the block in a class >= 2 frame, tfr_hull). *)
Lemma lay_blk_range : forall ly S (W : world SEGS) m md p,
  AR SEGS B ly S W m md -> tfr_hull ly S (p + 18) 32 ->
  asan_stack_malloc_c.ASAN_GT <= ly_F ly /\ ly_F ly + kFakeStackSize <= lib.Reusable.YM05.alloc_ceiling /\
  ly_F ly + kFakeFramesOff + 2 * 2 ^ 20 <= p + 18 /\ p + 50 <= ly_F ly + kFakeStackSize /\
  exists cid pos, In (cid, pos) (frames S) /\ 2 <= cid /\
    forall x, p + 18 <= x < p + 50 -> in_zr x (frame_rng ly (cid, pos)).
Proof.
  intros ly S W m md p HAR (cid & pos & Hin & Hcid & H1 & H2).
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR) as HGT.
  destruct (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize)
              ltac:(unfold owned_extents; cbn; tauto)) as [E0 E1].
  cbn [fst snd] in E1. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in E1.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  destruct (YG0s.frame_facts B ly S _ cid pos M Hin) as (Q1 & Q2 & _ & _ & _ & Q6 & Q7 & Q8 & Q9 & Q10 & _).
  assert (FX : forall x, p + 18 <= x < p + 50 -> in_zr x (frame_rng ly (cid, pos))).
  { intros x Hx. unfold in_zr, frame_rng. cbn [fst snd]. clear -H1 H2 Hx. Z.div_mod_to_equations; lia. }
  pose proof (FX (p + 18) ltac:(lia)) as X0. pose proof (FX (p + 49) ltac:(lia)) as X1.
  unfold in_zr, frame_rng, frame_addr in X0, X1. cbn [fst snd] in X0, X1.
  assert (cid * 2 ^ 20 >= 2 * 2 ^ 20) by nia.
  unfold fs_frame_off, kStackSizeLog in *. rewrite Z.shiftl_1_l in *.
  split; [exact HGT|]. split; [unfold ASAN_CEIL in *; lia|]. split; [lia|]. split; [lia|].
  exists cid, pos. split; [exact Hin|]. split; [exact Hcid | exact FX].
Qed.

(* A view's range_addressable is the raw memory's addressable (the shadow bytes read through the view are mrd's). *)
Lemma lay_raddr_addressable : forall (W : world SEGS) m lo n,
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF lo n -> 0 <= lo -> 0 <= n ->
  (forall a, lo <= a < lo + n -> A.AsanRT.app_mem a) -> lo + n <= A.AsanRT.APPMEM_END ->
  A.AsanRT.addressable m lo n.
Proof.
  intros W m lo n HR H0 Hn Happ Htop. unfold A.AsanRT.addressable. split; [exact H0|]. split; [exact Hn|].
  split; [exact Htop|]. intros i Hi. unfold A.AsanRT.addr_byte. split; [apply Happ; lia|].
  destruct (HR (lo + i) ltac:(lia)) as (s & Hs & Hok).
  assert (E : lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF (lo + i) = A.AsanRT.shadow_addr (lo + i))
    by (unfold lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; lia).
  rewrite E in Hs. destruct (A.ProgWorldShadow.pwsh_view_mrd W m _ _ Hs) as (b & Hb & Hbu).
  exists b. split; [exact Hb|].
  assert (Hsm : bv_unsigned b < 128) by (unfold lib.Reusable.YG0v.saddr_ok in Hok; lia).
  unfold A.AsanRT.shadow_ok. rewrite (A.ProgWorldShadow.pwsh_byte_signed_small b Hsm), Hbu.
  unfold lib.Reusable.YG0v.saddr_ok in Hok. lia.
Qed.

(* ~ outside: the address is in one of the intervals. *)
Lemma lay_not_outside : forall (WR : list lib.Lib.Frame.ivl) a,
  ~ lib.Lib.Frame.outside WR a -> Exists (fun iv => fst iv <= a < snd iv) WR.
Proof.
  induction WR as [|[lo hi] WR IH]; intros a H; cbn [lib.Lib.Frame.outside] in H.
  - exfalso. exact (H I).
  - destruct (Z_le_gt_dec lo a) as [H1|H1]; [destruct (Z_lt_le_dec a hi) as [H2|H2]|].
    + left. cbn [fst snd]. lia.
    + right. apply IH. intro Ho. apply H. split; [lia | exact Ho].
    + right. apply IH. intro Ho. apply H. split; [lia | exact Ho].
Qed.

Definition lay_frb (lyc : alayout) (pos : Z) : Z := asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos.

Lemma lay_r2_lift : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc
    (regs : bvmap 5 word) (p r md : Z) (fr mb nb : list byte) S2 regs2 mem2 md2 pos k
    (Q : world SEGS -> config -> Prop),
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->
  rget regs 4 = w64 (as_tp B) ->
  YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  (* the row of CTRL_FRAMES *)
  3 <= r <= 9 -> length fr = 24%nat -> RcLay.ly_k fr = r ->
  (forall i, (i < 24)%nat -> exists b, nth_error fr i = Some b /\
     lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)) = Some b) ->
  (* the model record (a BOX_CATALOGUE row) and, for b = 5 / 6, its name *)
  (exists i, md = VAL (A_OBJ A_CAT) + CAT_BYTES * i /\ 0 <= i < 11) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (bmb_z mb) -> length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  (* the 32-byte block *)
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 18) 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
  afobj SEGS B lyc Sc W memc p 50 -> tfr_hull lyc Sc (p + 18) 32 ->
  (* lay_to_ret's continuation facts *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
  frames S2 = (1, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc -> AR SEGS B lyc S2 W mem2 md2 ->
  lay_ret_regs regs regs2 ((spZ regs - 128) / 32 * 32) p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md ->
  lay_fs1 (ly_F lyc) pos (spZ regs - 4512) ((spZ regs - 128) / 32 * 32) (rget regs2 10) mem2 ->
  acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - TLAY_STK) (spZ regs) (fun _ => False) ->
  lib.Lib.Step.rw_cells A.Img0.rsegs mem2 (spZ regs - 96)
    (ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18) (rget regs 19) (rget regs 20)
       (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25) (rget regs 26)) ->
  (* the continuation at the callee entry *)
  (forall ms3 md3,
     (exists s0, ctrl_lay_block_F_R2_on.lay_F_R2_box_pre_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
        (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
        (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
        (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (A.MemNorm.normalize A.Img0.rsegs mem2)
        p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md 0 (ly_F lyc) fr (A.MemNorm.normalize A.Img0.rsegs mem2)
        (lay_frb lyc pos) (lay_frb lyc pos) ((spZ regs - 128) / 32 * 32) pos
        (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos)) s0 /\
        A.MemNorm.ms_rel A.Img0.rsegs ms3 s0 /\ A.MemNorm.ro_same A.Img0.rsegs mem2 (ms_mem ms3)) ->
     ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms3) md3 k ->
     lib.Lib.Frame.munch [(spZ regs - 4512, spZ regs); (lay_frb lyc pos, lay_frb lyc pos + 24);
       (lay_frb lyc pos / 8 + A.AsanRT.ASAN_K, lay_frb lyc pos / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)]
       mem2 (ms_mem ms3) ->
     SRr SEGS W (mkCfg ms3 md3) Q) ->
  SRr SEGS W (mkCfg (rmkst regs2 (w64 0x8566c) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb S2 regs2 mem2 md2 pos k Q
    Hal Hlo Hhi Htp HROc Hr Hfl Hk Hrom (ic & Emd & Hic) Hmd Hmbl HNM Hp0 Hp50 Hamr HTW HAF HHU HJ2 Hfrs2 Eab HAR2
    HRR HFS HACK HSV K.
  rewrite lay_TLAY_val in Hlo.
  assert (Efa : frame_addr lyc 1 pos = lay_frb lyc pos).
  { unfold lay_frb, frame_addr. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & G3 & _).
    rewrite <- G3. reflexivity. }
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  set (A := (spZ regs - 128) / 32 * 32) in *.
  set (f := VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) in *.
  set (frb := lay_frb lyc pos) in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ2 as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  (* the read-only premise at mem2: the image clause of acall_kept *)
  pose proof HACK as (_ & _ & HK3 & HK4 & _).
  assert (HRO2 : YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem2)).
  { apply (lay_arodata_kept _ _ HROc). intros a Ha Ho He. exact (HK3 a Ha Ho He). }
  destruct (LayBase.rt_facts_C B LAWS CTS RLO RHI lyc S2 W mem2 md2 HAR2
              (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO2 (Z.le_refl _) (Z.le_refl _)))
    as (Hro2 & AC0 & SC2).
  assert (Hslo' : ly_stk_lo lyc <= spZ regs - 4512) by (rewrite Eslo; lia).
  assert (Hshi' : spZ regs <= ly_stk_hi lyc) by (rewrite Eshi; lia).
  destruct (LayBase.win_facts B LAWS lyc S2 W mem2 md2 (spZ regs - 4512) (spZ regs) HAR2 Hro2 Hslo' ltac:(lia) Hshi'
              (fun a Ha => Hpres2 a ltac:(lia))) as (ST0 & AW0 & HHM & HAE & Hceil').
  assert (HHU2 : tfr_hull lyc S2 (p + 18) 32).
  { destruct HHU as (cid & pos' & Hin & Hc & Hh). exists cid, pos'. rewrite Hfrs2.
    split; [right; exact Hin | split; [exact Hc | exact Hh]]. }
  destruct (lay_blk_range lyc S2 W mem2 md2 p HAR2 HHU2) as (HGT & HFtop & HB1 & HB2 & HBF).
  destruct HFR_rng as (FR1 & FR2 & FR3). destruct HCAT_rng as (CA1 & CA2 & CA3).
  unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, ROW_BYTES, CAT_BYTES in *.
  unfold asan_stack_malloc_c.ASAN_GT in HGT. unfold kFakeFramesOff, kFakeStackSize in HB1, HB2, HFtop.
  (* route (C): the region R2 takes is in the cut's shadow (FA disjunct), so its shadow facts come from ctl_rt_C *)
  assert (HFal : ly_F lyc mod 4096 = 0)
    by exact (lib.Reusable.YG0f.lo_F_al _ (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR2))).
  assert (SR0 : A.ShadowRwOn.shadow_rw_on (ctrl_lay_block_F_R2_on.lay_F_R2_shadow_R (ly_F lyc) p)
                  (A.MemNorm.normalize A.Img0.rsegs mem2)).
  { apply (A.ShadowRwOn.shadow_rw_on_mono _ _ _ (fun a Ha => lay_on_R_cut lyc S2 p a HFal ltac:(lia) ltac:(lia) Ha)).
    exact SC2. }
  assert (Hf0 : 0 <= f) by (subst f; lia).
  assert (Hf1 : f + 24 <= asan_stack_malloc_c.ASAN_GT) by (subst f; unfold asan_stack_malloc_c.ASAN_GT; lia).
  pose proof (LayBase.lay_fp0_facts B LAWS CTS lyc S2 W mem2 md2 (spZ regs) p f HAR2 Hro2 ltac:(lia) HAE Hf0 Hf1 HBF)
    as FP0.
  pose proof (LayBase.lay_tls0_facts B LAWS CTS (A.ProgWorldTlsApart.fp_tls_apart B) lyc S2 W mem2 md2
                (spZ regs - 4512) (spZ regs) HAR2 Hro2
                Hslo' Hshi') as TLS0.
  assert (Hinro : forall x, in_roP SEGS RLO RHI x -> in_img SEGS x).
  { intros x [(s & Hs & _ & Hb) | Hx]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG x Hx)]. }
  (* the model record *)
  assert (HmdR : VAL (A_OBJ A_CAT) <= md /\ md + 296 <= VAL (A_OBJ A_CAT) + 11 * 296) by (rewrite Emd; nia).
  assert (Hmd8 : md mod 8 = 0) by (rewrite Emd; clear - CA3; Z.div_mod_to_equations; lia).
  assert (HmdB : lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 md mb).
  { apply (lay_view_kept_bytes W W memc mem2 md mb); [lia | rewrite Hmbl; lia | exact Hmd |].
    intros j Hj. rewrite Hmbl in Hj.
    assert (Hj' : 0 <= Z.of_nat j < 296) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
    destruct (HCAT_ro (md + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3). exact (HK3 _ (Hinro _ X1) X2 X3). }
  (* the name, for b = 5 / 6 *)
  assert (HNM2 : (RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
            RcBox.name_ok nb /\ lib.Lib.Mem.bytes_at A.Img0.rsegs mem2 (RcSynth.rname mb) nb /\
            0 <= RcSynth.rname mb /\ 1 <= Z.of_nat (length nb) /\
            RcSynth.rname mb + Z.of_nat (length nb) <= 0x5fe000 /\
            A.AsanRT.addressable mem2 (RcSynth.rname mb) (Z.of_nat (length nb))).
  { intros Hb5 Hh Hn. destruct (HNM Hb5 Hh Hn) as (Hok & Hg & (q & sz & Hq & Hq1 & Hq2) & Hrn).
    pose proof Hok as ((L1 & L2) & _).
    assert (Hlen : 1 <= Z.of_nat (length nb)) by (apply (Nat2Z.inj_le 1) in L1; exact L1).
    destruct (Hrn (RcSynth.rname mb) ltac:(lia)) as (Y1 & _).
    destruct (Hrn (RcSynth.rname mb + Z.of_nat (length nb) - 1) ltac:(lia)) as (Y2 & _).
    pose proof (lay_img_below _ (Hinro _ Y2)) as Yb. pose proof (A.ProgWorld.pws_segs_low _ (Hinro _ Y1)) as Ya.
    unfold A.Prog.ImgBounds.IMG_HI in Yb.
    split; [exact Hok|]. split.
    - apply (lay_view_kept_bytes W W memc mem2 _ nb); [lia | lia | exact Hg |].
      intros j Hj.
      assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length nb))
        by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
      destruct (Hrn (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as (Z1 & Z2 & Z3). exact (HK3 _ (Hinro _ Z1) Z2 Z3).
    - split; [lia|]. split; [exact Hlen|]. split; [lia|].
      apply (lay_glob_addressable lyc S2 W mem2 md2 q sz); [exact HAR2 | exact Hq | lia | lia | lia | lia |
        unfold A.AsanRT.LOWMEM_END; lia]. }
  (* the block: writable cells (the side stack is stk at nm, fs_place), addressable (afobj, its frame's shadow kept) *)
  set (nm := A.MemNorm.normalize A.Img0.rsegs mem2) in *.
  pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PStk) & _).
  unfold asan_stack_malloc_c.FS_SIZE in PStk.
  destruct (lib.Lib.Frame.stk_split A.Img0.rsegs nm (ly_F lyc) (p + 50) (ly_F lyc + 11571200) PStk ltac:(lia))
    as [PS1 _].
  destruct (lib.Lib.Frame.stk_carve A.Img0.rsegs nm (ly_F lyc) (p + 50) 32 PS1 ltac:(lia)) as (_ & ob & BLK).
  replace (p + 50 - Z.of_nat 32) with (p + 18) in BLK by lia.
  assert (Happ : forall a, p + 18 <= a < p + 50 -> A.AsanRT.app_mem a).
  { intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold A.AsanRT.app_mem,
      A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (AR0 : A.AsanRT.addressable mem2 (p + 18) 32).
  { destruct HAF as (_ & _ & Hra).
    apply (lay_raddr_addressable W mem2 (p + 18) 32); [| lia | lia | intros a Ha; apply Happ; lia |
      unfold A.AsanRT.APPMEM_END; lia].
    intros x Hx. destruct (Hra x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. destruct HHU as (cid & pos' & Hin & Hc & Hh1 & Hh2).
    pose proof HAR2 as (M2 & _).
    assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
    destruct (YG0s.frame_facts B lyc S2 _ cid pos' M2 Hin2) as (_ & _ & _ & _ & Q5 & _ & _ & Q8 & _ & Q10 & _).
    apply (HK4 cid pos' _ Hin); [| intro HF; exact HF].
    right. unfold in_zr, lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. cbn [fst snd]. unfold page_aligned in Q5. unfold frame_addr in Hh1, Hh2 |- *.
    clear - Hh1 Hh2 Hx Q5 Q8 Q10. Z.div_mod_to_equations; lia. }
  (* the Section facts of the re-based stretch at nm *)
  assert (Etp : bv_unsigned (reg_get regs 4) = A.AsanRT.RT_TP).
  { change (reg_get regs 4) with (rget regs 4). rewrite Htp, (A.ProgWorld.as_tp_RT_TP B CTS). unfold w64.
    apply A.ProgWorld_Fs.pw_u64. unfold A.AsanRT.RT_TP. lia. }
  assert (FP0' : RcAsanFP.fp [0%nat; 1%nat] nm (bv_unsigned (reg_get regs 4)) (ly_F lyc)
                   (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs)
                   (ctrl_lay_block_c.ctrl_lay_block_W p (spZ regs)) (ctrl_lay_block_c.ctrl_lay_block_D p f))
    by (rewrite Etp, lay_K_val; exact FP0).
  assert (TLS0' : ctrl_lay_block_c.ctrl_lay_block_tls nm (bv_unsigned (reg_get regs 4)) (ly_F lyc)
                    (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs))
    by (rewrite Etp, lay_K_val; exact TLS0).
  assert (AW0' : A.AsanRT.addressable nm (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
    by (rewrite lay_K_val; replace 4512 with (spZ regs - (spZ regs - 4512)) at 2 by lia; exact AW0).
  assert (ST0' : lib.Lib.Frame.stk A.Img0.rsegs nm (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs))
    by (rewrite lay_K_val; exact ST0).
  assert (HHM' : A.AsanRT.HIGHMEM_BEG <= spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) by (rewrite lay_K_val; exact HHM).
  assert (Rp : 0 <= p < 2 ^ 64) by lia.
  assert (Rf : 0 <= f < 2 ^ 64) by (subst f; lia).
  assert (Rmd : 0 <= md < 2 ^ 64) by lia.
  assert (Rg : 0 <= 0 < 2 ^ 64) by lia.
  assert (DJ1 : RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) (p + 18) (p + 50))
    by (unfold RcLay.ly_dj; rewrite lay_K_val; lia).
  assert (DJ2 : RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) f (f + 24))
    by (unfold RcLay.ly_dj; rewrite lay_K_val; subst f; lia).
  assert (DJ3m : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) md (md + 296) /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) (RcSynth.rname mb)
                 (RcSynth.rname mb + Z.of_nat (length nb)))).
  { intros _ _. unfold RcLay.ly_dj. rewrite lay_K_val. split; [lia|]. rewrite Hk. intros H5 Hh Hn.
    destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _). lia. }
  assert (F8 : f mod 8 = 0) by (subst f; clear - FR3; Z.div_mod_to_equations; lia).
  assert (F24 : f + 24 <= 2 ^ 64) by (subst f; lia).
  assert (FB : lib.Lib.Mem.bytes_at A.Img0.rsegs nm f fr)
    by exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem2 f fr Hro2 (lay_row_bytes W mem2 r fr HRO2 Hr Hfl Hrom)).
  assert (K9 : RcLay.ly_k fr <= 9) by lia.
  assert (P0 : p <> 0) by lia.
  assert (P50 : p + 50 <= 2 ^ 64) by lia.
  assert (DB1 : RcLay.ly_dj (p + 18) (p + 50) f (f + 24)) by (unfold RcLay.ly_dj; subst f; lia).
  assert (DB3 : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 -> RcLay.ly_dj (p + 18) (p + 50) md (md + 296))
    by (intros _ _; unfold RcLay.ly_dj; lia).
  assert (DBN : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 -> (RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) ->
                RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
                RcLay.ly_dj (p + 18) (p + 50) (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))).
  { intros _ _ H5 Hh Hn. rewrite Hk in H5. destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _).
    unfold RcLay.ly_dj. lia. }
  assert (MDP : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            md mod 8 = 0 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at A.Img0.rsegs nm md mb /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcBox.name_ok nb /\ lib.Lib.Mem.bytes_at A.Img0.rsegs nm (RcSynth.rname mb) nb)).
  { intros _ _. split; [exact Hmd8|]. split; [exact Hmbl|].
    split; [exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem2 md mb Hro2 HmdB)|].
    rewrite Hk. intros H5 Hh Hn. destruct (HNM2 H5 Hh Hn) as (N0 & N1 & _).
    split; [exact N0 | exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem2 _ nb Hro2 N1)]. }
  assert (AF : A.AsanRT.addressable nm f 24).
  { apply (A.MemNormTr.addressable_normalize mem2 f 24 Hro2).
    apply (lay_glob_addressable lyc S2 W mem2 md2 (VAL (A_OBJ A_FRAMES)) (11 * 24)); [exact HAR2 | exact HFR_glob |
      subst f; lia | subst f; lia | lia | subst f; lia | unfold A.AsanRT.LOWMEM_END; subst f; lia]. }
  assert (AR : A.AsanRT.addressable nm (p + 18) 32) by exact (A.MemNormTr.addressable_normalize mem2 _ _ Hro2 AR0).
  assert (AP50 : A.AsanRT.app_mem (p + 50)).
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold A.AsanRT.app_mem,
      A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (ARDJ : p + 50 <= A.AsanRT.RT_LO \/ A.AsanRT.RT_HI <= p + 18) by (right; unfold A.AsanRT.RT_HI; lia).
  assert (AMD : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            A.AsanRT.addressable nm md 296 /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 -> A.AsanRT.addressable nm (RcSynth.rname mb) (Z.of_nat (length nb)))).
  { intros _ _. split.
    - apply (A.MemNormTr.addressable_normalize mem2 md 296 Hro2).
      apply (lay_glob_addressable lyc S2 W mem2 md2 (VAL (A_OBJ A_CAT)) (11 * 296)); [exact HAR2 | exact HCAT_glob |
        lia | lia | lia | lia | unfold A.AsanRT.LOWMEM_END; lia].
    - rewrite Hk. intros H5 Hh Hn. destruct (HNM2 H5 Hh Hn) as (_ & _ & _ & _ & _ & N5).
      exact (A.MemNormTr.addressable_normalize mem2 _ _ Hro2 N5). }
  assert (FPM_gen : forall lo hi, 0 <= lo -> hi <= 0x5fe000 -> lo <= hi ->
            RcAsanFP.fp_dj [(lo, hi)] (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc))).
  { intros lo hi H0 H1 H2. unfold RcAsanFP.fp_dj, RcAsanFP.fp_w, RcAsanFP.fp_w1. cbn [flat_map app].
    unfold asan_stack_malloc_c.fs_hint, asan_stack_malloc_c.fs_flag, asan_stack_malloc_c.fs_frame,
      asan_stack_malloc_c.fs_M, asan_stack_malloc_c.fs_B. cbn [Z.of_nat].
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
    all: clear - H0 H1 H2 HGT; Z.div_mod_to_equations; lia. }
  assert (FPM : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            RcAsanFP.fp_dj [(md, md + 296)] (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc)) /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcAsanFP.fp_dj [(RcSynth.rname mb, RcSynth.rname mb + Z.of_nat (length nb))]
                 (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc)))).
  { intros _ _. split; [apply FPM_gen; lia|]. rewrite Hk. intros H5 Hh Hn.
    destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _). apply FPM_gen; lia. }
  (* the state at 0x8566c in the form the stretch takes *)
  pose proof HRR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  unfold lay_fs1 in HFS. cbv zeta in HFS.
  destruct HFS as (Hpos & Ha0fr & HFL1 & HFL8 & HFSH & HFADDR & HFSTK & HFAPP & HF64 & HFlo & HFhi & HFGT & HFstk2).
  change (asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) with frb in *.
  change (asan_stack_malloc_c.fs_B 1) with 128 in *.
  unfold asan_stack_malloc_c.FS_SIZE, asan_stack_malloc_c.ASAN_GT in HFhi, HFGT.
  change (rmkst regs2 (w64 0x8566c) mem2 (lib.Reusable.YK11.seg_rom SEGS)) with
    (lib.Lib.MState.MS regs2 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8566c) lib.Reusable.YK11.fp_csr None mem2
       (lib.Lib.PropExec.seg_rom A.Img0.rsegs)).
  apply (YA0nR.SRr_xregs_eqv SEGS W (lib.Lib.Regs6ss.mkR_of regs2) regs2);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs2))].
  unfold lib.Lib.Regs6ss.mkR_of.
  change (rget regs2 2) with (reg_get regs2 2) in R2. change (rget regs2 3) with (reg_get regs2 3) in R3.
  change (rget regs2 4) with (reg_get regs2 4) in R4. change (rget regs2 8) with (reg_get regs2 8) in R8.
  change (rget regs2 9) with (reg_get regs2 9) in R9. change (rget regs2 18) with (reg_get regs2 18) in R18.
  change (rget regs2 19) with (reg_get regs2 19) in R19. change (rget regs2 20) with (reg_get regs2 20) in R20.
  change (rget regs2 21) with (reg_get regs2 21) in R21. change (rget regs2 22) with (reg_get regs2 22) in R22.
  change (rget regs2 23) with (reg_get regs2 23) in R23. change (rget regs2 24) with (reg_get regs2 24) in R24.
  change (rget regs2 25) with (reg_get regs2 25) in R25. change (rget regs2 26) with (reg_get regs2 26) in R26.
  change (rget regs2 27) with (reg_get regs2 27) in R27. change (rget regs2 10) with (reg_get regs2 10) in Ha0fr.
  rewrite R2, R3, R4, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27, Ha0fr.
  refine (lay_SRr_norm HWX W (A.ProgBridge.RNG_W (w_H W)) md2 _ lib.Reusable.YK11.fp_regs _ lib.Reusable.YK11.fp_csr
            mem2
            (ctrl_lay_block_F_R2_on.lay_F_R2_box_pre_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
               (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
               (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm p f md 0
               (ly_F lyc) fr nm frb frb A pos (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos)))
            Q (A.ProgBridge.fp_avoids_RNG_W _) Hro2 _ _).
  { apply (ctrl_lay_block_F_R2_on.lay_F_R2_run_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
             (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
             (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm p f md 0
             (ly_F lyc) fr ob nil mb nb nil Rp Rf Rmd Rg Hal ST0' DJ1 DJ2 DJ3m F8 F24 Hfl FB K9
             (fun E2 : RcLay.ly_k fr = 2 => False_ind _ ltac:(lia)) P0 P50 BLK DB1 DB3
             DBN MDP AC0 SR0 HHM' HAE AW0' AF AR AP50 ARDJ AMD FP0' FPM MEMSF).
    all: try change (bv_unsigned (reg_get regs 2)) with (spZ regs); try fold A.
    - right. split; [exact Hpos|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    - lia.
    - exact Hpos.
    - unfold ctrl_lay_block.BI. split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|].
      split; [apply ctrl_lay_block.rd_mono_refl|]. split; [apply A.MemNorm.mem_inv_normalize|].
      split; [refine (A.MemNormTr.rw_cells_normalize mem2 _ _ Hro2 _ HSV);
              intros i Hi; apply A.MemNormTr.ro_addr_above_img;
              cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_block.SAVES] in Hi;
              unfold A.Prog.ImgBounds.IMG_HI; lia|].
      split; [intros _; apply (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem2 _ _ Hro2);
              replace (frb + 120) with (frb + 128 - 8) by lia;
              exact HFL8|].
      split; [exact AW0'|]. split; [exact FP0' | exact TLS0'].
    - exact (A.ProgBridge.rng_bytes_RNG_W (w_H W)).
    - exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W)).
    - rewrite lay_K_val. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B lyc S2 W mem2 md2 a HAR2 ltac:(unfold kFakeStackSize; lia))).
    - destruct (A.ProgWorldVisFrame.frame_vis B LAWS lyc S2 W mem2 md2 1 pos frb 128 HAR2
                  ltac:(rewrite Hfrs2; left; reflexivity) ltac:(rewrite Efa; lia) ltac:(rewrite Efa, E128; lia))
        as (_ & V2).
      destruct (V2 ltac:(lia) ltac:(rewrite Efa; clear - HF64; Z.div_mod_to_equations; lia)
                  ltac:(rewrite Efa, E128; clear - HF64; Z.div_mod_to_equations; lia)) as [V0 | V3]; [lia|].
      apply A.ProgBridge.rng_of_visible.
      assert (Es1 : A.Prog.rng_asan.sh_al8_lo frb = A.AsanRT.shadow_addr frb)
        by (unfold A.Prog.rng_asan.sh_al8_lo, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; clear - HF64;
            Z.div_mod_to_equations; lia).
      assert (Es2 : A.Prog.rng_asan.sh_al8_hi frb 128 - A.Prog.rng_asan.sh_al8_lo frb = 16)
        by (unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            clear - HF64; Z.div_mod_to_equations; lia).
      rewrite Es2, Es1 in V3. exact V3.
    - apply A.ProgBridge.rng_of_visible. unfold asan_memset_c.ASAN_MEMSET_K.
      split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B lyc S2 W mem2 md2 a HAR2 ltac:(unfold kFakeStackSize; lia))).
    - destruct HHU2 as (cid & pos' & Hin & Hc & Hh1 & Hh2).
      destruct (A.ProgWorldVisFrame.frame_vis B LAWS lyc S2 W mem2 md2 cid pos' (p + 18) 32 HAR2 Hin
                  ltac:(clear - Hh1; Z.div_mod_to_equations; lia) ltac:(clear - Hh2; Z.div_mod_to_equations; lia))
        as (_ & V2).
      destruct (V2 ltac:(lia) ltac:(clear - Hh1; Z.div_mod_to_equations; lia) ltac:(clear - Hh2; Z.div_mod_to_equations; lia))
        as [V0 | V3]; [left; exact V0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V3)].
    - unfold asan_memset_c.ASAN_MEMSET_K.
      destruct (A.ProgWorldVisWin.win_sh_vis B LAWS lyc S2 W mem2 md2 (A - 2208) 2208 HAR2 ltac:(lia) ltac:(lia) ltac:(lia))
        as [V0 | V3]; [left; exact V0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V3)].
    - apply A.ProgBridge.rng_of_visible.
      apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W));
        unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; subst f; lia.
    - apply A.ProgBridge.rng_of_visible.
      apply (lay_glob_shvis lyc S2 W mem2 md2 (VAL (A_OBJ A_FRAMES)) (11 * 24) f 3 HAR2 HFR_glob);
        [subst f; lia | subst f; lia | exact F8 | lia | subst f; lia | unfold A.AsanRT.LOWMEM_END; subst f; lia].
    - rewrite Hk. exact Hr. }
  (* after the run: the journal step with the stretch's write set *)
  intros ms3 md3 Hrun3 HP3 Hhid3 Hsame3.
  pose proof HP3 as (s0 & HB0 & HREL3 & HROS3).
  destruct HB0 as (mc3 & gj & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Es0 & FI3 & LC3 & AO3
    & MU3 & _).
  subst s0.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL3) as [Ems3 HMR3].
  assert (HMU3 : lib.Lib.Frame.munch [(spZ regs - 4512, spZ regs); (frb, frb + 24);
                   (frb / 8 + A.AsanRT.ASAN_K, frb / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)] mem2 (ms_mem ms3))
    by exact (A.MemNorm.munch_rel A.Img0.rsegs _ mem2 nm (ms_mem ms3) mc3
               (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem2 Hro2) HMR3 HROS3 MU3).
  assert (HJ3 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms3) md3 k).
  { lazymatch type of Hrun3 with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      refine (A.ProgWorld.ajournal_of_fsteps B LAWS HWX STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W ms0 ms3
                md2 md3 k _ _ HJ2 Hrun3 (A.ProgBridge.fp_avoids_RNG_W _) HMU3 Hsame3 _) end.
    intros a Ha Hout. apply lay_not_outside in Hout.
    rewrite !Exists_cons, Exists_nil in Hout. cbn [fst snd] in Hout. rewrite Eab.
    destruct Hout as [H | [H | [H | [H | []]]]].
    - left. lia.
    - right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite Efa, E128. lia.
    - right. right. right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      rewrite Efa, E128. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
      unfold A.AsanRT.ASAN_K in H. clear - H. Z.div_mod_to_equations; lia.
    - destruct (HTW a ltac:(lia)) as (Haw & _). unfold awr_byte in Haw |- *.
      destruct Haw as [X | [X | [X | (cid & pos' & Hin & X)]]];
        [left; exact X | right; left; exact X | right; right; left; exact X |].
      right. right. right. exists cid, pos'. split; [right; exact Hin | exact X]. }
  exact (K ms3 md3 HP3 HJ3 HMU3).
Qed.



(* ================================================================================================================
   6. The box call at 0x85b44 (TMB, a Theorem Labs lane's contract): p := md (a BOX_CATALOGUE row), b := ly_bb r,
   o := frb + 32 (in this call's class-1 frame), at sp = SP2, journal own = (1, pos) :: own.
   ================================================================================================================ *)
Lemma lay_addressable_raddr : forall (W : world SEGS) m lo n,
  A.AsanRT.addressable m lo n ->
  (forall x, lo <= x < lo + n -> w_H W (Z_to_bv 64 (A.AsanRT.shadow_addr x)) = false) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF lo n.
Proof.
  intros W m lo n (H0 & Hn & Htop & Ha) Hv x Hx.
  destruct (Ha (x - lo) ltac:(lia)) as (_ & b & Hb & Hok). replace (lo + (x - lo)) with x in Hb, Hok by lia.
  exists (bv_unsigned b). split.
  - assert (E : lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF x = A.AsanRT.shadow_addr x)
      by (unfold lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; lia).
    rewrite E, (A.ProgWorld.aview_vis_mrd W m _ (Hv x Hx)).
    change (lib.Lib.Mem.wa (A.AsanRT.shadow_addr x)) with (Z_to_bv 64 (A.AsanRT.shadow_addr x)) in Hb.
    rewrite Hb. reflexivity.
  - pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    unfold A.AsanRT.shadow_ok, bv_signed, bv_swrap, bv_wrap in Hok. change (bv_half_modulus 8) with 128 in Hok.
    change (bv_modulus 8) with 256 in Hok. unfold lib.Reusable.YG0v.saddr_ok.
    clear - Rb Hok. Z.div_mod_to_equations; lia.
Qed.

Lemma lay_garr8_kept : forall (H H' : word -> bool) m m' base (l : list Z),
  garr8 SEGS (mrestrict H m) base l ->
  (forall j, (j < length l)%nat -> aview SEGS H' m' (base + Z.of_nat j) = aview SEGS H m (base + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H' m') base l.
Proof.
  intros H H' m m' base l G K j Hj. destruct (G j Hj) as (V & R). split; [|exact R].
  intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (V 0%nat Hk).
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in V |- * by lia.
  specialize (K j Hj). unfold aview in K. rewrite V in K.
  destruct (lib.Reusable.YP09.mbyte SEGS (mrestrict H' m') (base + Z.of_nat j)) as [b'|] eqn:E;
    cbn [option_map] in K; [|discriminate K].
  injection K as K. f_equal. apply bv_eq. rewrite K. reflexivity.
Qed.

Lemma lay_bmb_addr : BASE + AF_reac_box_model_block = reac_box_model_block_c.REAC_BOX_MODEL_BLOCK.
Proof. vm_compute. reflexivity. Qed.

Lemma lay_addressable_of_rel : forall m m0 lo n, A.MemNorm.mem_rel A.Img0.rsegs m m0 ->
  A.AsanRT.addressable m0 lo n -> A.AsanRT.addressable m lo n.
Proof.
  intros m m0 lo n R (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b.
  split; [rewrite (A.MemNorm.mrd_rel A.Img0.rsegs m m0 _ R); exact Hb | exact Hok].
Qed.

(* The callee-saved registers after reac_box_model_block returns: the box-call state's (lay_F_R2_box_pre_on). *)
Definition lay_box_regs (regs regs4 : bvmap 5 word) (A p f md frb : Z) : Prop :=
  rget regs4 2 = w64 A /\ rget regs4 3 = rget regs 3 /\ rget regs4 4 = rget regs 4 /\
  rget regs4 8 = rget regs 2 /\ rget regs4 9 = w64 A /\ rget regs4 18 = w64 frb /\
  rget regs4 19 = w64 0 /\ rget regs4 20 = w64 f /\ rget regs4 21 = w64 (p + 18) /\
  rget regs4 22 = w64 md /\ rget regs4 23 = w64 (frb + 32) /\ rget regs4 24 = w64 (A.AsanRT.shadow_addr frb) /\
  rget regs4 25 = w64 frb /\ rget regs4 26 = w64 A.AsanRT.ASAN_K /\ rget regs4 27 = rget regs 27.

Lemma lay_box : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc
    (regs : bvmap 5 word) (p r md : Z) (fr mb nb : list byte) S2 mem2 pos k ms3 md3
    (Q : world SEGS -> config -> Prop),
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->
  rget regs 3 = w64 (as_gp B) -> rget regs 4 = w64 (as_tp B) ->
  YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  3 <= r <= 9 -> RcLay.ly_k fr = r ->
  (exists i, md = VAL (A_OBJ A_CAT) + CAT_BYTES * i /\ 0 <= i < 11) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (bmb_z mb) -> length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  count_cid 0 (frames Sc) < fs_frames 0 ->
  frames S2 = (1, pos) :: frames Sc ->
  acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - TLAY_STK) (spZ regs) (fun _ => False) ->
  (* the class-1 frame of this call *)
  0 <= pos < asan_stack_malloc_c.fs_M 1 -> asan_stack_malloc_c.ASAN_GT <= lay_frb lyc pos ->
  lay_frb lyc pos + 128 <= ly_F lyc + asan_stack_malloc_c.FS_SIZE -> lay_frb lyc pos mod 64 = 0 ->
  (* the block is in the side stack (above the image) *)
  asan_stack_malloc_c.ASAN_GT <= p + 18 ->
  (* lay_r2_lift's continuation facts *)
  (exists s0, ctrl_lay_block_F_R2_on.lay_F_R2_box_pre_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
     (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
     (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
     (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (A.MemNorm.normalize A.Img0.rsegs mem2)
     p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md 0 (ly_F lyc) fr (A.MemNorm.normalize A.Img0.rsegs mem2)
     (lay_frb lyc pos) (lay_frb lyc pos) ((spZ regs - 128) / 32 * 32) pos
     (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos)) s0 /\
     A.MemNorm.ms_rel A.Img0.rsegs ms3 s0 /\ A.MemNorm.ro_same A.Img0.rsegs mem2 (ms_mem ms3)) ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms3) md3 k ->
  lib.Lib.Frame.munch [(spZ regs - 4512, spZ regs); (lay_frb lyc pos, lay_frb lyc pos + 24);
    (lay_frb lyc pos / 8 + A.AsanRT.ASAN_K, lay_frb lyc pos / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)]
    mem2 (ms_mem ms3) ->
  (* the continuation at the box call's return 0x85828 *)
  (forall W4 ly4 S4 regs4 mem4 md4 gj,
     wle W W4 ->
     ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly4 S4 W4 mem4 md4 (k + EV_BMB) ->
     lay_box_regs regs regs4 ((spZ regs - 128) / 32 * 32) p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md
       (lay_frb lyc pos) ->
     frames S4 = frames S2 -> ablocks B ly4 S4 = ablocks B lyc S2 ->
     rget regs4 10 = w64 (RcSynth.rc mb (RcLay.ly_bb r)) ->
     garr8 SEGS (mrestrict (w_H W4) mem4) (lay_frb lyc pos + 32) (bmb_z (RcSynth.synth mb (RcLay.ly_bb r) nb)) ->
     tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc S2 W (ms_mem ms3) W4 mem4 ((spZ regs - 128) / 32 * 32)
       (fun a => lay_frb lyc pos + 32 <= a < lay_frb lyc pos + 32 + 32) ->
     lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms3) (spZ regs + -128)
       (lib.Lib.Cells.CB 32 gj :: ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
          (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25)
          (rget regs 26)) ->
     lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms3) (p + 18) [lib.Lib.Cells.CB 32 RcLay.ly_zero] ->
     lib.Lib.Mem.bytes_at A.Img0.rsegs (ms_mem ms3) (lay_frb lyc pos + 120)
       (lib.Lib.Mem.le8 (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos))) ->
     A.AsanRT.addressable (ms_mem ms3) (lay_frb lyc pos + 32) 32 ->
     SRr SEGS W4 (mkCfg (rmkst regs4 (w64 0x85828) mem4 (lib.Reusable.YK11.seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg ms3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb S2 mem2 pos k ms3 md3 Q
    Hal Hlo Hhi Hgp Htp HROc Hr Hk (ic & Emd & Hic) Hmd Hmbl HNM Hroom0 Hfrs2 HACK Hpos HFGT HFhi HF64 HPB HP3 HJ3 HMU3
    K.
  rewrite lay_TLAY_val in Hlo.
  assert (Efa : frame_addr lyc 1 pos = lay_frb lyc pos).
  { unfold lay_frb, frame_addr. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & G3 & _).
    rewrite <- G3. reflexivity. }
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  assert (HFlo : ly_F lyc <= lay_frb lyc pos).
  { unfold lay_frb, asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B. cbn [Z.of_nat]. lia. }
  set (A := (spZ regs - 128) / 32 * 32) in *.
  set (f := VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) in *.
  set (frb := lay_frb lyc pos) in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  pose proof HJ3 as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  pose proof HACK as (_ & _ & HK3 & _).
  destruct HCAT_rng as (CA1 & CA2 & CA3).
  unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, ROW_BYTES, CAT_BYTES in *.
  unfold asan_stack_malloc_c.ASAN_GT, asan_stack_malloc_c.FS_SIZE in *.
  pose proof (A.ProgWorld_Fs.pw_F_above B lyc S2 W (ms_mem ms3) md3 HAR3) as HGT. unfold asan_stack_malloc_c.ASAN_GT in HGT.
  pose proof HAR3 as (M3 & _). pose proof (am_layout _ _ _ _ M3) as LO.
  destruct (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F lyc, kFakeStackSize)
              ltac:(unfold owned_extents; cbn; tauto)) as [E0 E1].
  cbn [fst snd] in E0, E1. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in E1.
  assert (Hinro : forall x, in_roP SEGS RLO RHI x -> in_img SEGS x).
  { intros x [(s & Hs & _ & Hb) | Hx]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG x Hx)]. }
  (* the post of the R2 run, in the real memory *)
  pose proof HP3 as (s0 & HB0 & HREL3 & HROS3).
  destruct HB0 as (mc3 & gj & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Es0 & FI3 & LC3 & AO3
    & MU3 & _).
  subst s0.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL3) as [Ems3 HMR3].
  pose proof LC3 as (LCa & _ & _ & _ & _ & LCb & _).
  pose proof FI3 as (_ & FIb & _).
  assert (RW1 := A.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 LCa).
  assert (RW2 := A.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 LCb).
  assert (BW := proj2 (A.MemNorm.bytes_at_rel A.Img0.rsegs _ _ _ _ HMR3) (FIb ltac:(lia))).
  assert (AD3 := lay_addressable_of_rel _ _ _ _ HMR3 AO3).
  rewrite Ems3. clear Ems3.
  set (mem3 := ms_mem ms3) in *.
  (* views at mem3: the image clause of acall_kept, then the R2 write set above the image *)
  assert (HV3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
                  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
  { intros a Ha Ho He. rewrite (lay_view_img_munch W mem2 mem3 _ HMU3); [exact (HK3 a Ha Ho He) | | exact Ha].
    intros x Hx. cbn [lib.Lib.Frame.outside]. unfold A.AsanRT.ASAN_K. unfold A.Prog.ImgBounds.IMG_HI in Hx.
    repeat split; try exact I; clear - Hx HFGT HPB Hc0 Hceil Hslo Hlo Hhi; Z.div_mod_to_equations; lia. }
  assert (HRO3 : YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem3)) by exact (lay_arodata_kept _ _ HROc HV3).
  (* the call state as cfg_at *)
  lazymatch goal with |- SRr _ _ {| cfg_ms := lib.Lib.MState.MS ?R _ _ _ _ _ _; cfg_model := _ |} _ =>
    set (R3 := R) end.
  replace (Z_to_bv 64 reac_box_model_block_c.REAC_BOX_MODEL_BLOCK) with (Z_to_bv 64 (BASE + AF_reac_box_model_block))
    by (rewrite lay_bmb_addr; reflexivity).
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_model_block) R3 mem3 md3) Q).
  assert (EspR : spZ R3 = A).
  { unfold spZ. change (rget R3 2) with (Z_to_bv 64 A). apply A.ProgWorld_Fs.pw_u64. lia. }
  assert (EraR : raZ R3 = 0x85828).
  { unfold raZ. change (rget R3 1) with (Z_to_bv 64 0x85828). apply A.ProgWorld_Fs.pw_u64. lia. }
  assert (Hbb : 0 <= RcLay.ly_bb r < 2 ^ 64) by (unfold RcLay.ly_bb; repeat destruct (_ =? _); lia).
  assert (HmdR : VAL (A_OBJ A_CAT) <= md /\ md + 296 <= VAL (A_OBJ A_CAT) + 11 * 296) by (rewrite Emd; nia).
  assert (Hmd8 : md mod 8 = 0) by (rewrite Emd; clear - CA3; Z.div_mod_to_equations; lia).
  assert (Hin1 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (al_frames _ _ LAWS lyc S2 W mem3 md3 1 pos HAR3 Hin1) as (_ & _ & HFRb & HFRs).
  rewrite Efa, E128 in HFRb, HFRs. change (128 / 8) with 16 in HFRs.
  assert (Hpr : forall a, apresent (w_H W) mem3 a -> aview SEGS (w_H W) mem3 a <> None).
  { intros a (Hh & b & Hb). unfold aview, lib.Reusable.YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate. }
  assert (Esh : forall x, frb <= x < frb + 128 ->
            A.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr frb + (x - frb) / 8).
  { intros x Hx. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. clear - Hx HF64. Z.div_mod_to_equations; lia. }
  eapply SRr_bind.
  { apply (TMB STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem3 md3 k R3 md (RcLay.ly_bb r) (frb + 32)
             mb nb HJ3 HRO3).
    - change (rget R3 1) with (Z_to_bv 64 0x85828). apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
    - rewrite EraR. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - change (rget R3 11) with (Z_to_bv 64 (RcLay.ly_bb (RcLay.ly_k fr))). rewrite Hk. reflexivity.
    - reflexivity.
    - lia.
    - exact Hbb.
    - lia.
    - rewrite EspR. clear - HA1. Z.div_mod_to_equations; lia.
    - rewrite EspR. change REAC_BOX_MODEL_BLOCK_STK with 4320. lia.
    - rewrite EspR. lia.
    - rewrite Hfrs2. cbn [count_cid]. rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)). lia.
    - intros _. split; [exact Hmd8|]. split; [exact Hmbl|]. split.
      { apply (lay_garr8_kept (w_H W) (w_H W) memc mem3 md (bmb_z mb) Hmd). intros j Hj.
        unfold bmb_z in Hj. rewrite length_map, Hmbl in Hj.
        assert (Hj' : 0 <= Z.of_nat j < 296) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
        destruct (HCAT_ro (md + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3). exact (HV3 _ (Hinro _ X1) X2 X3). }
      split; [exists (VAL (A_OBJ A_CAT)), (11 * 296); split; [exact HCAT_glob | lia]|].
      split; [try unfold IMG_LO; lia|]. split; [try unfold IMG_HI; lia|].
      split; [intros x Hx; exact (HCAT_ro x ltac:(lia))|]. right. right. lia.
    - intros _ Hb5 Hh Hn. destruct (HNM Hb5 Hh Hn) as (Hok & Hg & Hq & Hrn).
      pose proof Hok as ((L1 & L2) & _).
      assert (Hlen : 1 <= Z.of_nat (length nb)) by (apply (Nat2Z.inj_le 1) in L1; exact L1).
      destruct (Hrn (RcSynth.rname mb + Z.of_nat (length nb) - 1) ltac:(lia)) as (Y2 & _).
      pose proof (lay_img_below _ (Hinro _ Y2)) as Yb. unfold A.Prog.ImgBounds.IMG_HI in Yb.
      split; [exact Hok|]. split.
      { apply (lay_garr8_kept (w_H W) (w_H W) memc mem3 _ (bmb_z nb) Hg). intros j Hj.
        unfold bmb_z in Hj. rewrite length_map in Hj.
        assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length nb))
          by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
        destruct (Hrn (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3). exact (HV3 _ (Hinro _ X1) X2 X3). }
      split; [exact Hq|]. split; [exact Hrn|]. right. right. lia.
    - intros _. split.
      { left. exists 1, pos. split; [exact Hin1|]. split; [lia|]. intros x Hx. unfold in_zr, frame_rng.
        cbn [fst snd]. rewrite Efa, E128. lia. }
      split; [intros x Hx Hi; pose proof (lay_img_below x Hi) as Hb; unfold A.Prog.ImgBounds.IMG_HI in Hb; lia|].
      split.
      { intros a Ha. split.
        - right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
          rewrite Efa, E128. lia.
        - destruct (HFRb a ltac:(lia)) as (Hp & Hno). split; [exact Hp|]. split; [exact Hno|]. rewrite EspR.
          unfold ESTACK. clear - Ha HFhi E1 Hc0 Hc1 HA1 Hceil Hslo Hlo Hhi. lia. }
      split.
      { split.
        - intros a Ha. destruct (HFRb a ltac:(lia)) as (Hp & _). split; [exact (Hpr a Hp)|]. rewrite EspR.
          unfold ESTACK. clear - Ha HFhi E1 Hc0 Hc1 HA1 Hceil Hslo Hlo Hhi. lia.
        - split.
          + apply (lay_addressable_raddr W mem3 (frb + 32) 32 AD3). intros x Hx. rewrite (Esh x ltac:(lia)).
            exact (proj1 (proj1 (HFRs ((x - frb) / 8) ltac:(clear - Hx; Z.div_mod_to_equations; lia)))).
          + split.
            * intros s Hs. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hs.
              replace s with (lib.Reusable.YG0f.shadow_addr frb + (s - lib.Reusable.YG0f.shadow_addr frb)) by lia.
              apply Hpr. apply (proj1 (HFRs (s - lib.Reusable.YG0f.shadow_addr frb) ltac:(unfold
                lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; clear - Hs HF64; Z.div_mod_to_equations; lia))).
            * split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - HFhi E1 Hc1 HFGT HFlo; lia|].
              split; lia. }
      right. rewrite EspR. change REAC_BOX_MODEL_BLOCK_STK with 4320. clear - HFhi E1 Hc0 Hc1 HA1 Hceil Hslo Hlo Hhi. lia. }
  cbv beta. intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & Eab4 & HIF).
  assert (Esel : (md =? 0) || (frb + 32 =? 0) = false) by (apply orb_false_iff; split; apply Z.eqb_neq; lia).
  rewrite Esel in HIF. destruct HIF as (Ha04 & Hg4 & HK4).
  change (rget R3 1) with (w64 0x85828).
  apply (K W4 ly4 S4 regs4 mem4 md4 gj Hwle HJ4).
  - unfold lay_box_regs.
    assert (P : forall rr, acallee_saved rr -> rget regs4 (Z_to_bv 5 rr) = rget R3 (Z_to_bv 5 rr)) by exact HP4.
    repeat split.
    all: lazymatch goal with
         | |- rget _ ?n = _ =>
             let z := eval vm_compute in (bv_unsigned n) in
             transitivity (rget R3 (Z_to_bv 5 z)); [exact (P z ltac:(unfold acallee_saved; lia)) | reflexivity]
         end.
  - exact Hfrs4.
  - exact Eab4.
  - exact Ha04.
  - exact Hg4.
  - rewrite EspR in HK4. exact HK4.
  - exact RW1.
  - exact RW2.
  - exact BW.
  - exact AD3.
Qed.

(* ================================================================================================================
   7. Region R3 (0x85828, the box call's return, -> 0x858f4 after the class-1 flag release): a Theorem Labs lane's route (C) twin
   lay_F_R3_run_on (ctrl_lay_block_F_R3_on.v: re-based k5 + k6 at g = 0 + stretch k7 + the release) on the normalized
   memory after the callee, its shadow region lay_F_R3_shadow_R from ctl_rt_C at the callee's return (lay_on_R_cut),
   then the journal step over the release (A.ProgWorldAstack.ctl_release_of_free_law at class 1).
   fuzz_grant overlap: the epilogue's class-1 release (0x858ec / 0x858f0) is the twin of grant's proved release
   in CtrlLayBlock.v (a working branch 5aae1e8a0ce).
   ================================================================================================================ *)
Lemma lay_raw_of_aview2 : forall (W W' : world SEGS) (mem mem' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> w_H W (Z_to_bv 64 a) = false -> w_H W' (Z_to_bv 64 a) = false -> ~ in_img SEGS a ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros W W' mem mem' a Ha Hh Hh' Hni E.
  rewrite (A.ProgWorld.aview_vis_mrd W' _ a Hh'), (A.ProgWorld.aview_vis_mrd W _ a Hh) in E.
  assert (Hs : lib.Lib.PropExec.seg_rom A.Img0.rsegs (Z_to_bv 64 a) = None).
  { apply (A.MemNorm.seg_rom_unmapped A.Img0.rsegs). rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact (find_segment_none AB1v.tfibsegs a Hni). }
  unfold lib.Lib.Mem.mrd in E. rewrite Hs in E.
  destruct (mem' (Z_to_bv 64 a)) as [b'|], (mem (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma lay_addressable_kept : forall (m m' : word -> option byte) lo n,
  A.AsanRT.addressable m lo n ->
  (forall x, lo <= x < lo + n -> m' (Z_to_bv 64 (A.AsanRT.shadow_addr x)) = m (Z_to_bv 64 (A.AsanRT.shadow_addr x))) ->
  A.AsanRT.addressable m' lo n.
Proof.
  intros m m' lo n (H0 & H1 & H2 & H) E. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold lib.Lib.Mem.mrd in Hb |- *. change (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (lo + i)))
    with (Z_to_bv 64 (A.AsanRT.shadow_addr (lo + i))) in Hb |- *.
  rewrite (E (lo + i) ltac:(lia)). exact Hb.
Qed.

Lemma lay_addr_sub : forall (m : word -> option byte) lo n x k,
  A.AsanRT.addressable m lo n -> lo <= x -> 0 <= k -> x + k <= lo + n -> A.AsanRT.addressable m x k.
Proof.
  intros m lo n x k (H0 & H1 & H2 & H) Hx Hk Hxk. split; [lia|]. split; [exact Hk|]. split; [lia|].
  intros i Hi. replace (x + i) with (lo + (x - lo + i)) by lia. apply H. lia.
Qed.

(* The shadow byte of an application address is apart from a range in low or high application memory. *)
Lemma lay_sh_apart : forall x lo n, 0 <= n -> (lo + n <= 0x7fff8000 \/ 0x10007fff8000 <= lo) -> 0 <= x < 2 ^ 47 ->
  ~ (lo <= x / 8 + 0x7fff8000 < lo + n).
Proof. intros x lo n Hn H Hx. Z.div_mod_to_equations. lia. Qed.

Lemma lay_r3_lift : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc
    (regs : bvmap 5 word) (p r md : Z) (fr mb nb gj : list byte) S2 mem2 pos k mem3
    (W4 : world SEGS) ly4 S4 regs4 mem4 md4 md3 (Q : world SEGS -> config -> Prop),
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->
  rget regs 4 = w64 (as_tp B) ->
  YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  3 <= r <= 9 -> length fr = 24%nat -> RcLay.ly_k fr = r ->
  (forall i, (i < 24)%nat -> exists b, nth_error fr i = Some b /\
     lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)) = Some b) ->
  (exists i, md = VAL (A_OBJ A_CAT) + CAT_BYTES * i /\ 0 <= i < 11) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (bmb_z mb) -> length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 18) 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
  afobj SEGS B lyc Sc W memc p 50 -> tfr_hull lyc Sc (p + 18) 32 ->
  asan_stack_malloc_c.ASAN_GT <= p + 18 ->
  frames S2 = (1, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - TLAY_STK) (spZ regs) (fun _ => False) ->
  0 <= pos < asan_stack_malloc_c.fs_M 1 -> asan_stack_malloc_c.ASAN_GT <= lay_frb lyc pos ->
  lay_frb lyc pos + 128 <= ly_F lyc + asan_stack_malloc_c.FS_SIZE -> lay_frb lyc pos mod 64 = 0 ->
  (* R2's write set and its memory facts at mem3 *)
  lib.Lib.Frame.munch [(spZ regs - 4512, spZ regs); (lay_frb lyc pos, lay_frb lyc pos + 24);
    (lay_frb lyc pos / 8 + A.AsanRT.ASAN_K, lay_frb lyc pos / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)]
    mem2 mem3 ->
  lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (spZ regs + -128)
    (lib.Lib.Cells.CB 32 gj :: ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
       (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25)
       (rget regs 26)) ->
  lib.Lib.Step.rw_cells A.Img0.rsegs mem3 (p + 18) [lib.Lib.Cells.CB 32 RcLay.ly_zero] ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 (lay_frb lyc pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos))) ->
  A.AsanRT.addressable mem3 (lay_frb lyc pos + 32) 32 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem3 md3 k ->
  wle W W4 ->
  (* TMB's post *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly4 S4 W4 mem4 md4 (k + EV_BMB) ->
  ly_F ly4 = ly_F lyc ->
  lay_box_regs regs regs4 ((spZ regs - 128) / 32 * 32) p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md (lay_frb lyc pos) ->
  frames S4 = frames S2 -> ablocks B ly4 S4 = ablocks B lyc S2 ->
  rget regs4 10 = w64 (RcSynth.rc mb (RcLay.ly_bb r)) ->
  garr8 SEGS (mrestrict (w_H W4) mem4) (lay_frb lyc pos + 32) (bmb_z (RcSynth.synth mb (RcLay.ly_bb r) nb)) ->
  tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc S2 W mem3 W4 mem4 ((spZ regs - 128) / 32 * 32)
    (fun a => lay_frb lyc pos + 32 <= a < lay_frb lyc pos + 32 + 32) ->
  (* the continuation at 0x858f4, after the release *)
  (forall ms5 md5,
     (exists s0, ctrl_lay_block_F_R3_on.lay_F_R3_end_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
        (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
        (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
        (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (A.MemNorm.normalize A.Img0.rsegs mem4)
        p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md 0 (ly_F lyc) fr nil mb nb nil
        (A.MemNorm.normalize A.Img0.rsegs mem4) gj (lay_frb lyc pos) ((spZ regs - 128) / 32 * 32) pos
        (Z_to_bv 64 (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos)) s0 /\
        A.MemNorm.ms_rel A.Img0.rsegs ms5 s0 /\ A.MemNorm.ro_same A.Img0.rsegs mem4 (ms_mem ms5)) ->
     ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly4
       (lib.Reusable.YG01.stack_free_state 1 pos S4) W4 (ms_mem ms5) md5 (k + EV_BMB) ->
     lib.Lib.Frame.munch [(p + 18, p + 50); ((spZ regs - 128) / 32 * 32 - 2224, (spZ regs - 128) / 32 * 32);
       (A.AsanRT.shadow_addr (lay_frb lyc pos), A.AsanRT.shadow_addr (lay_frb lyc pos) + 16);
       (lay_frb lyc pos, lay_frb lyc pos + 8);
       (asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos, asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos + 1)]
       mem4 (ms_mem ms5) ->
     (* what region R4 takes at its base memory *)
     YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W4) (ms_mem ms5)) ->
     lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms5) (spZ regs + -128)
       (lib.Lib.Cells.CB 32 gj :: ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
          (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25)
          (rget regs 26)) ->
     lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms5) (p + 18)
       [lib.Lib.Cells.CB 32 (ctrl_lay_block.LAY md 0 fr nil mb nb nil)] ->
     SRr SEGS W4 (mkCfg ms5 md5) Q) ->
  SRr SEGS W4 (mkCfg (rmkst regs4 (w64 0x85828) mem4 (lib.Reusable.YK11.seg_rom SEGS)) md4) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb gj S2 mem2 pos k mem3 W4 ly4 S4 regs4 mem4
    md4 md3 Q Hal Hlo Hhi Htp HROc Hr Hfl Hk Hrom (ic & Emd & Hic) Hmd Hmbl HNM Hp0 Hp50 Hamr HTW HAF HHU HPB Hfrs2 Eab
    HACK Hpos HFGT HFhi HF64 HMU3 RW1 RW2 BW AD3 HJ3 Hwle HJ4 EF4 HRR4 Hfrs4 Eab4 Ha04 Hg4 HK4 K.
  rewrite lay_TLAY_val in Hlo.
  assert (Efa : frame_addr lyc 1 pos = lay_frb lyc pos).
  { unfold lay_frb, frame_addr. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & G3 & _).
    rewrite <- G3. reflexivity. }
  assert (Efa4 : frame_addr ly4 1 pos = lay_frb lyc pos) by (rewrite <- Efa; unfold frame_addr; rewrite EF4; reflexivity).
  assert (Efl4 : flag_addr ly4 1 pos = asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos).
  { unfold flag_addr. rewrite EF4. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & _ & G4 & _).
    rewrite <- G4. reflexivity. }
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  assert (HFlo : ly_F lyc <= lay_frb lyc pos).
  { unfold lay_frb, asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B. cbn [Z.of_nat]. lia. }
  assert (HFcls : lay_frb lyc pos + 128 <= ly_F lyc + 36864 + 2 * 2 ^ 20).
  { unfold lay_frb, asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B. cbn [Z.of_nat].
    unfold asan_stack_malloc_c.fs_M in Hpos. cbn [Z.of_nat] in Hpos. lia. }
  assert (HFfl : ly_F lyc <= asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos < ly_F lyc + 36864).
  { unfold asan_stack_malloc_c.fs_flag. unfold asan_stack_malloc_c.fs_M in Hpos. cbn [Z.of_nat] in Hpos |- *. lia. }
  set (A := (spZ regs - 128) / 32 * 32) in *.
  set (f := VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) in *.
  set (frb := lay_frb lyc pos) in *.
  set (fa := asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos) in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & Hstk & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  pose proof HACK as (_ & _ & HK3 & _). pose proof HK4 as (HQ1 & HQ2 & HQ3 & HQ4 & HQ5 & HQ6).
  assert (Hinro : forall x, in_roP SEGS RLO RHI x -> in_img SEGS x).
  { intros x [(s & Hs & _ & Hb) | Hx]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG x Hx)]. }
  unfold asan_stack_malloc_c.ASAN_GT, asan_stack_malloc_c.FS_SIZE in HFGT, HFhi, HPB.
  (* the views at mem4 on the image: TMB's image clause, R2's write set, acall_kept's image clause *)
  assert (HV4 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
                  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) memc a).
  { intros a Ha Ho He. transitivity (aview SEGS (w_H W) mem3 a); [exact (HQ3 a Ha Ho He)|].
    rewrite (lay_view_img_munch W mem2 mem3 _ HMU3); [exact (HK3 a Ha Ho He) | | exact Ha].
    intros x Hx. cbn [lib.Lib.Frame.outside]. unfold A.AsanRT.ASAN_K. unfold A.Prog.ImgBounds.IMG_HI in Hx.
    repeat split; try exact I; clear - Hx HFGT HPB Hc0 Hceil Hslo Hlo Hhi; Z.div_mod_to_equations; lia. }
  assert (HRO4 : YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W4) mem4)) by exact (lay_arodata_kept _ _ HROc HV4).
  destruct (LayBase.rt_facts_C B LAWS CTS RLO RHI ly4 S4 W4 mem4 md4 HAR4
              (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO4 (Z.le_refl _) (Z.le_refl _)))
    as (Hro4 & AC0 & SC4).
  assert (Hslo' : ly_stk_lo ly4 <= spZ regs - 4512) by (rewrite Eslo; lia).
  assert (Hshi' : spZ regs <= ly_stk_hi ly4) by (rewrite Eshi; lia).
  destruct (LayBase.win_facts B LAWS ly4 S4 W4 mem4 md4 (spZ regs - 4512) (spZ regs) HAR4 Hro4 Hslo' ltac:(lia) Hshi'
              (fun a Ha => Hpres4 a ltac:(lia))) as (ST0 & AW0 & HHM & HAE & Hceil').
  assert (HHU4 : tfr_hull ly4 S4 (p + 18) 32).
  { destruct HHU as (cid & pos' & Hin & Hc & Hh). exists cid, pos'. rewrite Hfrs4, Hfrs2.
    unfold frame_addr in Hh |- *. rewrite EF4. split; [right; exact Hin | split; [exact Hc | exact Hh]]. }
  destruct (lay_blk_range ly4 S4 W4 mem4 md4 p HAR4 HHU4) as (HGT & HFtop & HB1 & HB2 & HBF).
  rewrite EF4 in HGT, HFtop, HB1, HB2.
  destruct HFR_rng as (FR1 & FR2 & FR3). destruct HCAT_rng as (CA1 & CA2 & CA3).
  unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, ROW_BYTES, CAT_BYTES in *.
  unfold asan_stack_malloc_c.ASAN_GT in HGT. unfold kFakeFramesOff, kFakeStackSize in HB1, HB2, HFtop.
  (* route (C): the region R3 takes is in the cut's shadow at the box call's return (FA disjunct, state S4) *)
  assert (HFal4 : ly_F ly4 mod 4096 = 0)
    by exact (lib.Reusable.YG0f.lo_F_al _ (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR4))).
  assert (SR3 : A.ShadowRwOn.shadow_rw_on (ctrl_lay_block_F_R3_on.lay_F_R3_shadow_R (ly_F lyc) p)
                  (A.MemNorm.normalize A.Img0.rsegs mem4)).
  { refine (A.ShadowRwOn.shadow_rw_on_mono _ _ _ _ SC4).
    intros a Ha. rewrite <- EF4 in Ha.
    exact (lay_on_R_cut ly4 S4 p a HFal4 ltac:(rewrite EF4; lia) ltac:(rewrite EF4; lia) Ha). }
  assert (Hf0 : 0 <= f) by (subst f; lia).
  assert (Hf1 : f + 24 <= asan_stack_malloc_c.ASAN_GT) by (subst f; unfold asan_stack_malloc_c.ASAN_GT; lia).
  pose proof (LayBase.lay_fp0_facts B LAWS CTS ly4 S4 W4 mem4 md4 (spZ regs) p f HAR4 Hro4 ltac:(lia) HAE Hf0 Hf1 HBF)
    as FP0. rewrite EF4 in FP0.
  pose proof (LayBase.lay_tls0_facts B LAWS CTS (A.ProgWorldTlsApart.fp_tls_apart B) ly4 S4 W4 mem4 md4
                (spZ regs - 4512) (spZ regs) HAR4 Hro4
                Hslo' Hshi') as TLS0. rewrite EF4 in TLS0.
  (* the model record and the name at mem4 *)
  assert (HmdR : VAL (A_OBJ A_CAT) <= md /\ md + 296 <= VAL (A_OBJ A_CAT) + 11 * 296) by (rewrite Emd; nia).
  assert (Hmd8 : md mod 8 = 0) by (rewrite Emd; clear - CA3; Z.div_mod_to_equations; lia).
  assert (HmdB : lib.Lib.Mem.bytes_at A.Img0.rsegs mem4 md mb).
  { apply (lay_view_kept_bytes W W4 memc mem4 md mb); [lia | rewrite Hmbl; lia | exact Hmd |].
    intros j Hj. rewrite Hmbl in Hj.
    assert (Hj' : 0 <= Z.of_nat j < 296) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
    destruct (HCAT_ro (md + Z.of_nat j) ltac:(lia)) as (X1 & X2 & X3). exact (HV4 _ (Hinro _ X1) X2 X3). }
  assert (HNM2 : (RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
            RcBox.name_ok nb /\ lib.Lib.Mem.bytes_at A.Img0.rsegs mem4 (RcSynth.rname mb) nb /\
            0 <= RcSynth.rname mb /\ 1 <= Z.of_nat (length nb) /\
            RcSynth.rname mb + Z.of_nat (length nb) <= 0x5fe000 /\
            A.AsanRT.addressable mem4 (RcSynth.rname mb) (Z.of_nat (length nb))).
  { intros Hb5 Hh Hn. destruct (HNM Hb5 Hh Hn) as (Hok & Hg & (q & sz & Hq & Hq1 & Hq2) & Hrn).
    pose proof Hok as ((L1 & L2) & _).
    assert (Hlen : 1 <= Z.of_nat (length nb)) by (apply (Nat2Z.inj_le 1) in L1; exact L1).
    destruct (Hrn (RcSynth.rname mb) ltac:(lia)) as (Y1 & _).
    destruct (Hrn (RcSynth.rname mb + Z.of_nat (length nb) - 1) ltac:(lia)) as (Y2 & _).
    pose proof (lay_img_below _ (Hinro _ Y2)) as Yb. pose proof (A.ProgWorld.pws_segs_low _ (Hinro _ Y1)) as Ya.
    unfold A.Prog.ImgBounds.IMG_HI in Yb.
    split; [exact Hok|]. split.
    - apply (lay_view_kept_bytes W W4 memc mem4 _ nb); [lia | lia | exact Hg |].
      intros j Hj.
      assert (Hj' : 0 <= Z.of_nat j < Z.of_nat (length nb))
        by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
      destruct (Hrn (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as (Z1 & Z2 & Z3). exact (HV4 _ (Hinro _ Z1) Z2 Z3).
    - split; [lia|]. split; [exact Hlen|]. split; [lia|].
      apply (lay_glob_addressable ly4 S4 W4 mem4 md4 q sz); [exact HAR4 | exact Hq | lia | lia | lia | lia |
        unfold A.AsanRT.LOWMEM_END; lia]. }
  set (nm := A.MemNorm.normalize A.Img0.rsegs mem4) in *.
  (* the class-1 frame's bytes and shadow at mem4, and their view equalities with mem3 (TMB's frame clause) *)
  assert (Hin1 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  assert (Hin14 : In (1, pos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  destruct (al_frames _ _ LAWS ly4 S4 W4 mem4 md4 1 pos HAR4 Hin14) as (_ & _ & HFRb & HFRs).
  rewrite Efa4, E128 in HFRb, HFRs. change (128 / 8) with 16 in HFRs.
  (* the raw bytes TMB keeps (W-visible at mem3, view kept by tcj_kept) *)
  pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  assert (RAW : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem3 a -> ~ in_img SEGS a ->
            aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem3 a -> mem4 (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
  { intros a Ha (Hh & _) Hni E. apply (lay_raw_of_aview2 W W4 mem3 mem4 a Ha Hh); [| exact Hni | exact E].
    destruct (w_H W4 (Z_to_bv 64 a)) eqn:E4; [|reflexivity]. rewrite (Hwle _ E4) in Hh. discriminate Hh. }
  assert (NIMG : forall a, A.Prog.ImgBounds.IMG_HI <= a -> ~ in_img SEGS a).
  { intros a Ha Hi. pose proof (lay_img_below a Hi). lia. }
  unfold A.Prog.ImgBounds.IMG_HI in NIMG.
  destruct (al_frames _ _ LAWS lyc S2 W mem3 md3 1 pos HAR3 Hin1) as (_ & _ & HFRb3 & HFRs3).
  rewrite Efa, E128 in HFRb3, HFRs3. change (128 / 8) with 16 in HFRs3.
  destruct HHU as (cid & pos' & HinB & HcB & HhB1 & HhB2).
  assert (HinB2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact HinB).
  destruct (al_frames _ _ LAWS lyc S2 W mem3 md3 cid pos' HAR3 HinB2) as (_ & _ & HBb3 & HBs3).
  pose proof (YG0s.frame_facts B lyc S2 _ cid pos' (proj1 HAR3) HinB2) as (BQ1 & BQ2 & _ & _ & BQ5 & _ & _ & BQ8 & _ & BQ10 & _).
  (* the saved registers and gj, the block's zeros, the flag pointer: TMB keeps them *)
  assert (RW1' : lib.Lib.Step.rw_cells A.Img0.rsegs mem4 (spZ regs + -128)
    (lib.Lib.Cells.CB 32 gj :: ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
       (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25)
       (rget regs 26))).
  { apply (LayLib.rw_cells_agree mem3 mem4 _ _ RW1). intros i Hi.
    cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_block.SAVES] in Hi.
    apply (RAW (spZ regs + -128 + i)); [lia | apply Hpres3; lia | apply NIMG; lia |].
    apply HQ1; [lia | change REAC_BOX_MODEL_BLOCK_STK with 4320; lia | cbn beta; lia]. }
  assert (RW2' : lib.Lib.Step.rw_cells A.Img0.rsegs mem4 (p + 18) [lib.Lib.Cells.CB 32 RcLay.ly_zero]).
  { apply (LayLib.rw_cells_agree mem3 mem4 _ _ RW2). intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi.
    assert (Hx : frame_addr lyc cid pos' <= p + 18 + i < frame_addr lyc cid pos' + fs_frame_bytes cid)
      by (clear - Hi HhB1 HhB2; Z.div_mod_to_equations; lia).
    destruct (HBb3 (p + 18 + i) Hx) as (Hp & _).
    apply (RAW (p + 18 + i)); [lia | exact Hp | apply NIMG; lia |].
    apply (HQ4 cid pos' _ HinB2); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | cbn beta; lia]. }
  assert (BW' : lib.Lib.Mem.bytes_at A.Img0.rsegs mem4 (frb + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 fa))).
  { apply (LayLib.bytes_at_agree mem3 mem4 _ _ BW). intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
    assert (Hi' : 0 <= Z.of_nat i < 8) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hi; exact Hi]).
    destruct (HFRb3 (frb + 120 + Z.of_nat i) ltac:(lia)) as (Hp & _).
    apply (RAW (frb + 120 + Z.of_nat i)); [lia | exact Hp | apply NIMG; lia |].
    apply (HQ4 1 pos _ Hin1); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, E128; lia | cbn beta; lia]. }
  (* the fake stack is in low or high application memory: its shadow is apart from its bytes *)
  pose proof HAR4 as (M4 & _). pose proof (am_layout _ _ _ _ M4) as LO4.
  destruct (proj1 (Forall_forall _ _) (lo_app _ LO4) (ly_F ly4, kFakeStackSize)
              ltac:(unfold owned_extents; cbn; tauto)) as [E0 E1].
  cbn [fst snd] in E0, E1. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in E0, E1.
  rewrite EF4 in E0, E1.
  assert (HFlh : frb + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= frb) by lia.
  assert (Hfrb47 : frb + 128 <= 2 ^ 47) by lia.
  assert (AD4 : A.AsanRT.addressable mem4 (frb + 32) 32).
  { apply (lay_addressable_kept mem3 mem4 _ _ AD3). intros x Hx.
    assert (Es : A.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr frb + (x - frb) / 8)
      by (unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF;
          clear - Hx HF64; Z.div_mod_to_equations; lia).
    assert (Hj : 0 <= (x - frb) / 8 < 16) by (clear - Hx; Z.div_mod_to_equations; lia).
    assert (Hsb : 0x7fff8000 <= A.AsanRT.shadow_addr x < 2 ^ 47)
      by (unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; clear - Hx Hfrb47 HFGT; Z.div_mod_to_equations; lia).
    assert (HnE : ~ (frb + 32 <= A.AsanRT.shadow_addr x < frb + 32 + 32)).
    { unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. apply (lay_sh_apart x (frb + 32) 32); lia. }
    destruct (HFRs3 _ Hj) as (Hp & _). rewrite Es in Hsb, HnE |- *.
    apply (RAW _); [lia | exact Hp | apply NIMG; lia |].
    apply (HQ4 1 pos _ Hin1); [| cbn beta; exact HnE].
    right. unfold in_zr. cbn [fst snd]. rewrite Efa, E128. change (128 / 8) with 16.
    clear - Hj. revert Hj. generalize ((x - frb) / 8). intros q Hq. lia. }
  (* the block is addressable at mem4: afobj's view, kept memc -> mem2 -> mem3 -> mem4 *)
  assert (Happ : forall a, p + 18 <= a < p + 50 -> A.AsanRT.app_mem a).
  { intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold A.AsanRT.app_mem,
      A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (AR4 : A.AsanRT.addressable mem4 (p + 18) 32).
  { destruct HAF as (_ & _ & Hra).
    apply (lay_raddr_addressable W4 mem4 (p + 18) 32); [| lia | lia | intros a Ha; apply Happ; lia |
      unfold A.AsanRT.APPMEM_END; lia].
    intros x Hx. destruct (Hra x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    set (sx := lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF x) in *.
    assert (Esx : sx = x / 8 + 2147450880) by (subst sx; unfold lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF; ring).
    assert (HBlh : p + 50 <= 0x7fff8000 \/ 0x10007fff8000 <= p + 18) by lia.
    assert (Hsx : in_zr sx (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)).
    { rewrite Esx. unfold in_zr, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. cbn [fst snd].
      unfold page_aligned in BQ5. clear - HhB1 HhB2 Hx BQ5 BQ8 BQ10. Z.div_mod_to_equations; lia. }
    assert (HnEs : ~ (frb + 32 <= sx < frb + 32 + 32)) by (rewrite Esx; apply (lay_sh_apart x (frb + 32) 32); lia).
    rewrite <- Hs. transitivity (aview SEGS (w_H W) mem3 sx); [exact (HQ4 cid pos' sx HinB2 (or_intror Hsx) HnEs) |].
    assert (Hsx' : lib.Lib.Frame.outside [(spZ regs - 4512, spZ regs); (frb, frb + 24);
                     (frb / 8 + A.AsanRT.ASAN_K, frb / 8 + A.AsanRT.ASAN_K + 12); (p + 18, p + 50)] sx).
    { rewrite Esx. cbn [lib.Lib.Frame.outside]. unfold A.AsanRT.ASAN_K.
      repeat split; try exact I;
        clear - Hx HB1 HFcls HFlo HFGT HFlh HBlh Hc0 Hceil' Hp50; Z.div_mod_to_equations; lia. }
    assert (Hsxr : 0 <= sx < 2 ^ 64) by (rewrite Esx; clear - Hx Hp50 Hp0; Z.div_mod_to_equations; lia).
    transitivity (aview SEGS (w_H W) mem2 sx).
    - apply aview_eq_of. unfold mrestrict. rewrite (HMU3 (Z_to_bv 64 sx)); [reflexivity|].
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. exact Hsx'.
    - pose proof HACK as (_ & _ & _ & HK4' & _). exact (HK4' cid pos' sx HinB (or_intror Hsx) (fun HF => HF)). }
  (* the Section facts of the re-based stretch at nm *)
  assert (Etp : bv_unsigned (reg_get regs 4) = A.AsanRT.RT_TP).
  { change (reg_get regs 4) with (rget regs 4). rewrite Htp, (A.ProgWorld.as_tp_RT_TP B CTS). unfold w64.
    apply A.ProgWorld_Fs.pw_u64. unfold A.AsanRT.RT_TP. lia. }
  assert (FP0' : RcAsanFP.fp [0%nat; 1%nat] nm (bv_unsigned (reg_get regs 4)) (ly_F lyc)
                   (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs)
                   (ctrl_lay_block_c.ctrl_lay_block_W p (spZ regs)) (ctrl_lay_block_c.ctrl_lay_block_D p f))
    by (rewrite Etp, lay_K_val; exact FP0).
  assert (TLS0' : ctrl_lay_block_c.ctrl_lay_block_tls nm (bv_unsigned (reg_get regs 4)) (ly_F lyc)
                    (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs))
    by (rewrite Etp, lay_K_val; exact TLS0).
  assert (AW0' : A.AsanRT.addressable nm (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
    by (rewrite lay_K_val; replace 4512 with (spZ regs - (spZ regs - 4512)) at 2 by lia; exact AW0).
  assert (ST0' : lib.Lib.Frame.stk A.Img0.rsegs nm (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs))
    by (rewrite lay_K_val; exact ST0).
  assert (HHM' : A.AsanRT.HIGHMEM_BEG <= spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) by (rewrite lay_K_val; exact HHM).
  assert (Rp : 0 <= p < 2 ^ 64) by lia.
  assert (Rf : 0 <= f < 2 ^ 64) by (subst f; lia).
  assert (Rmd : 0 <= md < 2 ^ 64) by lia.
  assert (Rg : 0 <= 0 < 2 ^ 64) by lia.
  assert (DJ1 : RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) (p + 18) (p + 50))
    by (unfold RcLay.ly_dj; rewrite lay_K_val; lia).
  assert (DJ2 : RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) f (f + 24))
    by (unfold RcLay.ly_dj; rewrite lay_K_val; subst f; lia).
  assert (DJ3m : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) md (md + 296) /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcLay.ly_dj (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs) (RcSynth.rname mb)
                 (RcSynth.rname mb + Z.of_nat (length nb)))).
  { intros _ _. unfold RcLay.ly_dj. rewrite lay_K_val. split; [lia|]. rewrite Hk. intros H5 Hh Hn.
    destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _). lia. }
  assert (F8 : f mod 8 = 0) by (subst f; clear - FR3; Z.div_mod_to_equations; lia).
  assert (F24 : f + 24 <= 2 ^ 64) by (subst f; lia).
  assert (FB : lib.Lib.Mem.bytes_at A.Img0.rsegs nm f fr)
    by exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem4 f fr Hro4 (lay_row_bytes W4 mem4 r fr HRO4 Hr Hfl Hrom)).
  assert (K9 : RcLay.ly_k fr <= 9) by lia.
  assert (P0 : p <> 0) by lia.
  assert (P50 : p + 50 <= 2 ^ 64) by lia.
  assert (DB1 : RcLay.ly_dj (p + 18) (p + 50) f (f + 24)) by (unfold RcLay.ly_dj; subst f; lia).
  assert (DB3 : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 -> RcLay.ly_dj (p + 18) (p + 50) md (md + 296))
    by (intros _ _; unfold RcLay.ly_dj; lia).
  assert (DBN : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 -> (RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) ->
                RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
                RcLay.ly_dj (p + 18) (p + 50) (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))).
  { intros _ _ H5 Hh Hn. rewrite Hk in H5. destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _).
    unfold RcLay.ly_dj. lia. }
  assert (MDP : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            md mod 8 = 0 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at A.Img0.rsegs nm md mb /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcBox.name_ok nb /\ lib.Lib.Mem.bytes_at A.Img0.rsegs nm (RcSynth.rname mb) nb)).
  { intros _ _. split; [exact Hmd8|]. split; [exact Hmbl|].
    split; [exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem4 md mb Hro4 HmdB)|].
    rewrite Hk. intros H5 Hh Hn. destruct (HNM2 H5 Hh Hn) as (N0 & N1 & _).
    split; [exact N0 | exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem4 _ nb Hro4 N1)]. }
  assert (AR : A.AsanRT.addressable nm (p + 18) 32) by exact (A.MemNormTr.addressable_normalize mem4 _ _ Hro4 AR4).
  assert (AP50 : A.AsanRT.app_mem (p + 50)).
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold A.AsanRT.app_mem,
      A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (ARDJ : p + 50 <= A.AsanRT.RT_LO \/ A.AsanRT.RT_HI <= p + 18) by (right; unfold A.AsanRT.RT_HI; lia).
  assert (AMD : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            A.AsanRT.addressable nm md 296 /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 -> A.AsanRT.addressable nm (RcSynth.rname mb) (Z.of_nat (length nb)))).
  { intros _ _. split.
    - apply (A.MemNormTr.addressable_normalize mem4 md 296 Hro4).
      apply (lay_glob_addressable ly4 S4 W4 mem4 md4 (VAL (A_OBJ A_CAT)) (11 * 296)); [exact HAR4 | exact HCAT_glob |
        lia | lia | lia | lia | unfold A.AsanRT.LOWMEM_END; lia].
    - rewrite Hk. intros H5 Hh Hn. destruct (HNM2 H5 Hh Hn) as (_ & _ & _ & _ & _ & N5).
      exact (A.MemNormTr.addressable_normalize mem4 _ _ Hro4 N5). }
  assert (FPM_gen : forall lo hi, 0 <= lo -> hi <= 0x5fe000 -> lo <= hi ->
            RcAsanFP.fp_dj [(lo, hi)] (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc))).
  { intros lo hi H0 H1 H2. unfold RcAsanFP.fp_dj, RcAsanFP.fp_w, RcAsanFP.fp_w1. cbn [flat_map app].
    unfold asan_stack_malloc_c.fs_hint, asan_stack_malloc_c.fs_flag, asan_stack_malloc_c.fs_frame,
      asan_stack_malloc_c.fs_M, asan_stack_malloc_c.fs_B. cbn [Z.of_nat].
    unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
    all: clear - H0 H1 H2 HGT; Z.div_mod_to_equations; lia. }
  assert (FPM : 3 <= RcLay.ly_k fr <= 9 -> md <> 0 ->
            RcAsanFP.fp_dj [(md, md + 296)] (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc)) /\
            ((RcLay.ly_bb (RcLay.ly_k fr) = 5 \/ RcLay.ly_bb (RcLay.ly_k fr) = 6) -> RcSynth.has mb <> 0 ->
               RcSynth.rname mb <> 0 ->
               RcAsanFP.fp_dj [(RcSynth.rname mb, RcSynth.rname mb + Z.of_nat (length nb))]
                 (RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc)))).
  { intros _ _. split; [apply FPM_gen; lia|]. rewrite Hk. intros H5 Hh Hn.
    destruct (HNM2 H5 Hh Hn) as (_ & _ & N0 & N1 & N2 & _). apply FPM_gen; lia. }
  (* the box call's result and the block's base bytes *)
  set (rr := RcSynth.rc mb (RcLay.ly_bb r)) in *.
  assert (Hrr : -1 <= rr <= 1).
  { subst rr. unfold RcSynth.rc. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
  assert (Elen : length (RcSynth.synth mb (RcLay.ly_bb r) nb) = 32%nat) by exact (RcSynthLib.rs_synth_len mb _ nb Hmbl).
  assert (EBASE : ctrl_lay_block.BASE md fr nil mb nb = RcLay.ly_Z md mb nb (RcLay.ly_bb r)).
  { unfold ctrl_lay_block.BASE, RcLay.ly_base. rewrite Hk.
    destruct (Z.eqb_spec r 0) as [E|E]; [lia|]. destruct (Z.eqb_spec r 1) as [E'|E']; [lia|].
    destruct (Z.eqb_spec r 2) as [E''|E'']; [lia | reflexivity]. }
  assert (HBr1 : rr = 1 -> lib.Lib.Mem.bytes_at A.Img0.rsegs nm (frb + 32) (ctrl_lay_block.BASE md fr nil mb nb) /\
                   length (ctrl_lay_block.BASE md fr nil mb nb) = 32%nat).
  { intros Er1. rewrite EBASE. unfold RcLay.ly_Z. destruct (Z.eqb_spec md 0) as [Em|Em]; [lia|].
    fold rr. rewrite Er1, Z.eqb_refl. split; [|exact Elen].
    apply (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem4 _ _ Hro4).
    apply (lay_view_kept_bytes W4 W4 mem4 mem4 (frb + 32) _); [lia | rewrite Elen; lia | exact Hg4 | intros; reflexivity]. }
  assert (HBrn : rr <> 1 -> ctrl_lay_block.BASE md fr nil mb nb = RcLay.ly_zero).
  { intros Er1. rewrite EBASE. unfold RcLay.ly_Z. destruct (Z.eqb_spec md 0) as [Em|Em]; [reflexivity|].
    fold rr. destruct (Z.eqb_spec rr 1) as [Er|Er]; [contradiction | reflexivity]. }
  (* the state at 0x85828 in the form the stretch takes *)
  pose proof HRR4 as (R2' & R3' & R4' & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  change (rmkst regs4 (w64 0x85828) mem4 (lib.Reusable.YK11.seg_rom SEGS)) with
    (lib.Lib.MState.MS regs4 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x85828) lib.Reusable.YK11.fp_csr None mem4
       (lib.Lib.PropExec.seg_rom A.Img0.rsegs)).
  apply (YA0nR.SRr_xregs_eqv SEGS W4 (lib.Lib.Regs6ss.mkR_of regs4) regs4);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs4))].
  unfold lib.Lib.Regs6ss.mkR_of.
  change (rget regs4 2) with (reg_get regs4 2) in R2'. change (rget regs4 3) with (reg_get regs4 3) in R3'.
  change (rget regs4 4) with (reg_get regs4 4) in R4'. change (rget regs4 8) with (reg_get regs4 8) in R8.
  change (rget regs4 9) with (reg_get regs4 9) in R9. change (rget regs4 18) with (reg_get regs4 18) in R18.
  change (rget regs4 19) with (reg_get regs4 19) in R19. change (rget regs4 20) with (reg_get regs4 20) in R20.
  change (rget regs4 21) with (reg_get regs4 21) in R21. change (rget regs4 22) with (reg_get regs4 22) in R22.
  change (rget regs4 23) with (reg_get regs4 23) in R23. change (rget regs4 24) with (reg_get regs4 24) in R24.
  change (rget regs4 25) with (reg_get regs4 25) in R25. change (rget regs4 26) with (reg_get regs4 26) in R26.
  change (rget regs4 27) with (reg_get regs4 27) in R27. change (rget regs4 10) with (reg_get regs4 10) in Ha04.
  rewrite R2', R3', R4', R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27, Ha04.
  refine (lay_SRr_norm HWX W4 (A.ProgBridge.RNG_W (w_H W4)) md4 _ lib.Reusable.YK11.fp_regs _ lib.Reusable.YK11.fp_csr
            mem4
            (ctrl_lay_block_F_R3_on.lay_F_R3_end_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
               (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
               (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm p f md 0
               (ly_F lyc) fr nil mb nb nil nm gj frb A pos (Z_to_bv 64 fa))
            Q (A.ProgBridge.fp_avoids_RNG_W _) Hro4 _ _).
  { apply (ctrl_lay_block_F_R3_on.lay_F_R3_run_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
             (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
             (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm p f md 0
             (ly_F lyc) fr nil mb nb nil Rp Rf Rmd Rg Hal ST0' DJ1 DJ2 DJ3m Hfl K9
             (fun E2 : RcLay.ly_k fr = 2 => False_ind _ ltac:(lia)) P0 P50 DB1 DB3 DBN MDP HHM' HAE AW0' AR AP50
             ARDJ AMD FP0' FPM MEMCF (A.ProgBridge.RNG_W (w_H W4)) nm gj rr frb frb A pos (Z_to_bv 64 fa)).
    all: try change (bv_unsigned (reg_get regs 2)) with (spZ regs); try fold A.
    - unfold ctrl_lay_block_F_R2_on.FI_on. split.
      { right. split; [exact Hpos|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
      split; [intros _; exact (A.MemNorm.bytes_at_normalize A.Img0.rsegs mem4 _ _ Hro4 BW')|].
      split; [exact AC0|]. split; [exact FP0'|]. split; [exact TLS0'|].
      intros x Hx _. change (bv_unsigned (reg_get regs 2)) with (spZ regs) in Hx. pose proof lay_K_val as EK.
      apply (lay_addr_sub nm (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) ctrl_lay_block_c.CTRL_LAY_BLOCK_K x 1 AW0');
        lia.
    - exact SR3.
    - unfold ctrl_lay_block.LC.
      split; [refine (A.MemNormTr.rw_cells_normalize mem4 _ _ Hro4 _ RW1'); intros i Hi;
              apply A.MemNormTr.ro_addr_above_img;
              cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_block.SAVES] in Hi;
              unfold A.Prog.ImgBounds.IMG_HI; lia|].
      split; [destruct (lib.Lib.Frame.stk_split A.Img0.rsegs nm _ (spZ regs + -128) _ ST0'
                ltac:(rewrite lay_K_val; lia)) as [ST1 _]; exact ST1|].
      split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|].
      split; [apply A.MemNorm.mem_inv_normalize|].
      split; [refine (A.MemNormTr.rw_cells_normalize mem4 _ _ Hro4 _ RW2'); intros i Hi;
              apply A.MemNormTr.ro_addr_above_img; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi;
              unfold A.Prog.ImgBounds.IMG_HI; lia|].
      exact FB.
    - exact (A.MemNormTr.addressable_normalize mem4 _ _ Hro4 AD4).
    - exact Hrr.
    - exact HBr1.
    - exact HBrn.
    - lia.
    - unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - left. lia.
    - left. rewrite lay_K_val. lia.
    - rewrite lay_K_val. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hpres4 a ltac:(lia))).
    - exact (A.ProgBridge.rng_bytes_RNG_W (w_H W4)).
    - exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W4)).
    - apply A.ProgBridge.rng_of_visible. unfold asan_memcpy_c.ASAN_MEMCPY_K.
      split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres4 a ltac:(lia))).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 a HAR4
        ltac:(rewrite EF4; unfold kFakeStackSize; lia))).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 a HAR4
        ltac:(rewrite EF4; unfold kFakeStackSize; lia))).
    - unfold asan_memcpy_c.ASAN_MEMCPY_K.
      destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly4 S4 W4 mem4 md4 (A - 2224) 2224 HAR4 ltac:(lia) ltac:(lia) ltac:(lia))
        as [V0 | V3]; [left; exact V0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V3)].
    - assert (HinB4 : In (cid, pos') (frames S4)) by (rewrite Hfrs4; exact HinB2).
      assert (HhB1' : frame_addr ly4 cid pos' <= (p + 18) / 64 * 64) by (unfold frame_addr in *; rewrite EF4; exact HhB1).
      assert (HhB2' : (p + 18 + 32 - 1) / 64 * 64 + 64 <= frame_addr ly4 cid pos' + fs_frame_bytes cid)
        by (unfold frame_addr in *; rewrite EF4; exact HhB2).
      destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly4 S4 W4 mem4 md4 cid pos' (p + 18) 32 HAR4 HinB4
                  ltac:(clear - HhB1'; Z.div_mod_to_equations; lia) ltac:(clear - HhB2'; Z.div_mod_to_equations; lia))
        as (_ & V2).
      destruct (V2 ltac:(lia) ltac:(clear - HhB1'; Z.div_mod_to_equations; lia)
                  ltac:(clear - HhB2'; Z.div_mod_to_equations; lia))
        as [V0 | V3]; [left; exact V0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V3)].
    - destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly4 S4 W4 mem4 md4 1 pos (frb + 32) 32 HAR4 Hin14
                  ltac:(rewrite Efa4; lia) ltac:(rewrite Efa4, E128; lia)) as (_ & V2).
      destruct (V2 ltac:(lia) ltac:(rewrite Efa4; clear - HF64; Z.div_mod_to_equations; lia)
                  ltac:(rewrite Efa4, E128; clear - HF64; Z.div_mod_to_equations; lia))
        as [V0 | V3]; [left; exact V0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ V3)].
    - reflexivity.
    - lia.
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 a HAR4
        ltac:(rewrite EF4; unfold kFakeStackSize; lia))).
    - destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly4 S4 W4 mem4 md4 1 pos frb 128 HAR4 Hin14
                  ltac:(rewrite Efa4; lia) ltac:(rewrite Efa4, E128; lia)) as (_ & V2).
      destruct (V2 ltac:(lia) ltac:(rewrite Efa4; clear - HF64; Z.div_mod_to_equations; lia)
                  ltac:(rewrite Efa4, E128; clear - HF64; Z.div_mod_to_equations; lia)) as [V0 | V3]; [lia|].
      apply A.ProgBridge.rng_of_visible.
      assert (Es1 : A.Prog.rng_asan.sh_al8_lo frb = A.AsanRT.shadow_addr frb)
        by (unfold A.Prog.rng_asan.sh_al8_lo, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K; clear - HF64;
            Z.div_mod_to_equations; lia).
      assert (Es2 : A.Prog.rng_asan.sh_al8_hi frb 128 - A.Prog.rng_asan.sh_al8_lo frb = 16)
        by (unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
            clear - HF64; Z.div_mod_to_equations; lia).
      rewrite Es2, Es1 in V3. exact V3.
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 a HAR4
        ltac:(rewrite EF4; unfold kFakeStackSize; lia))).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 a HAR4
        ltac:(rewrite EF4; unfold kFakeStackSize; lia))). }
  (* after the run: the journal step over the release (class 1) *)
  intros ms5 md5 Hrun5 HP5 Hhid5 Hsame5.
  pose proof HP5 as (s0 & HE0 & HREL5 & HROS5).
  destruct HE0 as (y1 & y5 & y6 & y7 & ya0 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y21 & y22 & y23
    & y28 & y29 & y30 & y31 & mc1 & gj1 & m3' & m4' & Es0 & MUa & FIa & LCa & MUb & WMb & RMb & MUc & WMc & RMc & MIc
    & HFc & Ew & _).
  subst s0.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL5) as [Ems5 HMR5].
  set (WR5 := [(p + 18, p + 50); (A - 2224, A); (A.AsanRT.shadow_addr frb, A.AsanRT.shadow_addr frb + 16);
               (frb, frb + 8); (fa, fa + 1)]).
  assert (MU5 : lib.Lib.Frame.munch WR5 nm m4').
  { apply (lib.Lib.Frame.munch_trans _ nm m3' m4'); [apply (lib.Lib.Frame.munch_trans _ nm mc1 m3') |].
    - eapply lib.Lib.Frame.munch_weaken; [| exact MUa]. intros x Hx. subst WR5. cbn [lib.Lib.Frame.outside] in Hx |- *.
      unfold asan_memcpy_c.ASAN_MEMCPY_K. clear - Hx. lia.
    - eapply lib.Lib.Frame.munch_weaken; [| exact MUb]. intros x Hx. subst WR5. cbn [lib.Lib.Frame.outside] in Hx |- *.
      clear - Hx. lia.
    - eapply lib.Lib.Frame.munch_weaken; [| exact MUc]. intros x Hx. subst WR5. cbn [lib.Lib.Frame.outside] in Hx |- *.
      clear - Hx. lia. }
  assert (HMU5 : lib.Lib.Frame.munch WR5 mem4 (ms_mem ms5))
    by exact (A.MemNorm.munch_rel A.Img0.rsegs _ mem4 nm (ms_mem ms5) m4'
               (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem4 Hro4) HMR5 HROS5 MU5).
  assert (HFL5 : lib.Reusable.YP09.mbyte SEGS (ms_mem ms5) (flag_addr ly4 1 pos) = Some (Z_to_bv 8 0)).
  { rewrite Efl4. destruct HFc as [[_ Hb] _]. destruct Hb as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)).
    cbn [nth_error lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app] in Hb.
    change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. fold fa in Hb.
    refine (eq_trans (A.MemNorm.mbyte_rel _ _ _ _ HMR5) _). exact Hb. }
  assert (HJ5 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly4
                  (lib.Reusable.YG01.stack_free_state 1 pos S4) W4 (ms_mem ms5) md5 (k + EV_BMB)).
  { lazymatch type of Hrun5 with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      refine (A.ProgWorldAstack.ctl_release_of_free_law B 1 LAWS ASF HWX ltac:(lia) STK sp0 FP ly S W0 mem0 md0 own
                ly4 S4 W4 ms0 ms5 md4 md5 (k + EV_BMB) pos
                _ WR5 HJ4 Hrun5 (A.ProgBridge.fp_avoids_RNG_W _) HMU5 Hsame5 _ HFL5) end.
    intros a Ha Hout. apply lay_not_outside in Hout. subst WR5.
    rewrite !Exists_cons, Exists_nil in Hout. cbn [fst snd] in Hout.
    rewrite Eab4, Eab.
    destruct Hout as [H | [H | [H | [H | [H | []]]]]].
    - left. destruct (HTW a ltac:(lia)) as (Haw & _). unfold awr_byte in Haw |- *.
      destruct Haw as [X | [X | [X | (cid' & pos'' & Hin & X)]]];
        [left; exact X | right; left; exact X | right; right; left; exact X |].
      right. right. right. exists cid', pos''. split; [right; exact Hin|]. unfold frame_addr in X |- *. rewrite EF4. exact X.
    - left. left. unfold asan_memcpy_c.ASAN_MEMCPY_K in *. lia.
    - left. right. right. right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      rewrite Efa4, E128. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in H. clear - H. Z.div_mod_to_equations; lia.
    - left. right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite Efa4, E128. lia.
    - right. rewrite Efl4. lia. }
  (* R4's base facts at ms_mem ms5 *)
  assert (HBlh : p + 50 <= 0x7fff8000 \/ 0x10007fff8000 <= p + 18) by lia.
  assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> (x < A.Prog.ImgBounds.IMG_HI \/ spZ regs - 128 <= x < spZ regs) ->
            lib.Lib.Frame.outside WR5 x).
  { intros x Hx0 Hx. subst WR5. cbn [lib.Lib.Frame.outside]. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    unfold A.Prog.ImgBounds.IMG_HI in Hx.
    repeat split; try exact I;
      clear - Hx HPB HFGT HFlo HFfl HFcls HFhi HFtop HGT HB1 HB2 HFlh HBlh Hc0 Hceil' HA1 Hlo Hspr Hfrb47;
      Z.div_mod_to_equations; lia. }
  assert (HMUx : forall x, 0 <= x < 2 ^ 64 -> (x < A.Prog.ImgBounds.IMG_HI \/ spZ regs - 128 <= x < spZ regs) ->
            ms_mem ms5 (Z_to_bv 64 x) = mem4 (Z_to_bv 64 x)).
  { intros x Hx0 Hx. apply HMU5. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. exact (HOUT x Hx0 Hx). }
  assert (HRO5 : YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W4) (ms_mem ms5))).
  { apply (lay_arodata_kept _ _ HRO4). intros a Ha Ho He.
    pose proof (lay_img_below a Ha) as Hb. pose proof (A.ProgWorld.pws_segs_low a Ha) as Hl. unfold kLowMemEnd in Hl.
    apply aview_eq_of. unfold mrestrict. rewrite (HMUx a ltac:(lia) (or_introl Hb)). reflexivity. }
  assert (HSV5 : lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms5) (spZ regs + -128)
    (lib.Lib.Cells.CB 32 gj :: ctrl_lay_block.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
       (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25)
       (rget regs 26))).
  { apply (LayLib.rw_cells_agree mem4 (ms_mem ms5) _ _ RW1'). intros i Hi.
    match type of Hi with context [Z.of_nat ?n] => replace (Z.of_nat n) with 128 in Hi by reflexivity end.
    apply HMUx; [lia | right; lia]. }
  assert (HBK5 : lib.Lib.Step.rw_cells A.Img0.rsegs (ms_mem ms5) (p + 18)
                   [lib.Lib.Cells.CB 32 (ctrl_lay_block.LAY md 0 fr nil mb nb nil)]).
  { pose proof LCa as (_ & _ & _ & _ & _ & BKa & _).
    apply (A.MemNormTr.rw_cells_of_rel _ _ _ _ HMR5).
    apply (LayLib.rw_cells_agree m3' m4'); [apply (LayLib.rw_cells_agree mc1 m3' _ _ BKa) |].
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply MUb.
      unfold lib.Lib.Mem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. cbn [lib.Lib.Frame.outside]. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
      repeat split; try exact I; clear - Hi HFlo HFcls HB1 HB2 HFlh HBlh HFGT Hfrb47; Z.div_mod_to_equations; lia.
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi. apply MUc.
      unfold lib.Lib.Mem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. cbn [lib.Lib.Frame.outside].
      repeat split; try exact I; clear - Hi HFfl HFcls HB1 HB2; lia. }
  exact (K ms5 md5 HP5 HJ5 HMU5 HRO5 HSV5 HBK5).
Qed.

(* ================================================================================================================
   8. Region R4 (0x858f4 -> ret) and the glue theorem.
   fuzz_grant overlap: the epilogue (stretch k = 8) is the twin of grant's proved epilogue in CtrlLayBlock.v
   (a working branch 5aae1e8a0ce).
   ================================================================================================================ *)
Lemma lay_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma lay_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

(* kb_ret_pc (lib/A/KindBGlue.v:61), same proof. *)
Lemma lay_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> lib.Lib.MState.ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  assert (Hm : bv_unsigned k mod 2 = 0).
  { rewrite <- Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite lay_mod2_land. apply lay_land_m2. }
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Lemma lay_garr8_of_bytes : forall (W : world SEGS) (m : word -> option byte) a (bs : list byte),
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs ->
  (forall j, (j < length bs)%nat -> w_H W (Z_to_bv 64 (a + Z.of_nat j)) = false) ->
  garr8 SEGS (mrestrict (w_H W) m) a (bmb_z bs).
Proof.
  intros W m a bs (H0 & H1 & Hb) Hh j Hj. unfold bmb_z in Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  assert (Hv : aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j (bmb_z bs) 0)).
  { rewrite (A.ProgWorld.aview_vis_mrd W m _ (Hh j Hj)). specialize (Hb j Hj).
    change (lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 (a + Z.of_nat j))) with
      (lib.Lib.Mem.mrd A.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat j))).
    rewrite Hb, E. cbn [option_map]. f_equal. unfold bmb_z.
    rewrite (nth_indep (map _ bs) 0 (bv_unsigned b)) by (rewrite length_map; exact Hj).
    rewrite map_nth. rewrite (nth_error_nth bs j b E). reflexivity. }
  exact (A.Prog.YC88.val_mem1_of_aview SEGS (w_H W) m _ _ Hv).
Qed.

Lemma lay_addr_val : BASE + AF_ctrl_lay_block = 0x855f4.
Proof. vm_compute. reflexivity. Qed.

Theorem pb_ctrl_lay_block : tctrl_lay_block_spec (SK := SK) B GLOBS (BASE + AF_ctrl_lay_block) RLO RHI.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p r i md mb nb
    HJ HRO Hra H4096 Hgp Htp Ha0 Ha1 Hr Ha2 Emd Hi Ha3 Hal Hlo Hhi Hroom1 Hroom0 Hp0 Hp50 Hamr Hnimg HTW HAF HHU Hmd
    Hmbl HNM.
  rewrite lay_addr_val.
  destruct (HFR_rom r Hr) as (fr & Hfl & Hk & Hrom).
  pose proof HJ as (HAR & HlyJ & _).
  destruct (LayBase.rt_facts_C B LAWS CTS RLO RHI lyc Sc W memc mdc HAR
              (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)))
    as (Hro & AC0 & _).
  (* R1 and the class-1 allocator event *)
  apply (lay_to_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) md
           _ HJ Hra Hgp Htp Ha0 Ha1 Ha2 Ha3 Hal Hlo Hhi Hroom1 Hro AC0).
  intros S2 regs2 mem2 md2 pos HJ2 Hfrs2 Hnin Eab HfS HAR2 Ha02 HRR HFS HACK HSV.
  pose proof HFS as HFS'. unfold lay_fs1 in HFS'. cbv zeta in HFS'.
  destruct HFS' as (Hpos & _ & _ & _ & _ & _ & _ & _ & HF64 & HFlo & HFhi & HFGT & _).
  assert (HHU2 : tfr_hull lyc S2 (p + 18) 32).
  { destruct HHU as (cid & pos' & Hin & Hc & Hh). exists cid, pos'. rewrite Hfrs2.
    split; [right; exact Hin | split; [exact Hc | exact Hh]]. }
  destruct (lay_blk_range lyc S2 W mem2 md2 p HAR2 HHU2) as (HGT & HFtop & HB1 & HB2 & _).
  assert (HPB : asan_stack_malloc_c.ASAN_GT <= p + 18) by (unfold kFakeFramesOff in HB1; lia).
  (* R2 *)
  apply (lay_r2_lift STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb S2 regs2 mem2 md2 pos k _
           Hal Hlo Hhi Htp HRO Hr Hfl Hk Hrom (ex_intro _ i (conj Emd Hi)) Hmd Hmbl HNM Hp0 Hp50 Hamr HTW HAF HHU
           HJ2 Hfrs2 Eab HAR2 HRR HFS HACK HSV).
  intros ms3 md3 HP3 HJ3 HMU3.
  (* the box call *)
  apply (lay_box STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb S2 mem2 pos k ms3 md3 _
           Hal Hlo Hhi Hgp Htp HRO Hr Hk (ex_intro _ i (conj Emd Hi)) Hmd Hmbl HNM Hroom0 Hfrs2 HACK Hpos HFGT HFhi HF64
           HPB HP3 HJ3 HMU3).
  intros W4 ly4 S4 regs4 mem4 md4 gj Hwle HJ4 HRR4 Hfrs4 Eab4 Ha04 Hg4 HK4 RW1 RW2 BW AD3.
  assert (EF4 : ly_F ly4 = ly_F lyc).
  { pose proof HJ4 as (_ & Hly4 & _). pose proof HJ3 as (_ & Hly3 & _).
    pose proof Hly4 as (_ & _ & _ & _ & _ & F4 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & F3 & _).
    rewrite F4, F3. reflexivity. }
  (* R3 *)
  apply (lay_r3_lift STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc regs p r md fr mb nb gj S2 mem2 pos k (ms_mem ms3)
           W4 ly4 S4 regs4 mem4 md4 md3 _ Hal Hlo Hhi Htp HRO Hr Hfl Hk Hrom (ex_intro _ i (conj Emd Hi)) Hmd Hmbl HNM
           Hp0 Hp50 Hamr HTW HAF HHU HPB Hfrs2 Eab HACK Hpos HFGT HFhi HF64 HMU3 RW1 RW2 BW AD3 HJ3 Hwle HJ4 EF4 HRR4
           Hfrs4 Eab4 Ha04 Hg4 HK4).
  intros ms5 md5 HP5 HJ5 HMU5 HRO5 HSV5 HBK5.
  (* R4: the epilogue (a Theorem Labs lane's lay_tail_F_R4_on, no shadow premise) on the normalized memory after the release *)
  set (Sf := lib.Reusable.YG01.stack_free_state 1 pos S4) in *.
  set (A := (spZ regs - 128) / 32 * 32) in *.
  set (f := VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  rewrite lay_TLAY_val in Hlo.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  assert (Efa : frame_addr lyc 1 pos = lay_frb lyc pos).
  { unfold lay_frb, frame_addr. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & G3 & _).
    rewrite <- G3. reflexivity. }
  assert (Efl : flag_addr lyc 1 pos = asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos).
  { unfold flag_addr. destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & _ & G4 & _).
    rewrite <- G4. reflexivity. }
  assert (EfrSf : frames Sf = frames Sc).
  { change (frames Sf) with (lib.Reusable.YG00.del_pos (frames S4) 1 pos). rewrite Hfrs4, Hfrs2.
    cbn [lib.Reusable.YG00.del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  assert (EabSf : ablocks B ly4 Sf = ablocks B lyc Sc) by (rewrite <- Eab, <- Eab4; reflexivity).
  pose proof HP5 as (s5 & HE5 & HREL5 & _).
  destruct HE5 as (y1 & y5 & y6 & y7 & ya0 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y21 & y22 & y23
    & y28 & y29 & y30 & y31 & mc1 & gj1 & m3' & m4' & Es5 & _).
  subst s5.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL5) as [Ems5 _].
  rewrite Ems5. clear HREL5 HP5.
  set (mem5 := ms_mem ms5) in *.
  pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & Hstk5 & _).
  pose proof Hstk5 as (_ & _ & Hceil & Hslo & Hshi & _).
  pose proof Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  destruct (LayBase.rt_facts_C B LAWS CTS RLO RHI ly4 Sf W4 mem5 md5 HAR5
              (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO5 (Z.le_refl _) (Z.le_refl _)))
    as (Hro5 & AC5 & _).
  assert (Hslo' : ly_stk_lo ly4 <= spZ regs - 4512) by (rewrite Eslo; lia).
  assert (Hshi' : spZ regs <= ly_stk_hi ly4) by (rewrite Eshi; lia).
  destruct (LayBase.win_facts B LAWS ly4 Sf W4 mem5 md5 (spZ regs - 4512) (spZ regs) HAR5 Hro5 Hslo' ltac:(lia) Hshi'
              (fun a Ha => Hpres5 a ltac:(lia))) as (ST5 & AW5 & HHM5 & HAE5 & Hceil5).
  assert (HHU5 : tfr_hull ly4 Sf (p + 18) 32).
  { destruct HHU as (cid & pos' & Hin & Hc & Hh). exists cid, pos'. rewrite EfrSf.
    unfold frame_addr in Hh |- *. rewrite EF4. split; [exact Hin | split; [exact Hc | exact Hh]]. }
  destruct (lay_blk_range ly4 Sf W4 mem5 md5 p HAR5 HHU5) as (_ & _ & _ & _ & HBF5).
  destruct HFR_rng as (FR1 & FR2 & FR3).
  unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, ROW_BYTES in FR1, FR2.
  assert (Hf0 : 0 <= f) by (subst f; unfold ROW_BYTES; lia).
  assert (Hf1 : f + 24 <= asan_stack_malloc_c.ASAN_GT) by (subst f; unfold asan_stack_malloc_c.ASAN_GT, ROW_BYTES; lia).
  pose proof (LayBase.lay_fp0_facts B LAWS CTS ly4 Sf W4 mem5 md5 (spZ regs) p f HAR5 Hro5 ltac:(lia) HAE5 Hf0 Hf1 HBF5)
    as FP5. rewrite EF4 in FP5.
  pose proof (LayBase.lay_tls0_facts B LAWS CTS (A.ProgWorldTlsApart.fp_tls_apart B) ly4 Sf W4 mem5 md5
                (spZ regs - 4512) (spZ regs) HAR5 Hro5
                Hslo' Hshi') as TLS5. rewrite EF4 in TLS5.
  assert (Etp : bv_unsigned (reg_get regs 4) = A.AsanRT.RT_TP).
  { change (reg_get regs 4) with (rget regs 4). rewrite Htp, (A.ProgWorld.as_tp_RT_TP B CTS). unfold w64.
    apply A.ProgWorld_Fs.pw_u64. unfold A.AsanRT.RT_TP. lia. }
  set (nm5 := A.MemNorm.normalize A.Img0.rsegs mem5) in *.
  destruct (RcLayLib.ly_rw_split2 A.Img0.rsegs mem5 (spZ regs + -128) (spZ regs + -96) [lib.Lib.Cells.CB 32 gj]
              _ HSV5 ltac:(cbn; lia)) as [_ SV5].
  assert (HHM5' : A.AsanRT.HIGHMEM_BEG <= spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) by (rewrite lay_K_val; exact HHM5).
  refine (lay_SRr_norm HWX W4 (A.ProgBridge.RNG_W (w_H W4)) md5 _ lib.Reusable.YK11.fp_regs _ lib.Reusable.YK11.fp_csr
            mem5
            (fun s => ctrl_lay_block_F_R4_on.lay_Q_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
               (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
               (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm5 p f md 0
               (ly_F lyc) fr nil mb nb nil nm5 s /\ ms_mem s = nm5)
            _ (A.ProgBridge.fp_avoids_RNG_W _) Hro5 _ _).
  { apply (ctrl_lay_block_F_R4_on.lay_tail_F_R4_on (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
             (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
             (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr nm5 p f md 0
             (ly_F lyc) fr nil mb nb nil HHM5' (A.ProgBridge.RNG_W (w_H W4)) nm5).
    all: try change (bv_unsigned (reg_get regs 2)) with (spZ regs).
    - apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hpres5 a ltac:(lia))).
    - refine (A.MemNormTr.rw_cells_normalize mem5 _ _ Hro5 _ SV5). intros ii Hii.
      apply A.MemNormTr.ro_addr_above_img.
      cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_block.SAVES] in Hii.
      unfold A.Prog.ImgBounds.IMG_HI. lia.
    - apply lib.Lib.Frame.munch_refl.
    - apply lib.Lib.Frame.wmono_refl.
    - apply A.MemNorm.mem_inv_normalize.
    - rewrite lay_K_val. exact ST5.
    - refine (A.MemNormTr.rw_cells_normalize mem5 _ _ Hro5 _ HBK5). intros ii Hii.
      apply A.MemNormTr.ro_addr_above_img. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hii.
      unfold A.Prog.ImgBounds.IMG_HI. unfold asan_stack_malloc_c.ASAN_GT in HPB. lia.
    - exact AC5.
    - rewrite lay_K_val. replace 4512 with (spZ regs - (spZ regs - 4512)) at 2 by lia. exact AW5.
    - rewrite Etp, lay_K_val. exact FP5.
    - rewrite Etp, lay_K_val. exact TLS5. }
  intros ms6 md6 Hrun6 (s6 & (HQ6 & Em6) & HREL6 & HROS6) Hhid6 Hsame6.
  destruct HQ6 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & Es6
    & _ & _ & _ & _ & BKq & _).
  subst s6. assert (Em6' : m'' = nm5) by exact Em6. clear Em6. subst m''.
  destruct (A.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL6) as [Ems6 HMR6].
  assert (HMU6 : lib.Lib.Frame.munch [] mem5 (ms_mem ms6))
    by exact (A.MemNorm.munch_rel A.Img0.rsegs [] mem5 nm5 (ms_mem ms6) nm5
               (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem5 Hro5) HMR6 HROS6 (lib.Lib.Frame.munch_refl [] nm5)).
  assert (HJ6 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly4 Sf W4 (ms_mem ms6) md6 (k + EV_BMB)).
  { lazymatch type of Hrun6 with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS HWX STK sp0 FP ly S W0 mem0 md0 own ly4 Sf W4 ms0 ms6 md5 md6
               (k + EV_BMB) _ [] HJ5 Hrun6 (A.ProgBridge.fp_avoids_RNG_W _) HMU6 Hsame6
               (fun a _ Hout => False_ind _ (Hout I))) end. }
  pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
  assert (Erp : lib.Lib.MState.ret_pc (reg_get regs 1) = reg_get regs 1) by exact (lay_ret_pc _ Hra).
  rewrite Erp in Ems6. rewrite Ems6.
  apply YA0n.SRr_ret.
  do 5 eexists. split; [reflexivity|].
  split; [exact HJ6|].
  split.
  { intros rr Hrr. unfold acallee_saved in Hrr.
    destruct Hrr as [Hr'|[Hr'|[Hr'|[Hr'|[Hr'|Hr']]]]]; [subst rr; reflexivity .. |].
    assert (Hr'' : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/
                   rr = 27) by lia.
    destruct Hr'' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  split; [exact EfrSf|].
  split; [exact EabSf|].
  split.
  { assert (ELAY : ctrl_lay_block.LAY md 0 fr nil mb nb nil = RcLay.ly_Z md mb nb (RcLay.ly_bb r)).
    { unfold ctrl_lay_block.LAY, RcLay.ly_lay. rewrite Z.eqb_refl. cbn [orb]. unfold RcLay.ly_base. rewrite Hk.
      destruct (Z.eqb_spec r 0) as [E|E]; [lia|]. destruct (Z.eqb_spec r 1) as [E'|E']; [lia|].
      destruct (Z.eqb_spec r 2) as [E''|E'']; [lia | reflexivity]. }
    assert (Elen : length (RcLay.ly_Z md mb nb (RcLay.ly_bb r)) = 32%nat).
    { unfold RcLay.ly_Z. destruct (_ =? 0); [reflexivity|].
      destruct (_ =? 1); [exact (RcSynthLib.rs_synth_len mb _ nb Hmbl) | reflexivity]. }
    pose proof (A.MemNormTr.rw_cells_of_rel _ _ _ _ HMR6 BKq) as BK6.
    destruct BK6 as [[_ Hb6] _]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb6. rewrite ?app_nil_r in Hb6.
    rewrite ELAY in Hb6.
    apply (lay_garr8_of_bytes W4 (ms_mem ms6) (p + 18) _ Hb6). intros j Hj. rewrite Elen in Hj.
    assert (Hj' : 0 <= Z.of_nat j < 32) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt in Hj; exact Hj]).
    unfold kFakeFramesOff, kFakeStackSize in HB1, HB2.
    exact (proj1 (A.ProgWorld_Fs.pw_F_present B ly4 S4 W4 mem4 md4 (p + 18 + Z.of_nat j) (proj1 HJ4)
                    ltac:(rewrite EF4; unfold kFakeStackSize; lia))). }
  (* what the call keeps *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkJ & _).
  pose proof HstkJ as (_ & _ & HceilJ & _).
  pose proof HJ3 as (HAR3 & _).
  assert (HMU3' := HMU3). rewrite <- Efa in HMU3'.
  assert (HK4' := HK4). rewrite <- Efa in HK4'.
  assert (HMU56 : lib.Lib.Frame.munch [(p + 18, p + 50); (A - 2224, A);
    (A.AsanRT.shadow_addr (frame_addr lyc 1 pos), A.AsanRT.shadow_addr (frame_addr lyc 1 pos) + 16);
    (frame_addr lyc 1 pos, frame_addr lyc 1 pos + 8); (flag_addr lyc 1 pos, flag_addr lyc 1 pos + 1)] mem4 (ms_mem ms6)).
  { rewrite Efa, Efl. apply (lib.Lib.Frame.munch_trans _ mem4 mem5 (ms_mem ms6) HMU5).
    eapply lib.Lib.Frame.munch_weaken; [| exact HMU6]. intros x _. exact I. }
  rewrite lay_TLAY_val in HACK.
  exact (C_ctrl_lay_block_kept.lay_tcj_final B LAWS lyc Sc S2 W W4 W memc
           mem2 (ms_mem ms3) mem4 (ms_mem ms6)
           (ms_mem ms3) mdc md3 (spZ regs) A p pos HAR HAR3 Hfrs2 Hnin Eab ltac:(lia) ltac:(lia) ltac:(lia) HHU
           HACK HMU3' HK4' HMU56 (fun a Ha => Hpres6 a ltac:(lia))).
Qed.

End e.
End d.
End b.

(* The glue's assumptions: the Section hypotheses above (the callee contract, the runtime footprint contracts, the
   core rules, ProgWorld's owed statements, the image facts) and nothing else. *)
Print Assumptions pb_ctrl_lay_block.
(* the discharged Section hypotheses, as the theorem's premises *)
Check pb_ctrl_lay_block.
