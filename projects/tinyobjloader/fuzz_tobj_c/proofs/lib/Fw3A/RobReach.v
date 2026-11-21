(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the walks' facts on the run's segment list and the run's
   start, and the read-only backing's robustness at every configuration a walk reaches.

   [Run.run_scfg] reads a binary against [run_segments segs inp sp mb] from
   [init_config (run_segments ..) ..] (see [Fw/RunSeg.v]'s header).  The walks prove [SOUND],
   [COMPLETE] and no error over the binary's own segments [segs] and [init_config segs ..]
   ([Fw/Safety.v]).  Part 1 moves the three onto the run's list and start, at the two costs
   [Fw/RunSeg.v] names: the binary carries no vDSO text of its own ([vdso_image segs = None],
   decided by conversion at a concrete image), and [RunSeg.rob_reach].

   Part 2 proves [rob_reach] from the walks themselves.  Every walk is generic in its world
   predicate [ok] and asks three frame obligations of it: at an instruction step
   ([SymSoundR.ok_frame], [SoundA.ok_frameA]), at a pending system call ([SymCall.ok_pframe],
   [SysCallA.ok_pframeA]) and at a halted process ([SymExit.ok_halted]).  The system-call
   obligation hands its producer [RomBase.sys_rob] at the call, which each call site proves
   from the number it pins.  [ok_rob] is the target obligation [ok_tgt] together with [sys_rob]
   at every configuration of a running process.  It meets the three obligations: an
   instruction configuration is robust for nothing ([RomBase.sys_rob_instr]), the system-call
   obligation is handed [sys_rob], and a halted process is not asked.  So a walk run at [ok_rob]
   proves [rob_reach] of its start ([safe_rob_reach]). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable Safety RomBase RunSeg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundR SymCall SymExit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA SysCallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* ------------------------------------------------------------------------------------------
   Part 1: [SOUND], [COMPLETE] and no error, from the binary's own list to the run's
   ------------------------------------------------------------------------------------------ *)

(** Every trace the run reaches is one the binary reaches over its own segments: a run over
    the run's list from the run's start is one over [segs] from the start with the larger
    backing ([RunSeg.star_app_back]), and so one over [segs] from [init_config segs ..]
    ([RunSeg.star_wrom_back]). *)
Theorem sound_run_init :
  forall segs inp (sp brk mb : word) pc ph rnd lim (Spec : list event -> Prop),
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_a segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  SOUND segs (init_config segs pc ph sp brk mb rnd lim inp) Spec ->
  SOUND (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) Spec.
Proof.
  intros segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob Hne Hs tr d Hst.
  unfold reaches_error_a in Hne. unfold star_a in Hst.
  rewrite init_config_run_segments in Hst. unfold run_segments at 1 in Hst.
  assert (Hr : rom_ext (ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)))
                       (seg_rom1 (run_segments segs inp sp mb)))
    by (rewrite init_config_rom; apply rom_ext_run_segments).
  assert (Hne2 : ~ reaches_error_cfg segs ACFG
                   (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                          (seg_rom1 (run_segments segs inp sp mb)))).
  { intros Hc. apply Hne.
    apply reaches_error_wrom_back with (r := seg_rom1 (run_segments segs inp sp mb));
      first [exact Hvi | exact Hrob | exact Hr | exact Hc]. }
  assert (Hst2 : star_cfg segs ACFG
                   (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                          (seg_rom1 (run_segments segs inp sp mb))) tr d).
  { apply star_app_back with (tail := vdso_segments (in_kernel inp) sp mb);
      try exact Hvi; try exact Hne2; try exact Hst;
      intros s Hs0; first [exact (vdso_segments_nx _ _ _ s Hs0) | exact (vdso_segments_nw _ _ _ s Hs0)]. }
  destruct (star_wrom_back segs ACFG Hvi (seg_rom1 (run_segments segs inp sp mb)) _ tr d Hst2
              (init_config segs pc ph sp brk mb rnd lim inp) eq_refl Hrob Hr) as (c & _ & Hc).
  exact (Hs tr c Hc).
Qed.

(** Every run of the binary over its own segments is a run of the run, at the larger backing
    ([RunSeg.star_wrom_fwd], then [RunSeg.star_app_fwd]). *)
Theorem complete_run_init :
  forall segs inp (sp brk mb : word) pc ph rnd lim (Spec : list event -> Prop),
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  COMPLETE segs (init_config segs pc ph sp brk mb rnd lim inp) Spec ->
  COMPLETE (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) Spec.
Proof.
  intros segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob Hc t Ht.
  destruct (Hc t Ht) as (c & Hst).
  exists (cwrom c (seg_rom1 (run_segments segs inp sp mb))).
  unfold star_a. rewrite init_config_run_segments. unfold run_segments at 1.
  apply star_app_fwd;
    try (intros s Hs0; first [exact (vdso_segments_nx _ _ _ s Hs0) | exact (vdso_segments_nw _ _ _ s Hs0)]);
    try exact Hvi.
  apply star_wrom_fwd;
    first [ exact Hvi | exact Hrob | exact Hst
          | rewrite init_config_rom; apply rom_ext_run_segments ].
Qed.

(** The three facts of a walk, on the run's segment list and the run's start. *)
Theorem facts_run_init :
  forall segs inp (sp brk mb : word) pc ph rnd lim (Spec : list event -> Prop),
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  SOUND segs (init_config segs pc ph sp brk mb rnd lim inp) Spec
  /\ COMPLETE segs (init_config segs pc ph sp brk mb rnd lim inp) Spec
  /\ ~ reaches_error_a segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  SOUND (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) Spec
  /\ COMPLETE (run_segments segs inp sp mb)
       (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) Spec
  /\ ~ reaches_error_a (run_segments segs inp sp mb)
         (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob (Hs & Hc & Hne).
  split; [|split].
  - exact (sound_run_init segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob Hne Hs).
  - exact (complete_run_init segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob Hc).
  - exact (reaches_error_a_run_init segs inp sp brk mb pc ph rnd lim Hvi Hrob Hne).
Qed.

(* ------------------------------------------------------------------------------------------
   Part 2: [rob_reach] from a walk
   ------------------------------------------------------------------------------------------ *)

Section Rob.
Variable segs : list Segment.
Variable Spec : list event -> Prop.

(** The target obligation, and the read-only backing's robustness at a running process. *)
Definition ok_rob (w : world) : Prop :=
  ok_tgt segs Spec w
  /\ (m_halted (cfg_model (w_cfg w)) = None -> sys_rob segs (w_cfg w)).

(** A walk safe for [ok_rob] reaches only robust configurations. *)
Lemma safe_rob_reach : forall c0,
  (forall n, safe segs ok_rob n (w0 c0)) -> rob_reach segs c0.
Proof using .
  intros c0 Hs tr c Hst Hh.
  exact (proj2 (@safe_reachable_ok segs ok_rob (w0 c0) ([] ++ tr, c) Hs (@star_wsteps segs c0 tr c [] Hst)) Hh).
Qed.

(** The frame obligations at [ok_rob]: the released target obligation's producers, and
    [sys_rob] from the obligation's own premise or from the configuration's shape. *)
Lemma ok_frame_rob_K : forall K, K_tcons Spec K -> ok_frame segs ok_rob K.
Proof using .
  intros K HK tr ms md ms' Hk Hidle Hp Hs. split.
  - exact (@ok_frame_tgt_K segs Spec K HK tr ms md ms' Hk Hidle Hp Hs).
  - intros _. apply sys_rob_instr. exact Hp.
Qed.

Lemma ok_pframe_rob_K : forall K, K_tcons Spec K -> ok_pframe segs ok_rob K.
Proof using .
  intros K HK tr ms md x8 Hk Hp Hok Hrob. split.
  - exact (@ok_pframe_tgt_K segs Spec K HK tr ms md x8 Hk Hp Hok Hrob).
  - intros _. exact Hrob.
Qed.

Lemma ok_halted_rob : ok_halted ok_rob Spec.
Proof using .
  intros tr ms md code Ht Hh. split.
  - exact (@ok_halted_tgt segs Spec tr ms md code Ht Hh).
  - intros Hn. exfalso. change (m_halted md = None) in Hn. congruence.
Qed.

Lemma ok_frameA_rob : forall J : jpredA,
  (forall rho tp tr md, J rho tp tr md -> tcons Spec tr) -> ok_frameA segs ok_rob J.
Proof using .
  intros J HJ rho tp tr ms md msv' Hj HMI Hh Hp Hs. split.
  - exact (@ok_frameA_tgt segs Spec J HJ rho tp tr ms md msv' Hj HMI Hh Hp Hs).
  - intros _. apply sys_rob_instr. exact Hp.
Qed.

Lemma ok_pframeA_rob : forall J : jpredA,
  (forall rho tp tr md, J rho tp tr md -> tcons Spec tr) -> ok_pframeA segs ok_rob J.
Proof using .
  intros J HJ rho tp tr ms md x8 Hj Hp Hok Hrob. split.
  - exact (@ok_pframeA_tgt segs Spec J HJ rho tp tr ms md x8 Hj Hp Hok Hrob).
  - intros _. exact Hrob.
Qed.

End Rob.
