(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear BothImages BothPlanImages Bo_code_102bcc_102df8 BoSmearCode SumsBothSpecs SumsBothClose.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext_stmt SEGS SC A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @emit_stmt SEGS SC A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext2_stmt SEGS SC A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Lemma sd_holes_only : forall HOLES D E fs T s,
  (forall h, HOLES h E fs = T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HT. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros H; try discriminate.
  - apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2. specialize (IHa H1 tr). specialize (IHb H2 tr). tauto.
  - apply andb_prop in H as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - rewrite HT. intros tr. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  (* #38: [AsanInit]'s Section takes the whole run as one [ProcInput], and takes the run's
     mmap base under exactly two facts.  The four old Variables are (only parsing) notations
     for [inp]'s projections, so every body below is unchanged text.  [mbase] and [Hlau] are
     here and NOWHERE DOWNSTREAM: the producer-side exception G3b ruled and Main endorsed,
     and [AsanInitL.SINV0L] binds the base existentially for every consumer past start-up.
     Every argument list below is the arity the [About] probe PRINTED
     (a source round on a NEVER-MERGE side ref), mirrored
     from the As twin rather than retyped: these lemmas are Section-generalised, so their
     explicit arguments are decided by an [eassumption] inside each proof and no reading of
     the source gives them.  Note [SINV0_frame] takes NO leading [segs]/[A] while
     [SINV0_agree] takes BOTH - the probe is what separates them. *)
  #[local] Notation argv := (in_argv inp) (only parsing).
  #[local] Notation envp := (in_envp inp) (only parsing).
  #[local] Notation uid := (in_uid inp) (only parsing).
  #[local] Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  (* #38: [valid_launch] is a SECOND launch fact, distinct from [Hlau]'s
     [entry_launch_ok_va], and AsanInit's Section generalises it BEFORE [Hfit].  The kernel
     named it: with [Hfit] in this slot, a farm round reported
     Bo/BoStartup.v:100 c.76-80, "Hfit has type entry_stack_fits sp (in_argv inp)
     (in_envp inp) while it is expected to have type valid_launch inp". *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  #[local] Notation SINV := (SINV0 BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  Let AH := argH0_high BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau.
  Let AS := argH0_sp0 sp rdraw inp.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.

  (* [comment removed for export] *)
  Theorem asan_node_x_sound_all : forall x, x_stmt BSEGS2 BOTH_H NX0 AsanInit.LIMIT SINV argH FS0 x.
  Proof.
    intros [ | | | | | | | | | | | ].
    - exact (both_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - eapply (init_x_sound_envscan BSEGS2 BOTH_H BPH2 both_wx both_in_hull both_hull_ok
                W_102c04 W_102c08 W_102c0c
                ltac:(cbn [x_envscan x_envscan_k BOTH_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_102c04) (fetch_lit _ _ _ _ eq_refl F_102c08) (fetch_lit _ _ _ _ eq_refl F_102c0c)
                ltac:(repeat split; reflexivity)
                D_102c04 D_102c08 D_102c0c
                AsanUbsan.M.init_pc sp rdraw brk0 mbase inp FS0 Hsp Hva Hve Hlaunch Hlau SINV (fun E M H => H) SF).
    - eapply (init_x_sound_pnscan BSEGS2 BOTH_H BPH2 both_wx both_in_hull both_hull_ok
                W_102cc0 W_102cc4 W_102cc8 W_102ccc W_102cd0
                ltac:(cbn [x_pnscan x_pnscan_k BOTH_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_102cc0) (fetch_lit _ _ _ _ eq_refl F_102cc4) (fetch_lit _ _ _ _ eq_refl F_102cc8)
                (fetch_lit _ _ _ _ eq_refl F_102ccc) (fetch_lit _ _ _ _ eq_refl F_102cd0)
                ltac:(repeat split; reflexivity)
                D_102cc0 D_102cc4 D_102cc8 D_102ccc D_102cd0
                AsanUbsan.M.init_pc sp rdraw brk0 mbase inp FS0 Hsp Hva Hve Hlau SINV (fun E M H => H) SF SA).
    - apply (init_x_sound_layout BSEGS2 BOTH_H sp rdraw inp FS0 SINV).
    - exact (both_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (both_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - (* [comment removed for export] *)
      intros args cs cs' E R FULL model T _ _ H. discriminate H.
    - (* [comment removed for export] *)
      exact (x_sound_smear BSEGS2 BOTH_H NX0 AsanInit.LIMIT SINV argH FS0 both_wx both_in_hull both_hull_ok SF both_smear_x both_smear_fwa).
  Qed.
End XAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition level_certified (KC0 BFUEL FUEL : nat) (HSs HSt : nat -> option acs) : Prop :=
  forall h ch, HSs h = Some ch ->
    exists (rs : list (Z * nat)) (p : plan) (s : shape),
      check BSEGS2 (mk_itab_ranges BSEGS2 rs) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSt KC0 BFUEL FUEL None ch p = COk s
      /\ holes_only s = true.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  (* #38: the fifteen launch pieces are one [ProcInput] now, and [AsanInit.inp] - the
     definition that assembled them - is gone with them, so [INP] is the run itself.
     Mirrors As/AsStartup.v:150-176 exactly; taking [inp] whole rather than rebuilding it
     with [mkProcInput_full] also avoids naming the five fields after [in_tmp], whose types
     this Section never had. *)
  Variable inp : ProcInput.
  #[local] Notation argv := (in_argv inp) (only parsing).
  #[local] Notation envp := (in_envp inp) (only parsing).
  #[local] Notation uid := (in_uid inp) (only parsing).
  #[local] Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS2 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* [init_cs_ok]'s premise list at #38, from the probe, in order: img_facts, valid_sp,
     valid_brk, valid_mmap_base, valid_argv, valid_envp, valid_id, valid_hwcap, valid_launch,
     entry_launch_ok_va - and NO entry_stack_fits.  Hence these two. *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [Run.valid_input_channel_reader]: [init_cs_ok]'s [co_rdr] (As/AsanInit.v:131) *)
  Hypothesis Hrdr : in_channel_reader inp = true.

  #[local] Notation SINV := (SINV0 BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation INP := inp.
  #[local] Notation FS := (in_fs inp).

  (* [comment removed for export] *)
  Variable RANGES : list (Z * nat).          (* [comment removed for export] *)
  Variables HS1 HSC HSA HSF : nat -> option acs.
  Variable plan1 : plan.
  Variable shape1 : shape.
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges BSEGS2 RANGES).
  (* LPS 727298f3: the start state of the run's own build ([BothImages.bhinit]) *)
  Hypothesis cert1 : check BSEGS2 IT BOTH_H NX0 LIM XN0 XE0 XB0 HS1 KC0 BFUEL FUEL None (bhinit (rseq_z (kb_rseq (in_kernel inp)))) plan1 = COk shape1.
  Hypothesis shape1_holes : holes_only shape1 = true.
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : LEVEL HS1 HSC.
  Hypothesis cert3 : LEVEL HSC HSA.
  Hypothesis cert4 : LEVEL HSA HSF.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Hypothesis HOLESF_sound : holes_stmt BSEGS2 BOTH_H LIM HSF SINV argH HOLES FS.

  Let AH := argH0_high BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP Hsp Hva Hve Hlau.
  Let AS := argH0_sp0 sp rdraw INP.
  Let AA := argH0_agree sp rdraw INP.
  Let SF := SINV0_frame BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP.
  Let SA := SINV0_agree BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP.
  (* [comment removed for export] *)
  Let SP := SINV0_pg BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP Hsp Hva Hve Hlau SINV (fun E M H => H).

  (* [comment removed for export] *)
  Lemma both_check_sound : forall RS HS,
    holes_stmt BSEGS2 BOTH_H LIM HS SINV argH HOLES FS ->
    forall fuel bfuel p cs s,
      check BSEGS2 (mk_itab_ranges BSEGS2 RS) BOTH_H NX0 LIM XN0 XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok BSEGS2 BOTH_H LIM SINV argH FS E cs R FULL model ->
        srealizes BSEGS2 (cfg_of BSEGS2 R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound BSEGS2 (mk_itab_ranges BSEGS2 RS) (itab_ranges_ok RS) BOTH_H NX0 LIM HS XN0 XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH E_SP0 AA SF SA
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) FS KC0
              (AsanNodesMmB.node_sys_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS both_res_len both_hull_ok both_shadow_ok AA SF SA AS E_SP0)
              (* #38: [node_brk2_sound] now captures [RES_hull] too.  Step 4a on its own Section
                 (As/AsanNodesMmB.v:241-263, Section SoundB) gives the hypothesis ORDER --
                 SEGS_in_hull, RES_hull, HULL_ok, SHADOW_ok, argH_high, argH_agree, SINV_frame,
                 SINV_agree, RES_len, RES_cover, argH_sp0, E_SP0 -- and this call passed a
                 Section-ordered SUBSET of it missing exactly [RES_hull].  The kernel named the
                 TYPE, not a sibling call: "expected Forall (fun iv => img_lo BOTH_H <= iv.1 /\
                 iv.1 + iv.2 <= img_hi BOTH_H) (segments_reserved ...)", which is [both_res_hull]. *)
              (AsanNodesMmB.node_brk2_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_hull both_hull_ok both_shadow_ok AH SF both_res_len both_res_cover AS)
              (node_mmap1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_res_cover both_hull_ok both_shadow_ok AH AS E_SP0 AA SF SA SP)
              (* #38, from the About print (exit 0, all 8 signatures):
                 node_mmapin1_sound_OBL and node_mprotect1_sound_OBL capture
                 SEGS_in_hull RES_len RES_cover HULL_ok SHADOW_ok argH_high argH_sp0 SINV_frame
                 and NOT RES_hull -- unlike node_mmap1_sound_OBL one line above, which does take it.
                 These two were OVER-SUPPLYING it.  Note the direction: node_brk2_sound needed
                 RES_hull ADDED and these two need it REMOVED, in adjacent lines of one term, so a
                 sibling call would have been the wrong donor either way. *)
              (node_mmapin1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_cover both_hull_ok both_shadow_ok AH AS SF)
              (node_mprotect1_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_cover both_hull_ok both_shadow_ok AH AS SF)
              (node_mmapgaps_sound_OBL BSEGS2 BOTH_H NX0 LIM SINV argH FS both_in_hull both_res_len both_res_cover both_hull_ok both_shadow_ok AH AS E_SP0 AA SF SA SP)
              (AsanNodesMmB.node_exit_sound BSEGS2 BOTH_H LIM SINV argH FS)
              (* #38: Section XAll's capture, PRINTED rather than inferred -- probe
                 run on a never-merge ref,
                 hosted after End XAll, which elaborates before this line fails:
                   sp rdraw brk0 mbase inp FS0 Hsp Hva Hve Hlaunch Hlau
                 and NO Hfit.  That is a measurement of THIS Section, not an inheritance of the
                 model-side entry_stack_fits claim that was promoted and withdrawn twice tonight:
                 Hfit is still declared and still live for the consumers that take it, it is
                 simply not in what this theorem captures. *)
              (asan_node_x_sound_all sp rdraw brk0 mbase INP FS Hsp Hva Hve Hlaunch Hlau)
              (node_join_sound BSEGS2 BOTH_H NX0 LIM SINV argH FS)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (both_node_fillfz_sound NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS)   (* [comment removed for export] *)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma level_sound : forall HSs HSt, LEVEL HSs HSt ->
    holes_stmt BSEGS2 BOTH_H LIM HSt SINV argH HOLES FS -> holes_stmt BSEGS2 BOTH_H LIM HSs SINV argH HOLES FS.
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. destruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (both_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESA_sound : holes_stmt BSEGS2 BOTH_H LIM HSA SINV argH HOLES FS.
  Proof. exact (level_sound HSA HSF cert4 HOLESF_sound). Qed.
  Lemma HOLESC_sound : holes_stmt BSEGS2 BOTH_H LIM HSC SINV argH HOLES FS.
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : holes_stmt BSEGS2 BOTH_H LIM HS1 SINV argH HOLES FS.
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape :
    srealizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp brk0 mbase rdraw LIM INP) (sd HOLES t_nil E0a FS shape1).
  Proof.
    pose proof both_img_facts as IMG.
    (* #38: [init_cfg_eq], [init_cs_ok] and [model0] all take AsanInit's Section order
       (segs A ph apc sp rdraw brk0 mbase inp), so [apc] moves in front of [sp] -- which is
       what the kernel named at :270 c.44-46, "sp has type word, expected N" -- and the
       fifteen launch components collapse to [INP].  [init_cs_ok]'s premise list is the one
       As/AsStartup.v:165-167 records from its own About probe: img_facts, valid_sp,
       valid_brk, valid_mmap_base, valid_argv, valid_envp, valid_id, valid_hwcap,
       valid_launch, entry_launch_ok_va -- and NO entry_stack_fits.  The As twin's
       as_startup_shape is still on the old form at this sha, so this is derived rather than
       mirrored; if that lane's port differs, its print wins and I take the hunk. *)
    rewrite (init_cfg_eq BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP eq_refl).
    (* [init_cs_ok]'s proof now reads the entry word ([AsanInit.init_kn_with_ok], AT_ENTRY),
       so it takes the Section's [Hapc] after [IMG]: [eq_refl], as at [init_cfg_eq] above. *)
    pose proof (init_cs_ok BSEGS2 BOTH_H BPH2 AsanUbsan.M.init_pc sp rdraw brk0 mbase INP
                  IMG eq_refl Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrdr) as HC.
    pose proof (both_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 (bhinit (rseq_z (kb_rseq (in_kernel inp)))) shape1 cert1 _ _ _ _ HC) as R.
    (* #38: [model0 segs sp rdraw brk0 mbase inp] -- PRINTED by a probe round.
       [rdraw] was ABSENT from this call rather than misplaced: the entry draw is part of the
       run's initial model now, and an absent argument is the direction an error-at-a-time
       cycle finds last.  The same 94 s probe confirmed the two calls above are already exact
       -- [init_cfg_eq segs A ph apc sp rdraw brk0 mbase inp Hapc] and [init_cs_ok ... IMG Hsp
       Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau] -- so one round settled all three. *)
    replace (m_fs (model0 BSEGS2 sp rdraw brk0 mbase INP)) with FS in R by reflexivity.
    exact R.
  Qed.

  Theorem as_startup_T :
    srealizes BSEGS2 (init_config BSEGS2 AsanUbsan.M.init_pc BPH2 sp brk0 mbase rdraw LIM INP) T.
  Proof.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
