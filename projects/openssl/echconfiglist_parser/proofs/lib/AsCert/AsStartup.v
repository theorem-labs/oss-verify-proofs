(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the startup sections take the run's input and mmap base with the launch facts and channel-reader premise; SINV0_agree_X; node and init lemmas instantiated by tactic; cert1 checks hinit at the run's CONFIG_RSEQ); the start-up is generic in the Leaf class of its srealizes walks (XN0_sound, XE0_sound and XB0_sound take it; Sections XAll and Startup have it in context). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages As_code_startx AsSmearCode SumsAsanSpecs SumsAsanClose.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import Leaf.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound {LF : Leaf} : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext_stmt SEGS SC LF A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound {LF : Leaf} : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @emit_stmt SEGS SC LF A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound {LF : Leaf} : forall SEGS (SC : StepCfg) A nx0 LIMIT SINV argH FS0, @ext2_stmt SEGS SC LF A nx0 LIMIT XB0 SINV argH FS0.
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

(* [AsanInit.SINV0_agree] now carries leading image binders its statement does not name
   (the build reads "APH" where it expects a [list Segment]), as [AsanInitL.argH0_agree_L]
   records for [argH0_agree]; its proof, at top level. *)
Lemma SINV0_agree_X : forall ph apc sp rdraw brk0 mbase inp E E' M, env_agree NX0 E E' ->
  SINV0 ph apc sp rdraw brk0 mbase inp E M -> SINV0 ph apc sp rdraw brk0 mbase inp E' M.
Proof.
  intros ph apc sp rdraw brk0 mbase inp E E' M Hag [H1 H2]. split.
  - intros n Hn. rewrite <- (proj1 Hag n) by (unfold NX0, V_EHDR in *; lia). apply H1. exact Hn.
  - intros a Ha. apply H2. rewrite (argH0_agree sp rdraw inp E E' a Hag). exact Ha.
Qed.

(** #38: the startup phase runs under [AsanInit.SINV0] at the run's OWN mmap base, because
    [AsanNodesStartXInit]'s Section takes one base with its [Hmb]/[Hlau] (route A of the
    lever-LOW ruling: [mbase] is a Variable HERE, the instantiation site, and nowhere past
    start-up, where [AsanInitL.SINV0L] closes it). [Proof using All] fixes the theorem's
    arity to this whole list, so its one caller below ([asan_check_sound]) is positional
    against a list it can read. *)
Section XAll.
  Context {LF : Leaf}.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  #[local] Notation SINV := (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  (** [AsanInit.argH0_high] is discharged over the hypotheses its proof reads *)
  Lemma xall_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  (* [argH0_high]'s four leading binders (segs, table, phdrs, entry) are read by its proof
     only, so no unification fixes them ([AsanInitL.argH0_high_L]); this image's are given. *)
  Proof. intros E a H. eapply (argH0_high ASEGS ASAN_H APH Asan.M.init_pc); eassumption. Qed.
  Let AH := xall_argH_high.
  Let AS := argH0_sp0 sp rdraw inp.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree_X APH Asan.M.init_pc sp rdraw brk0 mbase inp.
  (** LPS c0dd863a: [APS.cs_ok_agree]'s [EHDR_lt] at [NX0], by computation *)
  Let EH : (V_EHDR < NX0)%nat := proj1 (Nat.ltb_lt V_EHDR NX0) eq_refl.
  Ltac xall_args :=
    first [ exact AH | exact E_SP0 | exact AA | exact SF | exact SA | exact EH | exact (argH0_sp0 sp rdraw inp) | eassumption ].
  (** the obligations [AsanNodesStartXInit]'s Section leaves: its run hypotheses, the
      image's facts ([Hapc] is [eq_refl]: [Asan.M.init_pc] IS [a_entry ASAN_H]), and the
      class invariant, which here is [SINV0] itself *)
  Ltac close_xinit :=
    first [ eassumption | exact asan_img_facts | reflexivity
          | exact (fun E M (H : SINV E M) => H) | exact SF | exact SA ].

  (* [comment removed for export] *)
  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 x.
  Proof using All.
    intros [ | | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; xall_args.
    - eapply asan_node_x_sound_XIMemcpy; xall_args.
    - eapply asan_node_x_sound_XMemset; xall_args.
    - eapply asan_node_x_sound_XMemcpy; xall_args.
    - eapply asan_node_x_sound_XMemIsZero; xall_args.
    - eapply (init_x_sound_envscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_137b8c W_137b90 W_137b94
                ltac:(cbn [x_envscan x_envscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_137b8c) (fetch_lit _ _ _ _ eq_refl F_137b90) (fetch_lit _ _ _ _ eq_refl F_137b94)
                ltac:(repeat split; reflexivity)
                D_137b8c D_137b90 D_137b94
                Asan.M.init_pc sp rdraw brk0 mbase inp FS0).
      all: close_xinit.
    - eapply (init_x_sound_pnscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_137c48 W_137c4c W_137c50 W_137c54 W_137c58
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_137c48) (fetch_lit _ _ _ _ eq_refl F_137c4c) (fetch_lit _ _ _ _ eq_refl F_137c50)
                (fetch_lit _ _ _ _ eq_refl F_137c54) (fetch_lit _ _ _ _ eq_refl F_137c58)
                ltac:(repeat split; reflexivity)
                D_137c48 D_137c4c D_137c50 D_137c54 D_137c58
                Asan.M.init_pc sp rdraw brk0 mbase inp FS0).
      all: close_xinit.
    - eapply init_x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; xall_args.
    - eapply asan_node_x_sound_XPopFree; xall_args.
    - (* [comment removed for export] *)
      intros args cs cs' E R FULL model T _ _ H. discriminate H.
    - (* [comment removed for export] *)
      exact (x_sound_smear ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 asan_wx asan_in_hull asan_hull_ok SF asan_smear_x asan_smear_fwa).
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
      check ASEGS (mk_itab_ranges ASEGS rs) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSt KC0 BFUEL FUEL None ch p = COk s
      /\ holes_only s = true.

Section Startup.
  Context {LF : Leaf}.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  (** #38: the run's whole input, as [AsanInit]'s Section takes it *)
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* 08b1429: [Run.valid_input]'s reader clause, seeding [cs_ok]'s [co_rdr] *)
  Hypothesis Hrdrin : in_channel_reader inp = true.
  (** #38: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct, which
      [AsanInit.init_cs_ok] is discharged over *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation SINV := (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 mbase inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation fs := (in_fs inp).

  (* [comment removed for export] *)
  Variable RANGES : list (Z * nat).          (* [comment removed for export] *)
  Variables HS1 HSC HSA : nat -> option acs.   (* [comment removed for export] *)
  Variable plan1 : plan.
  Variable shape1 : shape.
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges ASEGS RANGES).
  (* LPS 727298f3: the start state of the run's own kernel build ([AsImages.hinit]) *)
  Hypothesis cert1 : check ASEGS IT ASAN_H NX0 LIM XN0 XE0 XB0 HS1 KC0 BFUEL FUEL None (hinit (rseq_z (kb_rseq (in_kernel inp)))) plan1 = COk shape1.
  Hypothesis shape1_holes : holes_only shape1 = true.
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : LEVEL HS1 HSC.
  Hypothesis cert3 : LEVEL HSC HSA.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T.
  Hypothesis HOLESA_sound : holes_stmt ASEGS ASAN_H LIM HSA SINV argH HOLES fs.   (* [comment removed for export] *)

  Lemma st_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply (argH0_high ASEGS ASAN_H APH Asan.M.init_pc); eassumption. Qed.
  Lemma st_SINV_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
  Proof. intros E M H. first [eapply SINV0_pg_E0; eassumption | eapply (SINV0_pg_E0 ASEGS ASAN_H); eassumption]. Qed.
  Let AH := st_argH_high.
  Let AS := argH0_sp0 sp rdraw inp.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree_X APH Asan.M.init_pc sp rdraw brk0 mbase inp.
  (* [comment removed for export] *)
  Let SP := st_SINV_pg.
  (** LPS c0dd863a: [APS.cs_ok_agree]'s [EHDR_lt] at [NX0], by computation *)
  Let EH0 : (V_EHDR < NX0)%nat := proj1 (Nat.ltb_lt V_EHDR NX0) eq_refl.

  (** instantiate the premises an [AsanInit] theorem's Section discharged: the run's
      hypotheses above, the image's facts, and [Hapc], which is [eq_refl] *)
  Ltac inst_init H :=
    repeat match type of H with
           | ?P -> _ =>
               let Hp := fresh "Hp" in
               assert (Hp : P) by first [ assumption | exact asan_img_facts | reflexivity ];
               specialize (H Hp); clear Hp
           end.

  (* The node lemmas' Section hypotheses, by type: at 727298f3 [node_brk2_sound] reads the
     image's reservations ([asan_res_hull]) where it read the hull, so its positional list moved. *)
  Ltac node_args :=
    first [ exact asan_in_hull | exact asan_hull_ok | exact asan_shadow_ok | exact asan_res_hull
          | exact asan_res_len | exact asan_res_cover | exact asan_wx | exact AH | exact AS | exact SF
          | exact SA | exact AA | exact E_SP0 | exact SP | exact EH0 | eassumption | exact _ | solve [eauto] ].

  (* [comment removed for export] *)
  Lemma asan_check_sound : forall RS HS,
    holes_stmt ASEGS ASAN_H LIM HS SINV argH HOLES fs ->
    forall fuel bfuel p cs s,
      check ASEGS (mk_itab_ranges ASEGS RS) ASAN_H NX0 LIM XN0 XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok ASEGS ASAN_H LIM SINV argH fs E cs R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound ASEGS (mk_itab_ranges ASEGS RS) (itab_ranges_ok RS) ASAN_H NX0 LIM HS XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH E_SP0 AA SF SA EH0
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) fs KC0
              (ltac:(intros y; eapply AsanNodesMmB.node_sys_sound; node_args))
              (ltac:(eapply AsanNodesMmB.node_brk2_sound; node_args))
              (ltac:(eapply node_mmap1_sound_OBL; node_args))
              (ltac:(eapply node_mmapin1_sound_OBL; node_args))
              (ltac:(eapply node_mprotect1_sound_OBL; node_args))
              (ltac:(eapply node_mmapgaps_sound_OBL; node_args))
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_H LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 mbase inp fs Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau)
              (node_join_sound ASEGS ASAN_H NX0 LIM SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (ltac:(intros hs ws cold fz n0 i; eapply asan_node_fillfz_sound; node_args))   (* [comment removed for export] *)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma level_sound : forall HSs HSt, LEVEL HSs HSt ->
    holes_stmt ASEGS ASAN_H LIM HSt SINV argH HOLES fs -> holes_stmt ASEGS ASAN_H LIM HSs SINV argH HOLES fs.
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. destruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (asan_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESC_sound : holes_stmt ASEGS ASAN_H LIM HSC SINV argH HOLES fs.
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : holes_stmt ASEGS ASAN_H LIM HS1 SINV argH HOLES fs.
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) (sd HOLES t_nil E0a fs shape1).
  Proof.
    pose proof (init_cfg_eq ASEGS ASAN_H APH Asan.M.init_pc sp rdraw brk0 mbase inp) as EQ. inst_init EQ.
    rewrite EQ.
    pose proof (init_cs_ok ASEGS ASAN_H APH Asan.M.init_pc sp rdraw brk0 mbase inp) as HC. inst_init HC.
    pose proof (asan_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 (hinit (rseq_z (kb_rseq (in_kernel inp)))) shape1 cert1 _ _ _ _ HC) as R.
    (* [m_fs] of the launch model is the input's file system, by computation *)
    exact R.
  Qed.

  (** [Proof using All]: the arity is this Section's whole list, so
      [EAsStartupTop.as_startup_srealizes] applies it against a list it can read *)
  Theorem as_startup_T :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) T.
  Proof using All.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
