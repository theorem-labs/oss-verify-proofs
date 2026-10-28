(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff FxDrive FxDrive3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages EAsStartupHSA EAsS6State EAsStartupTop.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI BrHole Br3Trans.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Start ES6End0 ES6End1 ES6End2 ES6End3 ES6End4 ES6End5 ES6Hole0 ES6Hole1 ES6Hole2 ES6Hole3 ES6Hole4 ES6Hole5.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Amb.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition MAINST_table : list (nat * acs) :=
  [(0%nat, es6end0); (1%nat, es6end1); (2%nat, es6end2); (3%nat, es6end3); (4%nat, es6end4); (5%nat, es6end5)].
Definition MAINST (h : nat) : option acs := hs_lookup h MAINST_table.

Lemma MAINST_pc : forall h ch, MAINST h = Some ch -> pc ch = A_MAIN.
Proof.
  intros h ch H. apply hs_lookup_cases in H. cbn [MAINST_table fold_right fst snd] in H.
  repeat (destruct H as [[_ ->]|H]; [vm_compute; reflexivity|]). destruct H.
Qed.

Definition P_main (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    MAINST h = Some ch /\ pc ch = A_MAIN /\
    c = cfg_of ASEGS R A_MAIN FULL model /\
    cs_ok ASEGS ASAN_H AsanInit.LIMIT
          (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          (in_fs inp) E ch R FULL model
    /\ bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp0.

(* [comment removed for export] *)
Lemma realizes_of_cfg : forall c T, realizes_cfg the_scfg ASEGS c T -> ShapeAlg.realizes ASEGS c T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hk IH | c Hh | c T T' H IH Heq].
  - apply (ShapeAlg.rz_node ASEGS c I evs nx T i0); [exact Hnode | exact IH].
  - apply ShapeAlg.rz_halt. exact Hh.
  - eapply ShapeAlg.rz_conseq; [exact IH | exact Heq].
Qed.
Lemma realizes_to_cfg : forall c T, ShapeAlg.realizes ASEGS c T -> realizes_cfg the_scfg ASEGS c T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hk IH | c Hh | c T T' H IH Heq].
  - apply (rzc_node the_scfg ASEGS c I evs nx T i0); [exact Hnode | exact IH].
  - apply rzc_halt. exact Hh.
  - eapply rzc_conseq; [exact IH | exact Heq].
Qed.

Section Chain.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp0.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  #[local] Notation SV := (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)).
  #[local] Notation argH := (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)).
  #[local] Notation ISP := (bv_unsigned sp0).
  Variable T : ShapeAlgBase.TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAIN : forall c, P_main sp0 brk0 mbase rdraw inp c -> ShapeAlg.realizes ASEGS c T.

  (* [comment removed for export] *)
  Lemma sinv_sp0 : forall E FULL, SV E FULL -> uE E e_sp0_early = ISP.
  Proof.
    intros E FULL [Hag _].
    assert (Ed : edenot E e_sp0_early = edenot (E0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) e_sp0_early).
    { unfold e_sp0_early. cbn [edenot]. rewrite (Hag 0%nat), (Hag 6%nat), (Hag 10%nat) by (unfold NX0; lia). reflexivity. }
    unfold uE. rewrite Ed. rewrite e_sp0_early_eq.
    exact (u_e_sp0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hsp Hva Hve Hfit).
  Qed.

  Lemma cxi_of : forall E ch R FULL m, cs_ok ASEGS ASAN_H AsanInit.LIMIT SV argH (in_fs inp) E ch R FULL m ->
    CXI.cs_ok ASEGS ASAN_H AsanInit.LIMIT SV argH ISP (in_fs inp) E ch R FULL m.
  Proof.
    intros E ch R FULL m HC. apply CXI.cs_ok_intro; [exact HC|].
    pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as X. unfold TOP, alloc_top, stack_max_size in X.
    pose proof (sinv_sp0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as Y. unfold uE in Y. rewrite Y in X. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hole_realizes : forall h ch E R FULL m,
    S6START h = Some ch ->
    cs_ok ASEGS ASAN_H AsanInit.LIMIT SV argH (in_fs inp) E ch R FULL m ->
    ShapeAlg.realizes ASEGS (cfg_of ASEGS R A_S6 FULL m) T.
  Proof.
    intros h ch E R FULL m Hh HC.
    assert (Epc : pc ch = A_S6) by (rewrite (S6START_pc h ch Hh); vm_compute; reflexivity).
    assert (K : forall END (he : nat), MAINST he = Some END ->
              BrHole.fx_hole the_scfg ASEGS ASAN_H AsanInit.LIMIT SV argH ISP (in_fs inp) ch END ->
              ShapeAlg.realizes ASEGS (cfg_of ASEGS R A_S6 FULL m) T).
    { intros END he HEND Hfx. apply realizes_of_cfg. rewrite <- Epc. unfold cfg_of.
      apply (Hfx E R FULL m T (cxi_of _ _ _ _ _ HC)).
      intros E1 R1 FULL1 m1 Hag HC1 Hfs. apply realizes_to_cfg.
      pose proof (MAINST_pc he END HEND) as Hp. unfold pc in Hp. rewrite Hp. apply MAIN.
      split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
      exists he, END, E1, R1, FULL1, m1. split; [exact HEND|]. split; [exact (MAINST_pc he END HEND)|]. split; [reflexivity|].
      split; [exact (CXI.cs_ok_aps _ _ _ _ _ _ _ _ _ _ _ _ HC1)|].
      pose proof (CXI.cs_ok_visp _ _ _ _ _ _ _ _ _ _ _ _ HC1) as V. exact V. }
    apply hs_lookup_cases in Hh. cbn [S6START_table fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end0 0%nat eq_refl (s6_hole_0 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end1 1%nat eq_refl (s6_hole_1 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end2 2%nat eq_refl (s6_hole_2 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end3 3%nat eq_refl (s6_hole_3 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end4 4%nat eq_refl (s6_hole_4 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh as [[-> ->]|Hh]; [exact (K es6end5 5%nat eq_refl (s6_hole_5 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Hsp Hva))|].
    destruct Hh.
  Qed.

  Theorem as_chain_srealizes :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
  Proof.
    apply (as_startup_srealizes sp0 brk0 mbase rdraw inp T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T_nil).
    intros c [_ (k & ch0 & E & R & FULL & m & Hk & Hpc & -> & HC)].
    destruct (s6_split ASEGS ASAN_H AsanInit.LIMIT SV argH (in_fs inp) k ch0 E R FULL m Hk HC) as (h & ch & Hh & _ & HC').
    exact (hole_realizes h ch E R FULL m Hh HC').
  Qed.
End Chain.
Check as_chain_srealizes.
