(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.LimSim Require Import LimSim LimSimMm LimSimMv LimSimWf LimSimSys.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run05mkCfg89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim6LimSim~~~~~~j35relim06config09sstep_cfg07step_to3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticspedmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateu55Modelj33MOK37Corelib4Init9Datatypeshi14list37Corelib4Init5Logichk13andhk13not06SError05SNext0h1budget_refused_atu55event89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim8LimSimMm~~~~~~hoe5MV_OKj39relim_cfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~huc8the_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~iif8realizes0hareaches_budget_refused_cfg89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim9LimSimSys~~~~~~ip34MOKcip3eMREMAP_MOVE_OKiif4TSet09cfg_modelhk12eq37Corelib7Numbers7BinNumsjh01Zu58m_vmmapsu58vm_limit89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim8LimSimMv~~~~~~jk42WF3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejp37Segment0bSpuriousCfg46Stdlib6ZArith6BinInt1Zju02le" s.
Import ListNotations.
Open Scope Z_scope.

Section Steps.
Variable segs : ltac2:(zQ "20!hj9!js8@1$0$1").
Variable cfg : ltac2:(zQ "10!jt3$0").
Variable L0 L : Z.
Hypothesis HLE : ltac2:(zQ "10!jv8@2$0?1L?2L0").

Ltac hrel H := first [ exact H | rewrite relim_halted; exact H | cbn [cfg_model cfg_ms]; rewrite relim_halted; exact H
                     | cbn [cfg_model cfg_ms] in *; rewrite ?relim_halted in *; exact H ].
Ltac krel H := first [ exact H | rewrite relim_killed; exact H | cbn [cfg_model cfg_ms]; rewrite relim_killed; exact H
                     | cbn [cfg_model cfg_ms] in *; rewrite ?relim_killed in *; exact H ].

(* [comment removed for export] *)
Lemma step_down_exact : ltac2:(zQ "h00!ic!na!o2!oa!p5!t5!hh3!hhb!hj9!hl5!hlc!hm3!hmb!hn2!ho6!ht7>2ms$5>1m$6>3evs@1$8$e>2st$4>0@2$7?2L0^3>0@1$f^4>0@1$a@2$d?4segs@2$0^6@2$1?1L^5>0@5$3?4segs?3cfg@2$0^7^6^5^4M4\2st$4P^5\1c$2M2\1c$2P^1\3ms'$5\2m'$6@2$9@5$3?4segs?3cfg@2$0^b@2$1?1L^a^9@1$c@2$0^2@2$1?1L^1@2$7?2L0^1@5$3?4segs?3cfg@2$0^8@2$1?1L^7^6$b").
Proof.
  intros ms m evs st HM MV NB Hs.
  remember (mkCfg ms m) as c eqn:Ec.
  destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
                 | ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
    injection Ec as -> ->.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Emat; [|discriminate].
    injection Ha as <- <-.
    assert (NN : materialize_model_accesses (relim L m) (@accessed_ranges _ report) <> None).
    { intros E. apply NB. split; [hrel Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact E]. }
    pose proof (materialize_relim_down L m _ _ Emat NN) as Emat'.
    split; [| unfold MOK; rewrite (materialize_limit _ _ _ Emat); exact HM].
    apply sstep_cfg_instr; [hrel Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat'. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|apply sstep_cfg_instr_fault; [hrel Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity]|discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Emat; [discriminate|].
    (* [comment removed for export] *)
    exfalso. apply NB. split; [hrel Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est|].
    destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m2|] eqn:E2; [exfalso | first [reflexivity | exact E2]].
    assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
    destruct (materialize_relim_up L m _ _ HLE' E2) as (m0 & E0 & _). rewrite E0 in Emat. discriminate.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|].
    + destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
    + apply sstep_cfg_instr_unmodeled; [hrel Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    assert (NN : materialize_model_accesses (relim L mm') (syscall_effect_accesses eff) <> None).
    { intros E. apply NB. split; [hrel Hh|]. right. exists x8. split; [exact Hp|]. right.
      exists eff, (relim L mm'), evs0. split; [exact Hsp0|]. split; [hrel Hh' | exact E]. }
    pose proof (materialize_relim_down L mm' _ _ Hmat NN) as Hmat'.
    split; [| unfold MOK; rewrite (materialize_limit _ _ _ Hmat); exact HM0].
    eapply sstep_cfg_syscall; [hrel Hh | exact Hp | exact Hsp0 | | hrel Hh' | exact Hmat'].
    intros SP. apply Hnsp. exact (spurious_relim_down cfg L0 L HLE _ m eff HM SP).
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    exfalso. apply NB. split; [hrel Hh|]. right. exists x8. split; [exact Hp|]. right.
    exists eff, (relim L mm'), evs0. split; [exact Hsp0|]. split; [hrel Hh'|].
    destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m2|] eqn:E2; [exfalso | first [reflexivity | exact E2]].
    assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
    destruct (materialize_relim_up L mm' _ _ HLE' E2) as (m3 & E3 & _). rewrite E3 in Hmat. discriminate.
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    split; [| exact HM0]. rewrite <- (relim_fs L mm').
    eapply sstep_cfg_exit; [hrel Hh | exact Hp | exact Hsp0 | hrel Hh' | krel Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    split; [| exact HM0]. rewrite <- (relim_fs L mm').
    eapply sstep_cfg_killed; [hrel Hh | exact Hp | exact Hsp0 | krel Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark segs L ms m x8 NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
    eapply sstep_cfg_syscall_unmodeled; [hrel Hh | exact Hp | exact Hsp0].
Qed.

End Steps.

Section Rz.
  Context {SC : StepCfg}.
  Variable segs : ltac2:(zQ "20!hj9!js8@1$0$1").
  Variable L0 L : Z.
  Hypothesis HLE : ltac2:(zQ "10!jv8@2$0?1L?2L0").

  Theorem realizes_relim_at : ltac2:(zQ "90!hu0!ii3!ima!hlc!o2!in6!itd!iu5!iv7>1c$4>1T$8>0@4$2?4segs?2SC^2^1>0@2$6?2L0^3>0@1$3@3$5?4segs@1$1?2SC@2$0?1L^4>0@3$7?4segs@1$1?2SC^5@4$2?4segs?2SC@2$0?1L^6^5").
  Proof.
    intros c T Hrz. induction Hrz as [c I evs nx T i0 [N1 N2] Hcont IH | c Hh | c T T' Hrz IH Heq]; intros HM NR MV.
    - destruct c as [ms m]. unfold MOKc in HM; cbn in HM. unfold relim_cfg; cbn.
      pose proof (not_reaches_here segs the_scfg _ NR) as NB. pose proof (MREMAP_MOVE_OK_here segs the_scfg _ MV) as MVH. cbn in MVH.
      apply (rz_node segs _ I evs (fun i => relim_cfg L (nx i)) T i0).
      + split.
        * intros i. pose proof (step_down_exact segs the_scfg L0 L HLE ms m (evs i) (SNext (nx i)) HM MVH NB (N1 i)) as Hs.
          destruct (nx i) as [ms' m']. exact (proj1 Hs).
        * intros e st Hs. pose proof (step_up segs the_scfg L0 L HLE ms m e st HM MVH NB Hs) as UP.
          destruct st as [c'|].
          -- destruct UP as (ms' & m0 & Hs0 & -> & HM0). destruct (N2 _ _ Hs0) as (j & -> & Ej).
             exists j. split; [reflexivity|]. injection Ej as E. rewrite <- E. reflexivity.
          -- exfalso. destruct (N2 _ _ UP) as (j & _ & Ej). discriminate Ej.
      + intros i. pose proof (N1 i) as Hs. destruct (nx i) as [ms' m'] eqn:Enx.
        pose proof (step_down_exact segs the_scfg L0 L HLE ms m (evs i) (SNext (mkCfg ms' m')) HM MVH NB Hs) as [Hs' HMi].
        pose proof (IH i) as IHi. rewrite Enx in IHi. apply IHi.
        * unfold MOKc. cbn. exact HMi.
        * exact (not_reaches_step segs the_scfg _ _ _ NR Hs').
        * exact (MREMAP_MOVE_OK_step segs the_scfg _ _ _ MV Hs).
    - apply rz_halt. unfold relim_cfg. cbn. rewrite relim_halted. exact Hh.
    - eapply rz_conseq; [apply IH; assumption | exact Heq].
  Qed.

  Theorem realizes_relim_closed : ltac2:(zQ "d0!ivf!hu0!ima!jga!hlc!ji9!o2!in6!jie!jj9!jod!ii3!iv7>1c$6>1T$c>0@3$3$5@1$9@1$8@1$0^2?2L0>0@1$a@1$0^3>0@1$4@3$7?4segs@1$b?2SC@2$1?1L^4>0@4$2?4segs?2SC^5^4@4$2?4segs?2SC@2$1?1L^6^5").
  Proof.
    intros c T HM Hwf NR Hrz. exact (realizes_relim_at c T Hrz HM NR (MREMAP_MOVE_OK_of_WF segs the_scfg c Hwf)).
  Qed.
End Rz.

(* [comment removed for export] *)
Corollary realizes_init_relim {SC : StepCfg} : forall segs pc ph sp brk0 mbase rnd (Lbig Lsmall : Z) inp T,
  Lsmall <= Lbig ->
  source_within_budget_scfg the_scfg Lsmall (mkImage segs pc ph) (mkEntry sp brk0 mbase rnd) inp ->
  realizes segs (init_config segs pc ph sp brk0 mbase rnd Lbig inp) T ->
  realizes segs (init_config segs pc ph sp brk0 mbase rnd Lsmall inp) T.
Proof.
  intros segs pc ph sp brk0 mbase rnd Lbig Lsmall inp T HLE NB Hrz.
  unfold source_within_budget_scfg, run_scfg_budget_refused in NB.
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in NB |- *.
  apply (realizes_relim_closed segs Lbig Lsmall HLE); [apply init_config_limit | apply init_config_WF | exact NB | exact Hrz].
Qed.
