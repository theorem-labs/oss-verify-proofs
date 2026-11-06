(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeMm BudgetBridgeDispatch BudgetBridgeStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeRun () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.BudgetBridgeRun.Run."; "OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.BudgetBridgeStep."], [["1list"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "0L"; "3SNext"; "3all_traces_error_cfg"; "3budget_refused_at"; "3config"; "3obs_trace_cfg"; "3reaches_error_cfg"; "3reaches_unmodeled_cfg"; "3sstep_cfg"; "3star_cfg"]; ["3unmodeled_at"; "4event"; "5nref"; "5okl"; "6liftc"; "6okc"; "0c"; "0c'"; "0c2"; "0c2'"; "0cfg"; "0evs"; "0segs"; "0tr"]]).
Definition bounded_pres_stmt : Prop :=
forall i m eff m' evs,
syscall_spec i m (Ok eff m' evs) ->
maps_bounded (vm_maps (m_vmmaps m)) -> maps_bounded (vm_maps (m_vmmaps m')).
Section Run.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L : Z.
Hypothesis MCLE : move_charge_le_stmt.
Hypothesis BND : bounded_pres_stmt.
Definition okl (c : config) : Prop :=
vm_limit (m_vmmaps (cfg_model c)) <= L /\ maps_bounded (vm_maps (m_vmmaps (cfg_model c))).
Definition nref (c : config) : Prop :=
forall tr c', star_cfg segs cfg c tr c' -> ~ budget_refused_at segs c'.
Lemma nref_here : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "<':&Br1%211&5&9vLr2%3221%511p071pQ>;1").
Proof. intros c H. apply (H [] c). apply star_cfg_refl. Qed.
Lemma nref_step : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "D':'0'A%211&Br3%211'>vLvJr4(7r2%211%7565491p019p0:1pQ@A1pQH?1pQ>C1").
Proof.
intros c evs c' H Hs tr c'' Hst. apply (H (evs ++ tr) c''). eapply star_cfg_step; eassumption.
Qed.
Lemma okc_of : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "?':&Br1%211&Cr2%211&EvLv6r3%43321p061p0:1pQ>>1").
Proof. intros c Hn [Hl Hb]. split; [exact (nref_here c Hn)|]. split; assumption. Qed.
Lemma okl_step : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "G':'0'A%211&Br3%211&Cr4%211'>vLvJr5(7%11:%6554381p018p091p0=1pQ@D1pQHB1pQ>F1").
Proof.
intros [ms m] evs c' Hn Hl Hs. pose proof (okc_of _ Hn Hl) as Hok.
remember (mkCfg ms m) as c eqn:Ec. remember (SNext c') as r eqn:Er.
destruct Hs as
[ms0 M ms' M' Hh Hs Ha | ms0 M Hh Hs Ha | ms0 M Hh Hs Ha
| ms0 M x8 eff M' M'' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms0 M x8 eff M' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms0 M x8 eff M' evs0 code Hh Hs Hsp Hh' Hk
| ms0 M x8 eff M' evs0 sig Hh Hs Hsp Hk
| ms0 M x8 Hh Hs Hsp ];
injection Ec as -> ->; try discriminate Er; injection Er as <-;
destruct Hl as [Hl Hb]; unfold okl; cbn [cfg_model] in *.
-
destruct (mi_account_step_model_frame segs _ _ _ _ Ha) as (_ & Hv & _).
rewrite Hv. split; assumption.
-
pose proof (okc_mark segs L _ _ _ Hok Hh Hs) as Hmk.
pose proof (spec_limit MCLE _ _ _ _ _ Hmk Hb Hsp) as Hl'.
pose proof (BND _ _ _ _ _ Hsp Hb) as Hb'.
rewrite <- (materialize_limit _ _ _ Hm) in Hl', Hb'.
split; [rewrite Hl'; exact Hl | exact Hb'].
-
pose proof (okc_mark segs L _ _ _ Hok Hh Hs) as Hmk.
pose proof (spec_limit MCLE _ _ _ _ _ Hmk Hb Hsp) as Hl'.
split; [rewrite Hl'; exact Hl | exact (BND _ _ _ _ _ Hsp Hb)].
-
pose proof (okc_mark segs L _ _ _ Hok Hh Hs) as Hmk.
pose proof (spec_limit MCLE _ _ _ _ _ Hmk Hb Hsp) as Hl'.
split; [rewrite Hl'; exact Hl | exact (BND _ _ _ _ _ Hsp Hb)].
Qed.
Lemma star_fwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "Q1':'0'A%211'?vLvJr3r2r1%6554321&Br4%211&Cr5%211'1&Dv6r6%3221%423:%C5BA281%:1<%82<1%9231p0;1p0?1p0C1pQ@N1pQLL1pQ>Q01").
Proof.
intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros Hn Hl.
- split; [apply star_cfg_refl | split; assumption].
- pose proof (step_fwd segs cfg L MCLE c1 evs (SNext c2) (okc_of c1 Hn Hl) Hs) as Hs'.
destruct (IH (nref_step _ _ _ Hn Hs) (okl_step _ _ _ Hn Hl Hs)) as (Hst' & Hn3 & Hl3).
split; [|split; assumption].
eapply star_cfg_step; [exact Hs' | exact Hst'].
Qed.
Lemma star_bwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "Q:':'0'A%211'?vLvJr3r2r1%6554321'2r5&Dv6%2216%53@41&B%11:&C%11='3'1r8%D5CB<1?r7%?3J1;%:1B%91C%7221%8241%9271qQ@Q01%<2Q11p0>1p0A1p0D1pQ>Q51p0L1pQDQ71pQLQ51pQBQ91").
Proof.
intros c2 tr c2' H. induction H as [c2 | c1 evs c2 tr c3 Hs Hst IH]; intros c Ec Hn Hl.
- exists c. split; [apply star_cfg_refl | auto].
- subst c1.
destruct (step_bwd segs cfg L MCLE c evs (SNext c2) (okc_of c Hn Hl) Hs) as ([c1'|] & Hs1 & E);
[|discriminate].
cbn in E. injection E as ->.
destruct (IH c1' eq_refl (nref_step _ _ _ Hn Hs1) (okl_step _ _ _ Hn Hl Hs1))
as (c' & Hst' & -> & Hn' & Hl').
exists c'. split; [eapply star_cfg_step; eassumption | auto].
Qed.
Lemma traces_iff : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "I':&Br1%211&Cr2%211'0'A%211&4&;vLvJr4%44321=&Dv6%2214%84761A%:251pQL<1p0@1p0D1pQ>H1").
Proof.
intros c Hn Hl tr. split.
- intros (tr' & c' & Hst & Hp). destruct (star_fwd c tr' c' Hst Hn Hl) as (Hst' & _).
exists tr', (liftc L c'). auto.
- intros (tr' & c2' & Hst & Hp).
destruct (star_bwd _ _ _ Hst c eq_refl Hn Hl) as (c' & Hst' & _ & _).
exists tr', c'. auto.
Qed.
Lemma errors_iff : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "E':&Br1%211&Cr2%211&4&<vLvJr3%43321&Dv6%2214%83761%:251p0<1p0@1pQ>D1").
Proof.
intros c Hn Hl. split.
- intros (tr & c' & evs & Hst & He). destruct (star_fwd c tr c' Hst Hn Hl) as (Hst' & Hn' & Hl').
exists tr, (liftc L c'), evs. split; [exact Hst'|].
exact (step_fwd segs cfg L MCLE c' evs SError (okc_of c' Hn' Hl') He).
- intros (tr & c2' & evs & Hst & He).
destruct (star_bwd _ _ _ Hst c eq_refl Hn Hl) as (c' & Hst' & -> & Hn' & Hl').
destruct (step_bwd segs cfg L MCLE c' evs SError (okc_of c' Hn' Hl') He) as ([c''|] & He' & E);
[discriminate|].
exists tr, c', evs. auto.
Qed.
Lemma unmodeled_at_iff : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "@':&EvLv6r1%43321&4&@r2%2271&D%1283%52:1%7241p091pQ>?1").
Proof.
intros [ms m] Hok. unfold unmodeled_at, liftc. cbn [cfg_ms cfg_model].
change (m_halted (setlim L m)) with (m_halted m).
split; intros (Hh & [(Hs & Ha) | (x8 & Hs & Hu)]); split; try exact Hh.
- left. split; [exact Hs|]. unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try reflexivity.
+ destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
+ discriminate.
- right. exists x8. split; [exact Hs|].
apply (sim_unm_iff L _ m (okc_sim segs L MCLE ms m x8 Hok Hh Hs)). exact Hu.
- left. split; [exact Hs|]. unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try reflexivity.
+ destruct (materialize_model_accesses (setlim L m) (@accessed_ranges _ report)); discriminate.
+ discriminate.
- right. exists x8. split; [exact Hs|].
apply (sim_unm_iff L _ m (okc_sim segs L MCLE ms m x8 Hok Hh Hs)). exact Hu.
Qed.
Lemma unmodeled_iff : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "E':&Br1%211&Cr2%211&4&=vLvJr3%43321&Dv6%2214%83761%:251p0<1p0@1pQ>D1").
Proof.
intros c Hn Hl. split.
- intros (tr & c' & Hst & Hu). destruct (star_fwd c tr c' Hst Hn Hl) as (Hst' & Hn' & Hl').
exists tr, (liftc L c'). split; [exact Hst'|].
apply (unmodeled_at_iff c' (okc_of c' Hn' Hl')). exact Hu.
- intros (tr & c2' & Hst & Hu).
destruct (star_bwd _ _ _ Hst c eq_refl Hn Hl) as (c' & Hst' & -> & Hn' & Hl').
exists tr, c'. split; [exact Hst'|].
apply (unmodeled_at_iff c' (okc_of c' Hn' Hl')). exact Hu.
Qed.
Lemma all_errors_fwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "E':'8vLvJr1%43321&Br2%211&Cr3%211&Dv6r4%3221%?3>=1p061p0:1p0>1pQ>D1").
Proof.
intros c H. induction H as [c (evs & to & Hst) Hnext IH]; intros Hn Hl.
constructor.
- exists evs, (lift_to L to). exact (step_fwd segs cfg L MCLE c evs to (okc_of c Hn Hl) Hst).
- intros evs' c2' Hs2.
destruct (step_bwd segs cfg L MCLE c evs' (SNext c2') (okc_of c Hn Hl) Hs2) as ([c'|] & Hs1 & E);
[|discriminate].
cbn in E. injection E as ->.
exact (IH evs' c' Hs1 (nref_step _ _ _ Hn Hs1) (okl_step _ _ _ Hn Hl Hs1)).
Qed.
Lemma all_errors_bwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "I':'8vLvJr1%43321'2r3&Dv6%2216%53;41&Br2%211&C%119r4%A3@?1p031p061p0:1pQ>F1p0B1pQBH1").
Proof.
intros c2 H. induction H as [c2 (evs & to & Hst) Hnext IH]; intros c Ec Hn Hl. subst c2.
constructor.
- destruct (step_bwd segs cfg L MCLE c evs to (okc_of c Hn Hl) Hst) as (r1 & Hs1 & _).
exists evs, r1. exact Hs1.
- intros evs' c' Hs1.
pose proof (step_fwd segs cfg L MCLE c evs' (SNext c') (okc_of c Hn Hl) Hs1) as Hs2.
exact (IH evs' (liftc L c') Hs2 c' eq_refl (nref_step _ _ _ Hn Hs1) (okl_step _ _ _ Hn Hl Hs1)).
Qed.
Lemma okc_lift_nref : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "?':&EvLv6r1%43321&5&9&Dr2%2271%4291%611p081pQ>>1").
Proof.
intros [ms m] Hok. unfold liftc. cbn [cfg_ms cfg_model].
intros (Hh & [(Hs & report & Hst & Hm) | (x8 & Hs & [Hmk | (eff & M' & evs & Hsp & Hh' & Hm)])]);
cbn [cfg_ms cfg_model] in *; change (m_halted (setlim L m)) with (m_halted m) in Hh.
- destruct (okc_instr_mat segs L ms m report Hok Hh Hs Hst) as (m1 & E1).
destruct Hok as (_ & Hle & _).
rewrite (materialize_setlim L m _ m1 Hle E1) in Hm. discriminate.
- pose proof (okc_mark segs L ms m x8 Hok Hh Hs) as Hmk0. destruct Hok as (_ & Hle & _).
rewrite (alloc_mark_setlim L _ m Hle Hmk0) in Hmk. discriminate.
- pose proof (okc_sim segs L MCLE ms m x8 Hok Hh Hs) as S.
destruct (sim_fwd_ok L _ m eff M' evs S Hsp) as (m0 & Hsp0 & ->).
destruct (okc_mat segs L ms m x8 eff m0 evs Hok Hh Hs Hsp0 Hh') as (m1 & E1).
pose proof (okc_mark segs L ms m x8 Hok Hh Hs) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (spec_limit MCLE _ m eff m0 evs Hmk Hb Hsp0) as Hl0.
rewrite (materialize_setlim L m0 _ m1 ltac:(rewrite Hl0; exact Hle) E1) in Hm. discriminate.
Qed.
Lemma nref_lift : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeRun "?':&Br1%211&Cr2%211&Dv6r3%3221%:11p061p0:1pQ>>1").
Proof.
intros c Hn Hl tr c2' Hst.
destruct (star_bwd _ _ _ Hst c eq_refl Hn Hl) as (c' & _ & -> & Hn' & Hl').
exact (okc_lift_nref c' (okc_of c' Hn' Hl')).
Qed.
End Run.
