(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim FileSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Nodes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Nodes.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Scfg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1None"; "1O"; "1Some"; "1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1unit"; "2and"; "2eq"; "2ex"]; ["2iff"; "2not"; "2or"; "3Z"; "4check_syscall"; "5CheckOk"; "5CheckUnmodeled"; "5check_result"; "5check_ret_only"; "5check_ret_only_copyins"; "6machine_state"; "6ms_gpr"; "6ms_svc_pending"; "6set_gpr0"; "7SError"; "7SNext"]; ["7advance_past_svc"; "7apply_effect"; "7mkCfg"; "7spurious_refusal_cfg"; "7sstep"; "7sstep_cfg"; "7step_to"; "7sys_input"; "8FdEntry"; "8Model"; "8SyscallEffect"; "8alloc_fd"; "8errno_ret"; "8event"; "8fd_lookup"; "8m_fds"]; ["8m_fs"; "8m_halted"; "8m_vm_lazy"; "8materialize_model_accesses"; "8syscall_effect_accesses"; "9openat_errnos"; ":is_exit_no"; ";check_open_result_copyins"; "<open_I"; "<open_nx"; "=fam_on"; ">TSet"; ">halt_ev"; ">node_ok"; ">t_alt2"; ">t_emit"]; [">t_exit"; "?srealizes"; "@In"; "0T"; "0code"; "0e"; "0eff"; "0eff0"; "0evs"; "0evs0"; "0fd"; "0m'"; "0m0"; "0mk"; "0model"; "0model'"]; ["0model''"; "0ms"; "0r"; "0reads"; "0scfg"; "0segs"; "0st"; "AZ_to_bv"; "Abv"; "Abv_and"; "0x8"]]).
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma sstep_svc_inv : ltac2:(TCodec.tc2 tcn__Nodes "T0'J'Q9'RHyR0%211'7'Q=%211'Q6'>':%117&Lr5%211(4r3%22=1%93741'Q4vRE(Q2r6%221:r2%645291'B'?'Q:'='G&D&Q7r:r8%33?21r9%632E1(Er1%22@1%Q03;41&QA%11K(2%11Q9%Q53Q331%Q63Q8=G%Q61Q?&QC&QDr4%211%42Q51%Q72QE?%Q>3721r7(O&Q0&Q1r;%221:%411%Q:21H%711%QH3QI91%Q52;1%Q62D1%Q72F1qU2R41%Q;2R51%M1Q?%QO3QM1K(9%11R4%R23R4C1%J1QL%L2QE1%Q21R=%R63O21(N%R83R9QK1%QE231%QF281%QG2<1%R62RAQ>%R=3R;Q;1&5(6&QL%12R:QC%33RE1A%53RFR41%RD3RFQK1%R92Q2R>%Q611%RG3RHQ81%R4241%R52<1qT:RO1%R92S01%R;2A1%R<2Q01%R:2QN1qTBS11%R>2S21qU0S91%R@2S:1qT>R@1%RB2RA1%R>3RJR<RH%R@31R8QG(F%S83RC21%S93S;S5Q8%S:3S;R0Q3%RG221%RH241qT>RJ1%RL2RK1%RN2;1p0S01p0S81pU>SC1pT<SE1pUFSI1pTNSM1pU4SO1").
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ left. eexists. repeat split; eauto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. left. repeat split; auto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
apply check_syscall_err_iff. assumption.
Qed.
Lemma sstep_cfg_svc_inv : ltac2:(TCodec.tc2 tcn__Nodes "T4'J'Q9'RHyR0%211'7'Q=%211'Q6'>':%117&Lr5%211(4r3%22=1%93741'Q5vREvRD(Q2r6%221;r2%75652:1'B'?'Q:'='G&D&Q7r:r8%33@21r9%632F1(Er1%22@1%Q13;41&A&Q3%14H98M%311&QA%11G(2%11Q>%Q:3Q831%Q;3Q=AK%Q;1QD&QC&QDr4%211%42Q:1%Q<2QJC%QC3721r7(O&Q0&Q1r;%221:%411%Q>21L%711%QM3QN91%Q92;1%Q:2D1qU2R81%Q>2R91(9%11R6%R43R6@1%G1QN%I2QF1%O1R?%R83L21(N%R:3R;QL1%QF231%QG281%QK2<1%QI2Q41%QJ2Q:1%Q:1R9%R;2RFQB%RB3R@21&5(6&QL%12R?QG%33RJ1D%53RKR81%RI3RKQO1%R=2Q2RC%Q611%RL3RMQ81%R8241%R92<1qT:S41%R=2S51%R?2B1%R=2R11qTBS51%RA2S61qU0S=1%RC2S>1qT>RC1%RE2RD1%RA3RNR?RK%RC31R;QF(F%S<3RF21%S=3S?S9Q:%S>3S?QOQ5%RJ221%RK241qT>RM1%RO2RN1%S12;1p0S31p0S<1pU>SG1pT<SI1pUFSM1pTNT11pU4T31").
Proof.
intros ms model x8 e st Hsvc Hss.
destruct (sstep_cfg_svc_cases segs scfg ms model x8 e st Hsvc Hss)
as [(eff & model' & evs & Hspec & Hrest) | (Hum & -> & ->)].
- left. exists eff, model', evs. split; [apply check_syscall_ok_iff; exact Hspec | exact Hrest].
- right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
apply check_syscall_err_iff. exact Hum.
Qed.
Lemma sstep_cfg_of_check : ltac2:(TCodec.tc2 tcn__Nodes "R?'J'Q9'RHyR0%211'Q:'7'Q=%211'>':%117&QAr5%211(2%11<%83631&Lr7%211(4%12B9%>3<31'G&D&Q7vREr8r6%43321%631B<(Er4r3%3221%K3<51&A&Q3vRDr9%?3>1F%4431>=%611%Q01?%Q43Q21M';%12Q;Q;%Q:11&QB%11O(9%115%Q<3531'Q5(Q2r<r;%3221(O&Q0&Q1%126F%311%921Q4%611%<5Q7K8Q?1p0>1p0G1p0J1p0Q21p0Q@1p0QG1pTBR11pTHR91pT>R61pUFR81pTNR<1pU4R>1").
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
apply (sstep_cfg_syscall segs scfg ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hns.
- exact Hh'.
- apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.
Lemma sstep_of_check : ltac2:(TCodec.tc2 tcn__Nodes "R5'J'Q9'RHyR0%211'Q:'7'Q=%211'>':%117&QAr5%211(2%11<%83631&Lr7%211(4%12B9%>3<31'G&D&Q7vREr8r6%43321%631B<(Er4r3%3221%K3<51';%12Q2Q2%Q111&QB%11<(9%115%Q33531'Q4(Q2r;r:%3221(O&Q0&Q1%126I%311%921Q4%611%<4N8L1p0>1p0Q:1p0H1p0Q61p0Q=1pTBQG1pTHQO1pT>QL1pUFQN1pTNR21pU4R41").
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hh'.
- apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.
Lemma node_chk_ev_sp : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
(exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
\/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
apply (node_svc segs scfg ms model x8 I effs ms' evs Hh Hsvc).
- intros i. apply check_syscall_ok_iff. apply Hok.
- exact Hns.
- intros eff m' ev Hspec. apply Hinv. apply check_syscall_ok_iff. exact Hspec.
- intros Hum. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. exact Hum.
- exact Hh'.
- exact Hlazy.
Qed.
Lemma node_chk_ev : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
apply (node_chk_ev_sp ms model x8 I effs ms' evs Hh Hsvc Hok Hns); try assumption.
intros eff m' ev Hc. left. exact (Hinv eff m' ev Hc).
Qed.
Lemma uniform_not_spurious : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (b : bool),
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = b) ->
forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i).
Proof.
intros ms model x8 I effs ms' evs b Hinv Hb i (Hoff & Hr & eff' & m' & ev' & Hspec & Hnr).
apply check_syscall_ok_iff in Hspec.
destruct (Hinv _ _ _ Hspec) as (j & -> & _ & _).
rewrite Hb in Hr. rewrite Hb in Hnr. congruence.
Qed.
Lemma node_chk_sp : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(exists i, eff = effs i /\ m' = ms' i /\ evs = [])
\/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok segs scfg (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
apply (node_chk_ev_sp ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hns); auto.
Qed.
Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
node_ok segs scfg (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.
Lemma node_det : ltac2:(TCodec.tc2 tcn__Nodes "S0'J'Q9'RHyR0%211'Q:'7'Q=%211'>':%117&QAr5%211(2%11<%83631&Lr7%211(4%12B9%>3<31&@'G&D&Q7vREr;r9%43321r3r:%83321(Er2r1%3221%N3>51'=r8%Q13Q5:1%Q23Q:7Hr6%Q43Q581%6231%7251%H291pTBQ91pTHQA1pT>Q>1&A%J3ID<%L31AH(F%Q?3O21%511pT>QE1%Q?1?%QC3QA1Q<';%12QJQJ%QI11&QB%11Q>(9%115%QK3531&QMvRD(Q2r<%221Q<'<q01Q2&Q0&Q1r=%221Q>%411%:21QCq081%>6QG=:981p0@1p0I1p0L1p0Q41p0R11p0R81pTDRB1pTJRJ1pT@RG1pUFRI1pTNRM1pU4RO1").
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
{ intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
- intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
- exact Hinv.
- exact Hnu.
- intros []; exact Hh0.
- intros []; exact Hlazy0.
- apply (uniform_not_spurious ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
(refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
intros []. reflexivity.
Qed.
Lemma node_ret_only : ltac2:(TCodec.tc2 tcn__Nodes "R:'J'Q9'RHyR0%211'7'Q=%211'>':%116&QAr5%211(2%11;%83631&Lr7%211(4%12A9%>3<31'Q:'G&D&Q7vREr9%3321;r1r8%73321&Hr6r4%3462H1%M3=51pT>?1';%12Q4Q4%Q411&QB%119(9%115%Q63531&QMvRD(Q2r;r:%3221'<q01Q4&Q0&Mr<%221N%411%;21Mq081%?6Q3>:981p0A1p0Q@1p0K1p0Q<1p0QC1pTBQM1pTHR41pU6R21pUFR31pTNR71pU4R91").
Proof.
intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
rewrite <- (apply_effect_no_write ms r).
apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
- intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
- intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
- exact Hh'.
- exact Hlazy.
Qed.
Lemma node_ret_only_copyins : ltac2:(TCodec.tc2 tcn__Nodes "RA'J'Q9'RHyR0%211'7';'8%2241%411'Q=%611'>':%11:&QAr6%211(2%11?%83631&Lr8%211(4%12E9%>3<31'Q:'G&D&Q7vREr:%3321;r1r9%73321&Ir7r5r4%4537I21%N3>61pT>@1%M15%Q13O1J%Q82Q:Q:%Q:11&QB%11Q1(9%115%Q83531&QMvRD(Q2r<r;%3221'<q01F&Q0&Mr=%221M%411%;21Q<q081%?6Q5>:981p0A1p0I1p0L1p0Q>1p0QE1pTBQO1pTHR:1pU6R81pU8R41pUFR:1pTNR>1pU4R@1").
Proof.
intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
rewrite <- (apply_effect_copyins_no_write ms r reads).
apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
- intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
- intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
- exact Hh'.
- exact Hlazy.
Qed.
Lemma rz_ret_only : ltac2:(TCodec.tc2 tcn__Nodes "R<'J'Q9'RHyR0%211'7'Q=%211&QK'>':%117&QAr6%211(2%11<%83631&Lr8%211(4%12B9%>3<31'Q:'G&D&Q7vREr:%3321;r1r9%73321&Hr7r5%3462H1%M3=51pT>?1';%12Q5Q5%Q511&QB%119(9%115%Q63531'R1vRD(Q2&Q0&Mr<%221F%411%621Q5%94M81Q<r=%9216&QO%12Q:J%>4Q2=31p061p0A1p0Q@1p0K1p0Q<1p0QC1pT8QM1pTBQO1pTHR61pU6R41pUFR51pTNR91pU4R;1").
Proof.
intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply srz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.
Lemma rz_ret_only_copyins : ltac2:(TCodec.tc2 tcn__Nodes "RC'J'Q9'RHyR0%211'7';'8%2241%411'Q=%611&QK'>':%11;&QAr7%211(2%11@%83631&Lr9%211(4%12F9%>3<31'Q:'G&D&Q7vREr;%3321;r1r:%73321&Ir8r6r5%4537I21%N3>61pT>@1%M15%Q13O1J%Q92Q;Q;%Q;11&QB%11Q1(9%115%Q83531'R1vRD(Q2&Q0&Mr=%221Q5%411%621G%94O81Gr>%9216&QO%12LQB%>4Q4=31p061p0A1p0I1p0L1p0Q>1p0QE1pT8QO1pTBR11pTHR<1pU6R:1pU8R61pUFR<1pTNR@1pU4RB1").
Proof.
intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply srz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.
Lemma rz_ret_only_silent : ltac2:(TCodec.tc2 tcn__Nodes "R8'J'Q9'RHyR0%211&QK'>':%114&QAr5%211(2%119%83631&Lr7%211(4%12?9%>3<31'Q:'G&D&Q7vREr9%3321;r1r8%73321&Hr6(9'Q=%211%5484J1%O3?71pT>A1'7';%12Q5Q5%311&QB%11<%<14%Q83421'R1vRD(Q2&Q0&Mr;%221H%411%621Q7%94O81Hr<%9216%<4Q2;1Q;p041p0?1p0Q@1p0I1p0Q<1p0QC1pT8QM1pTHR21pU6R01pUFR11pTNR51pU4R71").
Proof.
intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply srz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.
Lemma rz_ret_only_copyins_silent : ltac2:(TCodec.tc2 tcn__Nodes "R?'J'Q9'RHyR0%211'7';'8%2241%411&QK'>':%119&QAr6%211(2%11>%83631&Lr8%211(4%12D9%>3<31'Q:'G&D&Q7vREr:%3321;r1r9%73321&Ir7r5(9'Q=%211%6559K41%Q03@81pT>B1%O17%Q33Q11L%Q92Q;Q;%Q;11&QB%11Q3%<14%Q93421'R1vRD(Q2&Q0&Mr<%221Q6%411%621H%94Q081Q?r=%9216%<4Q3;1Lp041p0?1p0F1p0I1p0Q=1p0QD1pT8QN1pTHR81pU6R61pU8R21pUFR81pTNR<1pU4R>1").
Proof.
intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply srz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.
Lemma rz_det : ltac2:(TCodec.tc2 tcn__Nodes "S1'J'Q9'RHyR0%211'Q:&QK'>':%115&QAr5%211(2%11:%83631&Lr7%211(4%12@9%>3<31'7'Q=%211&@'G&D&Q7vREr;r9%43321r3r:%83321(Er2r1%3221%Q13>51'=r8%Q43Q6:1%Q53Q;7K(9%11G%Q83G91%7241%8261%I2:1pTBK1pTHQC1pT>Q@1&A%K3JE=%M31BI(F%QC3Q021%511pT>QG1r6%QD11%QH3QF1QA';%12QMQM%Q<11&QB%11QC%H14%QO3421'R1vRD(Q2&Q0&Q1r<%221Q>%411%621Q5%94QC81QOr=%9216%<4QF;1Q9p041p0?1p0G1p0K1p0Q31p0R41p0R;1pT8RE1pTJRK1pT@RH1pUFRJ1pTNRN1pU4S01").
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
eapply srz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.
Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs scfg c I (fun _ => []) nx ->
(forall i, srealizes segs scfg (nx i) (T i)) ->
srealizes segs scfg c (t_alt T).
Proof.
intros c I nx T i0 Hnode Hc.
apply (srz_conseq segs scfg c (t_alt (fun i => t_emit [] (T i)))).
- apply (srz_node segs scfg c I (fun _ => []) nx T i0 Hnode Hc).
- intros tr. split.
+ intros [i Hi]. exists i.
exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs scfg _ _ (Hc i)) tr) Hi).
+ intros [i Hi]. exists i.
exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs scfg _ _ (Hc i)) tr) Hi).
Qed.
Lemma rz_exit_chk : ltac2:(TCodec.tc2 tcn__Nodes "QA'J'Q9'RHyR0%211'>':%113&QAr2%211(2%118%83631&Lr4%211(4%12>9%>3<31&QFr3%211'R1vREvRD(Q2r6r5%3221&R0&RI&K(3%2271&RG+WO%22Q21%73Q341&Q@%11<%;231%C4BA=1p0E1p0I1p0Q01pUFQ:1pTNQ>1pU4Q@1").
Proof. intros. eapply srz_exit; eassumption. Qed.
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.
Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
(i : open_I model) : config :=
match i with
| inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
| inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
(mk (alloc_fd (m_fds model)))
end.
Lemma node_open : ltac2:(TCodec.tc2 tcn__Nodes "S1'J'Q9'RHyR0%211'7';'8%2241%411p069'>':%119&QAr4%211(2%11>%83631%>2@@%@11&QBr5%211(9%116%@3631&Lr7%211(4%12L9%F3D31'Q:'G&D&Q7vREr9%3321;r1r8%73321&QGr6%24154G%Q43<41pT>>1%418%Q411%Q83Q61Q1pTFQ@1%H1<%Q011%Q<3Q21MpTFQD1'Q8%Q>11&Q>&Q?r:%211&Q;%112%6231%QA19%QH3921&QJvRDr<%33Q121&QM(Q2r=%2215&QH%117'Q=%QF11q031&QI%138<Q;%;6Q=>8631p0=1p0B1p0N1p0Q31p0Q81p0QH1p0QO1p0R81pTLRB1pU8RD1pUFRJ1pTNRN1pU4S01").
Proof.
intros ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree Hon.
apply node_ok_of_pnode; [| exact Hon]. split.
- intros [[e He] | []]; cbn [open_nx].
+ rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
+ rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy].
rewrite Hchk. apply check_open_result_copyins_ok_iff.
right. exists (alloc_fd (m_fds model)). auto.
- intros e st Hss.
destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
exists (inl (exist _ er Her)). cbn [open_nx].
rewrite apply_effect_copyins_no_write. split; reflexivity.
* subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
injection Hmat as <-.
exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
* rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* congruence.
* rewrite Hmk in Hh2. discriminate.
+ exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.
Lemma rz_open : ltac2:(TCodec.tc2 tcn__Nodes "SI'J'Q9'RHyR0%211'7';'8%2241%411p069&QK'>':%11:&QAr6%211(2%11?%83631%?2AA%A11&QBr7%211(9%116%@3631&Lr9%211(4%12M9%F3D31'Q:'G&D&Q7vREr;%3321;r1r:%73321&QGr8%24154G%Q43<41pT>>1%418%Q411%Q83Q61Q1pTFQA1%H1<%Q011%Q<3Q21MpTFQE1'Q8%Q>11&Q>&Q?r<%211&Q;%112%6231%QA19%QH3921&QJvRDr>%33Q121'C&R2&QE%233Q21'R1(Q2&Q0&MrA&Q<r2%211%5241%711r@%:221%<4QBC1Kp0>1pT<B1r?%Q011%N11%?281%A11%Q313%D221%F4QLM1QH%F2C=&QN%12Q8QN%J4R0Q131p051p0>1p0Q21p0Q71p0QC1p0QH1p0QM1p0R=1p0RD1p0RM1p4S71p2S81pTLS:1pU8S<1pUFSB1pTNSF1pU4SH1").
Proof.
intros ms model x8 reads mk A B Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree Hon HA HB.
apply (srz_alt2 segs scfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
(open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- eapply node_open; eassumption.
- intros [e He]. cbn [open_nx]. apply HA. exact He.
- intros []. cbn [open_nx]. exact HB.
Qed.
End WithSegs.
