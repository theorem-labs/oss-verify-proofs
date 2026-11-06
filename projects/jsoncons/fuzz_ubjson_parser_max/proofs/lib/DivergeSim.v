(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__DivergeSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim.SelfJumpImage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim.WithFP1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1bool"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2iff"]; ["2not"; "2or"; "3Z"; "4Segment"; "4mkPhdrInfo"; "5MachineOk"; "5access_report"; "5fetch_word"; "5is_ecall"; "5machine_result"; "5machine_state"; "5memory_access"; "5mkAccessReport"; "5ms_pc"; "5ms_svc_pending"; "5step"]; ["5step_accesses"; "6SError"; "6SNext"; "6all_traces_error"; "6cfg_model"; "6cfg_ms"; "6config"; "6init_machine_state"; "6is_prefix"; "6mi_account_step"; "6mkCfg"; "6obs_trace"; "6reaches_error"; "6reaches_unmodeled"; "6segments_reserved"; "6sstep"]; ["6star"; "6step_to"; "7EntryDraw"; "8Model"; "8ProcInput"; "8event"; "8in_argv"; "8in_envp"; "8in_hwcap"; "8in_uid"; "8init_model"; "8m_halted"; "8m_vm_lazy"; "8materialize_model_accesses"; "9decode_any"; ":Jal"]; [":instr"; ";bvmap"; "<is_x0"; "0P"; ">spin_segs"; "?is_self_jump"; "?silent_loop"; "?spin_c"; "?spinning"; "?to_spin"; "=to_spin"; "@mkst"; "@v_addi"; "AIn"; "0T"; "0a"]; ["0brk0"; "0c"; "0c'"; "0c0"; "0c2"; "0cs"; "0evs"; "0evs_g"; "0fuel"; "0fx"; "0imm"; "0inp"; "0lim"; "0m"; "0mbase"; "0mem"]; ["0model"; "0model'"; "0ms"; "0ms'"; "0pc"; "0rd"; "0regs"; "0rnd"; "0rom"; "0segs"; "0sp"; "Bbv"; "Bbv_signed"; "0sz"; "0to"; "0tr"]; ["0tr2"; "0w"]]).
Local Ltac div_vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Section WithFP1.
Context {fx : FPState}.
Lemma is_prefix_nil_inv {A} : forall (tr : list A),
is_prefix tr [] -> tr = [].
Proof. destruct tr; [reflexivity | contradiction]. Qed.
Lemma is_prefix_app_mono {A} : forall (e a b : list A),
is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.
Lemma materialize_model_accesses_nil : ltac2:(TCodec.tc2 tcn__DivergeSim "C'QC'='8%113&QMr1(7':'S;yR0%211'6%5221%711%:291(1%12@;%@3>31pULB1").
Proof.
intros [fd [maps lazy materialized] io fs proc lim].
unfold materialize_model_accesses; cbn.
unfold materialize_accesses, newly_materialized_pages; cbn.
reflexivity.
Qed.
Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
mi_account_step segs ms model =
match materialize_model_accesses model ranges with
| Some model' => MachineOk (ms', model')
| None => MachineFault
end.
Proof.
intros segs ms model ms' ranges Hstep.
unfold mi_account_step. rewrite Hstep. reflexivity.
Qed.
Lemma mi_account_step_no_access : ltac2:(TCodec.tc2 tcn__DivergeSim "Q7'5'C%211'J'QC'='I'F%115%311&Q0r4r3%3221(E(Lr1(7&K%211%53A41%72=1%A3=91':%12ED%C11&Q9r5%231A@(9r2%24LK1C%B281%L3851p0<1pV8Q01pV2Q01pV6Q21pVDQ41").
Proof.
intros segs ms model ms' Hstep.
rewrite (mi_account_step_of_accesses segs ms model ms' [] Hstep).
rewrite materialize_model_accesses_nil. reflexivity.
Qed.
Lemma mi_account_step_halted : ltac2:(TCodec.tc2 tcn__DivergeSim "Q5'5'C%211'J'QC'='I':%1254%311&Q9r5r4r3%43321(E(9r2r1%34@?21%52<1%@3<71'8'S;yR0%211%411&QK%11;%21A%I3421p0:1pV4L1pV8N1pV2N1pV6Q01pVDQ21").
Proof.
intros segs ms model ms' model' Hacc.
destruct (mi_account_step_model_frame segs ms model ms' model' Hacc)
as (_ & _ & _ & _ & _ & Hproc & _).
unfold m_halted. rewrite Hproc. reflexivity.
Qed.
Lemma v_addi_0 : ltac2:(TCodec.tc2 tcn__DivergeSim ":'S;yR0%211'=&R<r1z%3221%53613pU071").
Proof.
intro a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma self_jump_step_accesses : ltac2:(TCodec.tc2 tcn__DivergeSim "RG'5'C%211'J'S;yQ0%211y5%411yE%611'B'='8yR0%;11%311&Nr5%211(0%116%:3631%:1A&Gr7&Mr6%211%5241(1%12I=%D3931'3&H%118(4%I3421':'R0%221M%L11&QN%11B(9(QO%12CLr4%449Q521%C291%Q63971&R2%11K(;%Q:3E21&S<%12Q?Oz%Q>3Q?21'I'F%11QJ%311&Q0r<r;%3221(E(L(7&K%211%43R571%62<1%QN3<81p0A1p0F1p0K1p0Q91p0Q?1p0QJ1pVLR61pUFR81pV<R;1pW4R>1pV6RB1pVDRD1").
Proof.
intros segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm.
unfold RiscvSemantics.step_accesses.
rewrite Hfetch.
unfold RiscvSemantics.decode_exec_accesses.
rewrite Hecall. cbv beta iota.
rewrite Hdecode. cbv beta iota.
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses Sem.exec
Sem.rget Sem.rset Sem.with_regs Sem.with_pc
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
rewrite Hx0. cbv beta iota.
rewrite b_addsext, Himm, v_addi_0.
destruct ms; cbn in Hsvc; subst; reflexivity.
Qed.
Lemma self_jump_account_fix : ltac2:(TCodec.tc2 tcn__DivergeSim "RF'5'C%211'J'QC'S;yQ0%211y5%411yE%611'B'='8yR0%;11%311&Nr6%211(0%116%:3631%:1A&Gr8&Mr7%211%5241(1r5%22J1%E3:41'3&H%11B(4%J3421':'R0%221N%M11&QN%11A(9(QO%12M@r4%449Q621%D291%Q73971&R2%11J(;%Q;3E21&S<%12Q@Nz%Q?3Q@21'I%F2QKQJ%211&Q9r=r<r;%43321(E%H4R3R243%2291%QK3941p0=1p0B1p0G1p0Q51p0Q;1p0QG1pVLR31pUFR51pV<R81pW4R;1pV2R?1pV6RA1pVDRC1").
Proof.
intros. eapply mi_account_step_no_access.
eapply self_jump_step_accesses; eassumption.
Qed.
Lemma step_j_self : ltac2:(TCodec.tc2 tcn__DivergeSim "RH'5'C%211&R1y5'S;yR0%211%5241'8y8%611%311p061yQ0%:11%;1<yE%=11'B'=%<16&Gr9r7%3221(1r4%22=1%93841'3&Hr5%211(4%?3521':'R0%221C%N11&QNr6%211(9(QO%12=Br3%44:L21%F2:1%M3:71&R2%11:(;%Q13G21&S<%12Q6>z%Q53Q621'I'J%211&Or>&R;vRIr=r<r;r:%6554321%9281(E%12=3%QE3=31p0A1p0F1p0K1p0Q:1p0QA1pVLQL1pUFQN1pV<R11pW4R31pVBR61pV0R71pV:R>1pV>R>1pVDRE1").
Proof.
intros segs regs pc mem rom w rd imm sz Hf He Hd Hx0 Hi.
unfold RiscvSemantics.step.
rewrite (self_jump_step_accesses segs (mkst regs pc mem rom) w rd imm sz
eq_refl Hf He Hd Hx0 Hi).
reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition silent_loop (P : config -> Prop) : Prop :=
forall c, P c ->
m_halted (cfg_model c) = None /\
ms_svc_pending (cfg_ms c) = None /\
exists ms' model',
mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
P (mkCfg ms' model').
Lemma silent_loop_cycle : ltac2:(TCodec.tc2 tcn__DivergeSim "R0'5'Q6%211&R=r1r2%33521'<'='8'S;yR0%211%411&QK&Q4%11;%311(0%117%<3731&N&Q5%11B%311%A3<16'>'J'QC'I':%1243%311&Q9vS9r4%>11%F12%53421(E(9%14>=Q4Q5%32;1%Q33;51(Q:%12Q8Q9r5%Q<3Q>21%Q9251qV4E1%H2F1qV8H1%J2I1%Q>2L1%Q?2Q21p0QA1pU4QG1&R6r3%QH3QJQG1qU4QK1%411p061pU<QM1").
Proof. intros cs H c. exact (H c). Qed.
Lemma silent_loop_sstep : ltac2:(TCodec.tc2 tcn__DivergeSim "Q7'Q6!p021'5'QE%211'QA&R6r4%211r5%113'Q?vS9r3%342571'<'=(7%11?%33?:1'>(Q2r1%211%83C?1r8%114%<231qU6M1%92N1%?2;1p0A1p0F1p0I1pVNM1pU>O1pU4Q51pT8Q41").
Proof.
intros P c evs to Hloop HP Hstep.
destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
inversion Hstep; subst; try congruence.
repeat match goal with
| H : mi_account_step ?s ?a ?b = MachineOk ?x,
H' : mi_account_step ?s ?a ?b = MachineOk ?y |- _ =>
rewrite H in H'; injection H'; intros; subst; clear H
end.
eauto 7.
Qed.
Lemma star_case : ltac2:(TCodec.tc2 tcn__DivergeSim "Q<'Q6'5'QE%211'Q@vS9r3r2r1%544321'A'<'=(7%11<%33<91r4%53A:1%7231'>'Q?r7(Q2%11@%44C3B1r5%F4ECB1r6&2%13KGE%B3K31%D251%E281qW2N1%?2O1qU:Q31%A2Q41qU>Q21%C2Q31%M2E1p0O1pU6Q91pW0Q71pU4Q;1").
Proof.
intros c tr c' H;
destruct H as [c | c1 evs c2 tr2 c3 Hstep Htail];
[left; auto | right; exists evs, c2, tr2; auto].
Qed.
Lemma silent_loop_star : ltac2:(TCodec.tc2 tcn__DivergeSim "Q0'Q6!p021&R6r1%211'5'QE%211'Q@vS9r3r2%443219r6r4%211'<'=(7%11=%33=61r7%11<%7231p091p0=1pU6K1pW0D1pU4M1p0I1pT8M1").
Proof.
intros P Hloop c tr c' Hstar.
induction Hstar as [c | c evs c2 tr c3 Hstep Hstar IH]; intros HP.
- auto.
- destruct (silent_loop_sstep P c evs _ Hloop HP Hstep)
as (-> & c2' & Heq & HP2).
injection Heq as <-.
destruct (IH HP2) as (-> & HP3). auto.
Qed.
Lemma silent_loop_star_nil : ltac2:(TCodec.tc2 tcn__DivergeSim "J'Q6!p021'5'QE%211&R6r4%211r5%113'Q@vS9r3%342571'=(7%11=%33=91p051p0:1p0=1pU6F1pW0B1pU4H1pT8G1").
Proof.
intros P c tr c' Hloop HP Hstar.
exact (proj1 (silent_loop_star P Hloop c tr c' Hstar HP)).
Qed.
Lemma silent_loop_no_error : ltac2:(TCodec.tc2 tcn__DivergeSim "A'Q6!p021&R6r2%211r3%113&@&Q<vS9%2215%411p061p091pU4?1pT8>1").
Proof.
intros P c Hloop HP (tr & c2 & evs & Hstar & Herr).
destruct (silent_loop_star P Hloop c tr c2 Hstar HP) as (_ & HP2).
destruct (silent_loop_sstep P c2 evs _ Hloop HP2 Herr)
as (_ & c' & Heq & _).
discriminate Heq.
Qed.
Lemma silent_loop_no_unmodeled : ltac2:(TCodec.tc2 tcn__DivergeSim "A'Q6!p021&R6r2%211r3%113&@&Q=vS9%2215%411p061p091pU4?1pT8>1").
Proof.
intros P c Hloop HP.
exact (no_error_no_unmodeled segs c (silent_loop_no_error P c Hloop HP)).
Qed.
Lemma silent_loop_obs_iff : ltac2:(TCodec.tc2 tcn__DivergeSim "K'Q6!p021&R6r2%211r3%113'5'QE%211&?&Q;vS9r4r1%43321'=(7%11:%33:51%:251pW0<1p0@1p0C1pU4I1pT8H1").
Proof.
intros P c Hloop HP tr. split.
- intros (tr' & c2 & Hstar & Hpre).
rewrite (silent_loop_star_nil P c tr' c2 Hloop HP Hstar) in Hpre.
exact (is_prefix_nil_inv tr Hpre).
- intros ->. apply obs_trace_nil.
Qed.
Lemma silent_loop_not_all_errors : ltac2:(TCodec.tc2 tcn__DivergeSim "A'Q6!p021&R6r2%211r3%113&@'Q3vS9%2215%411p061p091pU4?1pT8>1").
Proof.
intros P c Hloop HP Hall. revert HP.
induction Hall as [c Hprog Hnext IH]; intros HP.
destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
apply (IH [] (mkCfg ms' model')); [|exact HP'].
apply sstep_instr; assumption.
Qed.
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
ms_svc_pending ms = None ->
mi_account_step segs ms model = MachineOk (ms, model) ->
to_spin ms model
| ts_step : forall ms model ms' model',
ms_svc_pending ms = None ->
mi_account_step segs ms model = MachineOk (ms', model') ->
to_spin ms' model' ->
to_spin ms model.
Lemma ts_spin_no_access : ltac2:(TCodec.tc2 tcn__DivergeSim "Q5'J'QC'='8'S;yR0%211%411&Nr2%211(0%116%;3631'I'F%11@%311&Q0vS9r3%3221(E(L(7&K%211%43K71%62<1%K3<81'R9r4%221<p041p0E1pV2Q21pV6Q41").
Proof.
intros ms model Hsvc Hstep.
apply ts_spin; [exact Hsvc | exact (mi_account_step_no_access segs ms model ms Hstep)].
Qed.
Lemma ts_step_no_access : ltac2:(TCodec.tc2 tcn__DivergeSim "Q:'J'QC'='8'S;yR0%211%411&Nr3%211(0%116%;3631'I'F%11@%311&Q0vS9r4%3221(E(Lr2(7&K%211%53L41%72=1%L3=91'R9%12G<r6r5%4221p041p071p0I1pV8Q71pV2Q71pV6Q91").
Proof.
intros ms model ms' Hsvc Hstep Hspin.
exact (ts_step ms model ms' model Hsvc
(mi_account_step_no_access segs ms model ms' Hstep) Hspin).
Qed.
Lemma ts_spin_no_lazy : ltac2:(TCodec.tc2 tcn__DivergeSim "Q8'J'QC'='8'S;yR0%211%411&Nr2%211(0%116%;3631'5':%12::%311&QL%11:(7%115%D3531'I%11H&OvS9r4%3221(E%12N3%M3731'R9r5%2217p041p0>1p0H1pV2Q51pV6Q71").
Proof.
intros ms model Hsvc Hlazy Hstep.
apply ts_spin; [exact Hsvc|].
rewrite (mi_account_step_no_lazy segs ms model Hlazy).
rewrite Hstep. reflexivity.
Qed.
Lemma ts_step_no_lazy : ltac2:(TCodec.tc2 tcn__DivergeSim "Q='J'QC'='8'S;yR0%211%411&Nr3%211(0%116%;3631'5':%12::%311&QL%11:(7%115%D3531'I%11H&OvS9r5%3221(E%12NE%M3731'R9r4%2217r7r6%5221p041p081p0B1p0L1pV8Q:1pV2Q:1pV6Q<1").
Proof.
intros ms model ms' Hsvc Hlazy Hstep Hspin.
apply (ts_step ms model ms' model); [exact Hsvc| |exact Hspin].
rewrite (mi_account_step_no_lazy segs ms model Hlazy).
rewrite Hstep. reflexivity.
Qed.
Lemma ts_spin_of_step_j : ltac2:(TCodec.tc2 tcn__DivergeSim "R:'J'QC'S;yQ0%211y5%411yE%611'B'='8yR0%;11%311&Nr6%211(0%116%:3631%:1A&GvS9&Mr7%211%5241(1r5%22J1%E3:41'3&H%11B(4%J3421':'R0%221N%M11&QN%11A(9(QO%12M@r4%449Q621%D291%Q73971&R2%11J(;%Q;3E21&S<%12Q@Nz%Q?3Q@21'R9r<r;%3221p051p0:1p0?1p0M1p0Q31p0Q?1pVLQK1pUFQM1pV<R01pW4R31pV2R71pV6R91").
Proof.
intros. eapply ts_spin_no_access; [assumption|].
eapply self_jump_step_accesses; eassumption.
Qed.
Definition spinning (c : config) : Prop :=
to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.
Lemma spinning_silent_loop : ltac2:(TCodec.tc2 tcn__DivergeSim "3&R6&R8%211").
Proof.
intros [ms model] [Hspin Hh]; cbn in Hspin, Hh; cbn.
revert Hh.
destruct Hspin as [ms model Hsvc Hfix | ms model ms' model' Hsvc Hacc Hspin'];
intros Hh.
- refine (conj Hh (conj Hsvc _)).
exists ms, model. split; [exact Hfix|].
split; cbn; [apply ts_spin; assumption | exact Hh].
- refine (conj Hh (conj Hsvc _)).
exists ms', model'. split; [exact Hacc|].
split; cbn; [exact Hspin'|].
rewrite (mi_account_step_halted segs ms model ms' model' Hacc). exact Hh.
Qed.
Theorem spin_star_nil : ltac2:(TCodec.tc2 tcn__DivergeSim "Q6'J'QC'5'QE%211'Q6'R9r4r3%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531'Q@vS9(Q:r6r5%3221%6451DC(7%11J%D3J51p041p0<1p0H1pU6M1pW0O1pV2Q31pV6Q51").
Proof.
intros ms model tr c' Hspin Hh Hstar.
exact (silent_loop_star_nil spinning (mkCfg ms model) tr c'
spinning_silent_loop (conj Hspin Hh) Hstar).
Qed.
Theorem spin_obs_iff : ltac2:(TCodec.tc2 tcn__DivergeSim "Q5'J'QC'R9r2r1%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531'5'QE%211&?&Q;vS9(Q:r5r4%3221%6351G(7%11;%H3;J1%;241pW0=1p0A1p0M1pV2Q21pV6Q41").
Proof.
intros ms model Hspin Hh.
exact (silent_loop_obs_iff spinning (mkCfg ms model)
spinning_silent_loop (conj Hspin Hh)).
Qed.
Theorem spin_no_error_run : ltac2:(TCodec.tc2 tcn__DivergeSim "N'J'QC'R9r2r1%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531&@&Q<vS9(Q:r4r3%3221%6251%811p0:1p0F1pV2K1pV6M1").
Proof.
intros ms model Hspin Hh.
exact (silent_loop_no_error spinning (mkCfg ms model)
spinning_silent_loop (conj Hspin Hh)).
Qed.
Theorem spin_no_sstep_error : ltac2:(TCodec.tc2 tcn__DivergeSim "Q3'J'QC'R9r2r1%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531'5'QE%211&@'Q?vS9(Q:r5r4%3221(Q1%7462H1%911pU>;1p0?1p0K1pV2Q01pV6Q21").
Proof.
intros ms model Hspin Hh evs Herr.
destruct (silent_loop_sstep spinning (mkCfg ms model) evs SError
spinning_silent_loop (conj Hspin Hh) Herr)
as (_ & c' & Heq & _).
discriminate Heq.
Qed.
Theorem spin_no_unmodeled : ltac2:(TCodec.tc2 tcn__DivergeSim "N'J'QC'R9r2r1%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531&@&Q=vS9(Q:r4r3%3221%6251%811p0:1p0F1pV2K1pV6M1").
Proof.
intros ms model Hspin Hh.
exact (silent_loop_no_unmodeled spinning (mkCfg ms model)
spinning_silent_loop (conj Hspin Hh)).
Qed.
Theorem spin_not_all_errors : ltac2:(TCodec.tc2 tcn__DivergeSim "N'J'QC'R9r2r1%3221'='8'S;yR0%211%411&QK%11:(0%115%:3531&@'Q3vS9(Q:r4r3%3221%6251%811p0:1p0F1pV2K1pV6M1").
Proof.
intros ms model Hspin Hh.
exact (silent_loop_not_all_errors spinning (mkCfg ms model)
spinning_silent_loop (conj Hspin Hh)).
Qed.
Lemma obs_trace_of_star : ltac2:(TCodec.tc2 tcn__DivergeSim "E'Q6'5'QE%211'Q@vS9r4r3r2%544321&Q8%13935&Q;r6%23917p041p071pW0>1pU4B1pU>@1pU8D1").
Proof. intros c0 evs c tr Hstar Hpre. exists evs, c. auto. Qed.
Theorem spin_reach_obs : ltac2:(TCodec.tc2 tcn__DivergeSim "QF'Q6'5'QE%211'J'QC'Q@vS9r4r3(Q:r2r1%3221%847651'R9%1275'='8'S;yR0%211%411&QK%11?(0%115%:3531'<&Q8r7%23MC1&Q;r9%23K1Gp041pW0Q11r6%L281%Q14Q01LK&2%13Q78Q0%I3Q719p041pU6Q<1pW0Q:1%B2:1p0D1p0Q01p0Q31pV2Q=1pV6Q?1pT8QA1pU8QE1").
Proof.
intros c0 P ms model Hstar Hspin Hh. split.
- intros tr Hpre. exact (obs_trace_of_star c0 P _ tr Hstar Hpre).
- intros tr c' Htail.
rewrite (spin_star_nil ms model tr c' Hspin Hh Htail).
apply app_nil_r.
Qed.
Definition is_self_jump (ms : machine_state) : bool :=
match ms_svc_pending ms with
| Some _ => false
| None =>
match fetch_word segs (ms_pc ms) with
| Some w =>
if is_ecall w then false else
match decode_any w with
| Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
| _ => false
end
| None => false
end
end.
Lemma is_self_jump_to_spin : ltac2:(TCodec.tc2 tcn__DivergeSim "?'J'QC'='3&R5r2%211(;%63521'R9r3%2216p041pV2<1pV6>1").
Proof.
intros ms model H. unfold is_self_jump in H.
destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:Hfetch; [|discriminate].
destruct (is_ecall w) eqn:Hecall; [discriminate|].
destruct (decode_any w) as [[i sz]|] eqn:Hdecode; [|discriminate].
destruct i; try discriminate.
apply andb_prop in H as [Hx0 Himm].
apply Z.eqb_eq in Himm.
eapply ts_spin_of_step_j; eassumption.
Qed.
Fixpoint spin_c (fuel : nat) (ms : machine_state) (model : Model) : bool :=
match fuel with
| O => false
| S fuel' =>
if is_self_jump ms then true
else
match ms_svc_pending ms with
| Some _ => false
| None =>
match mi_account_step segs ms model with
| MachineOk (ms', model') => spin_c fuel' ms' model'
| _ => false
end
end
end.
Lemma spin_c_to_spin : ltac2:(TCodec.tc2 tcn__DivergeSim "B'6'J'QC'='3&R7r3r2r1%43321(;%83721'R9%1276p031pV2=1pV6?1pUBA1").
Proof.
induction fuel as [|fuel IH]; intros ms model H; cbn in H;
[discriminate|].
destruct (is_self_jump ms) eqn:Hj;
[exact (is_self_jump_to_spin ms model Hj)|].
destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hacc;
try discriminate.
exact (ts_step ms model ms' model' Hsvc Hacc (IH ms' model' H)).
Qed.
End WithSegs.
End WithFP1.
Ltac prove_to_spin fuel :=
apply (spin_c_to_spin _ fuel);
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Section WithFP2.
Context {fx : FPState}.
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.
Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
(evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.
Theorem spin_branch_toy_obs_iff : ltac2:(TCodec.tc2 tcn__DivergeSim "A'5'QE%211&?&Q;vS9vRCr1%43321&Q8&2vRGvR>%33<21%53=71%<271pW0>1").
Proof.
intro tr. split.
- intros (tr' & cend & Hstar & Hpre).
destruct (star_case segs c0 tr' cend Hstar)
as [[-> _] | (evs & c2 & tr2 & Hstep & Htail & ->)].
+ apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
+ destruct (Hsplit evs _ Hstep) as [[-> Heq] | [-> Heq]];
injection Heq as ->.
*
assert (Hobs2 : obs_trace segs c_g tr2)
by (exists tr2, cend; split; [exact Htail | apply is_prefix_refl]).
apply Hg_obs in Hobs2.
eapply is_prefix_trans; [exact Hpre|].
apply is_prefix_app_mono. exact Hobs2.
*
rewrite (silent_loop_star_nil segs P c_r tr2 cend Hloop HP_r Htail)
in Hpre.
apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
- intro Hpre.
destruct (proj2 (Hg_obs T) (is_prefix_refl T))
as (tr'' & cend & Hstar & HpreT).
exists (evs_g ++ tr''), cend. split.
+ exact (star_step segs c0 evs_g c_g tr'' cend Hstep_g Hstar).
+ eapply is_prefix_trans; [exact Hpre|].
apply is_prefix_app_mono. exact HpreT.
Qed.
Theorem spin_branch_toy_no_error : ltac2:(TCodec.tc2 tcn__DivergeSim "6&@&Q<vS9vRC%3221%511").
Proof.
intros (tr & cerr & evs & Hstar & Herr).
destruct (star_case segs c0 tr cerr Hstar)
as [[_ ->] | (evs1 & c2 & tr2 & Hstep & Htail & _)].
- destruct (Hsplit evs SError Herr) as [[_ Heq] | [_ Heq]]; discriminate.
- destruct (Hsplit evs1 _ Hstep) as [[_ Heq] | [_ Heq]];
injection Heq as ->.
+ apply Hg_noerr. exists tr2, cerr, evs. auto.
+ apply (silent_loop_no_error segs P c_r Hloop HP_r).
exists tr2, cerr, evs. auto.
Qed.
End TwoBranchToy.
End WithFP2.
Module SelfJumpImage.
Definition spin_seg : Segment := {|
seg_base := 0x10000;
seg_size := 4;
seg_perms := "r-x"%string;
seg_bytes := ["6f000000"%pstring]
|}.
Definition spin_segs : list Segment := [spin_seg].
Definition spin_img : Image :=
mkImage spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6).
Example j_dot_decodes :
decode_any (Z_to_bv 32 0x6f) = Some (Jal 0 (Z_to_bv 21 0), 4%Z).
Proof. div_vm_refl. Qed.
Lemma spin_img_to_spin : ltac2:(TCodec.tc2 tcn__DivergeSim "Q9'S;yR0%211'QB'B'QD'R:&R4&Q7yRPP0(DyRPR0yQHy6%43321r6r3&QFr1%211&QG%113&QI%115&QH%117%B9CA<;:7531&QJ&Q>%11Fr5r4r2%66432B1?%L3K81pUHN1pUJQ01pV@Q21pUNQ41pU2Q51pVFQ61").
Proof.
intros sp brk0 mbase rnd lim inp.
eapply ts_spin_of_step_j with (w := Z_to_bv 32 0x6f).
- reflexivity.
- div_vm_refl.
- div_vm_refl.
- apply j_dot_decodes.
- div_vm_refl.
- div_vm_refl.
Qed.
Example spin_img_obs_iff : forall lim en inp tr,
bh_traces (run spin_img lim en inp) tr <-> tr = [].
Proof.
intros lim [sp brk0 mbase rnd] inp tr.
cbn [run bh_traces spin_img]. unfold init_config.
apply spin_obs_iff.
- apply spin_img_to_spin.
- reflexivity.
Qed.
Example spin_img_no_error : forall lim en inp,
~ bh_errors (run spin_img lim en inp).
Proof.
intros lim [sp brk0 mbase rnd] inp.
cbn [run bh_errors spin_img]. unfold init_config.
apply spin_no_error_run.
- apply spin_img_to_spin.
- reflexivity.
Qed.
Example spin_img_not_all_errors : forall lim en inp,
~ bh_all_errors (run spin_img lim en inp).
Proof.
intros lim [sp brk0 mbase rnd] inp.
cbn [run bh_all_errors spin_img]. unfold init_config.
apply spin_not_all_errors.
- apply spin_img_to_spin.
- reflexivity.
Qed.
Example spin_img_to_spin_by_execution :
to_spin spin_segs
(init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6)
(Z_to_bv 64 65536) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))
[[]] [] (Z_to_bv 64 1000) hwcap_rv64gc)
(init_model (segments_reserved spin_segs) (Z_to_bv 64 1048576)
(Z_to_bv 64 0x7fff7f800000) (Z_to_bv 64 65536) 0x40000000%Z
(mkProcInput [[]] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48)).
Proof. prove_to_spin 1%nat. Qed.
End SelfJumpImage.
