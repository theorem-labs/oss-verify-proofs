(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ExitSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.MustExit."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim.WithSegs."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1orb"; "1prod"; "1true"; "2I"]; ["2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3le"; "3lt"; "4N"; "4Z"; "0F"; "0FA"; "0FR"; "5equiv"; "5modeled"; "6must_exit_with"]; ["7omni_strong_equiv"; "8nat_to_word"; "8word_le8"; "9PhdrInfo"; "9Segment"; "9mkImage"; ":Ok"; ":Unmodeled"; ":outcome"; ";exec"; ";exits_with"; ";omni_run"; "<Build_machine_state"; "<MachineOk"; "<fetch_word"; "<machine_result"]; ["<machine_state"; "<ms_fcsr"; "<ms_fregs"; "<ms_gpr"; "<ms_mem"; "<ms_pc"; "<ms_pc_val"; "<ms_reg"; "<ms_regs"; "<ms_resv"; "<ms_rom"; "<ms_svc_pending"; "<step"; "=SError"; "=SNext"; "=cfg_model"]; ["=config"; "=init_config"; "=init_machine_state"; "=is_prefix"; "=mkCfg"; "=mkEntry"; "=obs_trace"; "=reaches_error"; "=run"; "=sstep"; "=star"; "=step_to"; "=sys_input"; ">syscall_spec"; "?EntryDraw"; "?build_stack_bytes"]; ["?stack_to_mem"; "@ExitEv"; "@MemCopy"; "@Model"; "@ProcInput"; "@SyscallEffect"; "@SyscallInput"; "@event"; "@in_arg"; "@in_argv"; "@in_envp"; "@in_fs"; "@in_hwcap"; "@in_sysno"; "@in_uid"; "@m_fs"]; ["@m_halted"; "@m_vm_lazy"; "@mkEffectU"; "@with_halted"; "Aexit_spec"; "Bbv_eqb"; "Dexit_post"; "Don_path"; "Dsim_c"; "Dto_exit"; "Cenum_state"; "Cexit_post"; "Cis_exit_no"; "Coverlay_argc_bytes"; "Csim_c"; "Enth_error"]; ["Fadd"; "Feqb"; "Fof_nat"; "0abrk"; "0addr"; "0alim"; "0amb"; "0apc"; "0aph"; "0argv"; "0arnd"; "0asp"; "0brk0"; "0bytes"; "0c"; "0c'"]; ["0code"; "0code'"; "0eff"; "0envp"; "0evs"; "0fuel"; "0hw"; "0i"; "0init_pc"; "0init_rnd"; "0init_sp"; "0inp"; "0lim"; "0m"; "0m'"; "0mb"]; ["0model"; "0ms"; "0ms'"; "0o"; "0pc"; "0ph"; "0rbrk"; "0rest"; "0rlim"; "0rmb"; "0rnd"; "0rpc"; "0rph"; "0rrnd"; "0rsp"; "0segs"]; ["0source_segs"; "0sp"; "0st"; "GBV"; "GZ_to_bv"; "Gbv"; "Gbv_and"; "Gbv_unsigned"; "0target_segs"; "0tr"; "0uid"; "0v"; "0x8"]]).
Definition is_exit_no (no : word) : Prop :=
bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.
Lemma syscall_spec_exit : ltac2:(TCodec.tc2 tcn__ExitSim "I'RF'RC'Q8'RE%211&S<&RMr3%211%411&C&R=r4r2%33271&S4&RH(1%2261%4417<6%:261p0<1pY8B1pXLF1pX@H1").
Proof.
intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.
Lemma exit_dispatch_ok : ltac2:(TCodec.tc2 tcn__ExitSim "QB'RF'RC&S<&RMr2%211%411&R=r3(Q6'RE(S2&U4yR0z%3221(:'='U5%116'8y8%411%311%7251%911%9277%;11'RB%=11'9%>2<1%@11%F6B86641&S3&U6&RH(1%22N1+WO%L2K1%63L31%821Q6'RG%L11%Q44Q3<31%Q73Q6Q:1p0Q91pXLQ?1pX@QA1").
Proof.
intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
[], []. repeat split; reflexivity.
Qed.
Lemma exit_dispatch_ok_inv : ltac2:(TCodec.tc2 tcn__ExitSim "R2'RF'RC'RE'8'RG%211&S<&RMr5%211%411&R=r6(Q6r4r3r2%44?321%736:1'@'A(S2&U4yR0z%3221(:'='U5%116y8%311%M11%6241%811%8266%:11'RB%<11'9%=2;1%?11%E6A86641%G3Q9Q31&S3&U6&RHr7(1%3221+WO%M2L1%73M31%921Q9%Q23QEQ81%M1QC%Q43QCQ91%Q6231%Q72?1p0Q91p0QB1pX:QH1pXNQM1pX6QM1pXLQO1pX@R11").
Proof.
intros i m eff m' evs Hno Hspec.
apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.
Lemma exit_dispatch_no_unmodeled : ltac2:(TCodec.tc2 tcn__ExitSim "B'RF'RC&S<&RMr2%211%411&D&R=r3(Q7'RE%211%53491%711p091pXL?1pX@A1").
Proof.
intros i m Hno Hspec.
apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
sys_destruct.
Qed.
Lemma in_arg0_sys_input : ltac2:(TCodec.tc2 tcn__ExitSim "F'8'Q4%211'Q@'U5yR0%211'A&RH&R<r3r2r1%43321(1%7221&QC%1263%;3<31pZJ=1pY4A1pZ0C1").
Proof. reflexivity. Qed.
Lemma in_sysno_sys_input : ltac2:(TCodec.tc2 tcn__ExitSim "C'8'Q4%211'Q@'U5yR0%211'A&RM&R<r3r2r1%43321%611%83913pZJ:1pY4>1pZ0@1").
Proof. reflexivity. Qed.
Section WithSegs.
Variable segs : list Segment.
Variable code : word.
Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
ms_gpr ms 0 = code ->
to_exit ms
| te_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_exit ms' ->
to_exit ms.
Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
match fuel with
| O => false
| S fuel' =>
match ms_svc_pending ms with
| Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
&& bv_eqb (ms_gpr ms 0) code
| None =>
match RiscvSemantics.step segs ms with
| MachineOk ms' => sim_c fuel' ms'
| MachineFault | MachineUnmodeled => false
end
end
end.
Lemma sim_c_to_exit : ltac2:(TCodec.tc2 tcn__ExitSim "?'9'Q@'A'5&S8r2r1%3221(>%73621'S9%116p031pY4<1pX<>1").
Proof.
induction fuel as [|fuel IH]; intros ms H; [discriminate|].
cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
- apply andb_true_iff in H as [Hx8 Hgpr].
apply bv_eqb_eq in Hgpr.
eapply te_here; eauto.
apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
[left|right]; exact H.
- destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
[|discriminate|discriminate].
eapply te_step; eauto.
Qed.
Lemma sim_step : ltac2:(TCodec.tc2 tcn__ExitSim "Q8'9'Q@'A';'U5yR0%211%411&QKr2%211(0%116%;3631'Q?%11>&QLvTOr3%3221(Q=%12D<%D3731'5&S8r5%2218(>%J3521(2r6%211%8217%O3:16p061p0=1p0G1pY6Q41pY4Q51pX<Q71").
Proof.
intros fuel ms ms' Hsvc Hstep Hrec.
cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.
Lemma sim_c_exit_now : ltac2:(TCodec.tc2 tcn__ExitSim "Q@'9'Q@'U5yR0%211'A';%113&QKr2%211(3r1%2291%93741'5&<&SA&U7%12@:+RM%4221+RN%6241%8231(>%E3;21&S5&QCr4(1%3221vT0%63N21%M3C19&S8(2r6%211r5%5221%Q43J1@p081p0A1p0N1pZJQ91pY4Q=1pX<Q?1").
Proof.
intros fuel ms x8 Hsvc Hx8 Hcode.
cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.
Lemma sim_ecall_exit : ltac2:(TCodec.tc2 tcn__ExitSim "R6'9'Q@'A';'U5yR0%211%411&QKr1%211(0%116%;3631yQ0%;11%=11&Q>vTO&QEr2%211%5241(3(U3+SC(?%33=21%52=1%K3=71'5&<&SA&U7&QGr3y5+A%>321<%5241%72Q31+RM%:221+RN%<241%>231(>%Q=3A21&S5&QCr4(1%3221vT0%63QA21%QE3I19&S8(2r6%211%311r5%6221%QM3Q11Ap091p0B1p0Q51p0QF1pY4R31pX<R51").
Proof.
intros fuel ms Hsvc Hfetch Hcheck Hcode.
set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
apply (sim_step (S fuel) ms ms1 Hsvc).
- change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
- apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
+ subst ms1. reflexivity.
+ exact Hcheck.
+ exact Hcode.
Qed.
Lemma sstep_instr_inv : ltac2:(TCodec.tc2 tcn__ExitSim "QK'Q@'RC'8'RG%211'R;'A'='U5yR0%211%4211%:11&S1r4%211(:%116%<3631';%11:&QKr6%211(0%11?%D3631'Q?%11L&QLvTOr7%3221(Q=r5%22Q31%N3841'R9(R4r8%2219%44;17K'@%K1Q8%Q63Q8F1(QN%82?7%211%Q:3Q;>1%7251p091p0?1p0J1p0Q31pZ6QA1pX:QC1pY6QH1pY2QH1pY4QJ1").
Proof.
intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
inversion Hss; subst.
-
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; inversion H; subst end.
split; reflexivity.
-
match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-
match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
- congruence.
- congruence.
- congruence.
- congruence.
- congruence.
Qed.
Lemma sstep_exit_inv : ltac2:(TCodec.tc2 tcn__ExitSim "R5'Q@'RC'U5yR0%211'8'RG%211'R;'A';%117&S0r4%211(0%11<%83631&QKr6%211(3%12B9%>3<31&S<r5%211'R9vTO(R4r8r7%3221%64518D'@(6(RA&U6&QCr9(1%3221&U4+WO%22Q91%83Q:41&RO%11A%<231(:%11Q<%@3Q=31%Q;3Q=Q11(QN&S3%12:I%K2A1%411%QA3QBQ11%I271p0K1p0Q31p0Q71p0Q>1pZ6QH1pX:QJ1pZJQN1pY2R21pY4R41").
Proof.
intros ms model x8 evs st Hh Hsvc Hx8 Hss.
inversion Hss; subst; try congruence.
-
autorewrite with model in *.
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
H2 : ms_svc_pending ms = Some ?x,
H6 : m_halted ?model' = None |- _ =>
assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
destruct H3 as (_ & Hm & _); rewrite Hm in H6;
autorewrite with model in H6; discriminate
end.
-
autorewrite with model in *.
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
H2 : ms_svc_pending ms = Some ?x,
H6 : m_halted ?model' = None |- _ =>
assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
destruct H3 as (_ & Hm & _); rewrite Hm in H6;
autorewrite with model in H6; discriminate
end.
-
autorewrite with model in *.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
H2 : ms_svc_pending ms = Some ?x,
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
destruct H3 as (Heff & Hm & Hevs);
rewrite in_arg0_sys_input in Hm;
subst evs0 model';
assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
by (autorewrite with model in H6; congruence);
subst code
end.
cbn. split; reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
H2 : ms_svc_pending ms = Some ?x,
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
destruct H3 as (_ & Hm & _); rewrite Hm in H6;
autorewrite with model in H6; discriminate
end.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
H2 : ms_svc_pending ms = Some ?x |- _ =>
eapply exit_dispatch_no_unmodeled; [| exact H3];
rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
end.
Qed.
Lemma star_halted_nil : ltac2:(TCodec.tc2 tcn__ExitSim "Q5'R0'8'RG%211&D'A';'U5yR0%211%411&S0&QOr3%211%411(0%118%=3831%?11'R:vTOr4r2%4432;1'@(:%11I%G3I61r5%I3NA1%6231p081p0>1pX0Q21pZDQ01pWNQ41").
Proof.
intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
- split; reflexivity.
- exfalso. destruct c as [ms model]. cbn in Hh.
inversion Hss; subst; cbn in Hh; congruence.
Qed.
Definition exit_post (fs : Fs.Fs) : post :=
fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
/\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.
Lemma to_exit_exec : ltac2:(TCodec.tc2 tcn__ExitSim "Q:'Q@'RC'A';'U5yR0%211%411&S0r1%211(0%116%;3631'8'=%12::%311&S1r2%211(:%116%E3631'S9r4%211'Q9vTO(R4r5%2216&S6&RO%119%311%93851p0;1p0?1p0J1pY2Q71pY4Q91").
Proof.
intros ms model Hh Hlazy Hte.
induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_exit_star_only : ltac2:(TCodec.tc2 tcn__ExitSim "QO'Q@'RC'A';'U5yR0%211%411&S0r1%211(0%116%;3631'8'=%12::%311&S1r2%211(:%116%E3631'S9r4%211'RG%>11'R0'R:vTO(R4r7r6%3221%6451AK'Er3%B1<%Q63<21(6(RA&U6vT0&U4+WO%22Q:1%53Q;41&RO%11A%9231%;3I1=%QC3I?1%A2>1p0C1pWNK1pZDM1p0Q01p0Q41p0Q?1pY2QL1pY4QN1").
Proof.
intros ms model Hh Hlazy Hte tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
as (tr' & o & _ & HQ).
unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.
Lemma to_exit_star_admits : ltac2:(TCodec.tc2 tcn__ExitSim "QI'Q@'RC'A';'U5yR0%211%411&S0r1%211(0%116%;3631'8'=%12::%311&S1r2%211(:%116%E3631'S9r4%211'B'R0'R:vTO(R4r6r5%3221(6'RG(RA&U6vT0&U4+WO%22Q51%53Q641&RO%11<%9231%J1;%=3<21%D4C?1Q8qWNF1%H2G1p0J1p0N1p0Q91pY2QF1pY4QH1").
Proof.
intros ms model Hh Hlazy Hte.
destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Definition on_path (c : config) : Prop :=
(m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
to_exit (cfg_ms c))
\/ m_halted (cfg_model c) <> None.
Lemma on_path_step : ltac2:(TCodec.tc2 tcn__ExitSim "C'R0'8'RG%211&S7r3%211'R9vTOr4(QNr2%211%645481p018p091pX0@1pX:>1pWNB1").
Proof.
intros [ms model] evs [ms' model'] Hop Hss.
unfold on_path in *; cbn in Hop |- *.
destruct Hop as [[Hh [Hlazy Hte]] | Hh].
- destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
+
destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
Hh Hsvc Hx8 Hss) as [_ Hc'].
inversion Hc'; subst. right. cbn. discriminate.
+
destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
Hlazy Hsvc Hstep Hss) as [_ Hc'].
inversion Hc'; subst. left. repeat split; assumption.
-
exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma on_path_no_error : ltac2:(TCodec.tc2 tcn__ExitSim "A'R0'8'RG%211&S7r2%211&D'R9vTOr3(QM%443271%611p081pX:<1pWN@1").
Proof.
intros [ms model] evs Hop Hss.
unfold on_path in *; cbn in Hop.
destruct Hop as [[Hh [Hlazy Hte]] | Hh].
- destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
+ destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
discriminate.
+ destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
discriminate.
- inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma star_on_path : ltac2:(TCodec.tc2 tcn__ExitSim "A'R0'8'RG%211&S7r3%211'R:vTOr4r2%443261p016p071pX0>1pZD<1pWN@1").
Proof. exact (star_inv segs on_path on_path_step). Qed.
Lemma to_exit_no_error : ltac2:(TCodec.tc2 tcn__ExitSim "Q8'Q@'RC'A';'U5yR0%211%411&S0r1%211(0%116%;3631'8'=%12::%311&S1r2%211(:%116%E3631'S9r4%211&D&R7vTO(R4r5%2217%5241%711p091p0=1p0H1pY2Q51pY4Q71").
Proof.
intros ms model Hh Hlazy Hte. apply exec_no_error.
eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
End WithSegs.
Definition overlay_argc_bytes (sp : word) (argc : nat)
(base_mem : word -> option byte) : word -> option byte :=
let bytes := word_le8 (nat_to_word argc) in
fun addr =>
if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
else base_mem addr.
Lemma stm_at : ltac2:(TCodec.tc2 tcn__ExitSim "Q9'U5yR0%211'8y8%511%311'9&Gr1&7r3%2271%5241'A'I&U7%12@6&S@r5%42C1&SBr2%211%6241%;3:81';%11F&R@r6r4%332<1&S?%13L>F%D3731p0:1p0G1pX@N1pW:Q41pWLQ11pZ4Q61").
Proof. intros sp bytes addr i.
intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
2: { apply Z.leb_gt in E1; lia. }
replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
- rewrite Nat2Z.id. reflexivity.
- apply Z.ltb_ge in E2. lia.
Qed.
Lemma build_stack_starts_with_argc : ltac2:(TCodec.tc2 tcn__ExitSim "Q8'Q3'U5yR0%211'8y8%511%311%411'R>'B'A&R?r8r7r6r5r4r3r2%877654321&4&Q2&Q1&7%12B:%311%511r1%83G21%C3G:1qY@H1%F2I1pYFH1pX>O1pZFQ01pX8L1pWDM1pZ4Q31pY<Q71").
Proof.
intros ph sp argv envp uid hw rnd. unfold build_stack_bytes, len_word, nat_to_word.
destruct (string_addrs _ argv) as [? ?]. destruct (string_addrs _ envp) as [? ?].
eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.
Lemma word_le8_length : ltac2:(TCodec.tc2 tcn__ExitSim "?'U5yR0%211'A'9&7y8%711&Q2r1%211%6241u8%:3921pZH<1").
Proof. intro v. reflexivity. Qed.
Lemma build_stack_min_length : ltac2:(TCodec.tc2 tcn__ExitSim "O'Q3'U5yR0%211'8y8%511%311%411'R>'Fu8&7&R?r7r6r5r4r3r2r1%877654321%:2@1%=2<1pYF?1pX>F1pZFG1pX8C1pWDD1pZ4J1pY<N1").
Proof.
intros ph sp argv envp uid hw rnd.
destruct (build_stack_starts_with_argc ph sp argv envp uid hw rnd) as [rest Hr].
rewrite Hr, length_app, word_le8_length. lia.
Qed.
Lemma init_first8 : ltac2:(TCodec.tc2 tcn__ExitSim "R2'8'Q4%211'H'Q3'U5yR0%211'R>y8%511%;11%<11'9&Gr3u8%3221'A'I&U7r5%22@1&S@r9%52C1&SBr4%211%6241%<3;81';%11F&QD&R2r=r<r;r:r8r7%796543A21>Jr6%:221&S?&Q2&Q1&7%12Q59%311%511%73Q91N%Q23D91p0G1p0Q51pX>Q@1pZFQA1pX@Q<1pW:QC1pX8Q?1pWDQ@1pXDQE1pXFQG1pY<QK1pXBQM1pZ0QO1").
Proof.
intros segs init_pc ph init_sp init_rnd argv envp addr i uid hw Hi Haddr.
assert (Hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
= nth_error (word_le8 (nat_to_word (length argv))) i).
{ rewrite stack_to_mem_image_in_block
by (pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd);
unfold entry_block_top; lia).
rewrite (stm_at init_sp _ addr i);
[ | pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd); lia
| exact Haddr ].
destruct (build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd) as [rest Hr].
rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
change (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr)
with (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
| Some b => Some b
| None =>
if andb (Z.leb (bv_unsigned init_sp - stack_max_size)
(bv_unsigned addr))
(Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
then Some (Z_to_bv 8 0) else None
end).
rewrite Hstk.
destruct (nth_error (word_le8 (nat_to_word (length argv))) i) eqn:E; [reflexivity|].
apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.
Lemma actual_mem_is_overlay : ltac2:(TCodec.tc2 tcn__ExitSim "Q<'8'Q4%211'H'Q3'U5yR0%211'R>y8%511%;11%<11'A';%115p091&QD&R2r9r8r7r6r5r4r3r2r1%:9987654321%<11&S=&7%12E8%33;14%E3B51pX>L1pZFM1pX8I1pWDJ1pXDO1pXFQ11pY<Q51pXBQ71pZ0Q91").
Proof.
intros segs init_pc ph init_sp init_rnd argv envp uid hw.
apply functional_extensionality. intro addr.
unfold overlay_argc_bytes.
destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
[ apply Z.eqb_eq in E0;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
[ apply Z.eqb_eq in E1;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
[ apply Z.eqb_eq in E2;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
[ apply Z.eqb_eq in E3;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
[ apply Z.eqb_eq in E4;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
[ apply Z.eqb_eq in E5;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
[ apply Z.eqb_eq in E6;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
[ apply Z.eqb_eq in E7;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw); lia | ].
reflexivity.
Qed.
Lemma machine_state_eta : ltac2:(TCodec.tc2 tcn__ExitSim "G'Q@'Ar1(Q<&QH%113&QB%115&QF%117&QK%119&QI%11;&QA%11=&QD%11?&QJ%11A%A8?=;97531%D3EC1pY4F1").
Proof. intros []; reflexivity. Qed.
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
(init_sp : word) (init_rnd : EntryDraw) (argc : nat)
(base : word -> option byte) (uid : word)
(hw : word) : machine_state :=
{| ms_regs := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_pc_val := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_resv := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
ms_mem := overlay_argc_bytes init_sp argc base;
ms_rom := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.
Lemma init_eq_enum_state : ltac2:(TCodec.tc2 tcn__ExitSim "Q:'8'Q4%211'H'Q3'U5yR0%211'R>y8%511%;11%<11'A'Q@&R2r9r8r7r6r5r4r3r2r1%:9987654321&S:&7%12A7&QD%115%59?>=<;3187%C3B71pX>J1pZFK1pX8G1pWDH1pXDM1pXFO1pY<Q31pXBQ51pZ0Q71").
Proof.
intros segs init_pc ph init_sp init_rnd argv envp uid hw. unfold enum_state.
rewrite (machine_state_eta (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) at 1.
f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.
Lemma exit_omni_run : ltac2:(TCodec.tc2 tcn__ExitSim "QN'8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>r;r3r1&R2r:r9r8r5&RIr2%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21&Q;(Q5r<%231HD(R5r7r6%34GF21&S;r4&RK%11O%4231%=5:K6Q11p0?1pQFQ81pXHQ:1pX2Q>1pXJQ=1pYFQ?1pY0QA1pWJQB1pZ4QC1pY<QG1pY:QI1pZ0QK1").
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
cbn [omni_run]. unfold init_config.
exact (to_exit_exec segs code
(init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl (sim_c_to_exit segs code F _ Hsim)).
Qed.
Lemma exit_obs_iff : ltac2:(TCodec.tc2 tcn__ExitSim "R='8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>r;r3r1&R2r:r9r8r5&RIr2%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21'RG%Q511&C&R6r=&R1r<r7r6r4%5964OKJI321%8371N&R3(6(RA&U6&U4+WO%22Q@1%43QAQ11&RK%11<%8231(:%11H%<3I31%>3JQ=1%I2@1pZDK1p0N1pQFQG1pXHQI1pX2QM1pXJQL1pYFQN1pY0R01pWJR11pZ4R21pY<R61pY:R81pZ0R:1").
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
apply exec_obs_iff.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.
Lemma exit_no_error_run : ltac2:(TCodec.tc2 tcn__ExitSim "QI'8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>r;r3r1&R2r:r9r8r5&RIr2%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21&D&R7r<&R1r7r6%394KGFE21DJ%6251%811p0:1pQFQ31pXHQ51pX2Q91pXJQ81pYFQ:1pY0Q<1pWJQ=1pZ4Q>1pY<QB1pY:QD1pZ0QF1").
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma exit_must_exit_with : ltac2:(TCodec.tc2 tcn__ExitSim "QO'8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>r;r3r1&R2r:r9r8r5&RIr2%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21&O&U6r4&U4+WO%22Q31%53Q441(Q5r<%231NJ(R5r7r6%34ML21%>585L1Q2p0@1pQFQ91pXHQ;1pX2Q?1pXJQ>1pYFQ@1pY0QB1pWJQC1pZ4QD1pY<QH1pY:QJ1pZ0QL1").
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr o (_ & Hx). exact Hx.
Qed.
Lemma exit_omni_run_code_unique : ltac2:(TCodec.tc2 tcn__ExitSim "R3'8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>r<r4r2&R2r;r:r9r6&RIr3%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21&Q;(Q5r=%231HD(R5r8r7%34GF21&Q:%11L%:57H3N1&U6&U4+WO%22Q<1%43Q=M1%Q83Q=L1p071p0C1pX4Q@1pQFQ=1pXHQ?1pX2QC1pXJQB1pYFQD1pY0QF1pWJQG1pZ4QH1pY<QL1pY:QN1pZ0R01").
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
cbn [omni_run] in Hrun, Hex.
destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.
Lemma exit_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__ExitSim "RA'8'Q4%211'H'Q3'U5yR0%211'R>'RD'9'A'5&S>rBr4r2&R2rAr@r?r<&RIr3%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21r5r;r:r9r6%B1I%@1J%?1K%>1L%K9G87654321%Q04H:M1%Q33Q21=&Q0(Q5rDrC%3321Q5r=%531Q0A(R5r>%24Q6Q5Q41r8r7%54FE21%=59741Ip0?1p0L1pQHQE1pQJQF1pXHQH1pX2QK1pWFQK1pW>QM1pW8QN1pWHQO1pWBR31pW@R51pZBR71pYLR21pYDR41pY>R51pYNR61pYJR:1pYHR<1pZ2R>1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.
Lemma exit_strong_equiv : ltac2:(TCodec.tc2 tcn__ExitSim "RL'8'Q4%211'H'Q3'U5yR0%211'R>'I'RD'9'A'5&S>rDr4r2&R2rCrBrAr>&RIr3%211&RJ%113&RN%115&RL%117%>9A=<;:7531%C4BA@1(>%G3F21r=r5r<r;r:r7%C1J%A1K%@1L%?1M%L9:87654321%Q14;:N1%Q43Q31>'@&N&R8(Q5rFrE%3321Q8r?(R5r@%24Q8Q7Q61%94541G%;11&M%;3Q9KIr9r8%94KJ21%@44J1N%6281%D281p0F1p0Q41pQHQM1pQJQN1pXHR01pX2R41pW<R31pWFR51pW>R71pW8R81pWHR91pWBR=1pW@R?1pZBRA1pYBR;1pYLR=1pYDR?1pY>R@1pYNRA1pYJRE1pYHRG1pZ2RI1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
right. split.
- intro tr. cbn.
rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
reflexivity.
- cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
