(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Scfg KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesLibEK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Specif."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.KitNodesS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "0C"; "1None"; "1O"; "1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["1unit"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3proj1_sig"; "3sig"; "4Z"; "0E"; "0FS0"; "0FULL"; "0K"; "0KA"]; ["0KB"; "0LIMIT"; "5check_syscall"; "6CheckOk"; "6CheckUnmodeled"; "6check_result"; "7Segment"; "8MachineOk"; "8access_report"; "8fetch_word"; "8is_ecall"; "8machine_result"; "8machine_state"; "8memory_access"; "8mkAccessReport"; "8ms_gpr"]; ["8ms_svc_pending"; "8step_accesses"; "9SNext"; "9advance_past_svc"; "9apply_effect"; "9config"; "9mkCfg"; "9spurious_refusal_cfg"; "9sstep_cfg"; "9sys_input"; ":MemCopy"; ":Model"; ":SyscallEffect"; ":TASK_SIZE"; ":VmMaps"; ":event"]; [":m_fs"; ":m_halted"; ":m_tid"; ":m_vmmaps"; ":map_has"; ":mkEffectU"; ":mkVmMapsFull"; ":page_round_up_Z"; ":page_size"; ":syscall_effect_accesses"; ":vm_add_lazy"; ":vm_brk"; ":vm_init_sp"; ":vm_limit"; ":vm_maps"; ":vm_mmap_base"]; [":vm_noaccess"; ":vm_reserved"; ":vm_start_brk"; ":with_tid"; ":with_vm_backing"; ":with_vmmaps"; ";PID_MAX_ENVELOPE"; "<brk_grow_ok"; "<brk_unmaps"; "<brk_zeros"; "<forget_vm_ranges"; "<mmap_fixed_noaccess_b"; "<mmap_fixed_rw_b"; "<mmap_flags_core"; "<mmap_modeled_b"; "<mmap_noaccess_b"]; ["<with_mmap_backing"; "<with_mmap_destroyed"; "<with_mmap_replacement"; "=bvmap"; "0R"; ">epend"; "?brk_model"; "@ENOMEM_RET"; "@acs"; "@is_ecall_at"; "@nxt"; "@pc"; "@refuse"; "Acs_ok"; "Benv"; "Btwo64"]; ["Calloc_enomem_sysno_b"; "Dmunmap_model"; "Dunfill"; "Dzfill"; "Egetr"; "Emkst"; "Eregupd"; "Ev_addi"; "FT1"; "FT2"; "FT3"; "Fbrk_adm"; "Ft_alt3"; "Fthree"; "Ftid_I"; "GTSet"]; ["Gnode_ok"; "Grealizes"; "Gt_exit"; "Hsrealizes"; "0SEGS"; "0SINV"; "Iadd"; "Iland"; "Ile"; "Ilt"; "Imodulo"; "Ipow"; "0T"; "0a"; "0argH"; "0b"]; ["0c"; "0c0"; "0code"; "0cs"; "0d"; "0eff"; "0eff0"; "0evs"; "0evs0"; "0flags"; "0fxg"; "0h"; "0i"; "0l"; "0len"; "0m"]; ["0m'"; "0m0"; "0mem"; "0model"; "0ms"; "0ms'"; "0n"; "0nx"; "0p"; "0pc"; "0prot"; "0r"; "0ranges"; "0regs"; "0req"; "0rom"]; ["0scfg"; "0segs"; "JBV"; "JZ_to_bv"; "Jbv"; "Jbv_and"; "Jbv_unsigned"; "0t"; "0tid"; "0w"; "0x8"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section Noacc.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma sstep_of_check_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "R@'Q<'QK'UDyR0%211'QL'9'QO%211'C'<%117&R1r5%211(3%11<%83631&Q@r7%211(5%12B9%>3<31'Q5&Q2&QIvUAr8r6%43321%631B<(Q3r4r3%3221%K3<51&F&QGvU@r9%?3>1F%4431>=%611%Q01?%Q43Q21M'>':%22Q<1%Q;11&R9%11G(;%115%Q=3531'QH(QFr<r;%3221(QB&QC&QD%126G%311%921Q5%611%<5Q8L8Q@1p0>1p0H1p0K1p0Q31p0QA1p0QH1pY@R21pZ2R:1pY<R71p[FR91pZ8R=1pZ:R?1").
Proof. exact (sstep_cfg_of_check_noacc segs scfg). Qed.
Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
alloc_enomem_sysno_b (bv_unsigned x8) = false ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc.
apply (node_chk_ev_gen_noacc segs scfg ms model x8 I effs ms' evs materialize_model_accesses_nil Hh Hsvc Hok).
- intros i. apply not_unforced_na. exact Hal.
- intros eff m' ev Hc _. exact (Hinv eff m' ev Hc).
- exact Hnu.
- intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). apply Hh'.
- exact Hacc.
Qed.
Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
alloc_enomem_sysno_b (bv_unsigned x8) = false ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
node_ok segs scfg (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc.
apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hal Hok); auto.
Qed.
Lemma node_det_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "S:'Q<'QK'UDyR0%211'QL'9'QO%211'C'<%117&R1r5%211(3%11<%83631&Q@r7%211(5%12B9%>3<31'6&S@&UFr6%22I1%411(8%F3721&E'Q5&Q2&QIvUAr<r:%43321r3r;%83321(Q3r2r1%3221%Q63>51'Br9%Q93Q=:1r8%Q;3QC81%Q<3Q=8Q2%6221%7251%H291pY@QA1pZ2QI1pY<QF1&F%J3ID<%L31AH(Q4%QG3O21%511pY<QM1%QG1Q@%QK3QI1QD'>':%22R31%R211&R9%11I(;%115%R43531&T0vU@(QFr=%221Q='@q01Q3&QC&QDr>%221Q?%411%:21QDq081%>6QH=:981p0@1p0J1p0M1p0Q51p0R21p0R;1p0RB1pYBRL1pZ4S41pY>S11p[FS31pZ8S71pZ:S91").
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hal Hchk Hnu Hh0 Hacc.
apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc Hal).
- intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
- intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
- exact Hnu.
- intros []; exact Hh0.
- intros []; exact Hacc.
Qed.
Lemma rz_det_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "S;'Q<'QK'UDyR0%211'QL&SO'C'<%115&R1r5%211(3%11:%83631&Q@r7%211(5%12@9%>3<31'6&S@&UFr6%22G1%411(8%F3721'9'QO%211&E'Q5&Q2&QIvUAr<r:%43321r3r;%83321(Q3r2r1%3221%Q93>51'Br9%Q<3Q>:1r8%Q>3QD81(;%11H%QA3H:1%8241%9271%J2;1pY@L1pZ2QL1pY<QI1&F%L3KF>%N31CJ(Q4%QL3Q121%511pY<R01%QL1QE%R03QN1QI'>':%22R61%Q=11&R9%11K%H14%R83421'T1vU@(QF&QC&QDr=%221Q?%411%621Q6%94QD81Q5r>%9216%<4QG;1Q:p041p0?1p0H1p0K1p0Q31p0R51p0R>1p0RE1pXJRO1pZ4S51pY>S21p[FS41pZ8S81pZ:S:1").
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hal Hchk Hnu Hh0 Hacc Hc.
eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.
Lemma srz_det_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "S;'Q<'QK'UDyR0%211'QL&SO'C'<%115&R1r5%211(3%11:%83631&Q@r7%211(5%12@9%>3<31'6&S@&UFr6%22G1%411(8%F3721'9'QO%211&E'Q5&Q2&QIvUAr<r:%43321r3r;%83321(Q3r2r1%3221%Q93>51'Br9%Q<3Q>:1r8%Q>3QD81(;%11H%QA3H:1%8241%9271%J2;1pY@L1pZ2QL1pY<QI1&F%L3KF>%N31CJ(Q4%QL3Q121%511pY<R01%QL1QE%R03QN1QI'>':%22R61%Q=11&R9%11K%H14%R83421'T3vU@(QF&QC&QDr=%221Q?%411%621Q6%94QD81Q5r>%9216%<4QG;1Q:p041p0?1p0H1p0K1p0Q31p0R51p0R>1p0RE1pXJRO1pZ4S51pY>S21p[FS41pZ8S81pZ:S:1").
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hal Hchk Hnu Hh0 Hacc Hc.
eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
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
Lemma with_vm_backing_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "H'9'>'UDyR0%211%4211%611%713'QK'C'<%117&R1&RDr3r2r1%43321%611%713%;3921pZ0=1pZB?1pYLA1").
Proof. reflexivity. Qed.
Lemma vm_add_lazy_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "C'UDyR0%211'QK'C'<%114&R1&R:r3r2r1%43321%611%713%;3921pZ0=1pZ>?1pXL@1").
Proof. reflexivity. Qed.
Lemma with_mmap_backing_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "E'UDyR0%211'QK'C'<%114&R1&S0r4r3r2r1%544321%711%813%<3:21pZ0>1pZ>@1pXLA1pYDB1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma with_mmap_replacement_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "E'UDyR0%211'QK'C'<%114&R1&S2r4r3r2r1%544321%711%813%<3:21pZ0>1pZ>@1pXLA1pYDB1").
Proof.
intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
apply vm_forget_range_halted.
Qed.
Lemma with_mmap_destroyed_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "F'UDyR0%211'QN'QK'C'<%115&R1&S1r4r3r2r1%544321%711%813%<3:21pZ0>1pYH@1pZ>B1pXLC1").
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.
Lemma forget_vm_ranges_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "E'9'>'UDyR0%211%4211%611'QK'C'<%116&R1&RJr2r1%3221%511%613%:3821pZ0<1pZJ>1").
Proof.
induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.
Lemma brk_model_halted : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "C'UDyR0%211'QK'C'<%114&R1&S6r3r2r1%43321%611%713%;3921pZ0=1pZH?1pZN@1").
Proof.
intros. unfold brk_model, with_brk_next. cbv zeta.
rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.
Lemma stepacc_ecall_epend : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "R1&S3y5'UDyR0%211%5241'<y8%611%311p061yQ0%:11'C%812&Q9vUAr4%3221(5r1%2291%93841'6&Q:r2%211(?%?3521'Q;'Q8'Q<%211%411&QA&SEvTJr7r6r5%554321G%72I1(Q7(Q>&S5&SD(UB+A(A%33Q@21%52=1%76?>=<Q21(;&Q=%211%<3H41%>2H1%Q<3H@1p0N1p0Q51p[DQ@1p[0QC1pZ6QD1pZDQK1pZLQK1").
Proof.
intros regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma node_instr_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "QE'Q<'QK'C'<'UDyR0%211%411&R1r2%211(3%116%;3631&Q@r4%211%?3:15'Q;'Q8%11D%311&QAvUAr5%3221(Q7(Q>r3(;&Q=%211%53Q041%72=1%Q03=91&T0vU@(QFr6%221?'@'QO%=11q031%72D6q051%;6G:7631p0=1p0O1p0Q41pZ<QB1pZ8QB1pZ:QD1").
Proof.
intros ms model ms' Hh Hsvc Hstep.
assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
{ unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
rewrite materialize_model_accesses_nil. reflexivity. }
apply (node_ok_of_pnode_instr segs scfg); [exact Hsvc |].
split.
- intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
- intros e st Hss. exists tt.
inversion Hss; subst;
match goal with
| H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
| H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
end.
Qed.
Lemma rz_sys_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "R8&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11&SO'C%:1<&R1r3%211(3%11A%73631%A1:&Q9vUAr7%3221(5%12@;%?3731'6&Q:r4%211(?%E3521'T1vU@(QF&S5vTJr:r9r8&SD(UB+A(A%33Q@21%5281%;6:987I1r6%>221%A4M@1E&SEr;%25@1?>=%C21Q0r5%G4Q3F21p071p0J1p0Q11p0Q:1pXJQC1p[DQE1pZ8QH1p[0QJ1pZ6QK1pZDR21pZLR21").
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply rz_silent1; [| exact Hc].
apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.
Lemma epend_len : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "QO&S3y5'UDyR0%211%5241'<y8%611%311p061'J'C&SDr5(UB+;(A%33A21%6251&UCr1%22C1%;3C41'B&T9zr2%3221&T;+2+R0%3221%8261%:261&UF&Q?&S5vTJr7r6r4+A%L3Q:1J%O251%86765O41u1%;221%=2Q=1r3%Q63Q721&F%Q02QAJ%Q93QA61%311%O251p0F1p0Q21pYNQ?1p[0QA1pZ6QB1pZDQI1pZLQI1").
Proof.
intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
- apply u64_lit. lia.
- intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.
Lemma srz_sys_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "R8&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11&SO'C%:1<&R1r3%211(3%11A%73631%A1:&Q9vUAr7%3221(5%12@;%?3731'6&Q:r4%211(?%E3521'T3vU@(QF&S5vTJr:r9r8&SD(UB+A(A%33Q@21%5281%;6:987I1r6%>221%A4M@1E&SEr;%25@1?>=%C21Q0r5%G4Q3F21p071p0J1p0Q11p0Q:1pXJQC1p[DQE1pZ8QH1p[0QJ1pZ6QK1pZDR21pZLR21").
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply srz_silent1; [| exact Hc].
apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.
Lemma srz_munmap_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "T;&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11'J&SO'C%;14&Q9vUAr8%3221(5r4%22;1%93841'6&Q:r5%211(?%?3521%J1L&R1r7%211(3%11Q1%F3631&SDr<(UB+A(A%33Q;21%6251&UC+VG%22Q=1%Q13Q=41r=+:%;3QC19%>231%Q63QB1D&T:&UF%12QFQ5&R8%4221z%Q=3Q?21r?+;%G3QO1E%J231%D2QOQ>%QC3QO21&T9r9%22:1&T8&T6r;%B2R71&R7r:%211%6241&QM%9221&R4&R>&R3r>%211%411%<1>%Q:2RE1%833QA1%R:3R01QL'T3vU@(QF&SEvTJ&SFrC%QD2ROQ6%332Q?1&SGrB+4%3221&SB%N1R1%QL2S71rA%43QJ21r@%@5?;721&SA%13QN6QB%D231%G4ROF1Q9rD%F5E1C?9%H218%K4S3J1R>p051p0N1p0Q91p0QD1p0QH1p0QO1p0R71p0R=1p0RI1p0S11p0S81pQNSC1pYNSE1pXLT01p[DSH1pZ8SK1p[0SM1pZ6SN1pZDT51pZLT51").
Proof.
intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
rewrite H0, Hpr in Hchk.
eapply (srz_det_noacc ms model (getr regs 17)
(mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
[exact Hh | reflexivity | rewrite Hno; reflexivity | | | | reflexivity |].
- intros eff m' evs. split.
+ intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
+ intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
- rewrite munmap_model_halted. exact Hh.
- unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.
Lemma node_brk_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "RJ'Q<'QK'UDyR0%211'C'<%113&R1r2%211(3%118%83631&Q@r4%211(5%12>9%>3<31'J&UFr3%22D1+VF%D3521&T0vUAvU@(QFr6r5%3221'I&SK&Q?r7(4%3221r1%64<:21qZHQ51%92Q61(;'QO%211q041&QC&QD(R5&Hr8%A21?%C4IA1>qZHQB1%53QC1@'>'9y8%QI11%311%52QI1%C11&RI&R;&R3%11Q4%311%53N=1&RH%12?3'QJ%M11':%B2R61%Q011%K6E>8641%M2Q91%O11&S6%13Q:IQB%QD231qYJQ81%QI6QHQGQCQ9Q51p0QK1p0R21p0R91p[FRC1pZ8RG1pZ:RI1").
Proof.
intros ms model x8 Hh Hsvc Hno.
set (req := ms_gpr ms 0).
assert (Hfam : sc_alloc scfg = false -> injected_family_off scfg (sys_input segs ms x8) = true).
{ intros Ealloc. rewrite (injected_family_off_alloc scfg _ 214%Z);
[rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto]. }
apply (node_chk_ev_gen_noacc segs scfg ms model x8 {r : word | brk_adm scfg model req r}
(fun i => brk_eff ms model (proj1_sig i))
(fun i => brk_model req (proj1_sig i) model) (fun _ => []) materialize_model_accesses_nil Hh Hsvc).
- intros [r [Hr Hf]]. cbn [proj1_sig]. apply check_syscall_ok_iff. exact (brk_ok_intro segs ms x8 model r Hno Hr).
- intros [r [Hr Hf]]. cbn [proj1_sig].
destruct (sc_alloc scfg) eqn:Ealloc.
+ apply not_spurious_on. rewrite (injected_family_off_alloc scfg _ 214%Z);
[rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
+ destruct (brk_refusal_b model req r) eqn:Eref.
* apply not_spurious_forced. intros eff' m' evs' Hspec.
apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec.
destruct Hspec as (_ & _ & Hok' & _).
rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). apply (Hf eq_refl eq_refl). exact Hok'.
* apply not_spurious_nonrefusal. unfold brk_eff. cbn [eff_ret].
rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact Eref.
- intros eff m' ev Hc Hnsp. apply check_syscall_ok_iff in Hc.
pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hc) as (Heff & -> & Hok & ->).
fold req in Heff, Hok.
assert (Hadm : brk_adm scfg model req (eff_ret eff)).
{ split; [exact Hok|]. intros Ealloc Eref r' Hr'.
destruct (brk_refusal_b model req r') eqn:E'; [reflexivity|]. exfalso. apply Hnsp.
apply (spurious_intro scfg (sys_input segs ms x8) model eff (brk_eff ms model r') (brk_model req r' model) []).
- exact (Hfam Ealloc).
- rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact Eref.
- exact (brk_ok_intro segs ms x8 model r' Hno Hr').
- unfold brk_eff. cbn [eff_ret]. rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact E'. }
exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. unfold brk_eff. fold req.
split; [exact Heff | split; reflexivity].
- intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
exact (proj1 (check_syscall_err_iff _ _ _) Hc).
- intros eff m' ev Hc. apply check_syscall_ok_iff in Hc.
pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hc) as (_ & _ & _ & ->).
rewrite brk_model_halted. exact Hh.
- intros [r Hr]. reflexivity.
Qed.
Lemma srz_brk_query_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "RN&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11&SO'C%:13&Q9vUAr6%3221(5r2%22:1%93841'6&Q:r3%211(?%?3521%I1K&R1r5%211(3%11Q0%F3631&SDr:(UB+A(A%33Q:21%6251&UC+VF%22Q<1%Q13Q<41r;+:%;3QB19%>231z%92QC1%Q83QC31'T3vU@(QF&SEvTJ&SFr<&R;&R3r8%211%411%736A1&SG+4%22F1r9%>5=52Q21%@219%C4QIB1QHr=%B5A1?LQ6%D216r7%H4QNG21p061p0K1p0Q31p0Q?1p0QG1p0QN1pQNR91p[DR;1pZ8R>1p[0R@1pZ6RA1pZDRH1pZLRH1").
Proof.
intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hq : brk_adm scfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (rewrite H0; apply brk_adm_query; reflexivity).
apply (srz_cases1 segs scfg _ _ _ K (exist _ _ Hq) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)).
intros [r Hr]. cbn [proj1_sig].
assert (Er : r = vm_brk (m_vmmaps model)) by (apply (brk_adm_query scfg model); rewrite <- H0; exact Hr). subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.
Lemma srz_brk_grow_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "UE&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11'J&SO'C%;14&Q9vUAr7%3221(5r3%22;1%93841'6&Q:r4%211(?%?3521%J1L&R1r6%211(3%11Q1%F3631&SDr;(UB+A(A%33Q;21%6251&UC+VF%22Q=1%Q13Q=41'QN&R3r8%211&R;r1%211&T:&UF%12QH4&R8%4221z%Q?3QA21r9%8215%QB3QD14&T9r:%2271%<2R3Q:%4291&T6r5%@2R71r<%4221&T;+2+R0%3221%>251&T8&RB%11R0%K2RB1%L2RCQDr=%@221%7241rD+:%QC3RK1QA%QF231%Q42RKR:r>%H221%QC2RN1%RB3RN51&RGrA%Q;2S2QAr?%O221%QJ2S51%63511%RJ3R@1R<'T3vU@(QF&SEvTJ&SFrF%QH2S?QBr@%Q<221%R72SB1%635J1&SGrE+4%3221&SC%R>2SI9%23QM1Q3rC%A5@9521&RE(R6&RA%11QO(7'>%12T2T2(=%14T4T4R8<&R>%11R6%73531&R@%11R9%QK1R:&R=%11R<&R?%11R>&R<%11R@%D8B:87Q0531rB%G221%Q;2I1%Q>4T6Q=1QCrG%Q=5Q<1Q:Q3R1%Q?21N%QB4T:QA1Q:p051p0QE1p0QN1p0R81p0RA1p0RL1p0RO1p0S31p0S71tY0U3S?1tYHSFSC1p0SH1p0T41p0T<1p0TC1pR2TN1pY:U01p[DU21pZ8U51p[0U71pZ6U81pZDU?1pZLU?1").
Proof.
intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_adm scfg model (ms_gpr ms 0) r <-> r = req).
{ intros r. rewrite H0. rewrite (brk_adm_grow_cases scfg model req r Halloc); [| fold h; fold b; rewrite Hureq; lia ..].
rewrite Hadm. reflexivity. }
assert (Hr0 : brk_adm scfg model (ms_gpr ms 0) req) by (apply Hcases; reflexivity).
apply (srz_cases1 segs scfg _ _ _ KB (exist _ req Hr0) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)).
intros [r Hr]. cbn [proj1_sig]. fold h.
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
unfold brk_page_range.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned req))
by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.
Lemma srz_brk_grow_blocked_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "SM&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11&SO'C%:13&Q9vUAr7%3221(5r3%22:1%93841'6&Q:r4%211(?%?3521%I1K&R1r6%211(3%11Q0%F3631&SDr;(UB+A(A%33Q:21%6251&UC+VF%22Q<1%Q13Q<41'QN&R3r8%211&R;r1%211r>+:%B3QI1@%E231%Q=3QH19&T9z&UFr9%22QN1%5241&T8&RB%11Q:%72R31r:%92R51%6231%;2R7Q?%<2R8Q4%9221&RGr<%23G11(8%R23QH21'T3vU@(QF&SEvTJ&SFrC%231OQH&SGrB+4%3221rAr@%;5:7321r?%>221%A4RA@1ErD%@5?1=:7%B217r=%F4RFE21p061p0I1p0O1p0Q31p0Q;1p0QB1tY0S;QH1tYHQOQL1p0R11p0R=1p0RE1p0RL1pR0S71pZNSB1p[DS:1pZ8S=1p[0S?1pZ6S@1pZDSG1pZLSG1").
Proof.
intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hres : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
{ intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
- intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
- intros ->. left. reflexivity. }
assert (Hkeep : brk_adm scfg model (ms_gpr ms 0) b).
{ split; [apply Hres; reflexivity|]. intros _ E r' Hr'. apply Hres in Hr'. subst r'. exact E. }
apply (srz_cases1 segs scfg _ _ _ KA (exist _ b Hkeep) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)).
intros [r [Hr Hf]]. cbn [proj1_sig]. fold h.
pose proof (proj1 (Hres r) Hr) as Er. subst r. fold b.
rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
unfold ms. rewrite adv_ret_epend. exact HA.
Qed.
Lemma node_set_tid_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "RG'Q<'QK'UDyR0%211'C'<%113&R1r2%211(3%118%83631&Q@r4%211(5%12>9%>3<31'J&UFr3%22D1+S0%D3521&R2r5%211%H3F1A&T0vUAvU@(QFr7r6%3221&SN(;'QO%211q041&QC&QDr8(R5&H'B&T9zr1%N2Q@1%4231&RF%6231%8231q[@QD1%;3QE17'>'9y8%QK11%311%52QK1%J11%72QMQM%L11'QJ%N11':%<2R21%Q111%K6?86641%N2M1%Q011&RC%12CQ:%Q<231qYJQ91%QA6Q@Q?Q;Q:Q61p0QC1p0QH1p0QO1p0R61p[FR@1pZ8RD1pZ:RF1").
Proof.
intros ms model x8 Hh Hsvc Hno Htid.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
match eff with
| mkEffectU ret [] [] [] [] [] =>
if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
then CheckOk (with_tid ret model) [] else CheckReject
| _ => CheckReject end).
{ intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
apply (node_chk_noacc ms model x8 tid_I
(fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
(fun i => with_tid (proj1_sig i) model) Hh Hsvc ltac:(rewrite Hno; reflexivity)).
- intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
- intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
- intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
- intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
- intros [t Ht]. reflexivity.
Qed.
Lemma srz_set_tid_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "S7&S3y5'UDyR0%211%5241'<y8%611%311p061'QK&SOyQ0%<11'C%:12&Q9vUAr6%3221(5r1%2291%93841'6&Q:r2%211(?%?3521%I1K&R1r5%211(3%11Q0%F3631&SDr:(UB+A(A%33Q:21%6251&UC+S0%22Q<1%Q13Q<41&R2r7%211%Q53E1@'B&T9z&UF%12QFQ3%4231&RF%6231%8231'T3vU@(QF&SEvTJ&SFr>+:%N3R51L%4331Q<&SGr=+4%3221r<r;%=5<7321&RC%12QEQ9%A231r9%E4R1D21p0G1p[BRA1%E5D=:9Q?%G215r8%K4R7J21p051p0Q71p0Q<1p0QH1p0R01p0R71p[DRB1pQNRE1pZ8RG1p[0RI1pZ6RJ1pZDS11pZLS11").
Proof.
intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
apply (srz_conseq segs scfg _ (t_alt (fun _ : tid_I => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
| eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
intros [t Ht]. cbn [proj1_sig].
change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.
Lemma srz_exit_at_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "RI&S3y5'UDyR0%211%5241'<y8%611%311p061'QKyQ0%;11'C%912&Q9vUAr6%3221(5r2%2291%93841'6&Q:r3%211(?%?3521%H1J&R1r5%211(3%11O%F3631'G&SDr:(UB+A(A%33Q:21%6251&UC+RN%22Q<1%Q23Q<41+RM%52Q?1%Q53Q?71%?241r;+:%?3QF1=%B231%Q;3QE1I'T3vU@(QF&SEvTJr<r9%4532<J1r8%7221&T2&UE+WO%J2R41%33R5QF1&R0%118%7231%B4QKA91p0D1p0J1p0Q;1p0QC1p0QJ1pY6R>1p[DR61pZ8R91p[0R;1pZ6R<1pZDRC1pZLRC1").
Proof.
intros regs pc mem rom model w code HF HE Hh H17 H10.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
Lemma mmap_gates_core50 : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "Q9'UDyR0%211'C'J&RMr2%211+QB%63521'B'6&RNr3&UCz%22?1%53;41(8%@3821&RO%13?85%C3;14&RK%138;8(?%G3?21+3%>2K1%631@=%K3C1<&RL%134C@%N3F18%H241%I291%J2>1%K2B1p0M1pZFQ51pYDQ61").
Proof.
intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
rewrite Hc. repeat split; try (vm_compute; reflexivity).
all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.
Lemma srz_alt3 : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "Q7'QE'SMp012&SO&T0vUAvU@r5(;'QO%211q0:1r4%96876<21'T3(SH%911%34<;15r6(SI%211%74@?19r7(SJ%211%;4DC1=r9&SL%136:E%?4HG31p051p0:1p0?1p0D1p6O1p4Q01p2Q11pZ@Q31pY2Q61").
Proof.
intros c nx A B C Hnode HA HB HC.
apply (srz_conseq segs scfg c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
- apply (srz_cases c three nx _ T1 Hnode). intros [| |]; assumption.
- intros tr. unfold t_alt3, t_alt2, t_alt. split.
+ intros [[| |] H]; tauto.
+ intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
if Z.eqb prot 0
then mkVmMapsFull (vm_reserved h) (vm_maps h)
((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
else mmap_fixed_rw_next h addr n.
Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
mkVmMapsFull (vm_reserved h)
(maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].
Lemma with_mmap_replacement_halted' : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "E'UDyR0%211'QK'C'<%114&R1&S2r4r3r2r1%544321%711%813%<3:21pZ0>1pZ>@1pXLA1pYDB1").
Proof.
intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "F'UDyR0%211'QN'QK'C'<%115&R1&S1r4r3r2r1%544321%711%813%<3:21pZ0>1pYH@1pZ>B1pXLC1").
Proof. intros. reflexivity. Qed.
Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs, us with
| [], [] => CheckOk model []
| [], _ => if listNN_eqb us [(addr, n)]
then CheckOk (fixedin_destroyed_model addr n model) []
else CheckReject
| _, _ => CheckReject
end
else if (Z.eqb prot 0)
then match zs with
| [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
else match us with
| [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
| _ => CheckReject
end.
Proof.
intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
rewrite E1, H2, H3, H5, H0, Hu1.
destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
pose proof (u64_range addr) as Har.
destruct Hprot as [-> | ->].
-
rewrite G3. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
reflexivity.
-
rewrite G4, G5. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
rewrite (Hbud eq_refl).
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
destruct (errno_ret_in mmap_errnos r); [reflexivity|].
destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.
Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 222 ->
(prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
(if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
(fixedin_ok_model prot flags addr n model)) KB ->
srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
Htop Hrf Hmc Hbud) as Hchk.
cbv zeta in Hchk. fold n in Hchk.
assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
pose (effs := fun _ : unit => fixedin_ok_eff prot addr n).
pose (ms' := fun _ : unit => fixedin_ok_model prot flags addr n model).
assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
= CheckOk (fixedin_ok_model prot flags addr n model) []).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
assert (HretS : eff_ret (fixedin_ok_eff prot addr n) = addr) by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mmap_errnos r).
{ intros r. apply refusal_b_mmap_sys. exact Hno. }
assert (HB0 : KB []) by (eapply srealizes_nonempty; exact HB).
apply (srz_conseq segs scfg (mkCfg ms model) (t_alt (fun i : unit => t_emit [] KB))).
2:{ intro tr. split; [intros [i Hi]; exact (proj1 (t_emit_nil_eq KB HB0 tr) Hi) | intros H; exists tt; exact (proj2 (t_emit_nil_eq KB HB0 tr) H)]. }
apply (srz_node segs scfg (mkCfg ms model) unit (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))
(fun _ => KB) tt).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros []. exact HokS.
+ intros []. apply alloc_nonrefusal_step. cbv delta [effs] beta. rewrite HretS, Hrb. exact Haddr_ne.
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mmap_errnos r) eqn:Er.
*
exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
-- rewrite HretS, Hrb. exact Haddr_ne.
-- cbn [eff_ret]. rewrite Hrb. exact Er.
* rewrite Hchk in Hc. rewrite Er in Hc.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (Z.eqb prot 0) eqn:Ep.
-- destruct zs; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
-- destruct us; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
+
intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r).
* destruct zs; [|discriminate]. destruct us.
-- injection Hc as <- <-. exact Hh.
-- destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. cbn. exact Hh.
* destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
(destruct (bv_eqb r addr && listNN_eqb _ _)%bool; [|discriminate]); injection Hc as <- <-;
unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
+ intros []; cbv delta [effs] beta; unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity.
- intros []. cbv delta [effs ms'] beta. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
+ rewrite adv_unmaps1_epend. exact HB.
+ rewrite adv_zeros1_epend. exact HB.
Qed.
End Noacc.
Open Scope Z_scope.
Import AX2K AX2SK APK APSK.
Lemma is_ecall_at_sound : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "QD'9'Q6%211'S8'C'6&S9r2r1%3221(?%73621'B&T8z&S;%119%4231&T9&T6+4%2251&S?%5221'D'UDyQ0%211'<%112&Q9r4&UCyR0r3%D11%4231%7261(5%12<O%Q43;31&Q:%11Q2%Q73Q61Q1%Q0241q[DB1%F2C1%Q32H1%Q42O1p0Q61pY8Q?1pX:QA1").
Proof.
intros SEGS cs H. unfold is_ecall_at in H.
apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
apply Z.leb_le in H0. apply Z.ltb_lt in H4.
destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
repeat split; try assumption. exists w. auto.
Qed.
Lemma bv_and_255 : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "K'J'B&T8zr1%3221&T9&S?%2241%8241'C'UDyR0%211&UE&UCr2%2251+WO%4271%63831&T7%1264%82;1%>3;41p0@1pY4J1").
Proof.
intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
symmetry. apply u64_lit. unfold two64 in *.
pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.
Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.
Lemma v_addi_pc : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "K'J&T8zr1%3221&T9&T6r2+4%3221&S?%6221'C'UDyR0%211&SG&UCr3%2251%421<%?23=%5281%;3831p0=1p0E1pZBJ1").
Proof.
intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.
Section CsOk.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).
Lemma cs_ok_refuse : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK "Q>'S>'S8&S3y5'UDyR0%211%5241'<y8%611%311p061'QK'S=vT4v0vQ1vT5vT>vLr5r4r3r2r1%<;;:987654321r6&S<%118&SF(UB+:(A%33O21&UC&S7%22Q01%83@41%I;HGFEDC<:1@?p0>1pZ8L1pQLN1pV:Q41pY8Q;1pQHQ=1").
Proof.
intros E cs R FULL model HC.
assert (HMr : Mr A argH E (refuse cs) model FULL = Mr A argH E cs model FULL) by reflexivity.
assert (HA : allowA A E (refuse cs) = allowA A E cs) by reflexivity.
destruct HC; constructor; unfold refuse, set_pc, set_reg, with_ss, mk_ss in *;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_pc s_next] in *;
try assumption; try reflexivity.
apply regs_ok_set_n; [exact co_regs0 | lia | rewrite edenot_lit; reflexivity].
Qed.
Lemma pc_refuse : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK ">'S8'C'J&S;&S<r1%211%411&T6%614+4%3221%;3:51pY8=1").
Proof. reflexivity. Qed.
Lemma nxt_refuse : ltac2:(TCodec.tc2 tcn__AsanNodesLibEK ";'S8'C':&S:&S<r1%211%411%513%83721pY8:1").
Proof. reflexivity. Qed.
End CsOk.
