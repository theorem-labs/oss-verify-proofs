(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.LimSim Require Import LimSim LimSimMm LimSimArms LimSimMv LimSimWf.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "4h5LinuxProcessSemanticsfLinuxProcessSem3Sys8Dispatch07SpecArm37Corelib4Init9Datatypesje4bool37Corelib4Init5Logicld2eqje5false07sa_spec37Corelib7Numbers7BinNumso74Nposo71Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runqbh6alloc_budget_refused_b3h5LinuxProcessSemanticsfLinuxProcessSem5Statev15Modelv1dSyscallEffectv1cSyscallInputv18in_sysno05sa_no89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim6LimSim~~~~~~hl83DIRhl83MOKhl85relim89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim8LimSimMm~~~~~~hr65MV_OK35stdpp9bitvectorbdefinitionsig8bbv_unsignedje4Someje4listje6optionld3and0alookup_arm36Stdlib5Lists4Listild2In08dispatch99OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim9LimSimSys8Dispatch~~~~~~io06ARM_OK4h5LinuxProcessSemanticsfLinuxProcessSem3SyscSyscallTableitdaspec_table3h5LinuxProcessSemanticsfLinuxProcessSem5Specsji4csyscall_specqb6configqb9cfg_modelqb9refusal_big82bvqbh4spurious_refusal_cfgje4Noneld3not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjqedmachine_statejqeems_svc_pendingqbh1budget_refused_atqb5mkCfgqb9sys_inputv18m_haltedqb9sstep_cfgqb7step_told2exqb6SErrorqb5SNextv15eventqb8star_cfg99OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim9LimSimSys5Steps~~~~~~knbeMREMAP_MOVE_OKqbhareaches_budget_refused_cfg3h5LinuxProcessSemanticsh5EquivalenceDefinition8MustExitkvbh3must_exit_in_at_cfghl89relim_cfgknb4MOKc3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelm07SegmentqbbSpuriousCfgv18m_vmmapsv18vm_limit89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim9LimSimSys~~~~~~ls4eMREMAP_MOVE_OK46Stdlib6ZArith6BinInt1Zmi02leqbbinit_configo71Nlm08PhdrInfo3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutmlc9EntryDrawv19ProcInputlm05Imageqb9ExecEntrykvbh1must_exit_in_scfg3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalencemt4h9source_within_budget_scfg89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim8LimSimMv~~~~~~nid2WF" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Dispatch.
Variable L0 L : Z.
Hypothesis HLE : ltac2:(zQ "10!mj8@2$0?1L?2L0").

Definition ARM_OK : ltac2:(zQ "10!j5>1a$0P") := ltac2:(zQ "h20!l6!n1!n6!ne!q0!q7!t7!hhf!hi7!hj7!hk6!j5!hl1!hpf!hq6!hqd!hvf!ii5\1a$b>1d$0>1i$9>1m$7>0@3$1$5@2$h1@1$4#k0@1$a^2@1$c^4>0@2$e?2L0^2>0>0@3$1$0^5$2@3$1$0@2$6^5@2$f?1L^4$2>0>0@3$1$0^6$2@1$h0^5@8$d?2L0?1L$8^7^6^5@1$3^8@1$3^8").

Lemma lookup_arm_In : ltac2:(zQ "a0!j5!n1!q7!ij4!ijb!ik2!ikb!il1!hl1!in0>1t@1$4$0>1n$2>1a$0>0@3$1@1$5$0@2$7^3^2@2$3$0^1@2$6@3$9$0^2^4@3$1$2@1$8^2^3").
Proof.
  induction t as [|x t IH]; intros n a H; [discriminate H|]. cbn in H.
  destruct (Z.eqb (sa_no x) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.

Lemma dispatch_dir : ltac2:(zQ "h00!l6!n6!n1!j5!in6!ijb!t7!hhf!hi7!hj7!hpf!hq6!hqd!hvf!it3!in0>1t@1$5$3>0>1a$3>0@3$f$3^1^2@1$e^2>1d$0>1i$9>1m$7>0@2$b?2L0^1>0>0@3$2$0^4$1@3$2$0@2$6^4@2$c?1L^3$1>0>0@3$2$0^5$1@1$d^4@8$a?2L0?1L$8^6^5^4@1$4^8@1$4^8").
Proof.
  intros t Ht d i m HM G1 G2.
  destruct (lookup_arm t (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - destruct (lookup_arm_In _ _ _ E) as [Hin Hno].
    pose proof (Ht a Hin d i m (eq_sym Hno) HM G1 G2) as H.
    destruct d; intros o Ho; unfold dispatch in Ho |- *; rewrite E in Ho |- *; exact (H o Ho).
  - destruct d; intros o Ho; unfold dispatch in Ho |- *; rewrite E in Ho |- *;
      [ exact (dir_unmodeled L0 L true i m o Ho) | exact (dir_unmodeled L0 L false i m o Ho) ].
Qed.

Lemma spec_table_ok : ltac2:(zQ "40!j5!jh6!it3!in0>1a$0>0@3$3$0^1$1@1$2^2").
Proof.
  intros a Hin d i m Hno HM G1 G2.
  unfold spec_table in Hin.
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_17 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_19 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_20 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_21 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_22 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_23 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_24 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_25 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_29 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_32 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_35 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_46 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_48 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_56 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_57 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_59 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_61 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_62 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_63 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_64 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_65 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_66 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_67 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_68 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_72 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_73 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_78 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_79 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_80 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_82 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_83 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_85 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_93 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_94 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_96 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_98 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_101 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_113 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_119 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_123 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_124 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_130 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_131 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_132 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_134 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_135 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_144 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_146 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_147 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_149 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_157 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_158 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_159 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_160 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_167 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_169 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_172 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_174 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_175 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_176 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_177 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_178 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_198 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_199 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_200 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_201 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_202 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_203 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_204 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_205 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_206 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_207 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_208 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_209 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_210 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_211 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_212 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> brk_budget_refused_b (relim L m) (in_arg i 0) = false) by (intros Hd; specialize (G1 Hd); unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => brk_spec (in_arg i 0)) (fun i0 => brk_spec (in_arg i 0))); lazy beta; exact (sim_brk L0 L HLE d i m HM Gb) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_215 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (relim L m) = false) by (intros Hd; specialize (G1 Hd); unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i0 => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); lazy beta; exact (sim_mremap L0 L HLE d i m HM G2 Gb) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_220 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) (relim L m) = false) by (intros Hd; specialize (G1 Hd); unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (fun i0 => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); lazy beta; exact (sim_mmap L0 L HLE d i m HM Gb) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false) by (intros Hd; specialize (G1 Hd); unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i0 => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); lazy beta; exact (sim_mprotect L0 L HLE d i m HM Gb) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_233 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_242 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_260 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_261 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_278 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_435 L0 L d i m HM) |].
  destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_439 L0 L d i m HM) |].
  destruct Hin.
Qed.

Theorem syscall_spec_dir : ltac2:(zQ "c0!l6!n6!n1!jl2!t7!hhf!hi7!hj7!hpf!hq6!hqd!hvf>1d$0>1i$7>1m$5>0@2$9?2L0^1>0>0@3$2$0^4$1@3$2$0@2$4^4@2$a?1L^3$1>0>0@3$2$0^5$1@1$b^4@8$8?2L0?1L$6^6^5^4$3$3").
Proof. exact (dispatch_dir spec_table spec_table_ok). Qed.
End Dispatch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Steps.
Variable segs : ltac2:(zQ "20!ijb!lp5@1$0$1").
Variable cfg : ltac2:(zQ "10!lq0$0").
Variable L0 L : Z.
Hypothesis HLE : ltac2:(zQ "10!mj8@2$0?1L?2L0").

Definition MOKc : ltac2:(zQ "10!jm2>1c$0P") := ltac2:(zQ "30!jmb!jm2!hq6\1c$1@2$2?2L0@1$0^1").
Ltac halt_tac H := first [ exact H | rewrite relim_halted; exact H | cbn [cfg_model cfg_ms]; rewrite relim_halted; exact H ].
Ltac kill_tac H := first [ exact H | rewrite relim_killed; exact H | cbn [cfg_model cfg_ms]; rewrite relim_killed; exact H ].

Lemma refusal_b_relim : ltac2:(zQ "80!jn7!l6!n1!q0!hhf!hj7!hqd!jo3>1i$5>1m$4>1r@1$7@1$3#k0@3$2$1@3$0^3@2$6?1L^2^1@3$0^3^2^1").
Proof. intros. reflexivity. Qed.

Lemma spurious_relim_up : ltac2:(zQ "b0!jo9!hqd!l6!n6!n1!t7!hhf!hi7!hj7!hq6!hvf>1i$8>1m$6>3eff$7>0@2$9?2L0^2>0@3$4$2@2$5^4@2$1?1L^3$3>0@1$a^4>0@4$0?3cfg^6^5^4@4$0?3cfg^7@2$1?1L^6^5").
Proof.
  intros i m eff HM G MV (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)). split; [exact Hoff|]. split; [rewrite refusal_b_relim; exact Hr|].
  destruct (syscall_spec_dir L0 L HLE false i m HM (fun _ => G) (fun _ => MV) _ Hs) as ([e0 m0 ev0|] & Hs' & R); cbn in R; [|contradiction].
  destruct R as (-> & -> & -> & _). exists eff', (relim L m'), evs'. split; [exact Hs' | rewrite refusal_b_relim; exact Hnr].
Qed.

Lemma spurious_relim_down : ltac2:(zQ "60!jo9!hhf!hi7!hj7!hq6!hqd>1i$3>1m$1>3eff$2>0@2$4?2L0^2>0@4$0?3cfg^4@2$5?1L^3^2@4$0?3cfg^5^4^3").
Proof.
  intros i m eff HM (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)). split; [exact Hoff|]. split; [rewrite <- (refusal_b_relim i m); exact Hr|].
  destruct (syscall_spec_dir L0 L HLE true i m HM ltac:(discriminate) ltac:(discriminate) _ Hs) as ([e0 m0 ev0|] & Hs' & R); cbn in R; [|contradiction].
  destruct R as (<- & -> & <- & _). exists eff', m0, evs'. split; [exact Hs' | rewrite <- (refusal_b_relim i m); exact Hnr].
Qed.

(* [comment removed for export] *)
Lemma not_refused_mark : ltac2:(zQ "h20!q0!jo3!n1!ik2!hqd!jq1!ij4!l6!n6!jq8!ju5!jv6!t7!kg8!khd!ki5!hhf!kj1>2ms$a>1m$h0>2x8@1$1@1$0#k0>0@1$9@2$d?4segs@2$e^3@2$4?1L^2>0@3$2@1$3@1$1@1$0#k0@1$h1^3@1$5@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#k0@1$b^5@2$6@1$1@1$0#k0^3@3$2$7@2$c@3$f?4segs^6^4@2$4?1L^5$8").
Proof.
  intros ms m x8 NB Hh Hp. destruct (alloc_budget_refused_b (sys_input segs ms x8) (relim L m)) eqn:E; [|reflexivity].
  exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hp|]. left. exact E.
Qed.

(* [comment removed for export] *)
Lemma step_up : ltac2:(zQ "h20!khd!ju5!kjc!kk8!hhf!hqd!ikb!kl2!jm2!hq6!ijb!n1!jq8!kl7!km0!kg8!km8!hvf>2ms$1>1m$4>3evs@1$a$h0>2st$3>0@2$9?2L0^3>0@1$h1^4>0@1$c@2$f?4segs@2$0^6@2$5?1L^5>0@5$2?4segs?3cfg@2$0^7@2$5?1L^6^5^4M3\2st$3P^5\2c'$8@2$7$1\3ms'$1@2$7$4\2m0$4@2$6@5$2?4segs?3cfg@2$0^b^a^9@1$e@2$0^2^1@2$6@3$b$8^3@2$0^2@2$5?1L^1@2$9?2L0^1@5$2?4segs?3cfg@2$0^8^7^6$d").
Proof.
  intros ms m evs st HM MV NB Hs.
  remember (mkCfg ms (relim L m)) as c eqn:Ec.
  destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
                 | ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
    injection Ec as -> ->; rewrite relim_halted in Hh.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
    destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat; [|discriminate].
    injection Ha as <- <-.
    assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
    destruct (materialize_relim_up L m _ _ HLE' Emat) as (m0 & Emat0 & ->).
    exists (@access_value _ report), m0. split; [|split; [reflexivity| unfold MOK; rewrite (materialize_limit _ _ _ Emat0); exact HM]].
    apply sstep_cfg_instr; [exact Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat0. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|apply sstep_cfg_instr_fault; [exact Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity]|discriminate].
    destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat; [discriminate|].
    exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|].
    + destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)); discriminate.
    + apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    destruct (syscall_spec_dir L0 L HLE true _ m HM ltac:(discriminate) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (<- & -> & <- & HM0).
    rewrite relim_halted in Hh'.
    assert (HLE' : L <= vm_limit (m_vmmaps m0)) by (unfold MOK in HM0; rewrite HM0; exact HLE).
    destruct (materialize_relim_up L m0 _ _ HLE' Hmat) as (m0' & Hmat0 & ->).
    exists (advance_past_svc (apply_effect ms eff)), m0'. split; [|split; [reflexivity | unfold MOK; rewrite (materialize_limit _ _ _ Hmat0); exact HM0]].
    eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hsp0 | | exact Hh' | exact Hmat0].
    intros SP. apply Hnsp. apply spurious_relim_up; [exact HM | apply (not_refused_mark _ _ _ NB Hh Hp) | exact MV | exact SP].
  - (* [comment removed for export] *)
    exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hp|]. right.
    exists eff, mm', evs0. split; [exact Hsp | split; [exact Hh' | exact Hmat]].
  - (* [comment removed for export] *)
    destruct (syscall_spec_dir L0 L HLE true _ m HM ltac:(discriminate) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (<- & -> & <- & HM0).
    rewrite relim_halted in Hh'. rewrite relim_killed in Hk. rewrite relim_fs.
    exists ms, m0. split; [|split; [reflexivity | exact HM0]].
    eapply sstep_cfg_exit; [exact Hh | exact Hp | exact Hsp0 | exact Hh' | exact Hk].
  - (* [comment removed for export] *)
    destruct (syscall_spec_dir L0 L HLE true _ m HM ltac:(discriminate) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (<- & -> & <- & HM0).
    rewrite relim_killed in Hk. rewrite relim_fs.
    exists ms, m0. split; [|split; [reflexivity | exact HM0]].
    eapply sstep_cfg_killed; [exact Hh | exact Hp | exact Hsp0 | exact Hk].
  - (* [comment removed for export] *)
    destruct (syscall_spec_dir L0 L HLE true _ m HM ltac:(discriminate) ltac:(discriminate) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
    eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hp | exact Hsp0].
Qed.

(* [comment removed for export] *)
Lemma step_down : ltac2:(zQ "d0!ijb!khd!kk8!km8!kl2!kjc!hqd!jq8!ju5!kg8!hhf!hq6!hvf>2ms$8>1m$a>3evs@1$0$3>2st$2>0@2$b?2L0^3>0@1$c^4>0@1$7@2$9?4segs@2$1^6@2$6?1L^5>0@5$5?4segs?3cfg@2$1^7^6^5^4@2$4@1$0$3\4evs'@1$0$3@2$4$2\3st'$2@5$5?4segs?3cfg@2$1^a@2$6?1L^9^2^1").
Proof.
  intros ms m evs st HM MV NB Hs.
  remember (mkCfg ms m) as c eqn:Ec.
  destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
                 | ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
    injection Ec as -> ->.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [|discriminate].
    destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
    + eexists [], _. apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
    + exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [|  |discriminate].
    + destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [discriminate|].
      destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
      * eexists [], _. apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
      * exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
    + eexists [], SError. apply sstep_cfg_instr_fault; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; [destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate|discriminate|].
    eexists [], SError. apply sstep_cfg_instr_unmodeled; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
    + eexists evs0, _. eapply sstep_cfg_syscall; [halt_tac Hh | exact Hp | exact Hsp0 | | halt_tac Hh' | exact Emat1].
      intros SP. apply Hnsp. exact (spurious_relim_down _ _ _ HM SP).
    + exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
      exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
    + assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
      destruct (materialize_relim_up L mm' _ _ HLE' Emat1) as (m0' & Hmat0 & _). rewrite Hmat0 in Hmat. discriminate Hmat.
    + exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
      exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    eexists _, _. eapply sstep_cfg_exit; [halt_tac Hh | exact Hp | exact Hsp0 | halt_tac Hh' | kill_tac Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    eexists _, _. eapply sstep_cfg_killed; [halt_tac Hh | exact Hp | exact Hsp0 | kill_tac Hk].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
    destruct (syscall_spec_dir L0 L HLE false _ m HM (fun _ => G) (fun _ => MV) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
    eexists [], SError. eapply sstep_cfg_syscall_unmodeled; [halt_tac Hh | exact Hp | exact Hsp0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MREMAP_MOVE_OK : ltac2:(zQ "10!jm2>1c$0P") := ltac2:(zQ "60!jm2!ijb!jmb!kn0!km8!hvf\1c$0>2tr@1$1$4>2c'$0>0@5$3?4segs?3cfg^3^2^1@1$5@1$2^2").

Lemma MREMAP_MOVE_OK_here : ltac2:(zQ "40!jmb!jm2!hvf!ksb>1c$1>0@1$3^1@1$2@1$0^2").
Proof. intros c H. apply (H []). apply star_cfg_refl. Qed.
Lemma MREMAP_MOVE_OK_step : ltac2:(zQ "60!jm2!ksb!ijb!km0!kjc!km8>1c$0>3evs@1$2$5>2c'$0>0@1$1^3>0@5$4?4segs?3cfg^4^3@1$3^2@1$1^3").
Proof. intros c evs c' H Hs tr c'' Hstar. apply (H (evs ++ tr)). eapply star_cfg_step; [exact Hs | exact Hstar]. Qed.

Lemma not_reaches_here : ltac2:(zQ "40!jq8!kg8!jm2!ktd>1c$2>0@1$0@3$3?4segs?3cfg^1@1$0@2$1?4segs^2").
Proof. intros c H B. apply H. exists [], c. split; [apply star_cfg_refl | exact B]. Qed.
Lemma not_reaches_step : ltac2:(zQ "70!jq8!jm2!ktd!ijb!km0!kjc!km8>1c$1>3evs@1$3$6>2c'$1>0@1$0@3$2?4segs?3cfg^3>0@5$5?4segs?3cfg^4^3@1$4^2@1$0@3$2?4segs?3cfg^3").
Proof.
  intros c evs c' H Hs (tr & c'' & Hstar & B). apply H. exists (evs ++ tr), c''. split; [eapply star_cfg_step; [exact Hs | exact Hstar] | exact B].
Qed.

Theorem must_exit_relim_at : ltac2:(zQ "a0!lj3!lkb!ijb!jq8!q0!jm2!ktd!ll8!ksb!jo3>1S@1$2@1$9@1$4#k0>1c$5>0@4$0?3cfg?4segs^2^1>0@1$7^2>0@1$3@3$6?4segs?3cfg@2$1?1L^3>0@1$8^4@4$0?3cfg?4segs^6@2$1?1L^5").
Proof.
  intros S c Hme. induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros HM NR MV.
  - apply (must_exit_in_at_cfg_halted _ _ _ _ code); [cbn; halt_tac Hh | exact Hin | cbn; kill_tac Hk].
  - destruct c as [ms m]. unfold MOKc in HM; cbn in HM. unfold relim_cfg; cbn.
    pose proof (not_reaches_here _ NR) as NB. pose proof (MREMAP_MOVE_OK_here _ MV) as MVH. cbn in MVH.
    apply must_exit_in_at_cfg_running.
    + cbn. rewrite relim_halted. exact Hnone.
    + destruct Hprog as (evs & st & Hs). exact (step_down ms m evs st HM MVH NB Hs).
    + intros evs Hs. exact (Hnoerr evs (step_up ms m evs SError HM MVH NB Hs)).
    + intros evs c' Hs. destruct (step_up ms m evs (SNext c') HM MVH NB Hs) as (ms' & m0 & Hs0 & -> & HM0).
      apply (IH evs (mkCfg ms' m0) Hs0).
      * exact HM0.
      * exact (not_reaches_step _ _ _ NR Hs).
      * exact (MREMAP_MOVE_OK_step _ _ _ MV Hs0).
Qed.
End Steps.

Theorem must_exit_relim : ltac2:(zQ "h00!ijb!lj3!lkb!jq8!q0!q7!lp5!lq0!jmb!jm2!ktd!lqe!lr9!mge!mj8!jo3>4segs@1$0$6>3cfg$7>1S@1$0@1$f@1$4#k0>1c$9>1L$5>0@2$e^1@1$c@1$b@1$8^2>0@1$3@3$a^6^5@2$2^2^3>0@3$d^7^6^4>0@4$1^7^8^6^5@4$1^8^9^7@2$2^5^6").
Proof.
  intros segs cfg S c L HLE NR MV Hme.
  exact (must_exit_relim_at segs cfg (vm_limit (m_vmmaps (cfg_model c))) L HLE S c Hme eq_refl NR MV).
Qed.

(* [comment removed for export] *)
Lemma init_config_relim : ltac2:(zQ "d0!q0!jo3!q7!mje!ijb!n1!mkc!ml0!lp5!jm2!mp0!mpd!lkb>4segs@1$4$8>2pc$6>2ph$7>2sp@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$a>4Lbig$2>6Lsmall$2>3inp$b@3$5$9@9$3^a^9^8^7^6^5^4^2^1@2$c^2@9$3^a^9^8^7^6^5^4^3^1").
Proof. intros. reflexivity. Qed.
Lemma init_config_limit : ltac2:(zQ "e0!q0!jo3!q7!ijb!n1!mkc!ml0!lp5!jmb!mje!mp0!mpd!lqe!lr9>4segs@1$3$7>2pc$5>2ph$6>2sp@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$a>3lim$2>3inp$b@3$4$2@1$d@1$c@1$8@9$9^9^8^7^6^5^4^3^2^1^2").
Proof. intros. reflexivity. Qed.

Corollary must_exit_in_scfg_relim : ltac2:(zQ "h10!q0!jo3!mq9!mr2!ijb!q7!mre!mkc!ngf!ml0!lp5!lq0!mje!mp0!mpd!mge!mj8>3cfg$b>1S@1$4@1$1@1$0#k0>3img$2>4Lbig$5>6Lsmall$5>2en$3>3inp$e>0@2$h0^3^4>0@5$8^8^4^6^3^2>0M2\3img$2P^7\4segs@1$4$a\2pc$7\2ph$9M3\2en$3P^7\2sp@1$1@1$0#k0\4brk0@1$1@1$0#k0\5mbase@1$1@1$0#k0\3rnd$d@3$f^7^h0@9$c^7^6^5^4^3^2^1^d^a>0@6$6^a^9^8^7^5^4@6$6^b^a^9^7^6^5").
Proof.
  intros cfg S [segs pc ph] Lbig Lsmall [sp brk0 mbase rnd] inp HLE NB MV Hme.
  unfold must_exit_in_scfg in *. unfold source_within_budget_scfg, run_scfg_budget_refused in NB.
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in NB |- *.
  apply must_exit_relim; [rewrite init_config_limit; exact HLE | exact NB | exact MV | exact Hme].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem MREMAP_MOVE_OK_of_WF : ltac2:(zQ "70!ijb!lp5!lq0!jmb!jm2!nn6!mge>4segs@1$0$1>3cfg$2>1c$4>0@1$5@1$3^1@3$6^4^3^2").
Proof. intros segs cfg c Hwf tr c' Hstar. apply MV_OK_wf. exact (star_cfg_WF segs cfg _ _ _ Hstar Hwf). Qed.

Theorem MREMAP_MOVE_OK_init : ltac2:(zQ "c0!q0!jo3!ijb!mkc!q7!ml0!lp5!lq0!mje!mp0!mpd!mge>4segs@1$2$6>3cfg$7>2pc$3>2ph$5>2sp@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$9>3lim$4>3inp$a@3$b^a^9@9$8^a^8^7^6^5^4^3^2^1").
Proof. intros. apply MREMAP_MOVE_OK_of_WF. apply init_config_WF. Qed.

Corollary must_exit_in_scfg_relim_closed : ltac2:(zQ "b0!q7!mre!ijb!q0!ngf!mq9!mr2!lq0!mpd!mj8!jo3>3cfg$7>1S@1$2@1$a@1$3#k0>3img$5>4Lbig$0>6Lsmall$0>2en$6>3inp$8>0@2$9^3^4>0@5$4^8^4^6^3^2>0@6$1^9^8^7^6^4^3@6$1^a^9^8^6^5^4").
Proof.
  intros cfg S img Lbig Lsmall en inp HLE NB Hme.
  apply (must_exit_in_scfg_relim cfg S img Lbig Lsmall en inp HLE NB); [|exact Hme].
  destruct img, en. apply MREMAP_MOVE_OK_init.
Qed.
(* [comment removed for export] *)
