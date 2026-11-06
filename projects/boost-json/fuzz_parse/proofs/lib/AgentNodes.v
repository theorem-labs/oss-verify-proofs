(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AgentLib Scfg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmapk14Nonek14Somem2h3Build_machine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~vc6fp_csrvc7fp_regs37Corelib4Init5Logichka2eqk14boolk14listk14truehka1I3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehne7Segmentm29MachineOkm2afetch_wordm28is_ecallm2emachine_resultm24step79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes4FPX1~~~~~~hva5ependvc4getrvc4mksthf2BVhf4BvWfm26ms_gpr46Stdlib6ZArith6BinInt1Zim83addim86of_nathf7Z_to_bvm2cms_read_byte69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7FileSim~~~~~~iqa3mrbvc7seg_romm2h0ms_writable_bytem25wviewm28set_gpr03h5LinuxProcessSemanticsfLinuxProcessSem3Runjhch0advance_past_svcvc6regupdvc6v_addik13nilk14prodk13natjhccapply_effect3h5LinuxProcessSemanticsfLinuxProcessSem5Statejp27MemCopyjp29mkEffectUjp2cwith_copyins" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition epend : ltac2:(zQ "51!h9!jc!l9!p9!sf&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0$3") := ltac2:(zQ "91!h9!jc!l9!t7!te!u5!sf!hj7!hk0&>0@1$1@1$0#k0@1$2@1$1@1$0#8\4regs@2$6@1$0#5@1$1@1$0#k0\2pc@1$1@1$0#k0\3mem~0\3rom~0\2x8@1$1@1$0#k0@8$5^5@1$8?2fx^4@2$4@1$1@1$0#k0^1@1$3@1$1@1$0#k0@1$7?2fx^3^2").

Lemma step_ecall_epend : ltac2:(zQ "h61!h9!jc!l9!hle!p9!te!hm4!hmb!hn2!hn9!hr3!hre!hsa!ht7!hu2!hv3!sf!ijc!ik5!ikc!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$7$a>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$c^6^4@2$5@1$1@1$0#i0^1>0@3$3$6@1$d^2$8@3$3@1$e$4@2$f^8@5$h3?2fx^7^6^5^4@2$b$4@5$h1^7^6^5^4@2$h2^7@3$h4@1$0#5+h1Kv$9@2$h5@1$0#5+h1").
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma ms_gpr_epend0 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N0@2$8^5@3$9@1$0#5+aKv$3@2$a@1$0#5+a").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N1@2$8^5@3$9@1$0#5+bKv$3@2$a@1$0#5+b").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N2@2$8^5@3$9@1$0#5+cKv$3@2$a@1$0#5+c").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : ltac2:(zQ "90!h9!jc!hn9!hle!io0!io7!il3!il8!ip1@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N3Kd@3$6@1$0#5+dKv$2@2$7@1$0#5+d@1$1@1$0#5"). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : ltac2:(zQ "90!h9!jc!hn9!hle!io0!io7!il3!il8!ip1@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N4Kd@3$6@1$0#5+eKv$2@2$7@1$0#5+e@1$1@1$0#5"). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : ltac2:(zQ "90!h9!jc!hn9!hle!io0!io7!il3!il8!ip1@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N5Kd@3$6@1$0#5+fKv$2@2$7@1$0#5+f@1$1@1$0#5"). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N3@2$8^5@3$9@1$0#5+dKv$3@2$a@1$0#5+d").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N4@2$8^5@3$9@1$0#5+eKv$3@2$a@1$0#5+e").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : ltac2:(zQ "b1!h9!jc!l9!hn9!hle!ilf!sf!ijc!ik5!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$5@5$7^5^4^3^2^1N5@2$8^5@3$9@1$0#5+fKv$3@2$a@1$0#5+f").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

Lemma ms_read_byte_epend : ltac2:(zQ "b0!h9!jc!l9!hmb!hle!hr3!ipb!sf!ijc!iu4!iub>4segs@1$3$5>4regs@2$7@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2x8@1$1@1$0#k0@3$4>4addr@1$1@1$0#k0@1$2@1$1@1$0#8@1$6@5$8^4^3^2@1$a^5^1@2$9^5^2").
Proof. reflexivity. Qed.

Lemma ms_writable_byte_epend : ltac2:(zQ "a1!h9!jc!l9!hmb!hle!hr3!iv5!jg9!sf!ijc&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$3$5>4regs@2$8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0@3$4>4addr@1$1@1$0#k0@1$2@1$1@1$0#8@2$6^6@5$9^5^4^3^2^1@2$7^6^3").
Proof. reflexivity. Qed.

Lemma adv_set_epend : ltac2:(zQ "f1!h9!jc!l9!hn9!hle!p9!jh1!jk8!sf!ijc!ikc!jld!jm6!il3!il8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1v@1$1@1$0#k0@3$4$5@1$7@2$6@5$9^6^5^4^3^2^1@5$a?2fx@3$b^6@3$d@1$0#5+aKv$3@2$e@1$0#5+a^1@2$c^5+4^4^3").
Proof. intros. unfold epend. apply adv_set. Qed.

Lemma adv_eff_ret_epend : ltac2:(zQ "h53!h9!jc!jmf!jn5!l9!hmb!jnc!hn9!hle!p9!jk8!jo2!js0!jsb!sf!ijc!ikc!jld!jm6!il3!il8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$e@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0@3$8$9@1$a@2$b@5$f^6^5^4^3^2@6$d^1@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~2~2@1$2$c@1$2@2$3@1$1@1$0#k0$6@5$h0?2fx@3$h1^6@3$h3@1$0#5+aKv$7@2$h4@1$0#5+a^1@2$h2^5+4^4^3").
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_eff_ret_copyins_epend : ltac2:(zQ "h63!h9!jc!jmf!jn5!hmb!jnc!l9!hn9!hle!p9!jk8!jo2!js0!jsb!jt8!sf!ijc!ikc!jld!jm6!il3!il8&>0@1$1@1$0#k0@1$6@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$f@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>5reads@1$4@2$3@1$1@1$0#k0$5@3$8$9@1$a@2$b@5$h0^7^6^5^4^3@2$e^1@6$d^2@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~2~2@1$2$c@1$2@2$3@1$1@1$0#k0$5@5$h1?2fx@3$h2^7@3$h4@1$0#5+aKv$7@2$h5@1$0#5+a^2@2$h3^6+4^5^4").
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.

(* [comment removed for export] *)
Lemma rz_sys {SC : StepCfg} : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End FPX1.
(* [comment removed for export] *)
