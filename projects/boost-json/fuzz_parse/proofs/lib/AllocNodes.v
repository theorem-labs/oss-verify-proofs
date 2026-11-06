(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes Gap04 RefNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib4Init9Datatypesh84bool37Corelib7Numbers7BinNumsj74Nposj71Zh85falseh84true3h5LinuxProcessSemanticsfLinuxProcessSem3Runma9refusal_b3h5LinuxProcessSemanticsfLinuxProcessSem5Stateq25Modelq2cSyscallInputq28in_sysnoq28m_vmmaps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~vd8place_ok46Stdlib6ZArith6BinInt1Zhk22le35stdpp9bitvectorbdefinitionshm02bvhm0bbv_unsignedq26ENOMEMq29errno_rethm07Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ModelLevel.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {SC : StepCfg}.

  (* [comment removed for export] *)

  Lemma place_not_refusal : ltac2:(zQ "f0!h4!j0!l0!l7!lb!m3!p6!t0!t8!u7!v2!hj7!hla!hnd!ho3>1i$8>1m$7>1a@1$d@1$2#k0>2nZ$3>0@3$0$3@2$e@1$2#k0@1$9^4+te>0@3$0$1@3$b@1$a^4^3^2$5>0@2$cZ^3@3$0$1@3$6^7^6^5$4").
  Proof.
    intros i m a nZ Hno Hp HnZ. rewrite (refusal_b_mmap i m a Hno).
    apply bv_eqb_neq. intros ->.
    destruct (place_ok_unpack _ _ _ Hp) as (_ & _ & Htop & _).
    pose proof (alloc_top_lt (m_vmmaps m)) as Hlt.
    rewrite (errno_ret_unsigned ENOMEM) in Htop by (unfold ENOMEM; lia).
    unfold ENOMEM, alloc_top, stack_max_size, two_pow_64 in *.
    pose proof (word_unsigned_range (vm_init_sp (m_vmmaps m))). unfold two_pow_64 in *. lia.
  Qed.

  Lemma errno_is_refusal_mmap : ltac2:(zQ "c0!h4!j0!m3!l0!l7!p6!hp2!t0!t8!hpb!u7!ho3>1i$8>1m$7>0@3$0$4@2$b@1$3#k0@1$a^2+te@3$0$1@3$5^3^2@1$9$6$2").
  Proof. intros i m Hno. rewrite (refusal_b_mmap i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma errno_is_refusal_mprotect : ltac2:(zQ "c0!h4!j0!m3!l0!l7!p6!hp2!t0!t8!hpb!u7!ho3>1i$8>1m$7>0@3$0$4@2$b@1$3#k0@1$a^2+u2@3$0$1@3$5^3^2@1$9$6$2").
  Proof. intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma zero_not_refusal_mprotect : ltac2:(zQ "b0!h4!l0!j0!lb!l7!p6!t0!t8!u7!hq7!ho3>1i$7>1m$6>0@3$0$4@2$a@1$1#k0@1$8^2+u2@3$0$2@3$5^3^2@2$9@1$1#k0Z$3").
  Proof.
    intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_neq.
    intros E. apply (f_equal bv_unsigned) in E. rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. unfold ENOMEM, two_pow_64 in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma alloc_refusal_spurious {AF : AllocForced SC} : forall i m eff eff' m' evs',
    injected_family_off the_scfg i = true ->
    refusal_b i m (eff_ret eff) = true ->
    syscall_spec i m (Ok eff' m' evs') ->
    refusal_b i m (eff_ret eff') = false ->
    spurious_refusal_cfg the_scfg i m eff.
  Proof.
    intros i m eff eff' m' evs' Hoff Hr Hspec Hnr. split; [exact Hoff|]. split; [exact Hr|].
    nexists eff', m', evs'. auto.
  Qed.
End ModelLevel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : list Segment.
Context {SC : StepCfg} {AF : AllocForced SC}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.
(* [comment removed for export] *)
