(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hc4bptr37Corelib4Init9Datatypeslf4pairlf4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~o55blocklf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~t94cptr37Corelib4Init5Logichhe2eq37Corelib5Lists7ListDefhj83map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_free~~~~~~hl64lbrmo58blk_slot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~hq89lb_remove36Stdlib5Lists4Listhva2Inhva5NoDup36Stdlib7SortingbPermutationihcbPermutation" s.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lb_remove_lbrm : ltac2:(zQ "e0!h9!l8!n7!ne!sa!t2!hh7!hj2!hkf!hp5!hpd!hud!igd!ih3>2LB@1$5$4>1p$1>1A$0>1n$0>0@2$d$6@4$8$4$6$a^4>0@3$c@2$3@2$3$1$0$0@4$2@2$3$1$0$0@4$2$1$0^4^3^2^5@3$7@1$5$4@2$b^5^6@2$9^6@4$2@2$3$1$0$0@4$2$1$0^5^4^3").
Proof. intros LB p A n.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm : ltac2:(zQ "40!sa!t2!hp5!ij8>2LB@1$1$0>3LB'@1$1$0>3blk$0>0@3$3$0^3^2@3$3$0@2$2^4^2@2$2^3^2").
Proof. intros LB LB' blk. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm : ltac2:(zQ "50!sa!t2!hp5!igd!ij8>2LB@1$1$0>3LB'@1$1$0>3blk$0>1b$0>0@3$4$0^4^3>0@3$3$0^2@2$2^5^3@3$3$0^3@2$2^5^4").
Proof. intros LB LB' blk b. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.
End FP.
