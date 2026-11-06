(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_free_spec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_iface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."], [["0A"; "1list"; "1pair"; "1prod"; "2eq"; "3map"; "4Z"; "0LB"; "0LB'"; "5lbrm"; "6blk_slot"; "6block"; "7lb_remove"; "8cptr"; "9bptr"; ":In"]; [":NoDup"; ";Permutation"; "0b"; "0blk"; "0n"; "0p"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma lb_remove_lbrm : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_spec "Q6'1&;%211&>'6'@&=&5&:r4%349421%6251&?'3%12;:%221;(2r3%24?>91r2%446@21r5%:3721'4&<r6%2251&9%<4IH7C%=4?I1<%3251%83M51p0:1p0F1pQ:N1p2O1pQ<Q11p@Q31").
Proof. intros LB p A n.
intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
- pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
- tauto.
Qed.
Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.
Lemma lbrm_perm : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_spec "@'1&;%211'Ar3r2%33521&9r4%2214%3265%83:21p061pQ8<1pB<1p@=1").
Proof. intros LB LB' blk. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.
Lemma In_lbrm_perm : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_spec "E'1&;%211'Ar4r3%33521&?r2&9r5%2216%53;41%4239%73=91p031p0:1pQ6@1pQ8A1pBA1p@B1").
Proof. intros LB LB' blk b. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.
End CEIL_WRAP_1.
