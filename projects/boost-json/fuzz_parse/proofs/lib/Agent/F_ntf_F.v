(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstatehcarecord_seqhc7set_seqhc7upd_ctx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7F_ntf_B~~~~~~o48fm_factshch0c_free_meta_headhc4mctxhc5s_ctx37Corelib4Init5Logicv22eqhc4aptrhc4optr46Stdlib6ZArith6BinInt1Zhh92le37Corelib4Init9Datatypeshj74boolhj75falsev23andv23iffhcfsc_in_seq_rangehh93addhh94landhh92lt25stdpp9countablehp3bZ_countable35stdpp7numbers1Zhr36eq_dechj74list04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~htcaunmap_seqshtc5zeroshch1set_unmap_seq_map25stdpp4baseika5empty35stdpp9bitvectorbdefinitionsilf2bv25stdpp4gmapio24gmapio2agmap_empty" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition seq_st : ltac2:(zQ "20!h9!la>2ns$0>2sc$0>2st$1$1") := ltac2:(zQ "50!h9!la!m3!n0!na\2ns$0\2sc$0\2st$1@2$2^2@2$4@1$3^3^1").

Lemma fm_facts_ctx : ltac2:(zQ "90!s4!sf!u3!ua!hg6!hgb!la!hh2!na>2st$6>1f>1x$2$2>1g$5>0@3$4$7@1$1@1^2@1$3^3@1$1@1$3^3>0@2$0^4^2@2$0@2$8^4^5^3").
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.

Lemma seq_range_test : ltac2:(zQ "b0!hj1!hkf!hl7!hm0!hg6!hm6!h9!hmc!hne!ho5!hod>2sc$6>0@2$3@2$0Z^1@2$0^1+jf@2$5@2$a+hf@2$9@2$8^2-7+vvvvvvvvvvvvvvvf@3$4$1@1$7^2$2").
Proof. intros sc.
  intros Hsc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold sc_in_seq_range.
  destruct (Z.lt_ge_cases sc 7) as [L|GE].
  - replace ((sc + -7) mod 2 ^ 64) with (sc + -7 + 2^64).
    2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
    destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try discriminate; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unmap_seqs_empty : ltac2:(zQ "h00!h9!hq4!hs4!hse!hg6!ht6!ihe!iic!u3!la!ij5!na!il6!inc!ioe!ip6>2st$9@3$4@1$3@1$d@1$5#8@1$6@2$b\1c$8@2$a@2$c@4$e$0$2$1$0@4$f$0$2$1$0^1^1@1$7Ni0").
Proof. intros st. reflexivity. Qed.
