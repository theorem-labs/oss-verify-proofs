(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m54aptrm56mstate46Stdlib6ZArith6BinInt1Zr33add01N37Corelib4Init9Datatypest43fstt44pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~v93rdvhc8pans_memt44boolr34landr33mult43sndm5ec_mmap_counterm53ctxr33eqb37Corelib4Init5Logichob3andhob2eqm5cget_meta_recm5aget_stridem5aenframe_atr32ler33subhob2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcF_malloc_enf~~~~~~hu68enf_off0m58fold_offm55havocr33div" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_off0 : ltac2:(zQ "40!h9!lf!q3!qa>1o$1>3st1$3>1b$2>6stride$0>3idx$0$0") := ltac2:(zQ "h10!h9!sb!t1!lf!uc!v2!hk3!hk9!hl4!hlb!hm2!hm8!q3!hme!hnf!qa!ho5\1o$3\3st1$f\1b$c\6stride$0\3idx$0=1q$0@2$1@3$b$2$0^3@2$1+h0@2$a^2^1M8\0$8$0@2$h0@5$6$3$7^6^5@4$5$2$0@3$4$2$0^4@2$1^1-3Z@2$9@1$d@1$e^5+vf@2$9@2$1@2$1@5$6$3$7^6^5@4$5$2$0@3$4$2$0^4@2$1^1-2@2$a+hg0@5$6$3$7^6^5@4$5$2$0@3$4$2$0^4@2$1@2$1^1-2+1+1+vf").

Definition enf_leaf : ltac2:(zQ "40!q3!h9!qa!lf>1o$3>3st1$2>1g$0>1b$0>3idx$1>1n$1>3st'$2>1p$0P") := ltac2:(zQ "h60!h9!q3!hpf!qa!sb!hq6!hqc!hrb!t1!hm2!uc!hm8!hs8!ht5!hta!v2!hu0!iib!lf!ij7!ik2!ika\1o$h2\3st1$3\1g$1\1b$1\3idx$0\1n$0\3st'$3\1p$1@2$h0$0\3off$0@2$2@2$dZ^1@2$2@2$d@2$4@2$4@2$9+h0^1^4+4@1$7@2$6^8^7@2$2@3$5$1^2@4$f$8$0@3$a$8$0^6@2$4@2$4@2$4@3$b$8$0^6+h0@2$9@1$7@2$6^8^7^5@2$9+h0^1@2$2@3$5$3^3@3$h4^2^4@3$a$3$1@5$c^8^7^5^4^1@2$2@3$5$1^2@3$b$3$1@5$c^8^7^5^4^1@3$5$0^1@2$h3@5$h1^9^8^6@1$7@2$6^8^7^5@2$h5@2$e@2$e@1$7@2$6^8^7+4^4+h0").

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.
(* [comment removed for export] *)
