(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec
  XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto
  EhX_plain EhCut EhMatch EhPiece.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~ie4site06length37Corelib7Numbers7BinNumsnc1Zie7s_saved04bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~q95subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~v44expr06optionv48expr_eqbq96sg_getv44EVar37Corelib4Init5Logichm32eq04truenc4Nposq92Es89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hof5bindsv46edenotv43envv42ev35stdpp9bitvectorbdefinitionshv12bv04andb37Corelib4Init3Natiha3add36Stdlib5Lists4Listij37forallb37Corelib5Lists7ListDefil13nthil13seq3h5LinuxProcessSemantics5Riscv5Instrin67ALU_ADDie7s_fsizehof8CS_SLOTShof5FIXEDhofbsaved_countv44EAluv44ELit46Stdlib5Arith8PeanoNat3Natiu13ltb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jg36region04prod04pairie2vAie3ZLOie7CUR_OFFieaLOCALS_OFFie7USP_OFFie4vHDR46Stdlib6ZArith6BinInt1Zjoc3addjoc3sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~jr25pieceie7CUT1_PCie2PVie4cut1ie6cut1_Tie9cut1_regsie4endsjr27mkPiecehof7regions" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEP.

(* [comment removed for export] *)
Definition CS_SLOTS : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N8@3$1$0N9@3$1$0Nh2@3$1$0Nh3@3$1$0Nh4@3$1$0Nh5@3$1$0Nh6@3$1$0Nh7@3$1$0Nh8@3$1$0Nh9@3$1$0Nha@3$1$0Nhb@1$2$0").
(* [comment removed for export] *)
Definition saved_count : ltac2:(zQ "20!he!md>2st$1$0") := ltac2:(zQ "40!n4!p5!p9!md\2st$3@2$0$1@1$2^1").

(* [comment removed for export] *)
Definition binds : ltac2:(zQ "40!q3!he!uc!hj9>2sg$2>1n$1>1e$3$0") := ltac2:(zQ "80!hj9!hk0!hk8!q3!he!hl3!uc!hlc\2sg$6\1n$4\1e$0M1\1x@1$1$0$3@2$5^3^2\2e'$0@2$2^1^2@2$2@1$7^2^1").

Lemma binds_sound : ltac2:(zQ "d0!hn7!q3!he!hnd!ho3!hoa!uc!ht4!htd!hu6!huc!hj9!ige>1E$9>2sg$6>1n$2>1e$b>0@3$0$1@3$7^3^2^1$3@3$0@1$c@1$4#k0@2$a@2$5^5^4^3@2$8^5^2").
Proof.
  intros E sg n e H. unfold binds in H. destruct (sg_get sg n) as [e'|] eqn:Hg.
  - apply expr_eqb_eq in H. subst e'. apply Es_bound. exact Hg.
  - apply expr_eqb_eq in H. subst e. rewrite (Es_free E sg n Hg). reflexivity.
Qed.

Definition FIXED : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N0@3$1$0N1@3$1$0N2@3$1$0N3@3$1$0N4@3$1$0Nh4@3$1$0Nh5@3$1$0Nh6@3$1$0Nh7@3$1$0Nh8@3$1$0Nh9@3$1$0Nha@3$1$0Nhb@3$1$0Nhc@3$1$0Nhd@3$1$0Nhe@3$1$0Nhf@1$2$0").

(* [comment removed for export] *)
Definition shape_ok : ltac2:(zQ "30!q3!md!uc>2ph$0>2st$1>2sg$2$0") := ltac2:(zQ "h40!he!hlc!ht4!ih4!q3!iic!ik6!im8!imf!ipa!iq5!md!uc!iqf!irb!is4!it3!ita!hj9!ivc\2ph$4\2st$b\2sg$c@2$3@2$3@2$3@3$2^1Ni0@1$1Nme@3$2^1Ni2@3$h0$9@1$1Ni2@1$h1@1$a^2@3$6$0\1k$0=1n$0@2$5Ni0@4$7$0^1$dN0@3$2^3^1M4\0$4$h2@2$h3^2@1$f^4@1$1@2$5Nmf^2@1$1^1@2$8N0Nc@3$6$0\1n$0@3$2^2^1@1$1^1$e").                 (* [comment removed for export] *)

Definition regions : ltac2:(zQ "30!q3!h8!jk3>2ph$0@1$1$2") := ltac2:(zQ "f0!p5!jkd!hj9!jl3!i3!jl9!jle!q3!i9!jm4!jme!jnb!jo5!jq4!jqb\2ph$7@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$6@2$e@2$d@1$b^1+ii0$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5@1$a^1+l0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$9+im0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$cZ+p0@1$8@2$1@2$1$2$0$0").

Definition cont_piece : ltac2:(zQ "50!q3!he!md!uc!jv5>2ph$0>2cf$0>2st$2>4fuel$1>2sg$3$4") := ltac2:(zQ "c0!q3!he!jve!kg8!kgd!kh4!khd!ki9!md!uc!kj0!kjb\2ph$0\2cf$0\2st$8\4fuel$1\2sg$9@a$aN1^2@2$7^5^3@3$4^5^4^3$3$2@1$6^5@1$5^5@1$b^5^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

End PIECEP.
(* [comment removed for export] *)
