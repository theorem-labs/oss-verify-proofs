(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhPieceP.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhPieceP.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhPieceP.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~ie4site06length37Corelib7Numbers7BinNumsnc1Zie7s_saved04bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~q95subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~v44expr06optionv48expr_eqbq96sg_getv44EVar37Corelib4Init5Logichm32eq04truenc4Nposq92Es89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hof5bindsv46edenotv43envv42ev35stdpp9bitvectorbdefinitionshv12bv04andb37Corelib4Init3Natiha3add36Stdlib5Lists4Listij37forallb37Corelib5Lists7ListDefil13nthil13seq3h5LinuxProcessSemantics5Riscv5Instrin67ALU_ADDie7s_fsizehof8CS_SLOTShof5FIXEDhofbsaved_countv44EAluv44ELit46Stdlib5Arith8PeanoNat3Natiu13ltb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jg36region04prod04pairie2vAie3ZLOie7CUR_OFFieaLOCALS_OFFie7USP_OFFie4vHDR46Stdlib6ZArith6BinInt1Zjoc3addjoc3sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~jr25pieceie7CUT1_PCie2PVie4cut1ie6cut1_Tie9cut1_regsie4endsjr27mkPiecehof7regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER5EhCut3CUTkk64cut1kk66cut1_T" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH. Import PIECE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEP.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceP.PIECEP.

(* [comment removed for export] *)
Definition cont_piece : ltac2:(zQ "50!q3!he!md!uc!jv5>2ph$0>2cf$0>2st$2>4fuel$1>2sg$3$4") := ltac2:(zQ "c0!q3!he!jve!kg8!knf!ko7!khd!ki9!md!uc!kj0!kjb\2ph$0\2cf$0\2st$8\4fuel$1\2sg$9@a$aN1^2@2$7^5^3@3$4^5^4^3$3$2@1$6^5@1$5^5@1$b^5^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

End PIECEP.
(* [comment removed for export] *)
