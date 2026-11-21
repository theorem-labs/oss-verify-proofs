(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/EhPieceP.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/EhPieceP.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhPieceP.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~ie4site06length37Corelib7Numbers7BinNumsnd1Zie7s_saved04bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~qa5subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~v54expr06optionv58expr_eqbqa6sg_getv54EVar37Corelib4Init5Logichm42eq04truend4Nposqa2Esv56edenotv53envv52ev89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~hq45binds35stdpp9bitvectorbdefinitionshv32bv04andb37Corelib4Init3Natihc3add36Stdlib5Lists4Listij57forallb37Corelib5Lists7ListDefil33nthil33seq3h5LinuxProcessSemantics5Riscv5Instrin87ALU_ADDv54EAluv54ELitie7s_fsizehq48CS_SLOTShq45FIXEDhq4bsaved_count46Stdlib5Arith8PeanoNat3Natiu33ltb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jg56region04prod04pairie2vAie3ZLOie7CUR_OFFieaLOCALS_OFFie7USP_OFFie4vHDR46Stdlib6ZArith6BinInt1Zjoe3addjoe3sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~jr45pieceie7CUT1_PCie2PVie4cut1ie6cut1_Tie9cut1_regsie4endsjr47mkPiecehq47regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTkk94cut1kk96cut1_T" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEP.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP.

(* [comment removed for export] *)
Definition cont_piece : ltac2:(zQ "50!q4!he!ud!me!jv8>2ph$0>2cf$0>2st$3>4fuel$1>2sg$2$4") := ltac2:(zQ "c0!q4!he!ud!kg1!kgb!ko3!kob!ki0!kic!me!kj3!kje\2ph$0\2cf$0\2st$9\4fuel$1\2sg$2@a$aN1^2@2$8^5^3@3$5^5^4^3$4$3@1$7^5@1$6^5@1$b^5^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

End PIECEP.
(* [comment removed for export] *)
