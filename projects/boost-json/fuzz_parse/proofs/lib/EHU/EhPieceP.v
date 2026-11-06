(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~ie4site06length37Corelib7Numbers7BinNumsnd1Zie7s_saved04bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~qa5subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~v54expr06optionv58expr_eqbqa6sg_getv54EVar37Corelib4Init5Logichm42eq04truend4Nposqa2Esv56edenotv53envv52ev89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~hq45binds35stdpp9bitvectorbdefinitionshv32bv04andb37Corelib4Init3Natihc3add36Stdlib5Lists4Listij57forallb37Corelib5Lists7ListDefil33nthil33seq3h5LinuxProcessSemantics5Riscv5Instrin87ALU_ADDv54EAluv54ELitie7s_fsizehq48CS_SLOTShq45FIXEDhq4bsaved_count46Stdlib5Arith8PeanoNat3Natiu33ltb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jg56region04prod04pairie2vAie3ZLOie7CUR_OFFieaLOCALS_OFFie7USP_OFFie4vHDR46Stdlib6ZArith6BinInt1Zjoe3addjoe3sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~jr45pieceie7CUT1_PCie2PVie4cut1ie6cut1_Tie9cut1_regsie4endsjr47mkPiecehq47regions" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEP.

(* [comment removed for export] *)
Definition CS_SLOTS : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N8@3$1$0N9@3$1$0Nh2@3$1$0Nh3@3$1$0Nh4@3$1$0Nh5@3$1$0Nh6@3$1$0Nh7@3$1$0Nh8@3$1$0Nh9@3$1$0Nha@3$1$0Nhb@1$2$0").
(* [comment removed for export] *)
Definition saved_count : ltac2:(zQ "20!he!me>2st$1$0") := ltac2:(zQ "40!n5!p6!pa!me\2st$3@2$0$1@1$2^1").

(* [comment removed for export] *)
Definition binds : ltac2:(zQ "40!q4!he!ud!hja>2sg$2>1n$1>1e$3$0") := ltac2:(zQ "80!hja!hk1!hk9!q4!he!hl4!ud!hld\2sg$6\1n$4\1e$0M1\1x@1$1$0$3@2$5^3^2\2e'$0@2$2^1^2@2$2@1$7^2^1").

Lemma binds_sound : ltac2:(zQ "d0!hn8!q4!he!hne!ho4!hob!ud!hp0!hp9!hpf!hja!hua!ih0>1E$8>2sg$6>1n$2>1e$a>0@3$0$1@3$b^3^2^1$3@3$0@1$c@1$4#k0@2$9@2$5^5^4^3@2$7^5^2").
Proof.
  intros E sg n e H. unfold binds in H. destruct (sg_get sg n) as [e'|] eqn:Hg.
  - apply expr_eqb_eq in H. subst e'. apply Es_bound. exact Hg.
  - apply expr_eqb_eq in H. subst e. rewrite (Es_free E sg n Hg). reflexivity.
Qed.

Definition FIXED : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N0@3$1$0N1@3$1$0N2@3$1$0N3@3$1$0N4@3$1$0Nh4@3$1$0Nh5@3$1$0Nh6@3$1$0Nh7@3$1$0Nh8@3$1$0Nh9@3$1$0Nha@3$1$0Nhb@3$1$0Nhc@3$1$0Nhd@3$1$0Nhe@3$1$0Nhf@1$2$0").

(* [comment removed for export] *)
Definition shape_ok : ltac2:(zQ "30!q4!ud!me>2ph$0>2st$2>2sg$1$0") := ltac2:(zQ "h40!he!hld!hua!ih6!q4!iie!ik8!ima!in1!ipc!ud!iq7!iqe!hja!ir5!me!irf!isb!it4!ive\2ph$4\2st$f\2sg$a@2$3@2$3@2$3@3$2^1Ni0@1$1Nme@3$2^1Ni2@3$b$9@1$1Ni2@1$c@1$e^2@3$6$0\1k$0=1n$0@2$5Ni0@4$7$0^1$h0N0@3$2^3^1M4\0$4$d@2$h3^2@1$h2^4@1$1@2$5Nmf^2@1$1^1@2$8N0Nc@3$6$0\1n$0@3$2^2^1@1$1^1$h1").                 (* [comment removed for export] *)

Definition regions : ltac2:(zQ "30!q4!h8!jk5>2ph$0@1$1$2") := ltac2:(zQ "f0!p6!jkf!hja!jl5!i3!jlb!jm0!q4!i9!jm6!jn0!jnd!jo7!jq6!jqd\2ph$7@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$6@2$e@2$d@1$b^1+ii0$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5@1$a^1+l0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$9+im0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$cZ+p0@1$8@2$1@2$1$2$0$0").

Definition cont_piece : ltac2:(zQ "50!q4!he!ud!me!jv8>2ph$0>2cf$0>2st$3>4fuel$1>2sg$2$4") := ltac2:(zQ "c0!q4!he!ud!kg1!kgb!kh0!kh7!ki0!kic!me!kj3!kje\2ph$0\2cf$0\2st$9\4fuel$1\2sg$2@a$aN1^2@2$8^5^3@3$5^5^4^3$4$3@1$7^5@1$6^5@1$b^5^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

End PIECEP.
(* [comment removed for export] *)
