(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhPieceQ.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhPieceQ.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhPieceQ.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~i94expr04bool46Stdlib5Arith8PeanoNat3Natnb3eqb36Stdlib5Lists4Listpc7existsb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~r95subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~hg45shape89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~hl26region37Corelib7Numbers7BinNumshpc1Z05falsepc7forallb04andb03fst3h5LinuxProcessSemantics5Riscv5Instrht65aluopht65mulophg43inb04negb03snd04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~ii45bindsi96kentryi99sym_statehpc4Npos35stdpp9bitvectorbdefinitionsiof2bv37Corelib4Init5Logicir23andir22eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~it34SEGS06optionir22ex3h5LinuxProcessSemantics5Riscv7Preludeji85bvmapi93envi92ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~jm27FPStatei92ebi96s_nextjm26fp_csrjm24mkstjm27seg_romiof7Z_to_bv03nil04pair37Corelib4Init5Peanojud2lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~kg7cexpr_vars_lti96edenoti94s_pc89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~kme7know_okkme7regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~kt06mstepshl23INVhl27outsidehl2aregions_okhl24went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~ljf9mem_growspc2In04Somer96sg_get04None89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~lq45pc_pvlq4apc_regionslq48pc_entrylq45pc_sglq46pc_xknlq46pc_xpclq48pc_xregslq45piecelq48piece_okhg49Pgen_spechg4bshape_holdsit39COPY_SPECit39FILL_SPEClq4bpiece_checki98expr_eqbr96esubst04consr95unifyhg46dom_inr9aunify_regsr9abind_cellsr9crematch_fromlq46set_sg37Corelib4Init3Natmuc3add37Corelib5Lists7ListDefng53nthii48CS_SLOTS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~nif4sitei94EVarhg48slot_varng53mapng53seqht67ALU_ADDnif7s_fsizeii4bsaved_counti94EAlui94ELitnb3ltb03appmuc3sub46Stdlib6ZArith6BinInt1Zntc3addii48shape_okhg4astep_shapenif7CUT1_PCnif2PVnif4cut1nif6cut1_Tnif9cut1_regsii4acont_pieceii47regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER5EhCut3CUTole4cut1ole6cut1_T89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER8EhPieceP6PIECEPoq9acont_piece" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEQ.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceQ.PIECEQ.

Theorem Pcont_gen_of_check : ltac2:(zQ "h50!n5!he!ju2!i3!ihe!isd!oh5!oi0!op7!opf!oj8!nme!mne!ou8!ol3!nvb!mk8!og7!mm4!mn1!me>0$h2>0$h3>2ph$0>2cf$0>2st$b>4fuel$1>0@3$5$0@2$c@5$d^4^3^2^1@1$2@2$3$1$h4@2$f^4^2$4@7$h0@3$8^5^4^3$6@1$a^5@1$9^5@1$e^5$7@1$h1^3").
Proof.
  intros COPY FILL ph cf st fuel H.
  apply (Pgen_of_check_any COPY FILL (cont_piece ph cf st fuel []) (shape_ok ph st) (step_shape st) H).
  - intros n e Hin. destruct Hin.
  - destruct ph; vm_compute; reflexivity.
  - intros sg Hsg. eapply shape_ok_step_shape. exact Hsg.
Qed.

End PIECEQ.
