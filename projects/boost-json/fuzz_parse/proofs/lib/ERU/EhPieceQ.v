(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/EhPieceQ.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/EhPieceQ.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhPieceQ.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~i94expr04bool46Stdlib5Arith8PeanoNat3Natnb3eqb36Stdlib5Lists4Listpc7existsb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~r95subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~hg46region89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~hke5shape37Corelib7Numbers7BinNumshpd1Z05falsepc7forallb04andb03fst3h5LinuxProcessSemantics5Riscv5Instrht75aluopht75mulophke3inb04negb03snd04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~ii55bindsi96kentryi99sym_statehpd4Npos35stdpp9bitvectorbdefinitionsip12bv37Corelib4Init5Logicir43andir42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~it54SEGS06optionir42ex3h5LinuxProcessSemantics5Riscv7Preludejib5bvmapi93envi92ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~jm57FPStatei92ebi96s_nextjm56fp_csrjm54mkstjm57seg_romip17Z_to_bv03nil04pair37Corelib4Init5Peanojv02lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~kgacexpr_vars_lti96edenoti94s_pc89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~kn17know_okkn17regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~kt36mstepshg43INVhg47outsidehg4aregions_okhg44went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~lk29mem_growspc2In04Somer96sg_get04None89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~lq75pc_pvlq7apc_regionslq78pc_entrylq75pc_sglq76pc_xknlq76pc_xpclq78pc_xregslq75piecelq78piece_okhke9Pgen_spechkebshape_holdsit59COPY_SPECit59FILL_SPEClq7bpiece_checki98expr_eqbr96esubst04consr95unifyhke6dom_inr9aunify_regsr9abind_cellsr9crematch_fromlq76set_sg37Corelib4Init3Natmv03add37Corelib5Lists7ListDefng93nthii58CS_SLOTS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~nj34sitei94EVarhke8slot_varng93mapng93seqht77ALU_ADDi94EAlui94ELitnj37s_fsizeii5bsaved_countnb3ltb03appmv03sub46Stdlib6ZArith6BinInt1Znu13addii58shape_okhkeastep_shapenj37CUT1_PCnj32PVnj34cut1nj36cut1_Tnj39cut1_regsii5acont_pieceii57regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTom34cut1om36cut1_T89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU8EhPieceP6PIECEPoqfacont_piece" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEQ.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceQ.PIECEQ.

Theorem Pcont_gen_of_check : ltac2:(zQ "h50!n5!he!ju5!i3!ihf!isf!me!oha!oi5!opd!oq5!ojd!nn3!mo2!ouf!ol8!og0!mkc!ogc!mm8!mn5>0$h3>0$h4>2ph$0>2cf$0>2st$c>4fuel$1>0@3$5$0@2$d@5$e^4^3^2^1@1$2@2$3$1$6@2$h0^4^2$4@7$h1@3$9^5^4^3$7@1$b^5@1$a^5@1$f^5$8@1$h2^3").
Proof.
  intros COPY FILL ph cf st fuel H.
  apply (Pgen_of_check_any COPY FILL (cont_piece ph cf st fuel []) (shape_ok ph st) (step_shape st) H).
  - intros n e Hin. destruct Hin.
  - destruct ph; vm_compute; reflexivity.
  - intros sg Hsg. eapply shape_ok_step_shape. exact Hsg.
Qed.

End PIECEQ.
