(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP03.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP03.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP03.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~p05piecem34true37Corelib4Init7Decimalu32D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_4b47c~~~~~~ve2STm35falsem33natm34produ32D8u33Nil37Corelib4Init3Nathmfbof_num_uint37Corelib4Init6Numberhp0bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hr44expr02PV04cut104ends89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~ih15PAD_Tih18PAD_regsp07mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~in27regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~is35shapeis3akeep_shapeve1Pm34bool37Corelib4Init5Logicjib2eqp05pc_pvp0apc_regionsp0bpiece_checkis3bshape_holdsve2SHp08pc_entryp06pc_xknp06pc_xpcp08pc_xregsis39Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jr19COPY_SPECjr19FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_4e980~~~~~~kgb2STkgb1Pkgb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_5994c~~~~~~km82STkm81Pkm82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_59bb8~~~~~~ks52STks51Pks52SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6eab0~~~~~~li22STli21Pli22SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6eb94~~~~~~lnf2STlnf1Plnf2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6ec90~~~~~~ltc2STltc1Pltc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6edb4~~~~~~mj92STmj91Pmj92SH07CUT1_PC06cut1_T09cut1_regsih17REG_resih13RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2r_475a0~~~~~~ms42STis3cresume_shapems41Pms42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2r_4810c~~~~~~nj12STnj11Pnj12SH89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTnoe4cut189OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6EhCut24CUT2nt05PAD_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_4b47coh51P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_4e980om01P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_5994coqb1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_59bb8ov61P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_6eab0pk11P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_6eb94poc1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_6ec90pt71P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2p_6edb4qi21Pnoe6cut1_Tnt03RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2r_475a0qne1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP039P2r_4810cqs91P" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceQ.PIECEQ. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceQ.PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2p_4b47c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_4b47c.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!hka!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+krpu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!olb!ji4!tc!jjf!jk5!jkd!jla!jm8!jn7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!olb!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!jn7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4b47c.

Module P2p_4e980.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_4e980.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!kl7!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+kupu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!oq6!ji4!tc!jjf!jk5!jkd!jla!jm8!km2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!oq6!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!km2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4e980.

Module P2p_5994c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_5994c.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!kr4!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+lppu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!ov1!ji4!tc!jjf!jk5!jkd!jla!jm8!krf@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ov1!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!krf>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5994c.

Module P2p_59bb8.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_59bb8.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lh1!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+lpsi4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!pjc!ji4!tc!jjf!jk5!jkd!jla!jm8!lhc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pjc!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!lhc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59bb8.

Module P2p_6eab0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_6eab0.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lme!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+muqp8@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!po7!ji4!tc!jjf!jk5!jkd!jla!jm8!ln9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!po7!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!ln9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6eab0.

Module P2p_6eb94.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_6eb94.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lsb!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+murnc@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!pt2!ji4!tc!jjf!jk5!jkd!jla!jm8!lt6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pt2!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!lt6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6eb94.

Module P2p_6ec90.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_6ec90.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!mi8!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+musq4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!qhd!ji4!tc!jjf!jk5!jkd!jla!jm8!mj3@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qhd!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!mj3>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6ec90.

Module P2p_6edb4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2p_6edb4.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!mo5!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ns8!igb!ogc!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+mutm4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!qm8!ji4!tc!jjf!jk5!jkd!jla!jm8!mp0@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qm8!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!mp0>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6edb4.

Module P2r_475a0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2r_475a0.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v9!o2!tc!lf!mp6!nb!hl7!hld!hm4!hm9!ho1!hq5!hv9!ig1!qmd!mq7!mr2!qn7!im8!nh0@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!qs4!ji4!tc!jjf!jk5!jkd!jla!jm8!nib@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qs4!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!nib>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_475a0.

Module P2r_4810c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP03.P2r_4810c.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v9!o2!tc!lf!mp6!nb!hl7!hld!hm4!hm9!ho1!hq5!hv9!ig1!qmd!mq7!mr2!qn7!im8!nnd@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!rgf!ji4!tc!jjf!jk5!jkd!jla!jm8!no8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!rgf!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!no8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4810c.
