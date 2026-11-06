(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~p05piecem34true37Corelib4Init7Decimalu32D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_4b47c~~~~~~ve2STm35falsem33natm34produ32D8u33Nil37Corelib4Init3Nathmfbof_num_uint37Corelib4Init6Numberhp0bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hr44expr02PV04cut104ends89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~ih15PAD_Tih18PAD_regsp07mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~in27regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~is35shapeis3akeep_shapeve1Pm34bool37Corelib4Init5Logicjib2eqp05pc_pvp0apc_regionsp0bpiece_checkis3bshape_holdsve2SHp08pc_entryp06pc_xknp06pc_xpcp08pc_xregsis39Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jr19COPY_SPECjr19FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_4e980~~~~~~kgb2STkgb1Pkgb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_5994c~~~~~~km82STkm81Pkm82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_59bb8~~~~~~ks52STks51Pks52SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6eab0~~~~~~li22STli21Pli22SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6eb94~~~~~~lnf2STlnf1Plnf2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6ec90~~~~~~ltc2STltc1Pltc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2p_6edb4~~~~~~mj92STmj91Pmj92SH07CUT1_PC06cut1_T09cut1_regsih17REG_resih13RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2r_475a0~~~~~~ms42STis3cresume_shapems41Pms42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP039P2r_4810c~~~~~~nj12STnj11Pnj12SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2p_4b47c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+krkh0+o0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0+krpu0").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!hka!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+krpu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ji0!ji4!tc!jjf!jk5!jkd!jla!jm8!jn7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ji0!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!jn7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4b47c.

Module P2p_4e980.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+kuph4+in0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0+kupu0").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!kl7!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+kupu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kld!ji4!tc!jjf!jk5!jkd!jla!jm8!km2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kld!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!km2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4e980.

Module P2p_5994c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+lpou0+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0+lppu0").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!kr4!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+lppu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kra!ji4!tc!jjf!jk5!jkd!jla!jm8!krf@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kra!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!krf>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5994c.

Module P2p_59bb8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+lprkc+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0+lpsi4").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lh1!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+lpsi4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lh7!ji4!tc!jjf!jk5!jkd!jla!jm8!lhc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lh7!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!lhc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59bb8.

Module P2p_6eab0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muqk4+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0+muqp8").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lme!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+muqp8@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ln4!ji4!tc!jjf!jk5!jkd!jla!jm8!ln9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ln4!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!ln9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6eab0.

Module P2p_6eb94.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muri8+i0@3$1$0-h0@1$2$0+murnc").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!lsb!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+murnc@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lt1!ji4!tc!jjf!jk5!jkd!jla!jm8!lt6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lt1!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!lt6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6eb94.

Module P2p_6ec90.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+musi4+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@1$2$0+musq4").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!mi8!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+musq4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mie!ji4!tc!jjf!jk5!jkd!jla!jm8!mj3@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mie!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!mj3>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6ec90.

Module P2p_6edb4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+mutk8+j0@3$1$0-h0@3$1$0-h8@1$2$0+mutm4").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h30!tc!v9!mo5!hkf!hl7!o2!hld!hm4!hm9!ho1!hq5!hv9!ig1!ig5!igb!il3!ilc!im8!ir8@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+mutm4@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "10!jh2$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mob!ji4!tc!jjf!jk5!jkd!jla!jm8!mp0@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mob!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!mp0>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_6edb4.

Module P2r_475a0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+knlj4+m0@3$1$0-h0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v9!o2!tc!lf!mp6!nb!hl7!hld!hm4!hm9!ho1!hq5!hv9!ig1!mpf!mq7!mr2!mrd!im8!nh0@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "20!nh6!nh0@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ni6!ji4!tc!jjf!jk5!jkd!jla!jm8!nib@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ni6!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!nib>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_475a0.

Module P2r_4810c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+kogq0+i0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v9!o2!tc!lf!mp6!nb!hl7!hld!hm4!hm9!ho1!hq5!hv9!ig1!mpf!mq7!mr2!mrd!im8!nnd@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!jg9$0") := ltac2:(zQ "20!nh6!nnd@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!no3!ji4!tc!jjf!jk5!jkd!jla!jm8!no8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!no3!jnc!jk5!jkd!jo7!jp0!jp9!jq4!jv1!jve!no8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4810c.
