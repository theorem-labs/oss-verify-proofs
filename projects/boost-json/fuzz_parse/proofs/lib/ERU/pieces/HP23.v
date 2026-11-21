(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP23.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP23.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP23.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite37Corelib4Init7Decimalp02D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_66cc8~~~~~~qb2PHqb2STm34boolm35falsem33natm34prodm34truep02D8p03Nil37Corelib4Init5Logichif2eq37Corelib4Init3Nathk9bof_num_uint37Corelib4Init6NumberhmabUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hoe4expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~htbbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~iieacont_pieceiie8shape_ok99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_66d30~~~~~~ioe2PHioe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_66eac~~~~~~iu62PHiu62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_66f78~~~~~~jje2PHjje2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_672a8~~~~~~jp62PHjp62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_67368~~~~~~jue2PHjue2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_675c4~~~~~~kk62PHkk62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_6eb28~~~~~~kpe2PHkpe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_6ebfc~~~~~~kv62PHkv62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP239P2c_6ed2c~~~~~~lke2PHlke2ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU8EhPieceP6PIECEPlq6acont_piece" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2c_66cc8.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_66cc8.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!v7!vc!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66cc8.

Module P2c_66d30.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_66d30.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!ita!iu0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66d30.

Module P2c_66eac.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_66eac.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!jj2!jj8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66eac.

Module P2c_66f78.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_66f78.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!joa!jp0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66f78.

Module P2c_672a8.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_672a8.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!ju2!ju8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_672a8.

Module P2c_67368.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_67368.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kja!kk0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_67368.

Module P2c_675c4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_675c4.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kp2!kp8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_675c4.

Module P2c_6eb28.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_6eb28.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kua!kv0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_6eb28.

Module P2c_6ebfc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_6ebfc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!lk2!lk8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_6ebfc.

Module P2c_6ed2c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP23.P2c_6ed2c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!lpa!lq0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_6ed2c.
(* [comment removed for export] *)
