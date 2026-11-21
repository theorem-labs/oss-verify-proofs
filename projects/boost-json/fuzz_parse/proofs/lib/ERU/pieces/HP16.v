(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP16.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP16.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP16.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite37Corelib4Init7Decimalp02D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59db4~~~~~~qb2PHqb2STm34boolm35falsem33natm34prodm34truep02D8p03Nil37Corelib4Init5Logichif2eq37Corelib4Init3Nathk9bof_num_uint37Corelib4Init6NumberhmabUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hoe4expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~htbbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~iieacont_pieceiie8shape_ok99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59dcc~~~~~~ioe2PHioe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59df0~~~~~~iu62PHiu62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59e04~~~~~~jje2PHjje2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59ea0~~~~~~jp62PHjp62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59f58~~~~~~jue2PHjue2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59f68~~~~~~kk62PHkk62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_59f9c~~~~~~kpe2PHkpe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_5aa74~~~~~~kv62PHkv62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP169P2c_5b690~~~~~~lke2PHlke2ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU8EhPieceP6PIECEPlq6acont_piece" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2c_59db4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59db4.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!v7!vc!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59db4.

Module P2c_59dcc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59dcc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!ita!iu0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59dcc.

Module P2c_59df0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59df0.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!jj2!jj8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59df0.

Module P2c_59e04.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59e04.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!joa!jp0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59e04.

Module P2c_59ea0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59ea0.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!ju2!ju8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59ea0.

Module P2c_59f58.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59f58.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kja!kk0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59f58.

Module P2c_59f68.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59f68.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kp2!kp8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59f68.

Module P2c_59f9c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_59f9c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!kua!kv0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_59f9c.

Module P2c_5aa74.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_5aa74.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!lk2!lk8!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5aa74.

Module P2c_5b690.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP16.P2c_5b690.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q6!lpa!lq0!hg1!hg8!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!lu6!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5b690.
(* [comment removed for export] *)
