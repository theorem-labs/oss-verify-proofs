(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/pieces/HP13.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/pieces/HP13.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces Require HP13.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSitem24boolm25false37Corelib4Init7Decimalpe2D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_65a04~~~~~~r92PHr92STm23natm24prodm24truepe2D8pe3Nil37Corelib4Init5Logichid2eq37Corelib4Init3Nathk7bof_num_uint37Corelib4Init6Numberhm8bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~hocbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hteacont_piecehte8shape_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ijd4expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_662ac~~~~~~ioa2PHioa2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_663fc~~~~~~iu12PHiu12ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_66618~~~~~~jj82PHjj82ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_667dc~~~~~~jof2PHjof2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_667fc~~~~~~ju62PHju62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_66a1c~~~~~~kjd2PHkjd2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_66a3c~~~~~~kp42PHkp42ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_66a80~~~~~~kub2PHkub2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP139P1c_66abc~~~~~~lk22PHlk22ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER8EhPieceP6PIECEPlp9acont_piece" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P1c_65a04.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_65a04.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!hg4!hg9!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_65a04.

Module P1c_662ac.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_662ac.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!it5!itb!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_662ac.

Module P1c_663fc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_663fc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jic!jj2!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_663fc.

Module P1c_66618.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_66618.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jo3!jo9!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_66618.

Module P1c_667dc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_667dc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jta!ju0!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_667dc.

Module P1c_667fc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_667fc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!kj1!kj7!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_667fc.

Module P1c_66a1c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_66a1c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!ko8!koe!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_66a1c.

Module P1c_66a3c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_66a3c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!ktf!ku5!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_66a3c.

Module P1c_66a80.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_66a80.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!lj6!ljc!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_66a80.

Module P1c_66abc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP13.P1c_66abc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!lod!lp3!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lt8!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_66abc.
(* [comment removed for export] *)
