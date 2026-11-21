(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/pieces/HP23.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/pieces/HP23.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces Require HP23.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSite37Corelib4Init7Decimalof2D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66a1c~~~~~~qa2PHqa2STm24boolm25falsem23natm24prodm24trueof2D8of3Nil37Corelib4Init5Logichid2eq37Corelib4Init3Nathk7bof_num_uint37Corelib4Init6Numberhm8bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~hocbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hteacont_piecehte8shape_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ijd4expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66a3c~~~~~~ioa2PHioa2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66a80~~~~~~iu12PHiu12ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66abc~~~~~~jj82PHjj82ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66ad0~~~~~~jof2PHjof2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66b38~~~~~~ju62PHju62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66b4c~~~~~~kjd2PHkjd2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66bb8~~~~~~kp42PHkp42ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP239P2c_66bd0~~~~~~kub2PHkub2ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER8EhPieceP6PIECEPlk2acont_piece" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhPieceP.PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2c_66a1c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66a1c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!v5!va!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66a1c.

Module P2c_66a3c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66a3c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!it5!itb!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66a3c.

Module P2c_66a80.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66a80.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jic!jj2!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66a80.

Module P2c_66abc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66abc.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jo3!jo9!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66abc.

Module P2c_66ad0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66ad0.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jta!ju0!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66ad0.

Module P2c_66b38.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66b38.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!kj1!kj7!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66b38.

Module P2c_66b4c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66b4c.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!ko8!koe!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66b4c.

Module P2c_66bb8.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66bb8.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!ktf!ku5!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66bb8.

Module P2c_66bd0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP23.P2c_66bd0.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!lj6!ljc!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!lo1!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_66bd0.
(* [comment removed for export] *)
