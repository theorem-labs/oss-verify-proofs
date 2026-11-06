(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSitem24boolm25false37Corelib4Init7Decimalpe2D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5f83c~~~~~~r92PHr92STm23natm24prodm24truepe2D8pe3Nil37Corelib4Init5Logichid2eq37Corelib4Init3Nathk7bof_num_uint37Corelib4Init6Numberhm8bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~hocbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hteacont_piecehte8shape_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ijd4expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5f8ec~~~~~~ioa2PHioa2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5fa0c~~~~~~iu12PHiu12ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5fbd0~~~~~~jj82PHjj82ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5fc54~~~~~~jof2PHjof2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_5fdc4~~~~~~ju62PHju62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_60304~~~~~~kjd2PHkjd2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_603b4~~~~~~kp42PHkp42ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_60434~~~~~~kub2PHkub2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP109P1c_604a8~~~~~~lk22PHlk22ST" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P1c_5f83c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvnt0+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!hg4!hg9!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5f83c.

Module P1c_5f8ec.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvoo0+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!it5!itb!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5f8ec.

Module P1c_5fa0c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvpq0+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jic!jj2!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5fa0c.

Module P1c_5fbd0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvrm4+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jo3!jo9!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5fbd0.

Module P1c_5fc54.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvru8+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!jta!ju0!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5fc54.

Module P1c_5fdc4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lvtl8+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!kj1!kj7!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_5fdc4.

Module P1c_60304.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgip8+j0@3$1$0-h0@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!ko8!koe!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_60304.

Module P1c_603b4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgjk8+j0@3$1$0-h0@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!ktf!ku5!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_603b4.

Module P1c_60434.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgjs8+j0@3$1$0-h0@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!lj6!ljc!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_60434.

Module P1c_604a8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgkjc+j0@3$1$0-h0@1$2$0Z").
Definition PH : ltac2:(zQ "10!of$0") := ltac2:(zQ "10!p6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r4!lod!lp3!of!p6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_604a8.
(* [comment removed for export] *)
