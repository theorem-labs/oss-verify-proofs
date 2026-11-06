(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib4Init9Datatypesk63nil37Corelib7Numbers7BinNumsm41Z06mkSite37Corelib4Init7Decimalo92D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5dea0~~~~~~q42PHq42STk64boolk65falsek63natk64prodk64trueo92D8o93Nil37Corelib4Init5Logichi82eq37Corelib4Init3Nathk2bof_num_uint37Corelib4Init6Numberhm3bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ho74expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~ht4bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~ii7acont_pieceii78shape_okk64cons99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e044~~~~~~ioe2PHioe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e0e8~~~~~~iu62PHiu62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e248~~~~~~jje2PHjje2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e678~~~~~~jp62PHjp62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e82c~~~~~~jue2PHjue2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5e9f4~~~~~~kk62PHkk62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5ec48~~~~~~kpe2PHkpe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5edf8~~~~~~kv62PHkv62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP189P2c_5f000~~~~~~lke2PHlke2ST" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2c_5dea0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "30!le!nd!o1@4$2+ltuj4+i0@1$0$1Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!v0!v5!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5dea0.

Module P2c_5e044.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+ltvt8+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!ita!iu0!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e044.

Module P2c_5e0e8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+lugnc+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!jj2!jj8!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e0e8.

Module P2c_5e248.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+luhtc+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!joa!jp0!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e248.

Module P2c_5e678.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+lumgc+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!ju2!ju8!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e678.

Module P2c_5e82c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+luns0+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!kja!kk0!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e82c.

Module P2c_5e9f4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+lupo8+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!kp2!kp8!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5e9f4.

Module P2c_5ec48.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+lurtc+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!kua!kv0!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5ec48.

Module P2c_5edf8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+lutoc+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!lk2!lk8!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5edf8.

Module P2c_5f000.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!nd!io7!le!o1@4$3+luvp4+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!pf!lpa!lq0!va!hg1!hg9!le!hgf!hh6!hhd!hi2!hjc!hl4!hn8!hsc!ih8!imd!inb@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_5f000.
(* [comment removed for export] *)
