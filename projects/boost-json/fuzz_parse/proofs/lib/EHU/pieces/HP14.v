(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSitem34boolm35false37Corelib4Init7Decimalpf2D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_67368~~~~~~ra2PHra2STm33natm34prodm34truepf2D8pf3Nil37Corelib4Init5Logichif2eq37Corelib4Init3Nathk9bof_num_uint37Corelib4Init6NumberhmabUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hoe4expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~htbbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~iieacont_pieceiie8shape_ok99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_675c4~~~~~~ioe2PHioe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_6eab0~~~~~~iu62PHiu62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_6eb94~~~~~~jje2PHjje2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_6ec90~~~~~~jp62PHjp62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P1c_6edb4~~~~~~jue2PHjue2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P2c_475a0~~~~~~kk62PHkk62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P2c_4810c~~~~~~kpe2PHkpe2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P2c_4ba60~~~~~~kv62PHkv62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP149P2c_4ea60~~~~~~lke2PHlke2ST" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P1c_67368.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+mnivc+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!hg6!hgb!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_67368.

Module P1c_675c4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+mnll8+n0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!ita!iu0!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_675c4.

Module P1c_6eab0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muqk4+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0+muqp8").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!jj2!jj8!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_6eab0.

Module P1c_6eb94.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muri8+i0@3$1$0-h0@1$2$0+murnc").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!joa!jp0!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_6eb94.

Module P1c_6ec90.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+musi4+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@1$2$0+musq4").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!ju2!ju8!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_6ec90.

Module P1c_6edb4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+mutk8+j0@3$1$0-h0@3$1$0-h8@1$2$0+mutm4").
Definition PH : ltac2:(zQ "10!p0$0") := ltac2:(zQ "10!p7$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!kja!kk0!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P1c_6edb4.

Module P2c_475a0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+knlj4+m0@3$1$0-h0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!kp2!kp8!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_475a0.

Module P2c_4810c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+kogq0+i0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!kua!kv0!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_4810c.

Module P2c_4ba60.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+krpv4+o0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!lk2!lk8!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_4ba60.

Module P2c_4ea60.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+kupv4+in0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!r5!lpa!lq0!p0!p7!hh0!o2!hh6!hhd!hi4!hi9!hk3!hlb!hnf!ht3!ihf!in4!io2@3$b$3@2$f@5$h0$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$e@2$h1$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_4ea60.
(* [comment removed for export] *)
