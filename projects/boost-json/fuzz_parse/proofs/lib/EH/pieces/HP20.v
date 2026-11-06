(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSite37Corelib4Init7Decimalof2D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_60304~~~~~~qa2PHqa2STm24boolm25falsem23natm24prodm24trueof2D8of3Nil37Corelib4Init5Logichid2eq37Corelib4Init3Nathk7bof_num_uint37Corelib4Init6Numberhm8bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~hocbpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~hteacont_piecehte8shape_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ijd4expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_603b4~~~~~~ioa2PHioa2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_60434~~~~~~iu12PHiu12ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_604a8~~~~~~jj82PHjj82ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_60694~~~~~~jof2PHjof2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_6073c~~~~~~ju62PHju62ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_61780~~~~~~kjd2PHkjd2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_617c4~~~~~~kp42PHkp42ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_619e4~~~~~~kub2PHkub2ST99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP209P2c_61acc~~~~~~lk22PHlk22ST" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2c_60304.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgip8+j0@3$1$0-h0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!v5!va!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_60304.

Module P2c_603b4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgjk8+j0@3$1$0-h0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!it5!itb!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_603b4.

Module P2c_60434.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgjs8+j0@3$1$0-h0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jic!jj2!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_60434.

Module P2c_604a8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgkjc+j0@3$1$0-h0@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jo3!jo9!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_604a8.

Module P2c_60694.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgmi8+i0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!jta!ju0!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_60694.

Module P2c_6073c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mgmt0+i0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!kj1!kj7!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_6073c.

Module P2c_61780.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mhnh4+k0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!ko8!koe!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_61780.

Module P2c_617c4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mhnl8+k0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!ktf!ku5!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_617c4.

Module P2c_619e4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mhpn8+k0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!lj6!ljc!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_619e4.

Module P2c_61acc.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+mhqm0+k0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition PH : bool := true.
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "h20!q5!lod!lp3!vf!hg6!hge!o1!hh4!hhb!hi2!hi7!hk1!hl9!hnd!hsf!ii3!ij1!io2@3$b$3@2$e@5$f$1$4$2@1$c@1$d@1$9@1$0@1$0@1$0$a@1$6@2$7$5$h1@2$h0$1$2$8").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
End P2c_61acc.
(* [comment removed for export] *)
