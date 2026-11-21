(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP04.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP04.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP04.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~p05piece37Corelib4Init7Decimaltc2D0m34true07CUT1_PCm33natm34prodtc2D8tc3Nil37Corelib4Init3Nathhfbof_num_uint37Corelib4Init6Numberhk0bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hm44expr02PV06cut1_T09cut1_regs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hs87REG_reshs83RESp07mkPiece99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_4ba60~~~~~~ii62ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~in85shapein8cresume_shapeii61Pm34bool37Corelib4Init5Logiciu32eqp05pc_pvp0apc_regionsp0bpiece_checkin8bshape_holdsii62SHp08pc_entryp06pc_xknp06pc_xpcp08pc_xregsin89Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jma9COPY_SPECjma9FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_4ea60~~~~~~js42STjs41Pjs42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_59a60~~~~~~ki12STki11Pki12SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_59ca4~~~~~~kne2STkne1Pkne2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6eb28~~~~~~ktb2STktb1Pktb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6ebfc~~~~~~lj82STlj81Plj82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6ed2c~~~~~~lp52STlp51Plp52SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6edf4~~~~~~lv22STlv21Plv22SH89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTmkf6cut1_T89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6EhCut24CUT2mp33RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_4ba60mt61P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_4ea60ni11P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_59a60nmc1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_59ca4nr71P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_6eb28og21P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_6ebfcokd1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_6ed2cop81P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP049P2r_6edf4ou31P" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceQ.PIECEQ. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceQ.PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2r_4ba60.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_4ba60.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!in2@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!nhc!itc!v7!iv7!ivd!jg5!jh2!ji0!jif@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nhc!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!jif>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4ba60.

Module P2r_4ea60.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_4ea60.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!kh0@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!nm7!itc!v7!iv7!ivd!jg5!jh2!ji0!khb@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nm7!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!khb>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4ea60.

Module P2r_59a60.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_59a60.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!kmd@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!nr2!itc!v7!iv7!ivd!jg5!jh2!ji0!kn8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nr2!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!kn8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59a60.

Module P2r_59ca4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_59ca4.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!ksa@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!nvd!itc!v7!iv7!ivd!jg5!jh2!ji0!kt5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nvd!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!kt5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59ca4.

Module P2r_6eb28.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_6eb28.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!li7@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!ok8!itc!v7!iv7!ivd!jg5!jh2!ji0!lj2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ok8!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!lj2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6eb28.

Module P2r_6ebfc.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_6ebfc.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!lo4@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!op3!itc!v7!iv7!ivd!jg5!jh2!ji0!lof@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!op3!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!lof>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6ebfc.

Module P2r_6ed2c.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_6ed2c.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!lu1@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!ote!itc!v7!iv7!ivd!jg5!jh2!ji0!luc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ote!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!luc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6ed2c.

Module P2r_6edf4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP04.P2r_6edf4.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!mo9!hrd!iga!msf!ihc!mje@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!pi9!itc!v7!iv7!ivd!jg5!jh2!ji0!mk9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pi9!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!mk9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6edf4.
