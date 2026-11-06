(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~p05piece37Corelib4Init7Decimaltc2D0m34true07CUT1_PCm33natm34prodtc2D8tc3Nil37Corelib4Init3Nathhfbof_num_uint37Corelib4Init6Numberhk0bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hm44expr02PV06cut1_T09cut1_regs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hs87REG_reshs83RESp07mkPiece99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_4ba60~~~~~~ii62ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~in85shapein8cresume_shapeii61Pm34bool37Corelib4Init5Logiciu32eqp05pc_pvp0apc_regionsp0bpiece_checkin8bshape_holdsii62SHp08pc_entryp06pc_xknp06pc_xpcp08pc_xregsin89Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jma9COPY_SPECjma9FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_4ea60~~~~~~js42STjs41Pjs42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_59a60~~~~~~ki12STki11Pki12SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_59ca4~~~~~~kne2STkne1Pkne2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6eb28~~~~~~ktb2STktb1Pktb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6ebfc~~~~~~lj82STlj81Plj82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6ed2c~~~~~~lp52STlp51Plp52SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP049P2r_6edf4~~~~~~lv22STlv21Plv22SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2r_4ba60.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+krpv4+o0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!in2@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!in2@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!it7!itc!v7!iv7!ivd!jg5!jh2!ji0!jif@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!it7!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!jif>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4ba60.

Module P2r_4ea60.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+kupv4+in0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!kh0@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!kh0@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kh6!itc!v7!iv7!ivd!jg5!jh2!ji0!khb@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kh6!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!khb>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4ea60.

Module P2r_59a60.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+lppv4+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!kmd@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!kmd@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kn3!itc!v7!iv7!ivd!jg5!jh2!ji0!kn8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kn3!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!kn8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59a60.

Module P2r_59ca4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+lpsj8+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!ksa@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!ksa@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kt0!itc!v7!iv7!ivd!jg5!jh2!ji0!kt5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kt0!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!kt5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59ca4.

Module P2r_6eb28.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muqrc+j0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!li7@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!li7@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lid!itc!v7!iv7!ivd!jg5!jh2!ji0!lj2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lid!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!lj2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6eb28.

Module P2r_6ebfc.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+murp0+i0@3$1$0-h0@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!lo4@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!lo4@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!loa!itc!v7!iv7!ivd!jg5!jh2!ji0!lof@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!loa!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!lof>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6ebfc.

Module P2r_6ed2c.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muss0+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!lu1@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!lu1@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lu7!itc!v7!iv7!ivd!jg5!jh2!ji0!luc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lu7!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!luc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6ed2c.

Module P2r_6edf4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!k0$0") := ltac2:(zQ "40!lf!nb!o2!o8@4$3+muto8+j0@3$1$0-h0@3$1$0-h8@1$2$0Z").
Definition P : ltac2:(zQ "10!t4$0") := ltac2:(zQ "h40!v2!o2!v7!lf!ve!nb!hg7!hgd!hh4!hh9!hj1!hl5!hq9!hr1!hr5!hrd!iga!ih5!ihc!mje@a$h2N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h1$h3$d$4@1$f$2@1$e$2$h0@1$1@2$7$6$c").
Definition SH : ltac2:(zQ "10!ire$0") := ltac2:(zQ "20!is7!mje@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mk4!itc!v7!iv7!ivd!jg5!jh2!ji0!mk9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mk4!jj5!ivd!jg5!jk0!jk9!jl2!jld!jqa!jr7!mk9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_6edf4.
