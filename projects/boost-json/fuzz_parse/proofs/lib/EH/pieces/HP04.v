(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~of5piece37Corelib4Init7Decimalta2D0m24true07CUT1_PCm23natm24prodta2D8ta3Nil37Corelib4Init3Nathhdbof_num_uint37Corelib4Init6NumberhjebUIntDecimal02PV06cut1_T09cut1_regs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hn97REG_reshn93RESof7mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ht64expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP049P2r_59cac~~~~~~ii32ST89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~in45shapein4cresume_shapeii31Pm24bool37Corelib4Init5Logicite2eqof5pc_pvofapc_regionsofbpiece_checkin4bshape_holdsii32SHof8pc_entryof6pc_xknof6pc_xpcof8pc_xregsin49Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~jm59COPY_SPECjm59FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP049P2r_5a0ec~~~~~~jre2STjre1Pjre2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP049P2r_5a310~~~~~~kha2STkha1Pkha2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP049P2r_5a6d8~~~~~~kn62STkn61Pkn62SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2r_59cac.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lpsk0+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v0!o1!v5!le!vc!na!hg5!hgb!hh2!hh7!hif!hl3!hm2!hm6!hme!hra!hs5!hsc!ihb!ime@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!ir9$0") := ltac2:(zQ "20!is2!ime@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!it2!it7!v5!iv2!iv8!jg0!jgd!jhb!jia@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!it2!jj0!iv8!jg0!jjb!jk4!jkd!jl8!jq4!jr1!jia>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59cac.

Module P2r_5a0ec.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lqgo0+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v0!o1!v5!le!vc!na!hg5!hgb!hh2!hh7!hif!hl3!hm2!hm6!hme!hra!hs5!hsc!ihb!kg9@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!ir9$0") := ltac2:(zQ "20!is2!kg9@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kgf!it7!v5!iv2!iv8!jg0!jgd!jhb!kh4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kgf!jj0!iv8!jg0!jjb!jk4!jkd!jl8!jq4!jr1!kh4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_5a0ec.

Module P2r_5a310.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lqiq4+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v0!o1!v5!le!vc!na!hg5!hgb!hh2!hh7!hif!hl3!hm2!hm6!hme!hra!hs5!hsc!ihb!km5@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!ir9$0") := ltac2:(zQ "20!is2!km5@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kmb!it7!v5!iv2!iv8!jg0!jgd!jhb!kn0@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kmb!jj0!iv8!jg0!jjb!jk4!jkd!jl8!jq4!jr1!kn0>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_5a310.

Module P2r_5a6d8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lqmmc+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v0!o1!v5!le!vc!na!hg5!hgb!hh2!hh7!hif!hl3!hm2!hm6!hme!hra!hs5!hsc!ihb!ks1@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!ir9$0") := ltac2:(zQ "20!is2!ks1@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ks7!it7!v5!iv2!iv8!jg0!jgd!jhb!ksc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ks7!jj0!iv8!jg0!jjb!jk4!jkd!jl8!jq4!jr1!ksc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_5a6d8.
