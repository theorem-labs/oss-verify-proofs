(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~of5piecem24true37Corelib4Init7Decimalu12D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_4e344~~~~~~vc2STm25falsem23natm24produ12D8u13Nil37Corelib4Init3Nathmcbof_num_uint37Corelib4Init6NumberhodbUIntDecimal02PV04cut104ends89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hs15PAD_Ths18PAD_regsof7mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~ii17regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~in14expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~ire5shapeireakeep_shapevc1Pm24bool37Corelib4Init5Logicji52eqof5pc_pvofapc_regionsofbpiece_checkirebshape_holdsvc2SHof8pc_entryof6pc_xknof6pc_xpcof8pc_xregsire9Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~jqb9COPY_SPECjqb9FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59890~~~~~~kg42STkg41Pkg42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59bf8~~~~~~km02STkm01Pkm02SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59f48~~~~~~krc2STkrc1Pkrc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_5a264~~~~~~lh82STlh81Plh82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_5a650~~~~~~ln42STln41Pln42SH07CUT1_PC06cut1_T09cut1_regshs17REG_reshs13RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_479e4~~~~~~lve2STirecresume_shapelve1Plve2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_4b770~~~~~~mma2STmma1Pmma2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_4e570~~~~~~ms62STms61Pms62SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_59a10~~~~~~ni22STni21Pni22SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2p_4e344.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+kuit8+in0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@1$2$0+kukv0").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!hk7!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+kukv0@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!jha!jhe!ta!jj9!jjf!jk7!jl4!jm2!jn1@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!jha!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!jn1>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4e344.

Module P2p_59890.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lpoi4+m0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0+lppm4").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!kkf!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lppm4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kl5!jhe!ta!jj9!jjf!jk7!jl4!jm2!kla@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kl5!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!kla>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59890.

Module P2p_59bf8.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lproc+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@1$2$0+lpsic").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!kqb!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lpsic@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kr1!jhe!ta!jj9!jjf!jk7!jl4!jm2!kr6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kr1!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!kr6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59bf8.

Module P2p_59f48.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lputc+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@1$2$0+lqgk0").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lg7!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqgk0@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lgd!jhe!ta!jj9!jjf!jk7!jl4!jm2!lh2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lgd!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lh2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59f48.

Module P2p_5a264.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lqhv8+l0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0+lqim4").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lm3!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqim4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lm9!jhe!ta!jj9!jjf!jk7!jl4!jm2!lme@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lm9!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lme>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5a264.

Module P2p_5a650.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lqlu4+k0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@1$2$0+lqmic").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lrf!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!hr5!hrb!ig2!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqmic@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "10!jgc$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ls5!jhe!ta!jj9!jjf!jk7!jl4!jm2!lsa@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ls5!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lsa>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5a650.

Module P2r_479e4.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+knpn8+m0@3$1$0-h0@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!lt9!lu1!luc!lv7!ih7!ir6!mk9@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "20!mkf!mk9@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mlf!jhe!ta!jj9!jjf!jk7!jl4!jm2!mm4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mlf!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!mm4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_479e4.

Module P2r_4b770.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+krng4+q0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!lt9!lu1!luc!lv7!ih7!ir6!mr5@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "20!mkf!mr5@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mrb!jhe!ta!jj9!jjf!jk7!jl4!jm2!ms0@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mrb!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!ms0>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4b770.

Module P2r_4e570.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+kulg4+in0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!lt9!lu1!luc!lv7!ih7!ir6!nh1@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "20!mkf!nh1@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nh7!jhe!ta!jj9!jjf!jk7!jl4!jm2!nhc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nh7!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!nhc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4e570.

Module P2r_59a10.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!jf$0") := ltac2:(zQ "40!le!na!o1!o7@4$3+lppq4+m0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@1$2$0Z").
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!lt9!lu1!luc!lv7!ih7!ir6!nmd@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Definition SH : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "20!mkf!nmd@1$0$1").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nn3!jhe!ta!jj9!jjf!jk7!jl4!jm2!nn8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nn3!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!nn8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59a10.
