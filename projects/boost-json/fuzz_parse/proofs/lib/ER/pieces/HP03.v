(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/pieces/HP03.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/pieces/HP03.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP EhCut2 EhPieceQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces Require HP03.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~04site37Corelib7Numbers7BinNumsk51Z37Corelib4Init9Datatypesm24consm23nil06mkSite89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~of5piecem24true37Corelib4Init7Decimalu12D099OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_4e344~~~~~~vc2STm25falsem23natm24produ12D8u13Nil37Corelib4Init3Nathmcbof_num_uint37Corelib4Init6NumberhodbUIntDecimal02PV04cut104ends89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hs15PAD_Ths18PAD_regsof7mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~ii17regions89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~in14expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~ire5shapeireakeep_shapevc1Pm24bool37Corelib4Init5Logicji52eqof5pc_pvofapc_regionsofbpiece_checkirebshape_holdsvc2SHof8pc_entryof6pc_xknof6pc_xpcof8pc_xregsire9Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~jqb9COPY_SPECjqb9FILL_SPEC99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59890~~~~~~kg42STkg41Pkg42SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59bf8~~~~~~km02STkm01Pkm02SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_59f48~~~~~~krc2STkrc1Pkrc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_5a264~~~~~~lh82STlh81Plh82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2p_5a650~~~~~~ln42STln41Pln42SH07CUT1_PC06cut1_T09cut1_regshs17REG_reshs13RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_479e4~~~~~~lve2STirecresume_shapelve1Plve2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_4b770~~~~~~mma2STmma1Pmma2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_4e570~~~~~~ms62STms61Pms62SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP039P2r_59a10~~~~~~ni22STni21Pni22SH89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER5EhCut3CUTnne4cut189OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6EhCut24CUT2nrf5PAD_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_4e344og31P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_59890okd1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_59bf8op71P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_59f48ou11P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_5a264pib1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2p_5a650pn51Pnne6cut1_Tnrf3RES99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2r_479e4pt01P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2r_4b770qha1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2r_4e570qm41P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6pieces4HP039P2r_59a10qqe1P" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhPieceQ.PIECEQ. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhPieceQ.PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module P2p_4e344.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_4e344.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!hk7!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+kukv0@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!ok8!jhe!ta!jj9!jjf!jk7!jl4!jm2!jn1@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ok8!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!jn1>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4e344.

Module P2p_59890.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_59890.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!kkf!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lppm4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!op2!jhe!ta!jj9!jjf!jk7!jl4!jm2!kla@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!op2!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!kla>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59890.

Module P2p_59bf8.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_59bf8.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!kqb!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lpsic@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!otc!jhe!ta!jj9!jjf!jk7!jl4!jm2!kr6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!otc!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!kr6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59bf8.

Module P2p_59f48.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_59f48.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lg7!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqgk0@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!pi6!jhe!ta!jj9!jjf!jk7!jl4!jm2!lh2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pi6!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lh2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_59f48.

Module P2p_5a264.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_5a264.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lm3!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqim4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!pn0!jhe!ta!jj9!jjf!jk7!jl4!jm2!lme@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pn0!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lme>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5a264.

Module P2p_5a650.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2p_5a650.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h30!ta!v7!lrf!hkc!hl4!o1!hla!hm1!hm6!hne!hq2!hr1!nr7!hrb!nva!igb!ih7!im6!ir6@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+lqmic@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Lemma chk : ltac2:(zQ "90!pra!jhe!ta!jj9!jjf!jk7!jl4!jm2!lsa@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pra!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!lsa>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_5a650.

Module P2r_479e4.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2r_479e4.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!prf!lu1!luc!ps9!ih7!ir6!mk9@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Lemma chk : ltac2:(zQ "90!qh5!jhe!ta!jj9!jjf!jk7!jl4!jm2!mm4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qh5!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!mm4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_479e4.

Module P2r_4b770.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2r_4b770.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!prf!lu1!luc!ps9!ih7!ir6!mr5@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Lemma chk : ltac2:(zQ "90!qlf!jhe!ta!jj9!jjf!jk7!jl4!jm2!ms0@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qlf!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!ms0>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4b770.

Module P2r_4e570.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2r_4e570.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!prf!lu1!luc!ps9!ih7!ir6!nh1@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Lemma chk : ltac2:(zQ "90!qq9!jhe!ta!jj9!jjf!jk7!jl4!jm2!nhc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qq9!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!nhc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_4e570.

Module P2r_59a10.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.pieces.HP03.P2r_59a10.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!t2$0") := ltac2:(zQ "h40!v7!o1!ta!le!lt0!na!hl4!hla!hm1!hm6!hne!hq2!hr1!prf!lu1!luc!ps9!ih7!ir6!nmd@a$h1N2@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$3$4@1$1$3@1$h0$h3$c$4@1$e$2@1$d$2$f@1$1@2$7$6$h2").
Lemma chk : ltac2:(zQ "90!qv3!jhe!ta!jj9!jjf!jk7!jl4!jm2!nn8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qv3!jn6!jjf!jk7!jo1!joa!jp3!jpe!jua!jv7!nn8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2r_59a10.
