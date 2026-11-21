(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP02.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP02.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP02.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~05piece37Corelib4Init7Decimalkb2D037Corelib7Numbers7BinNumsm61Z37Corelib4Init9Datatypeso34conso33nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~q87FREE_PCq8cPoolPristineo33nato34prodo34truekb2D8kb3Nil37Corelib4Init3Nathi2bof_num_uint37Corelib4Init6Numberhk3bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hm74expr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~hr42PVq8eAFTER_CATCH_PCq83F5aq84FR_Tq87FR_regsq86REG_ct07mkPiece99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029F5a_pr_hi~~~~~~ij41Po34bool37Corelib4Init5Logicioc2eq05pc_pv0apc_regions0bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~is6bshape_holdsij42SH08pc_entry06pc_xkn06pc_xpc08pc_xregsis69Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jl29COPY_SPECjl29FILL_SPECo35false99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029F5a_pr_lo~~~~~~jr41Pjr42SHq88PoolIdleq86DONE_Tq89DONE_regsq83F5bq88REG_done99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP026F5b_id~~~~~~kjc1Pkjc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP026F5b_pr~~~~~~kp01Pkp02SHq83F5p99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP023F5p~~~~~~kua1Pkua2SHhr44sitehr46mkSite99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029P1h_475ac~~~~~~lkd2SThr44endsq85HF_PCq84HF_Tq87HF_regsq85cut1c89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceP6PIECEP~~~~~~ls87regionsis65shapeis6akeep_shapelkd1Plkd2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029P2k_475ac~~~~~~mjb2STq85PAD_Tq88PAD_regsmjb1Pmjb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029P2p_47538~~~~~~mqb2SThr44cut1mqb1Pmqb2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029P2p_48080~~~~~~nh02STnh01Pnh02SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP029P2p_4b3e0~~~~~~nmd2STnmd1Pnmd2SH89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6EhCut24CUT2nsa3F5ansa4FR_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029F5a_pr_hioh51P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029F5a_pr_loom01Pnsa6DONE_Tnsa3F5b99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP026F5b_idorc1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP026F5b_prpg41Pnsa3F5p99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP023F5ppl31Pnsa4HF_Tnsa5cut1c99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029P1h_475acpq91Pnsa5PAD_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029P2k_475acpvd1P89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTqk84cut199OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029P2p_47538qoa1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029P2p_48080qt51P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP029P2p_4b3e0ri01P" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceQ.PIECEQ. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceQ.PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module F5a_pr_hi.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.F5a_pr_hi.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!m1!nf!pb!q2!ua!v4!hg3!hg9!hh0!hh7!hhc!hj4!hl8!hqc!hv4!hva!og6!ogd!ih8!ii2!iib@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$8$e$4$h2@1$h1$5$h3@1$3@2$7$6$d").
Lemma chk : ltac2:(zQ "90!olb!io5!hh0!iq0!iq6!iqd!ir9!jgc!jhb@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!olb!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!jhb>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_pr_hi.

Module F5a_pr_lo.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.F5a_pr_lo.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!m1!nf!pb!q2!ua!v4!jqc!hg3!hg9!hh7!hhc!hj4!hl8!hqc!hv4!hva!og6!ogd!ih8!ii2!iib@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$6$e$4$h2@1$h1$5$h3@1$3@2$8$7$d").
Lemma chk : ltac2:(zQ "90!oq6!io5!hh0!iq0!iq6!iqd!ir9!jgc!kg5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!oq6!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!kg5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_pr_lo.

Module F5b_id.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.F5b_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!m1!q2!nf!hva!kgb!pb!hg3!hg9!hh7!hhc!hj4!hl8!hqc!hv4!oqb!khf!or5!kj1!iib@a$h2N1@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$2$3@1$1$2@1$h0$4$d$3$f@1$e$4$h1@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!ovf!io5!hh0!iq0!iq6!iqd!ir9!jgc!koa@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ovf!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!koa>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5b_id.

Module F5b_pr.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.F5b_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!m1!q2!nf!hva!v4!pb!hg3!hg9!hh7!hhc!hj4!hl8!hqc!hv4!oqb!khf!or5!kj1!iib@a$h2N1@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$2$3@1$1$2@1$h0$4$d$3$f@1$e$4$h1@1$1@2$7$6$c").
Lemma chk : ltac2:(zQ "90!pk7!io5!hh0!iq0!iq6!iqd!ir9!jgc!kte@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pk7!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!kte>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5b_pr.

Module F5p.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.F5p.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h40!m1!nf!pb!q2!hva!hg3!hg9!hh7!hhc!hj4!hl8!hqc!hv4!oqb!khf!pkc!ua!kgb!kj1!iib@a$h3N1@1$9@1$a@1$7@1$0@1$0@1$0$8@3$2$1$h0@3$2$1$4@1$3$1$f$c$4$e@1$d$h1$h2@1$3@2$6$5$b").
Lemma chk : ltac2:(zQ "90!pp3!io5!hh0!iq0!iq6!iqd!ir9!jgc!lj5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pp3!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!lj5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5p.

Module P1h_475ac.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.P1h_475ac.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!jqc!m1!lp9!hg3!q2!hg9!hh7!hhc!hj4!hl8!hqc!hv4!lpf!lq7!pp8!lr6!pq0!iib!mge@a$h1N1@1$8@1$9@1$6@1$1@1$1@1$1$7@2$c$0$2@2$h0$0$2$b$d$f$e@1$h2$0@1$4@2$5$3$a").
Lemma chk : ltac2:(zQ "90!puf!io5!hh0!iq0!iq6!iqd!ir9!jgc!mj5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!puf!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!mj5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P1h_475ac.

Module P2k_475ac.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.P2k_475ac.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h20!hh0!m1!mo7!hg3!q2!hg9!hh7!hhc!hj4!hl8!hqc!hv4!lpf!pv4!mp5!pq0!iib!mge@a$h0N1@1$8@1$9@1$6@1$1@1$1@1$1$7@2$c$0$2@2$f$0$2$b+knll0@1$e+1$d@1$h1$0@1$4@2$5$3$a").
Lemma chk : ltac2:(zQ "90!qk3!io5!hh0!iq0!iq6!iqd!ir9!jgc!mq5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qk3!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!mq5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2k_475ac.

Module P2p_47538.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.P2p_47538.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!hh0!m1!mv7!jqc!hg3!q2!hg9!hh7!hhc!hj4!hl8!hqc!hv4!qo2!lpf!pv4!mp5!iib!mge@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+knli0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!qt0!io5!hh0!iq0!iq6!iqd!ir9!jgc!nga@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qt0!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!nga>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_47538.

Module P2p_48080.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.P2p_48080.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!hh0!m1!nlc!jqc!hg3!q2!hg9!hh7!hhc!hj4!hl8!hqc!hv4!qo2!lpf!pv4!mp5!iib!mge@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+kogoc@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!rhb!io5!hh0!iq0!iq6!iqd!ir9!jgc!nm7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!rhb!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!nm7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_48080.

Module P2p_4b3e0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP02.P2p_4b3e0.
(* [comment removed for export] *)
Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!hh0!m1!nr9!jqc!hg3!q2!hg9!hh7!hhc!hj4!hl8!hqc!hv4!qo2!lpf!pv4!mp5!iib!mge@a$h1N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$e$0$2@3$d$0$3$2$c+krpu0@1$h0Z$f@1$h2$0@1$5@2$6$4$b").
Lemma chk : ltac2:(zQ "90!rm6!io5!hh0!iq0!iq6!iqd!ir9!jgc!ns4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!rm6!ji1!iq6!iqd!jib!jj3!jjb!jk5!jp2!jpf!ns4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4b3e0.
