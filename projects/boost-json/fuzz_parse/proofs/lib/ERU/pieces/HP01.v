(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/pieces/HP01.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/pieces/HP01.v. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces Require HP01.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~05piece37Corelib7Numbers7BinNumskb1Z37Corelib4Init9Datatypesm83app89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~o66kentrym84prodo64exprm83nil37Corelib4Init7Decimalu82D0m84consm84pair89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~hh13ZLOhh16img_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hm27th_geomhm2ath_scratchm84Nonem83natu82D8u83Nil37Corelib4Init3Natht5bof_num_uint37Corelib4Init6Numberhv6bUIntDecimalo63SSRo65saddro66sentryhh12NXhh12PVhh17newh_knhh12vAhm27AA_regshm27F1_regshm22SNhm2eopnew_frame_knhm2cth_frames_kn07mkPiece46Stdlib6ZArith6BinInt1Zip53sub99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP012F1~~~~~~ir41Pm84boolm84true37Corelib4Init5Logicjgc2eq05pc_pv0apc_regions0bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~jk6bshape_holdsir42SH08pc_entry06pc_xkn06pc_xpc08pc_xregsjk69Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jt29COPY_SPECjt29FILL_SPECm85falsehh17CUT1_PChh16cut1_Thh19cut1_regshm23F2hhm26HFB_knhm23PVBhm26REG_thhm2aglobals_knjk65shapejk6bthrow_shape99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP015F2h_0~~~~~~kpe1Pkpe2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP015F2h_s~~~~~~kv11Pkv12SHhh13lithm27F2_regshm27POOLHDRhm28PoolIdlehm28PoolLivehm26REG_tphm24TH_Thm27pool_kn99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_0_id~~~~~~lp61Plp62SHhm2cPoolPristine99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_0_pr~~~~~~lvc1Plvc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_s_id~~~~~~ml21Pml22SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_s_pr~~~~~~mq81Pmq82SHhm22F3hm26REG_hfo64EVar99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP012F3~~~~~~nh51Pnh52SHhm27FREE_PChm2eAFTER_CATCH_PChm23F5ahm24FR_Thm27FR_regshm26REG_ct99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP019F5a_id_hi~~~~~~nq61Pnq62SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP019F5a_id_lo~~~~~~nvd1Pnvd2SH89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTol46cut1_T89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6EhCut24CUT2op83F2h99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP015F2h_0otb1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP015F2h_spi21Pop84TH_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP018F2p_0_idpn11P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP018F2p_0_prprb1P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP018F2p_s_idqg51P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP018F2p_s_prqkf1Pop82F399OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP012F3qpf1Pop83F5aop84FR_T99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP019F5a_id_hiqv21P99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6pieces4HP019F5a_id_lorjd1P" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH. Import PIECE. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceP.PIECEP. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhPieceQ.PIECEQ. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhPieceQ.PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module F1.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F1.
(* [comment removed for export] *)

End F1.

Module F2h_0.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2h_0.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h70!kic!ve!o0!u2!m4!sb!kj4!hg3!hs4!t4!hsa!hsf!hu7!igb!tb!ooe!kk9!ot4!kld!km7!kme!kn8!ioc@a$h6N3@1$c@1$d@1$a@1$1@1$1@1$1$b@3$7$4$6@1$3$4@1$h1$0$h3$6@1$h0$0@3$2$5@1$f$0@3$2$5$h2@1$h5+1$h4@1$3@2$9$8$e").
Lemma chk : ltac2:(zQ "90!phd!ive!jg5!ji0!ji6!jid!jj9!joc!kub@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!phd!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!kub>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_0.

Module F2h_s.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2h_s.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h80!ve!o0!kic!u2!m4!sb!kj4!hg3!hs4!t4!jg5!hsa!hsf!hu7!igb!tb!ooe!kk9!ot4!kld!km7!kme!kn8!ioc@a$h7N3@1$d@1$e@1$b@1$0@1$0@1$0$c@3$7$4$6@1$3$4@1$h2$a$h4$6@1$h1$2@3$1$5@1$h0$2@3$1$5$h3@1$h6+1$h5@1$3@2$9$8$f").
Lemma chk : ltac2:(zQ "90!pm4!ive!jg5!ji0!ji6!jid!jj9!joc!lje@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pm4!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!lje>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_s.

Module F2p_0_id.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2p_0_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i30!hs4!o0!hg3!kic!u2!ve!tb!sb!t4!m4!kj4!lk4!hrd!hga!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!ooe!kk9!lkb!kld!ll6!km7!lm1!lmd!ln9!pm9!kn8!lob!ioc@a$i2N3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$h2+pohh0@1$h8@1$bZ@1$4$h4@3$hf$3Z$hc$h5@1$c$h3@3$2$0N2$hb$a@1$h7$3@3$1$7@1$h6$3@3$1$7$h9@3$1$7@1$i0+1@1$i1$hd$he@3$2@2$8$0$6@4$d$0$6N2@1$b$ha@1$4@2$8$0$6").
Lemma chk : ltac2:(zQ "90!pr6!ive!jg5!ji0!ji6!jid!jj9!joc!lu6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!pr6!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!lu6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_id.

Module F2p_0_pr.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2p_0_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i30!hs4!o0!hg3!kic!u2!ve!tb!sb!t4!m4!kj4!lk4!hrd!hga!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!ooe!kk9!lkb!kld!ll6!km7!lmd!luc!ln9!pm9!kn8!lob!ioc@a$i2N3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$h2+pohh0@1$h8@1$bZ@1$4$h4@3$hf$3Z$hd$h5@1$c$h3@3$2$0N2$hb$a@1$h7$3@3$1$7@1$h6$3@3$1$7$h9@3$1$7@1$i0+1@1$i1$hc$he@3$2@2$8$0$6@4$d$0$6N2@1$b$ha@1$4@2$8$0$6").
Lemma chk : ltac2:(zQ "90!qg0!ive!jg5!ji0!ji6!jid!jj9!joc!mkc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qg0!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mkc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_pr.

Module F2p_s_id.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2p_s_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i40!hs4!o0!hg3!u2!ve!tb!sb!kic!t4!m4!kj4!lk4!hrd!hga!jg5!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!ooe!kk9!lkb!kld!ll6!km7!lm1!lmd!ln9!pm9!kn8!lob!ioc@a$i3N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$h3+pohh0@1$h9@1$bZ@1$3$h5@3$i0$eZ$hd$h6@1$c$h4@3$2$0N2$hc$a@1$h8$7@3$1$6@1$h7$7@3$1$6$ha@3$1$6@1$i1+1@1$i2$he$hf@3$2@2$8$0$5@4$d$0$5N2@1$b$hb@1$3@2$8$0$5").
Lemma chk : ltac2:(zQ "90!qka!ive!jg5!ji0!ji6!jid!jj9!joc!mq2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qka!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mq2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_id.

Module F2p_s_pr.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F2p_s_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i40!hs4!o0!hg3!u2!ve!tb!sb!kic!t4!m4!kj4!lk4!hrd!hga!jg5!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!ooe!kk9!lkb!kld!ll6!km7!lmd!luc!ln9!pm9!kn8!lob!ioc@a$i3N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$h3+pohh0@1$h9@1$bZ@1$3$h5@3$i0$eZ$he$h6@1$c$h4@3$2$0N2$hc$a@1$h8$7@3$1$6@1$h7$7@3$1$6$ha@3$1$6@1$i1+1@1$i2$hd$hf@3$2@2$8$0$5@4$d$0$5N2@1$b$hb@1$3@2$8$0$5").
Lemma chk : ltac2:(zQ "90!qp4!ive!jg5!ji0!ji6!jid!jj9!joc!mv8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qp4!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mv8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_pr.

Module F3.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F3.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!ve!hg3!hs4!u2!jg5!m4!kj4!t4!hsa!hsf!hu7!igb!tb!ij7!ooe!kk9!qp9!ng4!ioc@a$h2N3@1$a@1$b@1$8@1$0@1$0@1$0$9@3$1$5$6@1$3$5$h0@3$1$2Nhb$d$6@1$f$4@1$e$4$h1@1$3@2$7$2$c").
Lemma chk : ltac2:(zQ "90!qte!ive!jg5!ji0!ji6!jid!jj9!joc!nlf@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!qte!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!nlf>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F3.

Module F5a_id_hi.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F5a_id_hi.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!ve!m4!hg3!u2!nm5!lm1!hs4!t4!jg5!hsa!hsf!hu7!igb!tb!ij7!nn0!qu3!qua!np1!npc!ioc@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$8$e$4$h2@1$h1$5$h3@1$3@2$7$6$d").
Lemma chk : ltac2:(zQ "90!rj8!ive!jg5!ji0!ji6!jid!jj9!joc!nv7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!rj8!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!nv7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_hi.

Module F5a_id_lo.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.pieces.HP01.F5a_id_lo.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!ve!m4!hg3!u2!nm5!lm1!kic!hs4!t4!hsa!hsf!hu7!igb!tb!ij7!nn0!qu3!qua!np1!npc!ioc@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$6$e$4$h2@1$h1$5$h3@1$3@2$8$7$d").
Lemma chk : ltac2:(zQ "90!ro3!ive!jg5!ji0!ji6!jid!jj9!joc!oke@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ro3!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!oke>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_lo.
