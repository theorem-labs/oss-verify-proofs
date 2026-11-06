(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~05piece37Corelib7Numbers7BinNumskb1Z37Corelib4Init9Datatypesm83app89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~o66kentrym84prodo64exprm83nil37Corelib4Init7Decimalu82D0m84consm84pair89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~hh13ZLOhh16img_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hm27th_geomhm2ath_scratchm84Nonem83natu82D8u83Nil37Corelib4Init3Natht5bof_num_uint37Corelib4Init6Numberhv6bUIntDecimalo63SSRo65saddro66sentryhh12NXhh12PVhh17newh_knhh12vAhm27AA_regshm27F1_regshm22SNhm2eopnew_frame_knhm2cth_frames_kn07mkPiece46Stdlib6ZArith6BinInt1Zip53sub99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP012F1~~~~~~ir41Pm84boolm84true37Corelib4Init5Logicjgc2eq05pc_pv0apc_regions0bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhPieceQ6PIECEQ~~~~~~jk6bshape_holdsir42SH08pc_entry06pc_xkn06pc_xpc08pc_xregsjk69Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~jt29COPY_SPECjt29FILL_SPECm85falsehh17CUT1_PChh16cut1_Thh19cut1_regshm23F2hhm26HFB_knhm23PVBhm26REG_thhm2aglobals_knjk65shapejk6bthrow_shape99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP015F2h_0~~~~~~kpe1Pkpe2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP015F2h_s~~~~~~kv11Pkv12SHhh13lithm27F2_regshm27POOLHDRhm28PoolIdlehm28PoolLivehm26REG_tphm24TH_Thm27pool_kn99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_0_id~~~~~~lp61Plp62SHhm2cPoolPristine99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_0_pr~~~~~~lvc1Plvc2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_s_id~~~~~~ml21Pml22SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP018F2p_s_pr~~~~~~mq81Pmq82SHhm22F3hm26REG_hfo64EVar99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP012F3~~~~~~nh51Pnh52SHhm27FREE_PChm2eAFTER_CATCH_PChm23F5ahm24FR_Thm27FR_regshm26REG_ct99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP019F5a_id_hi~~~~~~nq61Pnq62SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6pieces4HP019F5a_id_lo~~~~~~nvd1Pnvd2SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module F1.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i10!m4!o0!sb!t4!tb!u2!ve!hg3!hga!hl1!hl8!hq4!hqf!hrd!hs4!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!ij7!ijd!ik8!ike!il9!im4!ima!inc!ioc!iqd@a$hfN1@1$h1@1$h2@1$f@1$6@1$6@1$6$h0@3$7$0+tvsg8@1$5$0@6$h3+vjlp8$hb@1$5$h5@3$1$2$hd@3$1$2$c@3$1$2$h8@3$1$2$a$b$h6@1$d$h4$h7+tvsg8$ha@3$1$2$he@3$1$2$c@3$1$2$a$b@3$7@2$3@2$3$4$0$0@4$8@2$3$4$0$0@4$8$4$0$h9$9@2$i0$hc$9@1$5@2$3@2$3$4$0$0@1$5@2$3$e$4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!iv9!ive!jg5!ji0!ji6!jid!jj9!joc!jpb@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!iv9!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!jpb>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F1.

Module F2h_0.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h70!kic!ve!o0!u2!m4!sb!kj4!hg3!hs4!t4!hsa!hsf!hu7!igb!tb!kjf!kk9!kl6!kld!km7!kme!kn8!ioc@a$h6N3@1$c@1$d@1$a@1$1@1$1@1$1$b@3$7$4$6@1$3$4@1$h1$0$h3$6@1$h0$0@3$2$5@1$f$0@3$2$5$h2@1$h5+1$h4@1$3@2$9$8$e").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "10!kof$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ku6!ive!jg5!ji0!ji6!jid!jj9!joc!kub@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ku6!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!kub>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_0.

Module F2h_s.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h80!ve!o0!kic!u2!m4!sb!kj4!hg3!hs4!t4!jg5!hsa!hsf!hu7!igb!tb!kjf!kk9!kl6!kld!km7!kme!kn8!ioc@a$h7N3@1$d@1$e@1$b@1$0@1$0@1$0$c@3$7$4$6@1$3$4@1$h2$a$h4$6@1$h1$2@3$1$5@1$h0$2@3$1$5$h3@1$h6+1$h5@1$3@2$9$8$f").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "10!kof$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lj9!ive!jg5!ji0!ji6!jid!jj9!joc!lje@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lj9!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!lje>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_s.

Module F2p_0_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i30!hs4!o0!hg3!kic!u2!ve!tb!sb!t4!m4!kj4!lk4!hrd!hga!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!kjf!kk9!lkb!kld!ll6!km7!lm1!lmd!ln9!lo3!kn8!lob!ioc@a$i2N3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$h2+pohh0@1$h8@1$bZ@1$4$h4@3$hf$3Z$hc$h5@1$c$h3@3$2$0N2$hb$a@1$h7$3@3$1$7@1$h6$3@3$1$7$h9@3$1$7@1$i0+1@1$i1$hd$he@3$2@2$8$0$6@4$d$0$6N2@1$b$ha@1$4@2$8$0$6").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "80!hs4!tb!hg3!hga!t4!lk4!ll6!kof@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lu1!ive!jg5!ji0!ji6!jid!jj9!joc!lu6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lu1!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!lu6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_id.

Module F2p_0_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i30!hs4!o0!hg3!kic!u2!ve!tb!sb!t4!m4!kj4!lk4!hrd!hga!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!kjf!kk9!lkb!kld!ll6!km7!lmd!luc!ln9!lo3!kn8!lob!ioc@a$i2N3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$h2+pohh0@1$h8@1$bZ@1$4$h4@3$hf$3Z$hd$h5@1$c$h3@3$2$0N2$hb$a@1$h7$3@3$1$7@1$h6$3@3$1$7$h9@3$1$7@1$i0+1@1$i1$hc$he@3$2@2$8$0$6@4$d$0$6N2@1$b$ha@1$4@2$8$0$6").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "80!hs4!tb!hg3!hga!t4!lk4!ll6!kof@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mk7!ive!jg5!ji0!ji6!jid!jj9!joc!mkc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mk7!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mkc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_pr.

Module F2p_s_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i40!hs4!o0!hg3!u2!ve!tb!sb!kic!t4!m4!kj4!lk4!hrd!hga!jg5!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!kjf!kk9!lkb!kld!ll6!km7!lm1!lmd!ln9!lo3!kn8!lob!ioc@a$i3N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$h3+pohh0@1$h9@1$bZ@1$3$h5@3$i0$eZ$hd$h6@1$c$h4@3$2$0N2$hc$a@1$h8$7@3$1$6@1$h7$7@3$1$6$ha@3$1$6@1$i1+1@1$i2$he$hf@3$2@2$8$0$5@4$d$0$5N2@1$b$hb@1$3@2$8$0$5").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "80!hs4!tb!hg3!hga!t4!lk4!ll6!kof@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mpd!ive!jg5!ji0!ji6!jid!jj9!joc!mq2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mpd!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mq2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_id.

Module F2p_s_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "i40!hs4!o0!hg3!u2!ve!tb!sb!kic!t4!m4!kj4!lk4!hrd!hga!jg5!hsa!hsf!hu7!igb!iha!ii0!ii8!ij1!kjf!kk9!lkb!kld!ll6!km7!lmd!luc!ln9!lo3!kn8!lob!ioc@a$i3N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$h3+pohh0@1$h9@1$bZ@1$3$h5@3$i0$eZ$he$h6@1$c$h4@3$2$0N2$hc$a@1$h8$7@3$1$6@1$h7$7@3$1$6$ha@3$1$6@1$i1+1@1$i2$hd$hf@3$2@2$8$0$5@4$d$0$5N2@1$b$hb@1$3@2$8$0$5").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "80!hs4!tb!hg3!hga!t4!lk4!ll6!kof@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mv3!ive!jg5!ji0!ji6!jid!jj9!joc!mv8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mv3!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!mv8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_pr.

Module F3.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h30!ve!hg3!hs4!u2!jg5!m4!kj4!t4!hsa!hsf!hu7!igb!tb!ij7!kjf!kk9!mve!ng4!ioc@a$h2N3@1$a@1$b@1$8@1$0@1$0@1$0$9@3$1$5$6@1$3$5$h0@3$1$2Nhb$d$6@1$f$4@1$e$4$h1@1$3@2$7$2$c").
Definition SH : ltac2:(zQ "10!ko6$0") := ltac2:(zQ "70!hs4!tb!hg3!hga!t4!nge!kof@3$2@2$4$0$1@4$3$0$1Nhb@1$5Ni2$6").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nla!ive!jg5!ji0!ji6!jid!jj9!joc!nlf@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nla!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!nlf>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F3.

Module F5a_id_hi.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!ve!m4!hg3!u2!nm5!lm1!hs4!t4!jg5!hsa!hsf!hu7!igb!tb!ij7!nn0!no2!no9!np1!npc!ioc@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$8$e$4$h2@1$h1$5$h3@1$3@2$7$6$d").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nv2!ive!jg5!ji0!ji6!jid!jj9!joc!nv7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nv2!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!nv7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_hi.

Module F5a_id_lo.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k4$0") := ltac2:(zQ "h50!ve!m4!hg3!u2!nm5!lm1!kic!hs4!t4!hsa!hsf!hu7!igb!tb!ij7!nn0!no2!no9!np1!npc!ioc@a$h4N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$f@1$3$1@2$h0$5$6$e$4$h2@1$h1$5$h3@1$3@2$8$7$d").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ok9!ive!jg5!ji0!ji6!jid!jj9!joc!oke@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ok9!jq1!ji6!jid!jqb!jr3!jrb!js5!kh2!khf!oke>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_lo.
