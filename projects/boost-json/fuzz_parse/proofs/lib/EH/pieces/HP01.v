(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~05piece37Corelib7Numbers7BinNumska1Z37Corelib4Init9Datatypesm73app89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~o56kentrym74prodo54exprm73nil37Corelib4Init7Decimalu72D0m74consm74pair89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~hh03ZLOhh06img_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hm07th_geomhm0ath_scratchm74Nonem73natu72D8u73Nil37Corelib4Init3Natht2bof_num_uint37Corelib4Init6Numberhv3bUIntDecimalhh02NXhh02PVhh07newh_knhh02vAhm07AA_regshm07F1_regshm02SNhm0eopnew_frame_knhm0cth_frames_kn07mkPieceo53SSRo55saddro56sentry46Stdlib6ZArith6BinInt1Zip23sub99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP012F1~~~~~~ir11Pm74boolm74true37Corelib4Init5Logicjg82eq05pc_pv0apc_regions0bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~jk2bshape_holdsir12SH08pc_entry06pc_xkn06pc_xpc08pc_xregsjk29Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~jsd9COPY_SPECjsd9FILL_SPECm75falsehh07CUT1_PChh06cut1_Thh09cut1_regshm03F2hhm06HFB_knhm03PVBhm06REG_thhm0aglobals_knjk25shapejk2bthrow_shape99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP015F2h_0~~~~~~kp81Pkp82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP015F2h_s~~~~~~kua1Pkua2SHhh03lithm07F2_regshm07POOLHDRhm08PoolIdlehm08PoolLivehm06REG_tphm04TH_Thm07pool_kn99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP018F2p_0_id~~~~~~loe1Ploe2SHhm0cPoolPristine99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP018F2p_0_pr~~~~~~lv31Plv32SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP018F2p_s_id~~~~~~mk81Pmk82SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP018F2p_s_pr~~~~~~mpd1Pmpd2SHhm02F3hm06REG_hfo54EVar99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP012F3~~~~~~ng91Png92SHhm07FREE_PChm0eAFTER_CATCH_PChm03F5ahm04FR_Thm07FR_regshm06REG_ct99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP019F5a_id_hi~~~~~~np91Pnp92SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP019F5a_id_lo~~~~~~nuf1Pnuf2SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module F1.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "i10!m3!nf!sa!t3!ta!u1!vd!hg2!hg9!hkf!hl6!hq1!hqc!hra!hs1!hs7!hsc!hu4!ig8!ih7!ihd!ii3!iie!ij4!ijf!ika!il0!im2!in2!inb!io1!io9!iqa@a$hcN1@1$h1@1$h2@1$f@1$6@1$6@1$6$h0@3$7$0+tsnm0@1$5$0@6$hd+vggv0$h8@1$5$hf@3$1$2$ha@3$1$2$c@3$1$2$h5@3$1$2$a$b$h3@1$d$he$h4+tsnm0$h7@3$1$2$hb@3$1$2$c@3$1$2$a$b@3$7@2$3@2$3$4$0$0@4$8@2$3$4$0$0@4$8$4$0$h6$9@2$i0$h9$9@1$5@2$3@2$3$4$0$0@1$5@2$3$e$4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!iv5!iva!jg1!jhc!ji2!ji9!jj5!jo7!jp6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!iv5!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!jp6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F1.

Module F2h_0.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h70!ki6!vd!nf!u1!m3!kie!sa!hg2!hs1!t3!hs7!hsc!hu4!ig8!kj9!kk3!kl0!kl7!km1!km8!kn2!in2!ta@a$h5N3@1$c@1$d@1$a@1$1@1$1@1$1$b@3$7$4$5@1$3$4@1$h0$0$h2$5@1$f$0@3$2$6@1$e$0@3$2$6$h1@1$h4+1$h3@1$3@2$9$8$h6").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "10!ko9$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!ktf!iva!jg1!jhc!ji2!ji9!jj5!jo7!ku4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!ktf!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!ku4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_0.

Module F2h_s.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h80!vd!nf!ki6!u1!m3!kie!sa!hg2!hs1!t3!jg1!hs7!hsc!hu4!ig8!kj9!kk3!kl0!kl7!km1!km8!kn2!in2!ta@a$h6N3@1$d@1$e@1$b@1$0@1$0@1$0$c@3$7$4$5@1$3$4@1$h1$a$h3$5@1$h0$2@3$1$6@1$f$2@3$1$6$h2@1$h5+1$h4@1$3@2$9$8$h7").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "10!ko9$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lj1!iva!jg1!jhc!ji2!ji9!jj5!jo7!lj6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lj1!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!lj6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2h_s.

Module F2p_0_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "i30!hs1!nf!hg2!ki6!u1!vd!ta!sa!t3!m3!kie!ljc!hra!hg9!hs7!hsc!hu4!ig8!ih7!kj9!kk3!lk3!kl7!lke!km1!ll9!lm5!ln1!lnb!kn2!lo3!in2!inb!io1!io9@a$hfN3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$i0+pksm8@1$h5@1$bZ@1$4$i2@3$hc$3Z$h9$h2@1$c$i1@3$2$0N2$h8$a@1$h4$3@3$1$7@1$h3$3@3$1$7$h6@3$1$7@1$hd+1@1$he$ha$hb@3$2@2$8$0$6@4$d$0$6N2@1$b$h7@1$4@2$8$0$6").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "80!hs1!ta!hg2!hg9!t3!ljc!lke!ko9@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!lt8!iva!jg1!jhc!ji2!ji9!jj5!jo7!ltd@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!lt8!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!ltd>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_id.

Module F2p_0_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "i30!hs1!nf!hg2!ki6!u1!vd!ta!sa!t3!m3!kie!ljc!hra!hg9!hs7!hsc!hu4!ig8!ih7!kj9!kk3!lk3!kl7!lke!km1!lm5!lu3!ln1!lnb!kn2!lo3!in2!inb!io1!io9@a$hfN3@1$h0@1$h1@1$e@1$5@1$5@1$5$f@3$2$9$a@1$4$9@6$i0+pksm8@1$h5@1$bZ@1$4$i2@3$hc$3Z$ha$h2@1$c$i1@3$2$0N2$h8$a@1$h4$3@3$1$7@1$h3$3@3$1$7$h6@3$1$7@1$hd+1@1$he$h9$hb@3$2@2$8$0$6@4$d$0$6N2@1$b$h7@1$4@2$8$0$6").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "80!hs1!ta!hg2!hg9!t3!ljc!lke!ko9@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mjd!iva!jg1!jhc!ji2!ji9!jj5!jo7!mk2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mjd!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!mk2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_0_pr.

Module F2p_s_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "i40!hs1!nf!hg2!u1!vd!ta!sa!ki6!t3!m3!kie!ljc!hra!hg9!jg1!hs7!hsc!hu4!ig8!ih7!kj9!kk3!lk3!kl7!lke!km1!ll9!lm5!ln1!lnb!kn2!lo3!in2!inb!io1!io9@a$i0N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$i1+pksm8@1$h6@1$bZ@1$3$i3@3$hd$eZ$ha$h3@1$c$i2@3$2$0N2$h9$a@1$h5$7@3$1$6@1$h4$7@3$1$6$h7@3$1$6@1$he+1@1$hf$hb$hc@3$2@2$8$0$5@4$d$0$5N2@1$b$h8@1$3@2$8$0$5").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "80!hs1!ta!hg2!hg9!t3!ljc!lke!ko9@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mp2!iva!jg1!jhc!ji2!ji9!jj5!jo7!mp7@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mp2!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!mp7>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_id.

Module F2p_s_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "i40!hs1!nf!hg2!u1!vd!ta!sa!ki6!t3!m3!kie!ljc!hra!hg9!jg1!hs7!hsc!hu4!ig8!ih7!kj9!kk3!lk3!kl7!lke!km1!lm5!lu3!ln1!lnb!kn2!lo3!in2!inb!io1!io9@a$i0N3@1$h1@1$h2@1$f@1$4@1$4@1$4$h0@3$2$9$a@1$3$9@6$i1+pksm8@1$h6@1$bZ@1$3$i3@3$hd$eZ$hb$h3@1$c$i2@3$2$0N2$h9$a@1$h5$7@3$1$6@1$h4$7@3$1$6$h7@3$1$6@1$he+1@1$hf$ha$hc@3$2@2$8$0$5@4$d$0$5N2@1$b$h8@1$3@2$8$0$5").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "80!hs1!ta!hg2!hg9!t3!ljc!lke!ko9@3$2@2$4$0$1@4$3$0$1N2@1$5$6$7").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mu7!iva!jg1!jhc!ji2!ji9!jj5!jo7!muc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mu7!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!muc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F2p_s_pr.

Module F3.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!vd!hg2!hs1!u1!jg1!m3!kie!t3!hs7!hsc!hu4!ig8!ihd!kj9!kk3!mv2!mv8!in2!ta@a$h1N3@1$a@1$b@1$8@1$0@1$0@1$0$9@3$1$5$6@1$3$5$f@3$1$2Nhb$c$6@1$e$4@1$d$4$h0@1$3@2$7$2$h2").
Definition SH : ltac2:(zQ "10!ko0$0") := ltac2:(zQ "70!hs1!ta!hg2!hg9!t3!ko9!ng2@3$2@2$4$0$1@4$3$0$1Nhb@1$6Ni2$5").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nkd!iva!jg1!jhc!ji2!ji9!jj5!jo7!nl2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nkd!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!nl2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F3.

Module F5a_id_hi.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h50!vd!m3!hg2!u1!nl8!ll9!hs1!t3!jg1!hs7!hsc!hu4!ig8!ihd!nm3!nn5!nnc!no4!nof!in2!ta@a$h3N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$e@1$3$1@2$f$5$8$d$4$h1@1$h0$5$h2@1$3@2$7$6$h4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nu4!iva!jg1!jhc!ji2!ji9!jj5!jo7!nu9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nu4!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!nu9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_hi.

Module F5a_id_lo.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h50!vd!m3!hg2!u1!nl8!ll9!ki6!hs1!t3!hs7!hsc!hu4!ig8!ihd!nm3!nn5!nnc!no4!nof!in2!ta@a$h3N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$e@1$3$1@2$f$5$6$d$4$h1@1$h0$5$h2@1$3@2$8$7$h4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!oja!iva!jg1!jhc!ji2!ji9!jj5!jo7!ojf@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!oja!jpc!ji2!ji9!jq6!jqe!jr6!js0!kgc!kh9!ojf>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_id_lo.
