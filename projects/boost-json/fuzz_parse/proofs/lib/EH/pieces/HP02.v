(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XSegRun XSegAuto EhX_plain EhCut EhMatch EhPiece EhPieceP EhCut2 EhPieceQ.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~05piece37Corelib4Init7Decimalka2D037Corelib7Numbers7BinNumsm51Z37Corelib4Init9Datatypeso24conso23nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~q77FREE_PCq7cPoolPristineo23nato24prodo24trueka2D8ka3Nil37Corelib4Init3Nathi0bof_num_uint37Corelib4Init6Numberhk1bUIntDecimal89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~hm52PVq7eAFTER_CATCH_PCq73F5aq74FR_Tq77FR_regsq76REG_ct07mkPiece89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hu44expr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029F5a_pr_hi~~~~~~ij11Po24bool37Corelib4Init5Logicio82eq05pc_pv0apc_regions0bpiece_check89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~is2bshape_holdsij12SH08pc_entry06pc_xkn06pc_xpc08pc_xregsis29Pgen_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~jkd9COPY_SPECjkd9FILL_SPECo25false99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029F5a_pr_lo~~~~~~jqe1Pjqe2SHq78PoolIdleq76DONE_Tq79DONE_regsq73F5bq78REG_done99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP026F5b_id~~~~~~kj51Pkj52SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP026F5b_pr~~~~~~ko81Pko82SHq73F5p99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP023F5p~~~~~~ku11Pku12SHhm54sitehm56mkSite99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029P1h_479f0~~~~~~lk32SThm54endsq75HF_PCq74HF_Tq77HF_regsq75cut1c89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~lrd7regionsis25shapeis2akeep_shapelk31Plk32SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029P2k_479f0~~~~~~mif2STq75PAD_Tq78PAD_regsmif1Pmif2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029P2p_47924~~~~~~mpe2SThm54cut1mpe1Pmpe2SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029P2p_4b1c0~~~~~~ng22STng21Png22SH99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6pieces4HP029P2p_4b238~~~~~~nle2STnle1Pnle2SH" s.
Import ListNotations. Import AX2. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP. Import CUT2. Import PIECEQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

Module F5a_pr_hi.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h50!m0!ne!pa!q1!u8!v2!hg1!hg7!hge!hh5!hha!hj2!hl6!hq4!hqa!hrb!hs1!hs8!ht2!htb!ii9@a$h3N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$e@1$3$1@2$f$5$8$d$4$h1@1$h0$5$h2@1$3@2$7$6$h4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!inc!io1!hge!ipc!iq2!iq9!ir5!jg7!jh6@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!inc!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!jh6>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_pr_hi.

Module F5a_pr_lo.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h50!m0!ne!pa!q1!u8!v2!jq6!hg1!hg7!hh5!hha!hj2!hl6!hq4!hqa!hrb!hs1!hs8!ht2!htb!ii9@a$h3N1@1$b@1$c@1$9@1$0@1$0@1$0$a@3$2$1$4@3$2$1$e@1$3$1@2$f$5$6$d$4$h1@1$h0$5$h2@1$3@2$8$7$h4").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!jv9!io1!hge!ipc!iq2!iq9!ir5!jg7!jve@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!jv9!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!jve>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5a_pr_lo.

Module F5b_id.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!m0!q1!ne!hqa!kg4!pa!hg1!hg7!hh5!hha!hj2!hl6!hq4!kgf!kh8!ki4!kia!htb!ii9@a$h1N1@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$2$3@1$1$2@1$f$4$c$3$e@1$d$4$h0@1$1@2$7$6$h2").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!knd!io1!hge!ipc!iq2!iq9!ir5!jg7!ko2@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!knd!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!ko2>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5b_id.

Module F5b_pr.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!m0!q1!ne!hqa!v2!pa!hg1!hg7!hh5!hha!hj2!hl6!hq4!kgf!kh8!ki4!kia!htb!ii9@a$h1N1@1$a@1$b@1$8@1$0@1$0@1$0$9@3$5$2$3@1$1$2@1$f$4$c$3$e@1$d$4$h0@1$1@2$7$6$h2").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!kt0!io1!hge!ipc!iq2!iq9!ir5!jg7!kt5@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!kt0!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!kt5>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5b_pr.

Module F5p.
(* [comment removed for export] *)

Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h40!m0!ne!pa!q1!hqa!hg1!hg7!hh5!hha!hj2!hl6!hq4!kgf!kh8!ktb!u8!kg4!kia!htb!ii9@a$h2N1@1$9@1$a@1$7@1$0@1$0@1$0$8@3$2$1$f@3$2$1$4@1$3$1$e$b$4$d@1$c$h0$h1@1$3@2$6$5$h3").
Definition SH : shape := [].
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!li6!io1!hge!ipc!iq2!iq9!ir5!jg7!lib@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!li6!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!lib>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End F5p.

Module P1h_479f0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!lj1$0") := ltac2:(zQ "30!q1!ne!lj9@4$2+knpo4+h0@1$0$1+knpp4").
Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!jq6!m0!loe!hg1!q1!hg7!hh5!hha!hj2!hl6!hq4!lp4!lpc!lq4!lqb!lr5!htb!mg2!ii9@a$h0N1@1$8@1$9@1$6@1$1@1$1@1$1$7@2$b$0$2@2$f$0$2$a$c$e$d@1$h1$0@1$4@2$5$3$h2").
Definition SH : ltac2:(zQ "10!mgd$0") := ltac2:(zQ "10!mh6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mi4!io1!hge!ipc!iq2!iq9!ir5!jg7!mi9@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mi4!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!mi9>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P1h_479f0.

Module P2k_479f0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!lj1$0") := ltac2:(zQ "30!q1!ne!lj9@4$2+knpo4+h0@1$0$1+knpp4").
Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h20!hge!m0!mna!hg1!q1!hg7!hh5!hha!hj2!hl6!hq4!lp4!mo0!mo8!lr5!htb!mg2!ii9@a$fN1@1$8@1$9@1$6@1$1@1$1@1$1$7@2$b$0$2@2$e$0$2$a+knpp4@1$d+1$c@1$h0$0@1$4@2$5$3$h1").
Definition SH : ltac2:(zQ "10!mgd$0") := ltac2:(zQ "10!mh6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mp3!io1!hge!ipc!iq2!iq9!ir5!jg7!mp8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mp3!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!mp8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2k_479f0.

Module P2p_47924.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!lj1$0") := ltac2:(zQ "40!ne!pa!q1!lj9@4$3+knor8+m0@3$1$0-h0@1$2$0+knpj8").
Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!hge!m0!mu9!jq6!hg1!q1!hg7!hh5!hha!hj2!hl6!hq4!muf!lp4!mo0!mo8!htb!mg2!ii9@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+knpj8@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!mgd$0") := ltac2:(zQ "10!mh6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!mv7!io1!hge!ipc!iq2!iq9!ir5!jg7!mvc@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!mv7!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!mvc>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_47924.

Module P2p_4b1c0.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!lj1$0") := ltac2:(zQ "40!ne!pa!q1!lj9@4$3+krhl4+q0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0+krms4").
Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!hge!m0!nkd!jq6!hg1!q1!hg7!hh5!hha!hj2!hl6!hq4!muf!lp4!mo0!mo8!htb!mg2!ii9@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+krms4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!mgd$0") := ltac2:(zQ "10!mh6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nl3!io1!hge!ipc!iq2!iq9!ir5!jg7!nl8@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nl3!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!nl8>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4b1c0.

Module P2p_4b238.
(* [comment removed for export] *)
Definition ST : ltac2:(zQ "10!lj1$0") := ltac2:(zQ "40!ne!pa!q1!lj9@4$3+krhsc+q0@3$1$0-h0@3$1$0-h8@3$1$0-i0@3$1$0-i8@3$1$0-j0@3$1$0-j8@3$1$0-k0@3$1$0-k8@3$1$0-l0@3$1$0-l8@3$1$0-m0@3$1$0-m8@1$2$0+krms4").
Definition P : ltac2:(zQ "10!k3$0") := ltac2:(zQ "h30!hge!m0!nq9!jq6!hg1!q1!hg7!hh5!hha!hj2!hl6!hq4!muf!lp4!mo0!mo8!htb!mg2!ii9@a$h0N1@1$9@1$a@1$7@1$1@1$1@1$1$8@2$d$0$2@3$c$0$3$2$b+krms4@1$fZ$e@1$h1$0@1$5@2$6$4$h2").
Definition SH : ltac2:(zQ "10!mgd$0") := ltac2:(zQ "10!mh6$0").
(* [comment removed for export] *)
Lemma chk : ltac2:(zQ "90!nqf!io1!hge!ipc!iq2!iq9!ir5!jg7!nr4@3$3$1@2$6$0@3$7@1$4$0@1$5$0$8$2").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Theorem spec : ltac2:(zQ "b0!nqf!jhc!iq2!iq9!ji6!jie!jj6!jk0!joc!jp9!nr4>0$8>0$9@7$7@1$1$0@1$5$0@1$6$0@1$4$0@1$3$0@1$2$0$a").
Proof. intros C F. exact (Pgen_of_check C F P SH chk). Qed.
End P2p_4b238.
