(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/EhCut2.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/EhCut2.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAsanPlanCore XSegLib XSegRun EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhCut.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhCut2.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hd4expr37Corelib4Init3Natm93addhd4EVar37Corelib7Numbers7BinNumso81Z04listhd6kentry89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~r43lit04conshd5KWordhd2SA03nilr47vCANARY04boolr48flags_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hid9flags0_knhd3KWrhidapool_state03apphd5KDisjr43ZLOr42vAr45vAUXVhid2SN46Stdlib6ZArith6BinInt1Zhr63addhr63subhid2bShid4vREThd6KRangehd6KAlignr44RATPr43vGPr44vS10r44vS11r43vS8r43vS9r43addhidaboost_regshid2vNr47auxv_knr46img_knr47newh_knhid9flags_selhidaglobals_knhideopnew_frame_knhid9pool_geomhid7pool_knhidastatics_wrhid7th_geomhidath_scratchhd9sym_state04Nonehd3SSRhd5saddrhd6sentryr42NXhid5F1_knhid7F1_regshidcth_frames_knr44vHDRhid8blk_geomhid6F2H_knhid7F2_regs46Stdlib5Arith8PeanoNat3Natjk03eqbjk03leb04andbm93subr46UC_OFFhid8ucf_fromhid8ucx_from37Corelib5Lists7ListDefjp63seqr42PV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jr96region04prod04pair05falser49cursor_knr48geomT_knhid8hdrHF_knhr63oppr44siter46mkSite04truer47CUT1_PCr46cut1_Tr49cut1_regsr48geomB_knhid8CATCH_SThid6HFB_knhid5HF_PChid4HF_Thid7HF_regsr47CUR_OFFr45xslotr44vSPFr46hdr_knhid2RSr47s_fsizer47s_savedr43vRAhid9savedA_knr44s_ipr44vP2V3h5LinuxProcessSemantics5Riscv5Instrlgf7ALU_SUBhd4EAluhid9frameA_knhid6RES_PChid6RES_knhid8RES_regshid5C_SCRhid8CATCH_PChid7CT_regshid7ct_geomhid8cth_geomhiddAFTER_FREE_PChid4FR_Thid7POOLHDRjp63map89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~lt46ksubsthid8PoolLive89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTmid7auxv_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU6EhCut24CUT2mn25F1_knmn26F2H_knmid6cut1_Tmn24HF_Tmn26RES_knmn24FR_T" s.
Import ListNotations. Import AX2. Import SR. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT2.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2.
Definition F1_kn : ltac2:(zQ "50!hhc!q5!q1!qb!ho2>6steady$0>1u$2>1p$4@1$1$3") := ltac2:(zQ "h00!hp0!qb!hhc!q1!mm7!ik7!il0!ila!im7!in5!io7!ip4!ho2!ipf!iqd!ir8\6steady$2\1u$3\1p$c@3$0$1$9@3$0$1$f@3$0$1$6@3$0$1$5@3$0$1@1$7^3@3$0$1$4@3$0$1@1$8^2@3$0$1$d@3$0$1@1$b^1@3$0$1$e$a").
Definition F1 : ltac2:(zQ "40!hhc!q1!is6!ho2>6steady$0>1u$1>1p$3$2") := ltac2:(zQ "b0!it2!hhc!hgd!q1!it8!ite!iu6!iuf!mqe!ivd!ho2\6steady$1\1u$3\1p$a@6$4+vjlp8$9@1$2$6@3$8^3^2^1$7@1$0$5").
(* [comment removed for export] *)
Definition TH_T : ltac2:(zQ "50!hhc!q5!q1!qb!ho2>6steady$0>1u$2>1p$4@1$1$3") := ltac2:(zQ "f0!hp0!qb!hhc!q1!mm7!ik7!ila!im7!io7!ip4!ho2!ipf!jg8!iqd!ir8\6steady$2\1u$3\1p$a@3$0$1$c@3$0$1$e@3$0$1@1$9^1@3$0$1@1$7^2@3$0$1$b@3$0$1@1$6^3@3$0$1$4@3$0$1$5@3$0$1$d$8").
(* [comment removed for export] *)
Definition F2H_kn : ltac2:(zQ "30!hhc!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "h20!qb!hp0!hhc!va!hgd!hnc!hg8!mm7!ik7!v4!jh8!jhf!ila!im7!ipf!jg8!iqd!ir8\6steady$2@3$1$0@3$3$0@2$5@2$6$aZ@1$9+p0@1$4$0@3$1$0$f@3$1$0$h1@3$1$0@1$dZ@3$1$0$e@3$1$0@1$c^1@3$1$0$7@3$1$0$8@3$1$0$h0$b").
Definition F2h : ltac2:(zQ "20!hhc!is6>6steady$0$1") := ltac2:(zQ "a0!it2!hhc!hgd!it8!ite!iu6!iuf!jh8!mr7!jj5\6steady$1@6$3+pohh0@1$9$7@1$2$5@1$8^1$6@1$0$4").

(* [comment removed for export] *)
Definition HF_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h10!qb!hp0!va!kgf!hnc!hg8!hpd!v4!hq3!hgd!mm7!kh6!hi2!ki2!ik7!kid!kj9@3$1$0@3$2$0@2$4@2$5$8$6@1$7@1$h0$6@3$2$0@2$4@2$5$8+mn8@1$7+l0@1$9$0@3$1$0@1$b$3@3$1$0$f@3$1$0$c@3$1$0$a@3$1$0$e@1$d$3").
Definition cut1c : ltac2:(zQ "30!hhc!is6!kk0>6phase2$0>2st$2$1") := ltac2:(zQ "f0!it2!hp0!hhc!hgd!kl0!it8!qb!ite!iu6!kl6!iuf!ms1!km9!kn5!kk0\6phase2$2\2st$e@6$5$9@1$c^2@1$3$8@3$1$6@1$b^2@3$d^2$4^1$a@1$0$7").
(* [comment removed for export] *)
Definition F3 : ltac2:(zQ "10!is6$0") := ltac2:(zQ "h00!hp0!qb!it2!kgf!hgd!kl0!it8!ite!iu6!iuf!kn5!ko0!koc!kp6!msb!kq7@6$6$d$f@1$4$8@3$0$1$e@3$0$1$c@3$a$3$5$b$9@1$2$7").
Definition PAD_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h00!hp0!qb!ksb!kl0!hi2!mm7!ik7!va!hua!hq8!jh8!hv3!hp5!hg8!v4!hgd@3$0$1@1$2$3@3$0$1$4@3$0$1$5@3$0$1$6@3$7$1@3$8$9+kgggggggggg0+vvvvvvvvvvvvvuj0@3$7$1@3$8$a+1+ogggggggggg0@3$7$1@2$b$a+h0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hggg0@1$e+ukgg0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+vrpu0@1$e+hkm8@3$7$1@4$c@2$d$aZ@1$e+p0@2$d$9Z@1$e+ht0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hguri0@1$e+8@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hiusj8@1$e+8@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hiuup0@1$e+8@1$f$1").

(* [comment removed for export] *)
Definition RES_kn : ltac2:(zQ "30!q5!qb!kk0>2st$2@1$0$1") := ltac2:(zQ "he0!kk0!hp0!qb!va!hnc!hg8!hq3!hpd!v4!ht5!kt4!hgd!lk5!hua!hu2!lg1!hp5!jh8!kta!lje!lj3!lg8!ii3!ksb!kl0!hi2!mm7!ik7!ki2!hq8\2st$0@3$1$2@3$3$2@2$4@2$5$6$7@1$8@2$9$a$7@1$b$2@3$1$2@1$c^1@3$1$2@3$3$2@3$d$e@1$f^1@1$f^1@3$3$2@4$h0@2$5$h1Z@1$8+p0@2$5$6$a@1$8@1$h2^1@3$3$2@3$d@3$h3$h4$h5@2$h6$6$a+h0+ogggggggggg0@1$b$2@3$1$2@1$h7$h8@3$1$2$h9@3$1$2$ha@3$1$2$hb@3$1$2@1$hc$h8@3$3$2@4$h0@2$5$6$7@1$8@2$9$a$7@2$5$h1Z@1$8+p0@3$3$2@4$h0@2$5$6$7@1$8@2$9$a$7@2$5$hdZ@1$8+ht0@3$3$2@3$d$h5+kgggggggggg0+ogggggggggg0@1$b$2").
Definition RES : ltac2:(zQ "20!is6!kk0>2st$1$0") := ltac2:(zQ "a0!it2!hgd!it8!ite!iu6!iuf!kk0!ll2!mt3!lm6\2st$6@6$2$7$9@1$1$4@1$8^1$5@1$0$3").
Definition F5a : ltac2:(zQ "30!hhc!is6!ho2>2ps$2>2hi$0$1") := ltac2:(zQ "hf0!qb!hp0!hgd!ln2!it2!hhc!va!kl0!hnc!hg8!it8!ite!iu6!iuf!ii3!mm7!hi2!ksb!ik7!v4!hq3!jh8!lnb!lo7!lp2!lpd!im7!ip4!ho2!ipf!kj9\2ps$hc\2hi$5@6$a$h6@1$h7@2$e$h5+m0@1$2$c@3$1$0@3$6$0@2$8@2$9$h4@1$he$3@1$h3$3@1$2$0@3$1$0@1$h1$7@3$1$0@1$ha+1@3$1$0$hd@3$1$0@1$hb^2@3$1$0$h0@3$1$0$f@3$1$0$h2@3$1$0$h8@1$h9^1$d@1$4$b").
Definition FR_T : ltac2:(zQ "30!q5!qb!ho2>1p$2@1$0$1") := ltac2:(zQ "h40!qb!hp0!va!hg8!hq3!hg0!v4!ln2!htc!hgd!hnc!mm7!hi2!ik7!lp2!im7!ip4!ho2!ipf!kj9\1p$h1@3$1$0@3$2$0@3$5@2$3$4-8N8@1$6+knll8@3$2$0@3$5@2$3$4-h0N8@1$8N0@3$2$0@3$5@2$3$4-h8N8@1$8N1@3$2$0@2$a@2$3$4@1$h3$7@1$6$7@1$9$0@3$1$0@1$fZ@3$1$0$h2@3$1$0@1$h0^1@3$1$0$c@3$1$0$b@3$1$0$d$e").
Definition F5b : ltac2:(zQ "20!is6!ho2>1p$1$0") := ltac2:(zQ "e0!o1!it2!hgd!it8!ite!iu6!iuf!ii3!hq3!jh8!lq9!mtd!ii9!ho2\1p$d@6$3$a@5$c@1$0Nh3@2$7$8-i0$9@1$0Ni5@1$0N8@1$2$5@1$b^1$6@1$1$4").
Definition DONE_T : ltac2:(zQ "30!q5!qb!ho2>1p$2@1$0$1") := ltac2:(zQ "a0!hp0!qb!mm7!hi2!ik7!lp2!im7!ip4!ho2!ipf\1p$8@3$0$1@1$6Z@3$0$1$9@3$0$1@1$7^1@3$0$1$3@3$0$1$2@3$0$1$4$5").
Definition F5p : ltac2:(zQ "10!is6$0") := ltac2:(zQ "i30!qb!hp0!h8!hgd!m2!v4!va!kg3!ln2!ls2!it2!kg9!kl0!lsd!mh7!hnc!hg8!it8!ite!iu6!iuf!mm7!hi2!ksb!ik7!hq3!lnb!lo7!mi1!lp2!im7!ip4!ipf!hse!kj9@6$h1$ha@1$hb@1$5@2$i1$9+m0@1$3$h3@3$1$0@3$6$0@2$f@2$h0$h9@1$i2$8@1$5$8@1$3$0@3$1$0@4$d$0$0@1$e@3$6@2$7$2$4@4$b$2$4N2@1$5$9@1$3@2$7$2$4@1$h7$c@3$1$0@1$he+1@3$1$0$i0@3$1$0@1$hf$hc@3$1$0$h6@3$1$0$h5@3$1$0$h8$hd$h4@1$a$h2").
End CUT2.
(* [comment removed for export] *)
