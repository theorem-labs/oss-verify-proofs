(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhCut2.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhCut2.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAsanPlanCore XSegLib XSegRun EhCut EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhCut2.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hd4expr37Corelib4Init3Natm93addhd4EVar37Corelib7Numbers7BinNumso81Z04listhd6kentry89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~r43lit04conshd5KWordhd2SA03nilr47vCANARY04boolr48flags_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hic9flags0_knhd3KWrhicapool_state03appr43ZLOhd5KDisjr42vAr45vAUXVhic2SN46Stdlib6ZArith6BinInt1Zhr43addhr43subhic2bShic4vREThd6KRangehd6KAlignr44RATPr43vGPr44vS10r44vS11r43vS8r43vS9r43addhicaboost_regshic2vNr47auxv_knr46img_knr47newh_knhic9flags_selhicaglobals_knhiceopnew_frame_knhic9pool_geomhic7pool_knhicastatics_wrhic7th_geomhicath_scratchhd9sym_state04Noner42NXhic5F1_knhic7F1_regshd3SSRhd5saddrhd6sentryhiccth_frames_knr44vHDRhic8blk_geomhic6F2H_knhic7F2_regs46Stdlib5Arith8PeanoNat3Natjje3eqbjje3leb04andbm93subr46UC_OFFhic8ucf_fromhic8ucx_from37Corelib5Lists7ListDefjp43seqr42PV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jr76region04prod04pair05falser49cursor_knr48geomT_knhic8hdrHF_knhr43oppr44siter46mkSite04truer47CUT1_PCr46cut1_Tr49cut1_regsr48geomB_knhic8CATCH_SThic6HFB_knhic5HF_PChic4HF_Thic7HF_regsr47CUR_OFFr45xslotr44vSPFr46hdr_knhic2RSr47s_fsizer47s_savedr43vRAhic9savedA_knr44s_ipr44vP2V3h5LinuxProcessSemantics5Riscv5Instrlgd7ALU_SUBhic9frameA_knhd4EAluhic6RES_PChic6RES_knhic8RES_regshic5C_SCRhic8CATCH_PChic7CT_regshic7ct_geomhic8cth_geomhicdAFTER_FREE_PChic4FR_Thic7POOLHDRjp43maphic8PoolLive89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~lte6ksubst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER5EhCut3CUTmib7auxv_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER6EhCut24CUT2mmf5F1_knmmf6F2H_knmib6cut1_Tmmf4HF_Tmmf6RES_knmmf4FR_T" s.
Import ListNotations. Import AX2. Import SR. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT2.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut2.CUT2.
Definition F1_kn : ltac2:(zQ "50!hhb!q5!q1!ho0!qb>6steady$0>1u$2>1p$3@1$1$4") := ltac2:(zQ "h00!hoe!qb!hhb!q1!mm4!ik5!ike!il8!im5!in3!io5!ip2!ho0!ipd!iqb!ir6\6steady$2\1u$3\1p$c@3$0$1$9@3$0$1$f@3$0$1$6@3$0$1$5@3$0$1@1$7^3@3$0$1$4@3$0$1@1$8^2@3$0$1$d@3$0$1@1$b^1@3$0$1$e$a").
Definition F1 : ltac2:(zQ "40!hhb!q1!ho0!is4>6steady$0>1u$1>1p$2$3") := ltac2:(zQ "b0!it0!hhb!hgc!q1!it6!mqa!iu4!ho0!iuf!iv5!ivd\6steady$1\1u$3\1p$7@6$8+vggv0$6@1$2$a@3$5^3^2^1$4@1$0$9").
(* [comment removed for export] *)
Definition TH_T : ltac2:(zQ "50!hhb!q5!q1!ho0!qb>6steady$0>1u$2>1p$3@1$1$4") := ltac2:(zQ "f0!hoe!qb!hhb!q1!mm4!ik5!il8!im5!io5!ip2!ho0!ipd!jg6!iqb!ir6\6steady$2\1u$3\1p$a@3$0$1$c@3$0$1$e@3$0$1@1$9^1@3$0$1@1$7^2@3$0$1$b@3$0$1@1$6^3@3$0$1$4@3$0$1$5@3$0$1$d$8").
(* [comment removed for export] *)
Definition F2H_kn : ltac2:(zQ "30!hhb!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "h20!qb!hoe!hhb!v9!hgc!mm4!ik5!v3!jh6!jhd!il8!im5!ipd!jg6!iqb!ir6!hna!hg7\6steady$2@3$1$0@3$3$0@2$h0@2$h1$8Z@1$7+p0@1$4$0@3$1$0$d@3$1$0$f@3$1$0@1$bZ@3$1$0$c@3$1$0@1$a^1@3$1$0$5@3$1$0$6@3$1$0$e$9").
Definition F2h : ltac2:(zQ "20!hhb!is4>6steady$0$1") := ltac2:(zQ "a0!it0!hhb!hgc!it6!jh6!mr3!jj3!iuf!iv5!ivd\6steady$1@6$7+pksm8@1$6$4@1$2$9@1$5^1$3@1$0$8").

(* [comment removed for export] *)
Definition HF_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h10!qb!hoe!v9!kgd!hp3!v3!hq1!hna!hg7!hgc!mm4!kh4!hi1!ki0!ik5!kib!kj7@3$1$0@3$2$0@2$7@2$8$6$4@1$5@1$h0$4@3$2$0@2$7@2$8$6+mn8@1$5+l0@1$9$0@3$1$0@1$b$3@3$1$0$f@3$1$0$c@3$1$0$a@3$1$0$e@1$d$3").
Definition cut1c : ltac2:(zQ "30!hhb!kje!is4>6phase2$0>2st$1$2") := ltac2:(zQ "f0!it0!hoe!hhb!hgc!kke!kl4!it6!mrd!km7!kn3!kje!iuf!qb!iv5!ivd\6phase2$2\2st$a@6$b$5@1$8^2@1$3$e@3$1$c@1$7^2@3$9^2$4^1$6@1$0$d").
(* [comment removed for export] *)
Definition F3 : ltac2:(zQ "10!is4$0") := ltac2:(zQ "h00!hoe!qb!it0!kgd!hgc!kke!it6!kn3!kne!koa!kp4!ms7!kq5!iuf!iv5!ivd@6$d$a$c@1$4$f@3$0$1$b@3$0$1$9@3$7$3$5$8$6@1$2$e").
Definition PAD_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h00!hoe!qb!ks9!kke!hi1!mm4!ik5!v9!hu8!hq6!jh6!hv1!hp9!hg7!v3!hgc@3$0$1@1$2$3@3$0$1$4@3$0$1$5@3$0$1$6@3$7$1@3$8$9+kgggggggggg0+vvvvvvvvvvvvvuj0@3$7$1@3$8$a+1+ogggggggggg0@3$7$1@2$b$a+h0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hggg0@1$e+uhgg0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+vokt8@1$e+hkj0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d$9Z@1$e+ht0@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hgrlu0@1$e+8@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hirmv8@1$e+8@3$7$1@4$c@2$d$aZ@1$e+p0@2$d@1$eZ+hirpl0@1$e+8@1$f$1").

(* [comment removed for export] *)
Definition RES_kn : ltac2:(zQ "30!q5!kje!qb>2st$1@1$0$2") := ltac2:(zQ "he0!kje!hoe!qb!v9!hna!hg7!hq1!hp3!v3!ht3!kt2!hgc!ljc!hu8!hu0!kvf!hp9!jh6!kt8!lk9!lj1!lg6!ii1!ks9!kke!hi1!mm4!ik5!ki0!hq6\2st$0@3$1$2@3$3$2@2$4@2$5$6$7@1$8@2$9$a$7@1$b$2@3$1$2@1$c^1@3$1$2@3$3$2@3$d$e@1$f^1@1$f^1@3$3$2@4$h0@2$5$h1Z@1$8+p0@2$5$6$a@1$8@1$h2^1@3$3$2@3$d@3$h3$h4$h5@2$h6$6$a+h0+ogggggggggg0@1$b$2@3$1$2@1$h7$h8@3$1$2$h9@3$1$2$ha@3$1$2$hb@3$1$2@1$hc$h8@3$3$2@4$h0@2$5$6$7@1$8@2$9$a$7@2$5$h1Z@1$8+p0@3$3$2@4$h0@2$5$6$7@1$8@2$9$a$7@2$5$hdZ@1$8+ht0@3$3$2@3$d$h5+kgggggggggg0+ogggggggggg0@1$b$2").
Definition RES : ltac2:(zQ "20!kje!is4>2st$0$1") := ltac2:(zQ "a0!it0!hgc!it6!kje!ll0!msf!lm4!iuf!iv5!ivd\2st$3@6$7$4$6@1$1$9@1$5^1$2@1$0$8").
Definition F5a : ltac2:(zQ "30!hhb!ho0!is4>2ps$1>2hi$0$2") := ltac2:(zQ "hf0!qb!hoe!hgc!ln0!it0!hhb!v9!kke!it6!ii1!mm4!hi1!ks9!ik5!v3!hq1!jh6!ln9!lo5!lp0!lpb!im5!ip2!ho0!ipd!hna!hg7!iuf!iv5!ivd!kj7\2ps$h7\2hi$5@6$hb$h1@1$h2@2$9$h0+m0@1$2$hd@3$1$0@3$6$0@2$h9@2$ha$f@1$he$3@1$e$3@1$2$0@3$1$0@1$c$7@3$1$0@1$h5+1@3$1$0$h8@3$1$0@1$h6^2@3$1$0$b@3$1$0$a@3$1$0$d@3$1$0$h3@1$h4^1$8@1$4$hc").
Definition FR_T : ltac2:(zQ "30!q5!ho0!qb>1p$1@1$0$2") := ltac2:(zQ "h40!qb!hoe!v9!hq1!hg7!vf!v3!ln0!hta!hgc!mm4!hi1!ik5!lp0!im5!ip2!ho0!ipd!hna!kj7\1p$h0@3$1$0@3$2$0@3$5@2$4$3-8N8@1$6+knppc@3$2$0@3$5@2$4$3-h0N8@1$8N0@3$2$0@3$5@2$4$3-h8N8@1$8N1@3$2$0@2$h2@2$4$3@1$h3$7@1$6$7@1$9$0@3$1$0@1$eZ@3$1$0$h1@3$1$0@1$f^1@3$1$0$b@3$1$0$a@3$1$0$c$d").
Definition F5b : ltac2:(zQ "20!ho0!is4>1p$0$1") := ltac2:(zQ "e0!o1!it0!hgc!it6!ii1!hq1!jh6!lq7!mt9!ii7!ho0!iuf!iv5!ivd\1p$a@6$b$7@5$9@1$0Nh3@2$4$5-i0$6@1$0Ni5@1$0N8@1$2$d@1$8^1$3@1$1$c").
Definition DONE_T : ltac2:(zQ "30!q5!ho0!qb>1p$1@1$0$2") := ltac2:(zQ "a0!hoe!qb!mm4!hi1!ik5!lp0!im5!ip2!ho0!ipd\1p$8@3$0$1@1$6Z@3$0$1$9@3$0$1@1$7^1@3$0$1$3@3$0$1$2@3$0$1$4$5").
Definition F5p : ltac2:(zQ "10!is4$0") := ltac2:(zQ "i30!qb!hoe!h8!hgc!v3!m2!v9!kg1!ln0!ls0!it0!kg7!kke!lsb!it6!mm4!hi1!ks9!ik5!hq1!ln9!lo5!lt2!lp0!im5!ip2!ipd!mi1!hna!hg7!iuf!iv5!ivd!hsc!kj7@6$he$h4@1$h5@1$4@2$i1$9+m0@1$3$i0@3$1$0@3$6$0@2$hc@2$hd$h3@1$i2$8@1$4$8@1$3$0@3$1$0@4$d$0$0@1$hb@3$6@2$7$2$5@4$b$2$5N2@1$4$9@1$3@2$7$2$5@1$h1$c@3$1$0@1$h8+1@3$1$0$ha@3$1$0@1$h9$h6@3$1$0$h0@3$1$0$f@3$1$0$h2$h7$e@1$a$hf").
End CUT2.
(* [comment removed for export] *)
