(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAsanPlanCore XSegLib XSegRun EhCut EhMatch.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hd4expr37Corelib4Init3Natm93addhd4EVar37Corelib7Numbers7BinNumso81Z04listhd6kentry89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~r43lit04conshd5KWordhd2SA03nilr47vCANARY04boolr48flags_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~hic9flags0_knhd3KWrhicapool_state03appr43ZLOhd5KDisjr42vAr45vAUXVhic2SN46Stdlib6ZArith6BinInt1Zhr43addhr43subhic2bShic4vREThd6KRangehd6KAlignr44RATPr43vGPr44vS10r44vS11r43vS8r43vS9r43addhicaboost_regshic2vNr47auxv_knr46img_knr47newh_knhic9flags_selhicaglobals_knhiceopnew_frame_knhic9pool_geomhic7pool_knhicastatics_wrhic7th_geomhicath_scratchhd9sym_state04Noner42NXhic5F1_knhic7F1_regshd3SSRhd5saddrhd6sentryhiccth_frames_knr44vHDRhic8blk_geomhic6F2H_knhic7F2_regs46Stdlib5Arith8PeanoNat3Natjje3eqbjje3leb04andbm93subr46UC_OFFhic8ucf_fromhic8ucx_from37Corelib5Lists7ListDefjp43seqr42PV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jr76region04prod04pair05falser49cursor_knr48geomT_knhic8hdrHF_knhr43oppr44siter46mkSite04truer47CUT1_PCr46cut1_Tr49cut1_regsr48geomB_knhic8CATCH_SThic6HFB_knhic5HF_PChic4HF_Thic7HF_regsr47CUR_OFFr45xslotr44vSPFr46hdr_knhic2RSr47s_fsizer47s_savedr43vRAhic9savedA_knr44s_ipr44vP2V3h5LinuxProcessSemantics5Riscv5Instrlgd7ALU_SUBhic9frameA_knhd4EAluhic6RES_PChic6RES_knhic8RES_regshic5C_SCRhic8CATCH_PChic7CT_regshic7ct_geomhic8cth_geomhicdAFTER_FREE_PChic4FR_Thic7POOLHDRjp43maphic8PoolLive89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~lte6ksubst" s.
Import ListNotations. Import AX2. Import SR. Import CUT. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT2.
Definition bS : ltac2:(zQ "20!h8!m2>1k$0$1") := ltac2:(zQ "30!h8!nb!o1\1k$0@1$2@2$1Nnc^1").
Definition vRET := EVar 132. Definition vN := EVar 133.
Definition SN : Z := 1840.          (* [comment removed for export] *)
Definition RS : Z := 1152.          (* [comment removed for export] *)
Definition POOLHDR : Z := 0x109e20. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition flags0_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "70!v3!qb!v9!vf!hg7!hgc!hh1@3$2$1@3$3@2$4@1$0Z+hirmv8N8$6@3$2$1@3$3@2$4@1$0Z+hgrlu1N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu2N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu3N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu4N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu5N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu6N1@1$0Z@1$5$1").
Definition flags_sel : ltac2:(zQ "30!hhb!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "50!hhb!q5!hi1!hmd!qb\6steady$0M0\6steady$0@1$1$4^1$2$3").
(* [comment removed for export] *)
Definition globals_kn : ltac2:(zQ "30!q5!q1!qb>1u$1@1$0$2") := ltac2:(zQ "70!v3!qb!v9!vf!hg7!hgc!q1\1u$6@3$2$1@3$3@2$4@1$0Z+hgpsp0N8@1$0Z@3$2$1@3$3@2$4@1$0Z+hgpsp8N4@1$0^1@1$5$1").
Definition statics_wr : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "60!v3!qb!v9!hna!hg7!hgc@3$2$1@2$3@2$4@1$0Z+hgpsp0@1$0+h0@3$2$1@2$3@2$4@1$0Z+hgrlu0@1$0+8@1$5$1").
(* [comment removed for export] *)
Inductive pool_state := PoolPristine | PoolIdle | PoolLive.
Definition pool_kn : ltac2:(zQ "30!q5!ho0!qb>1p$1@1$0$2") := ltac2:(zQ "a2!v3!qb!v9!hg7!vf!hgc!ho0!hoe!q5!hna&@3$4@2$3@1$0Z+hgpsq0N8@1$0+hgpsrc&@3$4@2$3@1$0Z+hgpsrcN2@1$0+o0\1p$6@3$7$1M6\1p$6@1$8$1^1@3$2$1@3$4@2$3@1$0Z+hgpsq0N8@1$0Z@1$5$1@3$2$1~0@3$2$1~1@3$2$1@3$4@2$3@1$0Z+hgpsreN2@1$0+nd@1$5$1@3$2$1~0@3$2$1~1@3$2$1@3$4@2$3@1$0Z+hgpsreN2@1$0+l8@3$2$1@3$4@2$3@1$0Z+hgpuhcN2@1$0Z@3$2$1@3$4@2$3@1$0Z+hgpuheN2@1$0+i5@1$5$1@3$2$1@2$9@2$3@1$0Z+hgpsq0@1$0+ih0@1$5$1").
Definition pool_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "c0!v3!hg7!qb!v9!hp3!hp9!hgc!hq1!hq6!hqe!hsc!ht3@3$3$2@4$5@2$1$7$4@1$0@2$b@2$a$9+h0$4@2$1@1$0Z+hgpsq0@1$0+ih0@3$3$2@4$5@2$1@1$0Z+hgpsq0@1$0+ih0@2$1$8Z@1$0+q0@1$6$2").

(* [comment removed for export] *)
Definition opnew_frame_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "a0!qb!v9!hq1!hqe!vf!hg7!hgc!hta!hu0!hsc@3$1$0@3$4@2$5$2$3N8@1$7N0@3$1$0@3$4@2$5$2@2$9$3+8N8$8@1$6$0").
Definition th_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "e0!qb!v9!hq1!hp3!v3!hq6!hu8!hg7!hgc!hqe!hv1!hp9!hsc!ht3@3$1$0@3$6$2+kgggggggggg0+ogggggggggg0@3$1$0@3$6$5+kgggggggggg0+vvvvvvvvvvvvvvm0@3$1$0@2$a$2+h0@3$1$0@4$b@2$7$2$3@1$4@2$d@2$c$9+h0$3@2$7$5Z@1$4+q0@1$8$0").
Definition th_scratch : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "a0!hp3!qb!v9!hgc!v3!hq1!hqe!hna!hg7!ht3@3$2$1@2$7@2$8$5$0@1$4@2$9$6$0@1$3$1").
(* [comment removed for export] *)
Definition boost_regs : ltac2:(zQ "20!m2!q5>2ra$0>2sp$0>2s0$0>2a0$0>2a1$0@1$1$0") := ltac2:(zQ "c0!m2!v9!o1!hta!v3!hgc!hva!ig1!ig7!ige!ih5!ihb\2ra$0\2sp$0\2s0$0\2a0$0\2a1$0@3$1$0@1$4Z@3$1$0^5@3$1$0^4@3$1$0$7@3$1$0@1$4$6@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0^3@3$1$0@1$3N1@3$1$0^2@3$1$0^1@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3N2@3$1$0@1$3N3@3$1$0@1$3N4@3$1$0@1$3N5@3$1$0@1$3N6@3$1$0@1$3N7@3$1$0$a@3$1$0$b@3$1$0$8@3$1$0$9@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$5$0").
(* [comment removed for export] *)
Definition F1_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "70!v3!ii1!hq1!hqe!ii7!ij5!o1@5$4@1$0+vgguc@2$1$2$3$5@1$0Z@1$6N8").
Definition F1_kn : ltac2:(zQ "50!hhb!q5!q1!ho0!qb>6steady$0>1u$2>1p$3@1$1$4") := ltac2:(zQ "h00!hoe!qb!hhb!q1!ijb!ik5!ike!il8!im5!in3!io5!ip2!ho0!ipd!iqb!ir6\6steady$2\1u$3\1p$c@3$0$1$9@3$0$1$f@3$0$1$6@3$0$1$5@3$0$1@1$7^3@3$0$1$4@3$0$1@1$8^2@3$0$1$d@3$0$1@1$b^1@3$0$1$e$a").
Definition F1 : ltac2:(zQ "40!hhb!q1!ho0!is4>6steady$0>1u$1>1p$2$3") := ltac2:(zQ "b0!it0!hhb!hgc!q1!it6!itb!iu4!ho0!iuf!iv5!ivd\6steady$1\1u$3\1p$7@6$8+vggv0$6@1$2$a@3$5^3^2^1$4@1$0$9").
(* [comment removed for export] *)
Definition th_frames_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "d0!qb!v9!hq1!hqe!vf!hg7!ht3!v3!hoe!hgc!hta!in3!ij5@3$8$0@3$1$0@3$4@2$5$2@2$6$3+j0N8@1$7+p0@3$1$0@3$4@2$5$2@2$6$3+i8N8@1$7+pklk8@3$1$0@3$4@2$5$2@2$6$3+h8N8@1$aN1@3$1$0@3$4@2$5$2@2$6$3+h0N8$c@3$1$0@3$4@2$5$2@2$6$3+8N8@1$7+vghi0@1$9$0$b").
Definition AA_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "60!v3!ii1!hq1!hqe!ii7!ht3@5$4@1$0+pksm8@2$1$2@2$5$3+j0@1$0+p0@1$0+h0@1$0+p0").
Definition TH_T : ltac2:(zQ "50!hhb!q5!q1!ho0!qb>6steady$0>1u$2>1p$3@1$1$4") := ltac2:(zQ "f0!hoe!qb!hhb!q1!ijb!ik5!il8!im5!io5!ip2!ho0!ipd!jg6!iqb!ir6\6steady$2\1u$3\1p$a@3$0$1$c@3$0$1$e@3$0$1@1$9^1@3$0$1@1$7^2@3$0$1$b@3$0$1@1$6^3@3$0$1$4@3$0$1$5@3$0$1$d$8").
(* [comment removed for export] *)
Definition F2_regs : ltac2:(zQ "20!m2!q5>2a0$0@1$1$0") := ltac2:(zQ "80!o1!ii1!v3!hq1!hqe!ii7!m2!ht3\2a0$6@5$5@1$0Nh3@2$1$3@2$7$4+j0@1$2+p0^1@1$0N8").
Definition blk_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "f0!v3!hg7!qb!v9!jh6!hp9!hp3!hgc!hq1!hq6!hqe!hv1!hu8!hsc!ht3@3$3$2@3$c$4+1+ogggggggggg0@3$3$2@2$b$4+h0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hggg0@1$0+uhgg0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+vokt8@1$0+hkj0@3$3$2@4$5@2$1$8$6@1$0@2$e@2$d$a+h0$6@2$1$4Z@1$0+p0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1$9Z@1$0+q0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hgrlu0@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hirmv8@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hirpl0@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hgpsp0@1$0+ii0@1$7$2").
(* [comment removed for export] *)
Definition F2H_kn : ltac2:(zQ "30!hhb!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "h20!qb!hoe!hhb!v9!hgc!ijb!ik5!v3!jh6!jhd!il8!im5!ipd!jg6!iqb!ir6!hna!hg7\6steady$2@3$1$0@3$3$0@2$h0@2$h1$8Z@1$7+p0@1$4$0@3$1$0$d@3$1$0$f@3$1$0@1$bZ@3$1$0$c@3$1$0@1$a^1@3$1$0$5@3$1$0$6@3$1$0$e$9").
Definition F2h : ltac2:(zQ "20!hhb!is4>6steady$0$1") := ltac2:(zQ "a0!it0!hhb!hgc!it6!jh6!ji9!jj3!iuf!iv5!ivd\6steady$1@6$7+pksm8@1$6$4@1$2$9@1$5^1$3@1$0$8").

(* [comment removed for export] *)
Definition ucx_val : ltac2:(zQ "20!h8!m2>1i$0$1") := ltac2:(zQ "h10!hhb!m2!jl9!jm0!nb!v3!h8!ii1!jm7!jmd!hq1!jh6!o1!hva!jn3!ig1!hta\1i$6M0\0$0$1@2$2^1N0@1$5+tiqscM0\0$0$1@2$2^1N1@1$5+tiqscM0\0$0$1@2$2^1N2$aM0\0$0$1@2$2^1N3$fM0\0$0$1@2$2^1N4@1$5$dM0\0$0$1@2$2^1N8@2$7$b+m0M0\0$0$1@2$2^1N9@1$5+vluq8M0\0$0$1@2$2^1Na@2$7$a$eM0\0$0$1@2$2^1Nh2@2$7$b+o0M0\0$0$1@2$8@2$3Nh3^1@2$3^1Nh7@1$h0@2$9^1Nh0M0\0$0$1@2$8@2$3Nh8^1@2$3^1Nhb@1$c@2$4Nh4@2$9^1Nh8@1$cM0\0$0$6@2$3^1N7@2$4Nq7^1M0\0$0$6@2$3^1Nh1@2$4Nq4^1@2$4Npa^1").
Fixpoint ucx_from (i n : nat) : list kentry :=
  match n with O => [] | S n' => KWord (SA vA (UC_OFF + 8 * Z.of_nat i)) 8 (ucx_val i) :: ucx_from (S i) n' end.
Fixpoint ucf_from (j n : nat) : list kentry :=
  match n with O => [] | S n' => KWord (SA vA (UC_OFF + 256 + 8 * Z.of_nat j)) 8 (EVar (140 + j)%nat) :: ucf_from (S j) n' end.
Definition HFB_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "e0!qb!v9!hq1!vf!hg7!hta!v3!jh6!hoe!ii1!hgc!jnc!jo8!hu0@3$8$0@2$cN0Ni0@3$8$0@2$bN0Ni0@3$1$0@3$3@2$4$2+ms8N8@1$5N7@3$1$0@3$3@2$4$2+mt0N8@1$5N6@3$1$0@3$3@2$4$2+mt8N8@1$5N5@3$1$0@3$3@2$4$2+mu0N8@1$5N4@3$1$0@3$3@2$4$2+mu8N8@1$5N3@3$1$0@3$3@2$4$2+mv0N8@2$9$7+o0@3$1$0@3$3@2$4$2+mv8N8@1$6+vluq8@3$1$0@3$3@2$4$2+ng0N8$7@3$1$0@3$3@2$4$2+ng8N8@1$6+pkno0@3$1$0@3$3@2$4$2+nh0N8@1$5N2@3$1$0@3$3@2$4$2+nh8N8@1$5N1@3$1$0@3$3@2$4$2+ni0N8@2$9$7+o0@3$1$0@3$3@2$4$2+ni8N8@1$6+vghk0@3$1$0@3$3@2$4$2+nj0N8@1$5N0@3$1$0@3$3@2$4$2+nj8N8$d@1$a$0").
(* [comment removed for export] *)
Definition PVB : ltac2:(zQ "20!q5!h8@1$0$1") := ltac2:(zQ "40!hoe!h8!jqb!jr2@3$0$1$3@2$2NocNie").
Definition REG_th : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "c0!q1!kg1!m2!kg7!v9!hp3!v3!hgc!hq1!jh6!hqe!ht3@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8$5@2$b$a$5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$6Z+hgpsp0+h0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$6Z+hgrlu0+7@1$7@2$1@2$1$2$0$0").
Definition REG_tp : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "b0!q1!kg1!m2!kg7!v9!v3!hp3!hgc!hq1!hqe!ht3@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8$6@2$a$9$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgpsq0+ih0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgpsp0+h0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgrlu0+7@1$7@2$1@2$1$2$0$0").

(* [comment removed for export] *)
Definition HF_PC : Z := 0xd2c6c.
Definition HF_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "e0!m2!v9!o1!v3!hgc!hva!ii1!hq1!ig1!jh6!ig7!ige!ih5!ihb@3$1$0@1$3Z@3$1$0@1$3+tirs0@3$1$0$7@3$1$0$8@3$1$0@1$3$5@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@2$6$9+m0@3$1$0@1$3+vppq8@3$1$0@1$3+6@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3+hhhle@3$1$0@1$3+hhrqe@3$1$0@1$3+hiht5@3$1$0@1$3+pkuq8@3$1$0@1$3+hhpg8@3$1$0@1$3+8@3$1$0$c@3$1$0$d@3$1$0$a@3$1$0$b@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$4$0").
(* [comment removed for export] *)
Definition hdrHF_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "90!jh6!qb!v9!hg7!v3!vf!hgc!ii1!hna@3$2$1@3$5@2$3$0+8N8@1$4+1@3$2$1@3$5@2$3$0+h0N8@1$4+vluq8@3$2$1@3$5@2$3$0+h8N8@1$4+pitqc@3$2$1@3$5@2$3$0+i0N8@1$4+nntr4@3$2$1@3$5@2$3$0+i8N8@1$4+nnsq8@3$2$1@3$5@2$3$0+j0N8@1$4Z@3$2$1@3$5@2$3$0+j8N4@1$4Z@3$2$1@3$5@2$3$0+jcN4@1$4+1@3$2$1@3$5@2$3$0+k0N8@1$4+invof@3$2$1@3$5@2$3$0+k8N8@1$4+invn0@3$2$1@3$5@2$3$0+l0N8@1$4+knpp4@3$2$1@3$5@2$3$0+l8N8@2$7$0+o0@3$2$1@3$5@2$3$0+m0N8@1$4+kjkskuknkjirirg0@3$2$1@3$5@2$3$0+m8N8@1$4+pkms8@3$2$1@3$5@2$3$0+n0N8@1$4Z@3$2$1@3$5@2$3$0+n8N8@1$4Z@3$2$1@3$5@2$3$0+o0N8@1$4+vlug0@3$2$1@2$8@2$3$0Z@1$4+p0@1$6$1").
Definition HF_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h10!qb!hoe!v9!kgd!hp3!v3!hq1!hna!hg7!hgc!ijb!kh4!hi1!ki0!ik5!kib!kj7@3$1$0@3$2$0@2$7@2$8$6$4@1$5@1$h0$4@3$2$0@2$7@2$8$6+mn8@1$5+l0@1$9$0@3$1$0@1$b$3@3$1$0$f@3$1$0$c@3$1$0$a@3$1$0$e@1$d$3").
Definition CATCH_ST : ltac2:(zQ "10!kje$0") := ltac2:(zQ "30!hgc!q1!kk5@4$2+knpo4+h0@1$0$1+knpp4").
(* [comment removed for export] *)
Definition cut1c : ltac2:(zQ "30!hhb!kje!is4>6phase2$0>2st$1$2") := ltac2:(zQ "f0!it0!hoe!hhb!hgc!kke!kl4!it6!kle!km7!kn3!kje!iuf!qb!iv5!ivd\6phase2$2\2st$a@6$b$5@1$8^2@1$3$e@3$1$c@1$7^2@3$9^2$4^1$6@1$0$d").
(* [comment removed for export] *)
Definition F3 : ltac2:(zQ "10!is4$0") := ltac2:(zQ "h00!hoe!qb!it0!kgd!hgc!kke!it6!kn3!kne!koa!kp4!kpd!kq5!iuf!iv5!ivd@6$d$a$c@1$4$f@3$0$1$b@3$0$1$9@3$7$3$5$8$6@1$2$e").
Definition REG_hf : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "b0!q1!kg1!m2!kg7!v9!hq1!hp3!hgc!kr0!jh6!kj7@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$6@1$a$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$8+im0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5+mn8+l0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@1$7@2$1@2$1$2$0$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PAD_regs : ltac2:(zQ "30!q5!q1!m2>3sel$1@1$0$2") := ltac2:(zQ "b0!m2!v9!kra!v3!hgc!q1!hva!ii1!ig1!jh6!ks2\3sel$5@3$1$0@1$3Z@3$1$0@1$2N1@3$1$0$a@3$1$0$8@3$1$0@1$3$6@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@2$7$9+m0@3$1$0@1$3^1@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@1$4$0").
Definition PAD_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h00!v3!qb!hg7!v9!jh6!hp9!hoe!hq6!hu8!hgc!kke!ijb!hi1!ks9!ik5!hv1@3$6$1@1$d$a@3$6$1$c@3$6$1$b@3$6$1$e@3$3$1@3$8$7+kgggggggggg0+vvvvvvvvvvvvvvm0@3$3$1@3$8$4+1+ogggggggggg0@3$3$1@2$f$4+h0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hggg0@1$0+uhgg0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+vokt8@1$0+hkj0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2$7Z@1$0+q0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hgrlu0@1$0+8@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hirmv8@1$0+8@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hirpl0@1$0+8@1$9$1").

(* [comment removed for export] *)
Definition RES_PC : Z := 0xd30f4.
Definition RES_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "80!ii1!hq1!jh6!kt2!hta!ii7!hu0!o1@5$5$6@2$0$1$3@1$4N0@2$0$2+m0@1$7N8").
(* [comment removed for export] *)
Fixpoint savedA_kn (fsize : Z) (offs : list Z) (k : nat) : list kentry :=
  match offs with [] => [] | off :: r => KWord (SA vA (RS + fsize + off)) 8 (sslot k) :: savedA_kn fsize r (S k) end.
Definition frameA_kn : ltac2:(zQ "30!q5!kje!qb>2st$1@1$0$2") := ltac2:(zQ "d0!kt8!v9!ku2!kje!hq1!kuc!kt2!kv2!vf!hg7!qb!hsc!ht3\2st$3@3$1$a@3$8@2$9$4@2$c@2$b$6@1$0^1+8N8$5@3$7@1$0^1@1$2^1N0").
Definition RES_kn : ltac2:(zQ "30!q5!kje!qb>2st$1@1$0$2") := ltac2:(zQ "he0!qb!hoe!v9!v3!hg7!hp3!hq1!kt2!hgc!hp9!hu8!ht3!kke!kvf!jh6!lg6!lj1!ii1!ijb!hi1!ki0!ks9!ik5!kt8!kje!hq6!ljc!hu0!lk9!hna\2st$h8@3$1$0@3$2$0@2$hd@2$4$6$5@1$3@2$b$7$5@1$8$0@3$1$0@1$ha^1@3$1$0@3$2$0@3$a$hb@1$d^1@1$d^1@3$2$0@4$9@2$4$eZ@1$3+p0@2$4$6$7@1$3@1$h7^1@3$2$0@3$a@3$hc$h0$f@2$h1$6$7+h0+ogggggggggg0@1$8$0@3$1$0@1$h5$c@3$1$0$h3@3$1$0$h2@3$1$0$h6@3$1$0@1$h4$c@3$2$0@4$9@2$4$6$5@1$3@2$b$7$5@2$4$eZ@1$3+p0@3$2$0@4$9@2$4$6$5@1$3@2$b$7$5@2$4$h9Z@1$3+q0@3$2$0@3$a$f+kgggggggggg0+ogggggggggg0@1$8$0").
Definition RES : ltac2:(zQ "20!kje!is4>2st$0$1") := ltac2:(zQ "a0!it0!hgc!it6!kje!ll0!lla!lm4!iuf!iv5!ivd\2st$3@6$7$4$6@1$1$9@1$5^1$2@1$0$8").
Definition REG_res : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "b0!q1!kg1!m2!kg7!v9!hp3!hgc!hq1!jh6!kt2!ht3@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$7$5@2$a$9$5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8Z+p0@1$6@2$1@2$1$2$0$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CATCH_PC : Z := 0x47994.
Definition FREE_PC : Z := 0xdc61c.
Definition AFTER_FREE_PC : Z := 0x948a0.
Definition AFTER_CATCH_PC : Z := 0x47984.
Definition C_SCR : Z := 4096.
Definition CT_regs : ltac2:(zQ "20!m2!q5>2a0$0@1$1$0") := ltac2:(zQ "50!o1!hq1!hta!ii7!m2\2a0$4@5$3@1$0Nh3$1@1$2N0^1@1$0N8").
Definition ct_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "d0!qb!v9!v3!hg7!hq1!hq6!hu8!ln0!hp9!hgc!lg6!hv1!kj7@3$1$0@3$6$4+kgggggggggg0+ogggggggggg0@3$1$0@2$b$4+h0@3$1$0@3$6$5+kgggggggggg0+vvvvvvvvvvvvvvm0@3$1$0@3$6$a+kgggggggggg0+ogggggggggg0@3$1$0@4$8@2$3$4@1$c$7@1$2$7@2$3$5Z@1$2+q0@3$1$0@4$8@2$3@1$2Z+hgpsp0@1$2+ii0@2$3$5Z@1$2+q0@1$9$0").
Definition cth_geom : ltac2:(zQ "30!hhb!q5!qb>2hi$0@1$1$2") := ltac2:(zQ "f0!v3!hg7!qb!jh6!v9!hp9!hhb!ln0!hu8!hgc!hq1!hq6!hv1!kj7!ht3\2hi$6@3$4$2M6\2hi$6$2^1@3$8$3+hitgg0+ogggggggggg0@3$8$3+1@2$e+hggg0+p0@3$4$2@2$c$3+h0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hggg0@1$0+uhgg0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+vokt8@1$0+hkj0@3$4$2@4$5@2$1$a@1$d$7@1$0$7@2$1$3Z@1$0+p0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1$bZ@1$0+q0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hgpsp0@1$0+ii0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hgrlu0@1$0+8@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hirmv8@1$0+8@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hirpl0@1$0+8@1$9$2").
(* [comment removed for export] *)
Definition F5a : ltac2:(zQ "30!hhb!ho0!is4>2ps$1>2hi$0$2") := ltac2:(zQ "hf0!qb!hoe!hgc!ln0!it0!hhb!v9!kke!it6!ii1!ijb!hi1!ks9!ik5!v3!hq1!jh6!ln9!lo5!lp0!lpb!im5!ip2!ho0!ipd!hna!hg7!iuf!iv5!ivd!kj7\2ps$h7\2hi$5@6$hb$h1@1$h2@2$9$h0+m0@1$2$hd@3$1$0@3$6$0@2$h9@2$ha$f@1$he$3@1$e$3@1$2$0@3$1$0@1$c$7@3$1$0@1$h5+1@3$1$0$h8@3$1$0@1$h6^2@3$1$0$b@3$1$0$a@3$1$0$d@3$1$0$h3@1$h4^1$8@1$4$hc").
Definition FR_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "70!jh6!ii1!v3!hq1!lq7!ii7!o1@5$5@1$2$4@2$1$3-i0$0$0@1$6N8").
Definition FR_T : ltac2:(zQ "30!q5!ho0!qb>1p$1@1$0$2") := ltac2:(zQ "h40!qb!hoe!v9!hq1!hg7!vf!v3!ln0!hta!hgc!ijb!hi1!ik5!lp0!im5!ip2!ho0!ipd!hna!kj7\1p$h0@3$1$0@3$2$0@3$5@2$4$3-8N8@1$6+knppc@3$2$0@3$5@2$4$3-h0N8@1$8N0@3$2$0@3$5@2$4$3-h8N8@1$8N1@3$2$0@2$h2@2$4$3@1$h3$7@1$6$7@1$9$0@3$1$0@1$eZ@3$1$0$h1@3$1$0@1$f^1@3$1$0$b@3$1$0$a@3$1$0$c$d").
Definition REG_ct : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "b0!q1!kg1!m2!kg7!v9!v3!ln0!hgc!hq1!jh6!kj7@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8@1$a$6$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgpsp0+ii0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgrlu0+7@1$7@2$1@2$1$2$0$0").
(* [comment removed for export] *)
Definition F5b : ltac2:(zQ "20!ho0!is4>1p$0$1") := ltac2:(zQ "e0!o1!it0!hgc!it6!ii1!hq1!jh6!lq7!lr8!ii7!ho0!iuf!iv5!ivd\1p$a@6$b$7@5$9@1$0Nh3@2$4$5-i0$6@1$0Ni5@1$0N8@1$2$d@1$8^1$3@1$1$c").
Definition DONE_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "40!o1!hq1!hta!ii7@5$3@1$0Nh3$1@1$2N0@1$0Ni5@1$0N8").   (* [comment removed for export] *)
Definition DONE_T : ltac2:(zQ "30!q5!ho0!qb>1p$1@1$0$2") := ltac2:(zQ "a0!hoe!qb!ijb!hi1!ik5!lp0!im5!ip2!ho0!ipd\1p$8@3$0$1@1$6Z@3$0$1$9@3$0$1@1$7^1@3$0$1$3@3$0$1$2@3$0$1$4$5").
Definition REG_done : ltac2:(zQ "20!q5!jv7@1$0$1") := ltac2:(zQ "a0!q1!kg1!m2!kg7!v9!v3!ln0!hgc!hq1!kj7@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8@1$9$6$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgpsp0+ii0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgrlu0+7@1$7@2$1@2$1$2$0$0").
(* [comment removed for export] *)
Definition F5p : ltac2:(zQ "10!is4$0") := ltac2:(zQ "i30!qb!hoe!h8!hgc!v3!m2!v9!kg1!ln0!ls0!it0!kg7!kke!lsb!it6!ijb!hi1!ks9!ik5!hq1!ln9!lo5!lt2!lp0!im5!ip2!ipd!mi1!hna!hg7!iuf!iv5!ivd!hsc!kj7@6$he$h4@1$h5@1$4@2$i1$9+m0@1$3$i0@3$1$0@3$6$0@2$hc@2$hd$h3@1$i2$8@1$4$8@1$3$0@3$1$0@4$d$0$0@1$hb@3$6@2$7$2$5@4$b$2$5N2@1$4$9@1$3@2$7$2$5@1$h1$c@3$1$0@1$h8+1@3$1$0$ha@3$1$0@1$h9$h6@3$1$0$h0@3$1$0$f@3$1$0$h2$h7$e@1$a$hf").
End CUT2.
(* [comment removed for export] *)
