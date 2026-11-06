(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAsanPlanCore XSegLib XSegRun EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhCut.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hd4expr37Corelib4Init3Natm93addhd4EVar37Corelib7Numbers7BinNumso81Z04listhd6kentry89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~r43lit04conshd5KWordhd2SA03nilr47vCANARY04boolr48flags_kn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~hid9flags0_knhd3KWrhidapool_state03apphd5KDisjr43ZLOr42vAr45vAUXVhid2SN46Stdlib6ZArith6BinInt1Zhr63addhr63subhid2bShid4vREThd6KRangehd6KAlignr44RATPr43vGPr44vS10r44vS11r43vS8r43vS9r43addhidaboost_regshid2vNr47auxv_knr46img_knr47newh_knhid9flags_selhidaglobals_knhideopnew_frame_knhid9pool_geomhid7pool_knhidastatics_wrhid7th_geomhidath_scratchhd9sym_state04Nonehd3SSRhd5saddrhd6sentryr42NXhid5F1_knhid7F1_regshidcth_frames_knr44vHDRhid8blk_geomhid6F2H_knhid7F2_regs46Stdlib5Arith8PeanoNat3Natjk03eqbjk03leb04andbm93subr46UC_OFFhid8ucf_fromhid8ucx_from37Corelib5Lists7ListDefjp63seqr42PV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~jr96region04prod04pair05falser49cursor_knr48geomT_knhid8hdrHF_knhr63oppr44siter46mkSite04truer47CUT1_PCr46cut1_Tr49cut1_regsr48geomB_knhid8CATCH_SThid6HFB_knhid5HF_PChid4HF_Thid7HF_regsr47CUR_OFFr45xslotr44vSPFr46hdr_knhid2RSr47s_fsizer47s_savedr43vRAhid9savedA_knr44s_ipr44vP2V3h5LinuxProcessSemantics5Riscv5Instrlgf7ALU_SUBhd4EAluhid9frameA_knhid6RES_PChid6RES_knhid8RES_regshid5C_SCRhid8CATCH_PChid7CT_regshid7ct_geomhid8cth_geomhiddAFTER_FREE_PChid4FR_Thid7POOLHDRjp63map89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~lt46ksubsthid8PoolLive" s.
Import ListNotations. Import AX2. Import SR. Import CUT. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT2.
Definition bS : ltac2:(zQ "20!h8!m2>1k$0$1") := ltac2:(zQ "30!h8!nb!o1\1k$0@1$2@2$1Nnc^1").
Definition vRET := EVar 132. Definition vN := EVar 133.
Definition SN : Z := 1840.          (* [comment removed for export] *)
Definition RS : Z := 1152.          (* [comment removed for export] *)
Definition POOLHDR : Z := 0x10d360. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition flags0_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "70!v4!qb!va!hg0!hg8!hgd!hh2@3$2$1@3$3@2$4@1$0Z+hiusj8N8$6@3$2$1@3$3@2$4@1$0Z+hguri1N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri2N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri3N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri4N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri5N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri6N1@1$0Z@1$5$1").
Definition flags_sel : ltac2:(zQ "30!hhc!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "50!hhc!q5!qb!hi2!hmf\6steady$0M0\6steady$0@1$1$2^1$3$4").
(* [comment removed for export] *)
Definition globals_kn : ltac2:(zQ "30!q5!q1!qb>1u$1@1$0$2") := ltac2:(zQ "70!v4!qb!va!hg0!hg8!hgd!q1\1u$6@3$2$1@3$3@2$4@1$0Z+hgtht0N8@1$0Z@3$2$1@3$3@2$4@1$0Z+hgtht8N4@1$0^1@1$5$1").
Definition statics_wr : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "60!v4!qb!va!hnc!hg8!hgd@3$2$1@2$3@2$4@1$0Z+hgtht0@1$0+h0@3$2$1@2$3@2$4@1$0Z+hguri0@1$0+8@1$5$1").
(* [comment removed for export] *)
Inductive pool_state := PoolPristine | PoolIdle | PoolLive.
Definition pool_kn : ltac2:(zQ "30!q5!qb!ho2>1p$2@1$0$1") := ltac2:(zQ "a2!v4!qb!va!hg8!hg0!hgd!ho2!hp0!q5!hnc&@3$4@2$3@1$0Z+hgthu0N8@1$0+hgthvc&@3$4@2$3@1$0Z+hgthvcN2@1$0+o0\1p$6@3$7$1M6\1p$6@1$8$1^1@3$2$1@3$4@2$3@1$0Z+hgthu0N8@1$0Z@1$5$1@3$2$1~0@3$2$1~1@3$2$1@3$4@2$3@1$0Z+hgthveN2@1$0+nd@1$5$1@3$2$1~0@3$2$1~1@3$2$1@3$4@2$3@1$0Z+hgthveN2@1$0+l8@3$2$1@3$4@2$3@1$0Z+hgtjlcN2@1$0Z@3$2$1@3$4@2$3@1$0Z+hgtjleN2@1$0+i5@1$5$1@3$2$1@2$9@2$3@1$0Z+hgthu0@1$0+ih0@1$5$1").
Definition pool_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "c0!v4!hg8!qb!va!hp5!hpd!hgd!hq3!hq8!hr0!hse!ht5@3$3$2@4$4@2$1$7$5@1$0@2$b@2$a$9+h0$5@2$1@1$0Z+hgthu0@1$0+ih0@3$3$2@4$4@2$1@1$0Z+hgthu0@1$0+ih0@2$1$8Z@1$0+q0@1$6$2").

(* [comment removed for export] *)
Definition opnew_frame_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "a0!qb!va!hg0!hg8!hq3!hr0!hgd!htc!hu2!hse@3$1$0@3$2@2$3$4$5N8@1$7N0@3$1$0@3$2@2$3$4@2$9$5+8N8$8@1$6$0").
Definition th_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "e0!qb!va!hq3!hua!hg8!hpd!v4!hq8!hgd!hv3!hp5!hr0!hse!ht5@3$1$0@3$3$2+kgggggggggg0+ogggggggggg0@3$1$0@3$3$7+kgggggggggg0+vvvvvvvvvvvvvvm0@3$1$0@2$9$2+h0@3$1$0@4$a@2$4$2$5@1$6@2$d@2$c$b+h0$5@2$4$7Z@1$6+q0@1$8$0").
Definition th_scratch : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "a0!qb!hpd!va!hgd!hnc!hg8!v4!hq3!hr0!ht5@3$2$0@2$4@2$5$7$1@1$6@2$9$8$1@1$3$0").
(* [comment removed for export] *)
Definition boost_regs : ltac2:(zQ "20!m2!q5>2ra$0>2sp$0>2s0$0>2a0$0>2a1$0@1$1$0") := ltac2:(zQ "c0!m2!va!o1!htc!v4!hgd!hvc!ig3!ig9!ih0!ih7!ihd\2ra$0\2sp$0\2s0$0\2a0$0\2a1$0@3$1$0@1$4Z@3$1$0^5@3$1$0^4@3$1$0$7@3$1$0@1$4$6@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0^3@3$1$0@1$3N1@3$1$0^2@3$1$0^1@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3N2@3$1$0@1$3N3@3$1$0@1$3N4@3$1$0@1$3N5@3$1$0@1$3N6@3$1$0@1$3N7@3$1$0$a@3$1$0$b@3$1$0$8@3$1$0$9@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$5$0").
(* [comment removed for export] *)
Definition F1_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "70!v4!o1!ii3!hq3!hr0!ii9!ij7@5$5@1$0+vjlp4@2$2$3$4$6@1$0Z@1$1N8").
Definition F1_kn : ltac2:(zQ "50!hhc!q5!q1!qb!ho2>6steady$0>1u$2>1p$4@1$1$3") := ltac2:(zQ "h00!hp0!qb!hhc!q1!ijd!ik7!il0!ila!im7!in5!io7!ip4!ho2!ipf!iqd!ir8\6steady$2\1u$3\1p$c@3$0$1$9@3$0$1$f@3$0$1$6@3$0$1$5@3$0$1@1$7^3@3$0$1$4@3$0$1@1$8^2@3$0$1$d@3$0$1@1$b^1@3$0$1$e$a").
Definition F1 : ltac2:(zQ "40!hhc!q1!is6!ho2>6steady$0>1u$1>1p$3$2") := ltac2:(zQ "b0!it2!hhc!hgd!q1!it8!ite!iu6!iuf!iv4!ivd!ho2\6steady$1\1u$3\1p$a@6$4+vjlp8$9@1$2$6@3$8^3^2^1$7@1$0$5").
(* [comment removed for export] *)
Definition th_frames_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "d0!qb!va!hg0!hg8!hq3!hr0!ht5!v4!hp0!hgd!htc!in5!ij7@3$8$0@3$1$0@3$2@2$3$4@2$6$5+j0N8@1$7+p0@3$1$0@3$2@2$3$4@2$6$5+i8N8@1$7+pnpv0@3$1$0@3$2@2$3$4@2$6$5+h8N8@1$aN1@3$1$0@3$2@2$3$4@2$6$5+h0N8$c@3$1$0@3$2@2$3$4@2$6$5+8N8@1$7+vjls8@1$9$0$b").
Definition AA_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "60!v4!ii3!hq3!hr0!ii9!ht5@5$4@1$0+pohh0@2$1$2@2$5$3+j0@1$0+p0@1$0+h0@1$0+p0").
Definition TH_T : ltac2:(zQ "50!hhc!q5!q1!qb!ho2>6steady$0>1u$2>1p$4@1$1$3") := ltac2:(zQ "f0!hp0!qb!hhc!q1!ijd!ik7!ila!im7!io7!ip4!ho2!ipf!jg8!iqd!ir8\6steady$2\1u$3\1p$a@3$0$1$c@3$0$1$e@3$0$1@1$9^1@3$0$1@1$7^2@3$0$1$b@3$0$1@1$6^3@3$0$1$4@3$0$1$5@3$0$1$d$8").
(* [comment removed for export] *)
Definition F2_regs : ltac2:(zQ "20!m2!q5>2a0$0@1$1$0") := ltac2:(zQ "80!o1!m2!ii3!v4!hq3!hr0!ii9!ht5\2a0$1@5$6@1$0Nh3@2$2$4@2$7$5+j0@1$3+p0^1@1$0N8").
Definition blk_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "f0!v4!hg8!qb!va!jh8!hp5!hpd!hgd!hv3!hua!hq3!hq8!hr0!hse!ht5@3$3$2@3$9$4+1+ogggggggggg0@3$3$2@2$8$4+h0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hggg0@1$0+ukgg0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+vrpu0@1$0+hkm8@3$3$2@4$5@2$1$a$6@1$0@2$e@2$d$c+h0$6@2$1$4Z@1$0+p0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1$bZ@1$0+q0@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hguri0@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hiusj8@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hiuup0@1$0+8@3$3$2@4$5@2$1$4Z@1$0+p0@2$1@1$0Z+hgtht0@1$0+ii0@1$7$2").
(* [comment removed for export] *)
Definition F2H_kn : ltac2:(zQ "30!hhc!q5!qb>6steady$0@1$1$2") := ltac2:(zQ "h20!qb!hp0!hhc!va!hgd!hnc!hg8!ijd!ik7!v4!jh8!jhf!ila!im7!ipf!jg8!iqd!ir8\6steady$2@3$1$0@3$3$0@2$5@2$6$aZ@1$9+p0@1$4$0@3$1$0$f@3$1$0$h1@3$1$0@1$dZ@3$1$0$e@3$1$0@1$c^1@3$1$0$7@3$1$0$8@3$1$0$h0$b").
Definition F2h : ltac2:(zQ "20!hhc!is6>6steady$0$1") := ltac2:(zQ "a0!it2!hhc!hgd!it8!ite!iu6!iuf!jh8!jib!jj5\6steady$1@6$3+pohh0@1$9$7@1$2$5@1$8^1$6@1$0$4").

(* [comment removed for export] *)
Definition ucx_val : ltac2:(zQ "20!h8!m2>1i$0$1") := ltac2:(zQ "h10!hhc!m2!jlb!jm2!nb!v4!h8!ii3!jm9!jmf!o1!hq3!jh8!hvc!jn5!ig3!htc\1i$6M0\0$0$1@2$2^1N0@1$5+tlvn4M0\0$0$1@2$2^1N1@1$5+tlvn4M0\0$0$1@2$2^1N2$bM0\0$0$1@2$2^1N3$fM0\0$0$1@2$2^1N4@1$5$dM0\0$0$1@2$2^1N8@2$7$c+m0M0\0$0$1@2$2^1N9@1$5+vpjr0M0\0$0$1@2$2^1Na@2$7$b$eM0\0$0$1@2$2^1Nh2@2$7$c+o0M0\0$0$1@2$8@2$3Nh3^1@2$3^1Nh7@1$h0@2$9^1Nh0M0\0$0$1@2$8@2$3Nh8^1@2$3^1Nhb@1$a@2$4Nh4@2$9^1Nh8@1$aM0\0$0$6@2$3^1N7@2$4Nq7^1M0\0$0$6@2$3^1Nh1@2$4Nq4^1@2$4Npa^1").
Fixpoint ucx_from (i n : nat) : list kentry :=
  match n with O => [] | S n' => KWord (SA vA (UC_OFF + 8 * Z.of_nat i)) 8 (ucx_val i) :: ucx_from (S i) n' end.
Fixpoint ucf_from (j n : nat) : list kentry :=
  match n with O => [] | S n' => KWord (SA vA (UC_OFF + 256 + 8 * Z.of_nat j)) 8 (EVar (140 + j)%nat) :: ucf_from (S j) n' end.
Definition HFB_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "e0!qb!va!hg0!hg8!hq3!htc!v4!jh8!hp0!ii3!hgd!jne!joa!hu2@3$8$0@2$cN0Ni0@3$8$0@2$bN0Ni0@3$1$0@3$2@2$3$4+ms8N8@1$5N7@3$1$0@3$2@2$3$4+mt0N8@1$5N6@3$1$0@3$2@2$3$4+mt8N8@1$5N5@3$1$0@3$2@2$3$4+mu0N8@1$5N4@3$1$0@3$2@2$3$4+mu8N8@1$5N3@3$1$0@3$2@2$3$4+mv0N8@2$9$7+o0@3$1$0@3$2@2$3$4+mv8N8@1$6+vpjr0@3$1$0@3$2@2$3$4+ng0N8$7@3$1$0@3$2@2$3$4+ng8N8@1$6+pnsi8@3$1$0@3$2@2$3$4+nh0N8@1$5N2@3$1$0@3$2@2$3$4+nh8N8@1$5N1@3$1$0@3$2@2$3$4+ni0N8@2$9$7+o0@3$1$0@3$2@2$3$4+ni8N8@1$6+vjlu8@3$1$0@3$2@2$3$4+nj0N8@1$5N0@3$1$0@3$2@2$3$4+nj8N8$d@1$a$0").
(* [comment removed for export] *)
Definition PVB : ltac2:(zQ "20!q5!h8@1$0$1") := ltac2:(zQ "40!hp0!h8!jqd!jr4@3$0$1$3@2$2NocNie").
Definition REG_th : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "c0!q1!kg3!m2!kg9!va!hpd!v4!hgd!hq3!jh8!hr0!ht5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8$5@2$b$a$5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$6Z+hgtht0+h0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$6Z+hguri0+7@1$7@2$1@2$1$2$0$0").
Definition REG_tp : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "b0!q1!kg3!m2!kg9!va!v4!hpd!hgd!hq3!hr0!ht5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8$6@2$a$9$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgthu0+ih0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgtht0+h0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hguri0+7@1$7@2$1@2$1$2$0$0").

(* [comment removed for export] *)
Definition HF_PC : Z := 0xd6114.
Definition HF_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "e0!m2!va!o1!v4!hgd!hvc!ii3!hq3!ig3!jh8!ig9!ih0!ih7!ihd@3$1$0@1$3Z@3$1$0@1$3+tmgm8@3$1$0$7@3$1$0$8@3$1$0@1$3$5@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@2$6$9+m0@3$1$0@1$3+vsuu8@3$1$0@1$3+6@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3+hhhn7@3$1$0@1$3+hhrs7@3$1$0@1$3+hihue@3$1$0@1$3+pojl0@3$1$0@1$3+hhpi1@3$1$0@1$3+8@3$1$0$c@3$1$0$d@3$1$0$a@3$1$0$b@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$4$0").
(* [comment removed for export] *)
Definition hdrHF_kn : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "90!qb!jh8!va!hg8!hg0!v4!hgd!hnc!ii3@3$2$0@3$4@2$3$1+8N8@1$5+1@3$2$0@3$4@2$3$1+h0N8@1$5+vpjr0@3$2$0@3$4@2$3$1+h8N8@1$5+pmil4@3$2$0@3$4@2$3$1+i0N8@1$5+nrilc@3$2$0@3$4@2$3$1+i8N8@1$5+nrhl0@3$2$0@3$4@2$3$1+j0N8@1$5Z@3$2$0@3$4@2$3$1+j8N4@1$5Z@3$2$0@3$4@2$3$1+jcN4@1$5+1@3$2$0@3$4@2$3$1+k0N8@1$5+ioghf@3$2$0@3$4@2$3$1+k8N8@1$5+iogg0@3$2$0@3$4@2$3$1+l0N8@1$5+knll0@3$2$0@3$4@2$3$1+l8N8@2$8$1+o0@3$2$0@3$4@2$3$1+m0N8@1$5+kjkskuknkjirirg0@3$2$0@3$4@2$3$1+m8N8@1$5+pnrn0@3$2$0@3$4@2$3$1+n0N8@1$5Z@3$2$0@3$4@2$3$1+n8N8@1$5Z@3$2$0@3$4@2$3$1+o0N8@1$5+vpjg8@3$2$0@2$7@2$3$1Z@1$5+p0@1$6$0").
Definition HF_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h10!qb!hp0!va!kgf!hnc!hg8!hpd!v4!hq3!hgd!ijd!kh6!hi2!ki2!ik7!kid!kj9@3$1$0@3$2$0@2$4@2$5$8$6@1$7@1$h0$6@3$2$0@2$4@2$5$8+mn8@1$7+l0@1$9$0@3$1$0@1$b$3@3$1$0$f@3$1$0$c@3$1$0$a@3$1$0$e@1$d$3").
Definition CATCH_ST : ltac2:(zQ "10!kk0$0") := ltac2:(zQ "30!hgd!q1!kk7@4$2+knlk0+h0@1$0$1+knll0").
(* [comment removed for export] *)
Definition cut1c : ltac2:(zQ "30!hhc!is6!kk0>6phase2$0>2st$2$1") := ltac2:(zQ "f0!it2!hp0!hhc!hgd!kl0!it8!qb!ite!iu6!kl6!iuf!km0!km9!kn5!kk0\6phase2$2\2st$e@6$5$9@1$c^2@1$3$8@3$1$6@1$b^2@3$d^2$4^1$a@1$0$7").
(* [comment removed for export] *)
Definition F3 : ltac2:(zQ "10!is6$0") := ltac2:(zQ "h00!hp0!qb!it2!kgf!hgd!kl0!it8!ite!iu6!iuf!kn5!ko0!koc!kp6!kpf!kq7@6$6$d$f@1$4$8@3$0$1$e@3$0$1$c@3$a$3$5$b$9@1$2$7").
Definition REG_hf : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "b0!q1!kg3!m2!kg9!va!hq3!hpd!hgd!kr2!jh8!kj9@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$6@1$a$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5$8+im0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$5+mn8+l0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@1$7@2$1@2$1$2$0$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PAD_regs : ltac2:(zQ "30!q5!q1!m2>3sel$1@1$0$2") := ltac2:(zQ "b0!m2!va!krc!v4!hgd!q1!hvc!ii3!ig3!jh8!ks4\3sel$5@3$1$0@1$3Z@3$1$0@1$2N1@3$1$0$a@3$1$0$8@3$1$0@1$3$6@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@2$7$9+m0@3$1$0@1$3^1@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@1$4$0").
Definition PAD_T : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "h00!v4!qb!hg8!va!jh8!hp5!hp0!hua!hq8!hgd!kl0!hv3!ijd!hi2!ksb!ik7@3$6$1@1$e$a@3$6$1$d@3$6$1$c@3$6$1$f@3$3$1@3$7$8+kgggggggggg0+vvvvvvvvvvvvvvm0@3$3$1@3$7$4+1+ogggggggggg0@3$3$1@2$b$4+h0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hggg0@1$0+ukgg0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+vrpu0@1$0+hkm8@3$3$1@4$5@2$2$4Z@1$0+p0@2$2$8Z@1$0+q0@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hguri0@1$0+8@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hiusj8@1$0+8@3$3$1@4$5@2$2$4Z@1$0+p0@2$2@1$0Z+hiuup0@1$0+8@1$9$1").

(* [comment removed for export] *)
Definition RES_PC : Z := 0xd659c.
Definition RES_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "80!ii3!o1!hq3!jh8!kt4!htc!ii9!hu2@5$6$7@2$0$2$4@1$5N0@2$0$3+m0@1$1N8").
(* [comment removed for export] *)
Fixpoint savedA_kn (fsize : Z) (offs : list Z) (k : nat) : list kentry :=
  match offs with [] => [] | off :: r => KWord (SA vA (RS + fsize + off)) 8 (sslot k) :: savedA_kn fsize r (S k) end.
Definition frameA_kn : ltac2:(zQ "30!q5!qb!kk0>2st$2@1$0$1") := ltac2:(zQ "d0!kta!va!hg0!hg8!qb!ku4!kk0!hq3!kue!kt4!kv4!hse!ht5\2st$6@3$1$4@3$2@2$3$7@2$c@2$b$9@1$0^1+8N8$8@3$a@1$0^1@1$5^1N0").
Definition RES_kn : ltac2:(zQ "30!q5!qb!kk0>2st$2@1$0$1") := ltac2:(zQ "he0!qb!hp0!va!hg8!v4!hpd!hq3!kt4!hgd!hp5!hua!ht5!kl0!lg1!jh8!lg8!lj3!lje!hnc!ii3!ijd!hi2!ki2!ksb!ik7!kta!kk0!hq8!lk5!hu2\2st$ha@3$1$0@3$2$0@2$h2@2$3$6$5@1$4@2$b$7$5@1$8$0@3$1$0@1$hc^1@3$1$0@3$2$0@3$a$hd@1$d^1@1$d^1@3$2$0@4$9@2$3$eZ@1$4+p0@2$3$6$7@1$4@1$h9^1@3$2$0@3$a@3$h1$h0$f@2$h3$6$7+h0+ogggggggggg0@1$8$0@3$1$0@1$h7$c@3$1$0$h5@3$1$0$h4@3$1$0$h8@3$1$0@1$h6$c@3$2$0@4$9@2$3$6$5@1$4@2$b$7$5@2$3$eZ@1$4+p0@3$2$0@4$9@2$3$6$5@1$4@2$b$7$5@2$3$hbZ@1$4+q0@3$2$0@3$a$f+kgggggggggg0+ogggggggggg0@1$8$0").
Definition RES : ltac2:(zQ "20!is6!kk0>2st$1$0") := ltac2:(zQ "a0!it2!hgd!it8!ite!iu6!iuf!kk0!ll2!llc!lm6\2st$6@6$2$7$9@1$1$4@1$8^1$5@1$0$3").
Definition REG_res : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "b0!q1!kg3!m2!kg9!va!hpd!hgd!hq3!jh8!kt4!ht5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$7$5@2$a$9$5@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8Z+p0@1$6@2$1@2$1$2$0$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CATCH_PC : Z := 0x47550.
Definition FREE_PC : Z := 0xdfac4.
Definition AFTER_FREE_PC : Z := 0x97d48.
Definition AFTER_CATCH_PC : Z := 0x47540.
Definition C_SCR : Z := 4096.
Definition CT_regs : ltac2:(zQ "20!m2!q5>2a0$0@1$1$0") := ltac2:(zQ "50!o1!m2!hq3!htc!ii9\2a0$1@5$4@1$0Nh3$2@1$3N0^1@1$0N8").
Definition ct_geom : ltac2:(zQ "20!q5!qb@1$0$1") := ltac2:(zQ "d0!qb!va!v4!hg8!hua!hq3!hq8!hp5!ln2!hgd!hv3!lg8!kj9@3$1$0@3$4$5+kgggggggggg0+ogggggggggg0@3$1$0@2$a$5+h0@3$1$0@3$4$6+kgggggggggg0+vvvvvvvvvvvvvvm0@3$1$0@3$4$b+kgggggggggg0+ogggggggggg0@3$1$0@4$7@2$3$5@1$c$8@1$2$8@2$3$6Z@1$2+q0@3$1$0@4$7@2$3@1$2Z+hgtht0@1$2+ii0@2$3$6Z@1$2+q0@1$9$0").
Definition cth_geom : ltac2:(zQ "30!hhc!q5!qb>2hi$0@1$1$2") := ltac2:(zQ "f0!v4!hg8!qb!jh8!va!hp5!hhc!hua!ln2!hgd!hv3!hq3!hq8!kj9!ht5\2hi$6@3$4$2M6\2hi$6$2^1@3$7$3+hjhgg0+ogggggggggg0@3$7$3+1@2$e+hggg0+p0@3$4$2@2$a$3+h0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hggg0@1$0+ukgg0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+vrpu0@1$0+hkm8@3$4$2@4$5@2$1$b@1$d$8@1$0$8@2$1$3Z@1$0+p0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1$cZ@1$0+q0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hgtht0@1$0+ii0@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hguri0@1$0+8@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hiusj8@1$0+8@3$4$2@4$5@2$1$3Z@1$0+p0@2$1@1$0Z+hiuup0@1$0+8@1$9$2").
(* [comment removed for export] *)
Definition F5a : ltac2:(zQ "30!hhc!is6!ho2>2ps$2>2hi$0$1") := ltac2:(zQ "hf0!qb!hp0!hgd!ln2!it2!hhc!va!kl0!hnc!hg8!it8!ite!iu6!iuf!ii3!ijd!hi2!ksb!ik7!v4!hq3!jh8!lnb!lo7!lp2!lpd!im7!ip4!ho2!ipf!kj9\2ps$hc\2hi$5@6$a$h6@1$h7@2$e$h5+m0@1$2$c@3$1$0@3$6$0@2$8@2$9$h4@1$he$3@1$h3$3@1$2$0@3$1$0@1$h1$7@3$1$0@1$ha+1@3$1$0$hd@3$1$0@1$hb^2@3$1$0$h0@3$1$0$f@3$1$0$h2@3$1$0$h8@1$h9^1$d@1$4$b").
Definition FR_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "70!jh8!o1!ii3!v4!hq3!lq9!ii9@5$6@1$3$5@2$2$4-i0$0$0@1$1N8").
Definition FR_T : ltac2:(zQ "30!q5!qb!ho2>1p$2@1$0$1") := ltac2:(zQ "h40!qb!hp0!va!hg8!hq3!hg0!v4!ln2!htc!hgd!hnc!ijd!hi2!ik7!lp2!im7!ip4!ho2!ipf!kj9\1p$h1@3$1$0@3$2$0@3$5@2$3$4-8N8@1$6+knll8@3$2$0@3$5@2$3$4-h0N8@1$8N0@3$2$0@3$5@2$3$4-h8N8@1$8N1@3$2$0@2$a@2$3$4@1$h3$7@1$6$7@1$9$0@3$1$0@1$fZ@3$1$0$h2@3$1$0@1$h0^1@3$1$0$c@3$1$0$b@3$1$0$d$e").
Definition REG_ct : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "b0!q1!kg3!m2!kg9!va!v4!ln2!hgd!hq3!jh8!kj9@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8@1$a$6$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$9Z+p0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgtht0+ii0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hguri0+7@1$7@2$1@2$1$2$0$0").
(* [comment removed for export] *)
Definition F5b : ltac2:(zQ "20!is6!ho2>1p$1$0") := ltac2:(zQ "e0!o1!it2!hgd!it8!ite!iu6!iuf!ii3!hq3!jh8!lq9!lra!ii9!ho2\1p$d@6$3$a@5$c@1$0Nh3@2$7$8-i0$9@1$0Ni5@1$0N8@1$2$5@1$b^1$6@1$1$4").
Definition DONE_regs : ltac2:(zQ "20!q5!m2@1$0$1") := ltac2:(zQ "40!o1!hq3!htc!ii9@5$3@1$0Nh3$1@1$2N0@1$0Ni5@1$0N8").   (* [comment removed for export] *)
Definition DONE_T : ltac2:(zQ "30!q5!qb!ho2>1p$2@1$0$1") := ltac2:(zQ "a0!hp0!qb!ijd!hi2!ik7!lp2!im7!ip4!ho2!ipf\1p$8@3$0$1@1$6Z@3$0$1$9@3$0$1@1$7^1@3$0$1$3@3$0$1$2@3$0$1$4$5").
Definition REG_done : ltac2:(zQ "20!q5!jv9@1$0$1") := ltac2:(zQ "a0!q1!kg3!m2!kg9!va!v4!ln2!hgd!hq3!kj9@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0$8@1$9$6$6@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hgtht0+ii0@3$4@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$5Z+hguri0+7@1$7@2$1@2$1$2$0$0").
(* [comment removed for export] *)
Definition F5p : ltac2:(zQ "10!is6$0") := ltac2:(zQ "i30!qb!hp0!h8!hgd!m2!v4!va!kg3!ln2!ls2!it2!kg9!kl0!lsd!mh7!hnc!hg8!it8!ite!iu6!iuf!ijd!hi2!ksb!ik7!hq3!lnb!lo7!mi1!lp2!im7!ip4!ipf!hse!kj9@6$h1$ha@1$hb@1$5@2$i1$9+m0@1$3$h3@3$1$0@3$6$0@2$f@2$h0$h9@1$i2$8@1$5$8@1$3$0@3$1$0@4$d$0$0@1$e@3$6@2$7$2$4@4$b$2$4N2@1$5$9@1$3@2$7$2$4@1$h7$c@3$1$0@1$he+1@3$1$0$i0@3$1$0@1$hf$hc@3$1$0$h6@3$1$0$h5@3$1$0$h8$hd$h4@1$a$h2").
End CUT2.
(* [comment removed for export] *)
