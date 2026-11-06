(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W8 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0 ASlot_M1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W10."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "1Some"; "1cons"; "1list"; "1nil"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "4epi_frame"; "5ag_frame"; "6asegs"; "7grp_hdr_cov"]; ["7unk_agree"; "8C8"; "8CB"; "8cell"; "8cells_bytes"; "9wa"; ":rw_cells"; ";RKGroup"; ";Unknown"; ";aptr"; ";cell_read"; ";cellval"; ";get_shadow"; ";ghdr"; ";mstate"; ";r_base"]; [";r_kind"; ";r_len"; ";region"; ";rkind"; ";round_up_pg"; ";s_groups"; ";s_regions"; ";s_shadow"; ";shadow"; "<add"; "<le"; "<lt"; "<mul"; "0b"; "0h"; "0j"]; ["0m"; "0mE"; "0o"; "0off"; "0r"; "0rav"; "0rid"; "0s0v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0sc"; "0st"; "0stE"; "=is_Some"]; ["=lookup"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "?N_countable"; "?Z_countable"; "?prod_countable"; "@prod_eq_dec"; "Agmap"; "Agmap_lookup"; "Beq_dec"; "Ceq_dec"; "0tp"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition epi_frame (jj : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 jj; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
Lemma ag_frame_epi : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M2 "QK'R2yR0%211'5y8%511%311p051';'3%115&F&>r:r9&=r8r7r6r5r4r3r2r1%9887654321%>4=<;1r;&<&D(2'C(A&R1&Q<+2%22E1%42Q31%611(BuQ8%221H(4%11<%>3=31%?3>71%A11%C71MLKJIH%Q44Q3EQ21p0G1pS<Q?1pS@Q@1pSBQA1pSDQB1pSFQC1pSHQD1pS0Q=1pSJQ@1p2QA1pS2QC1").
Proof. intros m A sc j s4v s3v s2v s1v s0v rav.
intros FR. unfold ag_frame in FR. unfold epi_frame.
pose proof (rw_cells_merge asegs m A [] [C8 (Z_to_bv 64 (sc * 2)); CB 40 j] [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] FR) as X.
cbn [app cells_size csize Nat.add] in X. exact X.
Qed.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Lemma errno_lit2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M2 ";'7';&Q9&R3yR0vR<%3221-U4%6221+SY[L%:3921").
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma unk_agree_keep : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M2 "T2'N'R2yR0%211'5y8%511%311pTL51'7'R8':&R:&R4'Q8%544321&Q7r2%211vQM%411%<3631'Q2'Q3&Q0r1%211(G%C3521%I17&R0%E4DCB9&R9%14FED;r3&Q6r6%211%86K@7541(1%12BG%Q03<31r4%81H%>6Q1F=;21%62G;%Q53A21p061p0D1pS:K1pS>Q71&I&8&QO'M&R7';&R;%34Q?Q>21&R6&R5%26QBQAQ@541%QD4;418%O4<529&Q5r5%211%Q56@=54Q:1%?2>1%51QB%Q86C@87Q=1%B2A1%D241pRLF1%QB1Q0%R23QD1Q@'6&Q:z%221Q5&Q;&Q4&Q1%11B%311%52Q;1%:271'K&J&Lr7%22R81%421K(H%11QD%RF3831&9&?r8%23R@1QO%411r=&E&Q9&O%117%321@%511%711vQ@%113%S63S831p0<1p0B1p0L1p0Q81p0R61pRNQM1pS8QN1pS:S11pS>S=1&@vQB%23RG1QJp041p0QD1p0R<1p0S:1pS4SH1pSNT11").
Proof. intros stE mE.
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.
End LEVEL.
End CEIL_WRAP_1.
