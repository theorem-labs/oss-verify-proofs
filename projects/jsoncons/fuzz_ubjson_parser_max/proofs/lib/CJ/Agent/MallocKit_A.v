(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0C"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "4write_to_mem"; "5asegs"; "6b8"]; ["6ticks_ok"; "6wz"; "7mem"; "7pres_except"; "8ivl"; "8munch"; "8outside"; "8wmono"; "9le4"; "9wa"; ":aptr"; ":conc"; ":enframe_at"; ":get_shadow"; ":ghdr"; ":havoc"]; [":lowbit"; ":mctx"; ":meta"; ":mstate"; ":region"; ":s_groups"; ":s_regions"; ":set_size"; ":set_tick"; ":shadow"; ":upd_ctx"; ":upd_meta"; ":wr16"; ":wr32"; ":wr8"; ";add"]; [";div"; ";le"; ";lt"; ";modulo"; ";of_nat"; ";pow"; "0W"; "0a"; "0b"; "0bs"; "0e"; "0f"; "0g"; "0k"; "0m"; "0m'"]; ["0m0"; "0n"; "0off"; "0p"; "0q"; "0rid"; "0st"; "<bv"; "<bv_unsigned"; "=N_countable"; "=Z_countable"; "=prod_countable"; ">prod_eq_dec"; "?gmap"; "@eq_dec"; "Aeq_dec"]; ["0t"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ticks_ok_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "@'Q3&J'Q2p011&@r3%211&Q;r2r4%33521%711p061pSH:1pSJ=1pT>?1").
Proof. intros st g f. intros T; exact T. Qed.
Lemma ticks_ok_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "='Q3'Q1p011&@r2%211&Q:r3%2241%611p051pSH91pT><1").
Proof. intros st f. intros T; exact T. Qed.
Lemma ticks_ok_wr16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "?'Q3&J'<&@r3%211&Q<r2r4%33521%711p061pU4:1pT8<1pT>>1").
Proof. intros st p v. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
Lemma ticks_ok_wr32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "?'Q3&J'<&@r3%211&Q=r2r4%33521%711p061pU4:1pT8<1pT>>1").
Proof. intros st p v. intros T. unfold wr32. repeat apply ticks_ok_wr8. exact T. Qed.
Lemma ticks_ok_set_size : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "D&J'<'Q3&@r1%211&Q7r6r5r4r3r2%6554321%:11p091pT>=1pSB?1pT4@1pSFB1pT8C1").
Proof. intros p e n b st.
intros T. unfold set_size.
destruct (5 <=? _); destruct (negb _); repeat first [apply ticks_ok_wr8 | apply ticks_ok_wr32]; exact T.
Qed.
Lemma get_shadow_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "@'Q3';'8'Q9&M&Q8r2r3%3221r1%6221%7242%:3921pT<<1pU2=1pT>?1").
Proof. intros st t rid. reflexivity. Qed.
Lemma get_shadow_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "E'Q3&J'Q2p011';'8'Q9&M&Q;r3r2r4%43321r1%7221%8242%;3:21pT<=1pSH?1pSJB1pT>D1").
Proof. intros st g f rid. reflexivity. Qed.
Lemma s_regions_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "F'Q3&J'<'8'R=';&R>&R9'Q4%544321&Q6&Q>r2r1r3%43321%611%713%?3921pU4A1pT8C1pT>E1").
Proof. intros st p v. reflexivity. Qed.
Lemma s_groups_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "L'Q3&J'<'8'R=&R<';&R>&R?%443271&R;&R9&R:%36762;51'N%;4>621&Q5&Q>r2r1r3%43321%611%713%E3921pU4G1pT8I1pT>K1").
Proof. intros st p v. reflexivity. Qed.
Lemma conc_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "B'Q3&J'<'8&K&Q>r3r2r4%43321r1%7221%8242%:3;21pT:=1pU4=1pT8?1pT>A1").
Proof. intros st p v q. reflexivity. Qed.
Lemma conc_wr16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "B'Q3&J'<'8&K&Q<r3r2r4%43321r1%7221%8242%:3;21pT:=1pU4=1pT8?1pT>A1").
Proof. intros st p v q. reflexivity. Qed.
Lemma conc_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "A'Q3';&J'8'<&K&Q8r2r3%3221r1%6221%7242%:3921pT:<1pU2>1pT>@1").
Proof. intros st t q. reflexivity. Qed.
Lemma conc_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "D'Q3&J'Q2p011'8'<&K&Q;r3r2r4%43321r1%7221%8242%;3:21pT:?1pSH>1pSJA1pT>C1").
Proof. intros st g f q. reflexivity. Qed.
Lemma conc_havoc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "B'Q3&J'<'8&K&Or3r2r4%43321r1%7221%8242%:3;21pT:=1pT4=1pT8?1pT>A1").
Proof. intros st p n q. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma conc_set_size : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "F&J'<'Q3'8&K&Q7r6r5r4r3r2%6554321r1%9221%:242%<3>21pT:@1pT>?1pSBA1pT4B1pSFD1pT8E1").
Proof. intros p e n b st q. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma conc_enframe_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "H'Q3&J'<'8&K&2&Lr6r5r4r3r2%6554321%83=<1r1%;221%<292%>3?21pT:A1pT6A1pT4B1pSLC1pSJE1pT>G1").
Proof. intros st g k n off q. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.
Lemma le4_bytes : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "QB'<'7&QAzr1%3221&QB&QE+2+Q0%3221%5271%;271'8'4'R7y8%211%411&H&Ar2%211%411(1&?&QC+X0%2271%411&Q@%12:4%6215%811+RPP0%52>1%:219%<11+`PPP0%92B1%?11(5%11I%C3J31%D3K71%E3L<1%F3MA1%Q23MH1p0Q41pU4QA1").
Proof.
intros v Hv. unfold le4, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
assert (E : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256)).
{ intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
rewrite (E v) at 1. rewrite (E (v / 256)) at 1. rewrite (E (v / 65536)) at 1. reflexivity.
Qed.
Lemma lowbit_facts : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "L'<'7&QBzr1%3221&QE+2+Q0%3221%8261%:261'9&QA%12;:%=2;7%?221'8&Q0r3%211%?2>A%53F21%F271qSLH1%=2I1p0?1pU4K1").
Proof.
intros v Hv. destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
split; [|unfold lowbit; exact E]. split; [exact Hk|].
destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma pres_write : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "QL'<!p021&B'4'R7y8%211%411&Cr5r4r3%43321&QAz%2214&Q?&QD&3%12=8%311%52;1&QE+2+R0%3221%=251'7r6r1%A221&QB%>2JG%@11%B261%4261%9261r:r2%211p041pU6Q:1r9r8&=r7&I%11C%4331Q7%Q93761p091p0I1p0Q51p0Q91pSDQ?1pS@QH1pSNQF1pT2QG1p2QI1").
Proof.
intros C m0 m a bs HP Ha Hl HC x Hx HCx.
destruct (HP x Hx HCx) as [E W].
assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
{ rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply HCx, HC. lia. }
split.
- rewrite NE. exact E.
- intros Hw. apply wview_write_mono. apply W, Hw.
Qed.
Lemma pres_except_munch_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "QM'<!p021&B'R7yR0%211'6y8%511%311p051'4&D%211&Cr5r4r3%43321&Er2%23154&G&>%23198'7&QAzr1%3221&QB&QE+2+R0%3221%5271%;271&:r:%11C%311&Fr7%221Jp041p091pU6Q?1r9r8r6%Q43321p051p0L1p0Q01p0Q41pS>Q:1pT0Q>1pSNQG1pT2QH1p2QJ1").
Proof.
intros C m0 m m' W HP MU WM HW. eapply pres_except_trans; [exact HP|]. eapply pres_except_of_munch; eauto.
Qed.
Lemma b8_of_byte : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A ";'R7y8%211'8&?&R8r1%2261%411%63713pU681").
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma byte_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A "?'R7y8%211'7&QAz&R8r1%2271%5241&QB+X0%2241%:241pU6<1").
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
End CEIL_WRAP_1.
