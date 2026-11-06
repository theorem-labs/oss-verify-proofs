(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B F_malloc_bigw.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W15.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W15 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W15.CEIL_WRAP_1.SEQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "0RUNp"; "6wz"; "7mem"; "8evt"; "9mkR"; "9munch"; "9wmono"]; [":MS"; ";mem_inv"; "<account_bounce"; "<bounces"; "<c_seq"; "<ctx"; "<is_bouncing"; "<mstate"; "<step_seq"; "<unmap_seq"; "=rsegs"; ">rseqW"; "?RMLOCK"; "?rmrep"; "@seg_rom"; "Ab2z"]; ["Ale"; "Alt"; "0a0"; "0a1"; "0a2"; "0a3"; "0a3'"; "0a4"; "0a5"; "0a5'"; "0a6"; "0a6'"; "0a7"; "0a7'"; "0fc"; "0gp"]; ["0i"; "0m"; "0m'"; "0m0"; "0ms'"; "0ra"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s7"; "0s8"; "0s9"]; ["0sc"; "0sp"; "0st"; "BZ_to_bv"; "Bbv"; "0t0"; "0t0'"; "0t1"; "0t1'"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.
Section SE.
Local Abbreviation SEC_T_rbounce_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W15 "UM'R4yR0%211&8y5%2213yQ0%711'G&;&Mv9r2r1%43321'2&Q0z&D&Er3%211%411%7261&Q1+X0%2241%<241'5&Cr5%221B%@2?1%9228%C221pS271&Ir6%221I%G2F1%@22?%J221pS2>1&A&J%221?&<'7'4'1y8%QC11%311p0QC1'3r7&@&=rQ=rQ<rQ;rQ:rQ7&R3vR0%22R01rQ6rQ5rQ4rQ3r4rQ1&:r>%QG11%QI11%411rMrLrKrJ&L%C2RA1rIrHrGrFrErDrCrBrA%Q3OQ2Q1Q0OQGQNNKJIHGFER8@R@?>=<:987654321r@+cdS8%Q02RN1r?(0%11S0&N%11QH%Q=798653RH1%Q@3QGQ?1&O&F%12Q9Q0%311%Q<2S:1%QF3S:Q61&>&Kr=%3321S3&?%13R63S5%R82R7S6&B%12QEQ<%S<3S;1S9%S8241%S9261%S:291%S;2>1%S<2E1qS6R71%R=2R81qRLSL1%R?2SM1qRDSN1%RA2SO1qR>T01%RC2T11qTBT21%RE2T31qT>T41%RG2T51qS:RI1rQ2rQ0rOrNr<r;r:%RGOR>R=R<R;7R96R?54R3R2R1R0QMQLQKQJQIQHQGQNQFQEQCQ@R7Q1321r9+cc]D%RD2TB1r8%RM75421QCS@QA%S83S:>1p0S:1p0S>1p0SF1p0SO1p0T=1pS4TC1pT6TE1pRNTG1p>TJ1pTLTN1pTJTO1pTHU01pTFU11pSBU21pS@U31pT0U41pSNU51pSLU61pSJU71pSHU81pSFU91pSDU:1pRJU;1pRFU<1pRBU=1pR@U>1pR<U?1pR:U@1pR8UA1pR6UB1pS>UC1pTDUD1pT@UE1pT<UF1pTNUG1pS0UH1pT4UI1pS<UJ1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 7%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 9%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 10%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 11%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 15%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 16%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 17%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 18%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 19%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 20%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 21%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 22%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 23%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 24%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 25%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 26%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 27%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 28%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 29%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 30%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 31%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rbounce_walk) 32%nat 0%nat).
Lemma rbounce_walk : ltac:(sec_stmt2 constr:(SEC_T_rbounce_walk) 33%nat 0%nat).
Proof.
intros MR SEQ BR USR MI.
pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold rseqW in MU.
unfold RCTX, RMLOCK in *.
assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
rmrep stX mX -> stX = account_bounce sc st -> mem_inv rsegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
munch [(954560 + 848, 954560 + 913)]%Z m mX -> wmono rsegs m mX ->
evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 954552) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d068) fc None m' (seg_rom rsegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch [(954560 + 848, 954560 + 913)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 954552) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d064) fc None mX (seg_rom rsegs))).
{ intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
pose proof (rmrep_seq_read stX mX (wa (954560 + 912)) MRX eq_refl) as RDS.
replace (wa (954560 + 912)) with (Z_to_bv 64 (954552 + 920)) in RDS by (unfold wa; f_equal; lia).
assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
{ rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite SQX in RDS.
step. rewrite ?zxb_b8 by lia. clear RDS.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
step. rewrite ?(unsigned_lit sc) by lia. step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
assert (HO : sc_in_seq_range sc = false).
{ unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
- replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
step. step.
eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
- unfold account_bounce. rewrite HO. reflexivity.
- unfold is_bouncing. rewrite HO. reflexivity. }
rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
destruct (Z.lt_ge_cases sc 7) as [L7|G7].
{ exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
rewrite Z.mod_small in K by lia.
assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
step. rewrite ?(unsigned_lit (sc + -7)) by lia.
pose proof (rmrep_bounces_read st m (sc - 7) (wa (954560 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
replace (wa (954560 + 880 + (sc - 7))) with (Z_to_bv 64 (954552 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
step. rewrite ?zxb_b8 by lia. clear RDB.
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_read rsegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (954552 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
step. rewrite ?zxb_b8 by lia. clear RDU.
step. step.
set (nos := 100 <=? bounces st (sc - 7)).
assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
{ rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
change (bv_wrap 64 100) with 100.
destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
rewrite A3. clear A3.
assert (AB : account_bounce sc st =
(if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
else st)) by (unfold account_bounce; rewrite IN; reflexivity).
step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
{ eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
pose proof (rmrep_seq_read st m (wa (954560 + 912)) MR eq_refl) as RDS.
replace (wa (954560 + 912)) with (Z_to_bv 64 (954552 + 920)) in RDS by (unfold wa; f_equal; lia).
step. rewrite ?zxb_b8 by lia. clear RDS.
step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
{
apply Z.ltb_lt in K2.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite Bool.andb_false_r. exact MR. }
apply Z.ltb_ge in K2.
assert (AB2 : account_bounce sc st =
(if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
{ rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
clear AB K1 K2.
pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
pose proof (u8arr_store_ok rsegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (954552 + (sc + -7) + 888)) BA
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
-
step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (954560 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. step. st1. rewrite (le1_lit 150) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (954560 + 880 + (sc - 7)) [b8 150] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End SE.
Lemma rseq_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W15 "U2'R4yR0%211&8y5%2213yQ0%711'G&;&Mv9r3r1%43321'2&Q0z&D&Er4%211%411%7261&Q1+X0%2241%<241&A&J%221B&>&Kr5%3321>&?r6%23814&<'7'4'1y8%Q;11%311p0Q;1'3&@&=rQ9rQ8rQ7rQ6rQ5rQ4rQ3&R3vR0%22QI1rQ2rQ1rQ0rOrNrM+O%:2R11r2rKrJrIrHrG&L%B2R91rFrErDrCrBrAr@r?r>%Q4OQ3Q2Q1Q0ONMJIHGFEDBA@?>=<:987654321r=+cdTD%O2RF1r<(0%11RH&N%11QO%Q>798653R@1%Q@3QGRB1r:%R13R01RC%QN3R42RD%R62R5RE&Hr;%211%RL3RK1RI%RH251%RI271%RJ291%RK2<1qS6QN1%R42QO1qRHS;1%R62S<1qS:R81rL&:r8%S011%S211%411%R6OR2R1R0QOQKQJQIQLQHQGQF6QBQAQ@1Q?Q>Q;Q:Q9Q<Q8Q7Q6Q5Q4Q3Q1NB+cdS8%R02SG1r9%R;74K21Q0RFN%RE3RN<1p0RG1p0RK1p0S01p0S41p0SB1pS4SH1pS8SI1pT6SK1pRNSM1p>T01pTLT41pTJT51pTHT61pTFT71pSBT81pS@T91pT0T:1pSNT;1pSLT<1pSJT=1pSHT>1pSFT?1pSDT@1pRJTA1pRBTB1pR@TC1pR<TD1pR:TE1pR8TF1pR6TG1pS>TH1pTDTI1pT@TJ1pT<TK1pTNTL1pS0TM1pT4TN1pS<TO1").
Proof.
intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
set (q := c_seq (ctx st)) in *.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
replace (954560 + 912) with 955472 in C6 by reflexivity. replace (954560 + 848) with 955408 in US by reflexivity.
assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv rsegs mj ->
munch [(954560 + 848, 954560 + 913)]%Z m0 mj -> wmono rsegs m0 mj ->
evt rsegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 954552) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d094) fc None m' (seg_rom rsegs)
/\ munch [(954560 + 848, 954560 + 913)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 954552) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9d08c) fc None mj (seg_rom rsegs))).
{ intros mj stj ns NS MRj CTj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (954560 + 912) with 955472 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (954552 + 920)) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
step. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (954560 + 912) [b8 ns] MUj WMj SOK.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned q) by lia.
eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
pose proof (munch_refl [(954560 + 848, 954560 + 880)]%Z m) as MUz. pose proof (wmono_refl rsegs m) as WMz.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UZ : u8arr rsegs mX 955408 (zeros 32));
[ apply (u8arr_of_rw_cells rsegs mX 955408 32);
lazymatch goal with H : rw_cells rsegs mX 955408 _ |- _ =>
apply (rw_cells_congr rsegs mX 955408 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRz : rmrep stz mX);
[ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
| clear MUc WMc ] end.
step. step.
lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono rsegs m0 ?mX, MIc : mem_inv rsegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
Lemma rmm_seq_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W15 "UM'R4yR0%211&8y5%2213yQ0%711'G&;&Mv9r2r1%43321'2&Q0z&D&Er3%211%411%7261&Q1+X0%2241%<241'5&Cr5%221B%@2?1%9228%C221pS271&Ir6%221I%G2F1%@22?%J221pS2>1&A&J%221?&<'7'4'1y8%QC11%311p0QC1'3r7&@&=rQ=rQ<rQ;rQ:rQ7&R3vR0%22R01rQ6rQ5rQ4rQ3r4rQ1+O%:2R81rMrLrKrJ&L%@2R>1rIrHrGrFrErDrCrBrA%Q0OONMLQDQKKHGFEDCB@R5R=?>=<:987654321r@+cdTD%M2RK1r?(0%11RM&N%11QE%Q:798653RE1%Q=3QDQ<1&O&Fr>%22Q71%411%Q:2S81%QD3S8Q41&>&Kr=%3321S1&?%13R43S3%R62R5S4&H&B%12QD>%311%S<3S;1S9%S8261%S9281%S:2;1%S;2@1%S<2H1qS6R71%R=2R81qRLSL1%R?2SM1qRHSN1%RA2SO1qR>T01%RC2T11qTBT21%RE2T31qT>T41%RG2T51qS:RI1rQ2rQ0rOrNr<r;r:%RGOR>R=R<R;7R96R?54R6R5R4R3R0QOQNQMQLQKQJR1QIQHQFQCQ:Q3321r9+cc]D%RD2TB1r8%RM75421QFS@QD%S83S:>1p0S:1p0S>1p0SF1p0SO1p0T=1pS4TC1pT6TE1pRNTG1p>TJ1pTLTN1pTJTO1pTHU01pTFU11pSBU21pS@U31pT0U41pSNU51pSLU61pSJU71pSHU81pSFU91pSDU:1pRJU;1pRFU<1pRBU=1pR@U>1pR<U?1pR:U@1pR8UA1pR6UB1pS>UC1pTDUD1pT@UE1pT<UF1pTNUG1pS0UH1pT4UI1pS<UJ1").
Proof.
intros until m. intros MR SEQ BR USR MI.
eapply evt_cut; [eapply rbounce_walk; eassumption|].
cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
{ unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite <- SEQ'.
eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
do 6 eexists. split; [reflexivity|]. subst a3'.
repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.
End CEIL_WRAP_1.
