(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_bigw.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMalloc_fp RF_enframe RMallocKit_A2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_malloc_bigw () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_bigw."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_malloc_bigw.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "0F"; "0G"]; ["4machine_state"; "5bvmap"; "0RUNp"; "6big_meta"; "6big_st"; "7sxv"; "8b8"; "8meta_word"; "8ticks_ok"; "8wz"; "8zeros"; "9mem"; ":C4"; ":C8"; ":cell"; ";evt"]; ["<mkR"; "<munch"; "<stk"; "<wmono"; "=MS"; "=ret_pc"; ">bytes_at"; ">le4"; ">mem_inv"; "?alloc_ceiling"; "@rw_cells"; "Arsegs"; "Brseq_post"; "CRCTX"; "CRMLOCK"; "Crmrep"]; ["Crmunmap_entry"; "Dc_seq"; "Dctx"; "Dmstate"; "Dstep_seq"; "Du32"; "Eseg_rom"; "Fadd"; "Fland"; "Fle"; "Flor"; "Flt"; "Fof_nat"; "Fpow"; "Fsub"; "0a0"]; ["0a0'"; "0a1"; "0a1'"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0c"; "0c0"; "0fc"; "0g"; "0gp"; "0gw"; "0k"]; ["0lo"; "0m"; "0m'"; "0ms'"; "0n"; "0ndw"; "0nw"; "0o"; "0ra'"; "0rav"; "0rid"; "0s0v"; "0s10"; "0s11"; "0s1v"; "0s1w"]; ["0s2"; "0s2v"; "0s3"; "0s3v"; "0s4"; "0s4v"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "GZ_to_bv"; "Gbv"; "Gbv_swrap"]; ["Gbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x"; "0xw"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rzeros_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "QH'S>yR0%211'5y8%511%311p051'='3&QIzr2%3221&QGr3&QL%115%4231&QM+2+R0%3221%=251'8r1%@2?1&QKr4%=11%3251%7251&Q6&Q;r7r6%F21H(1&F%11L(4%11Q4%53Q531%;4:971p0=1pU@Q51r5&J%11D%A4@>31p051p0L1p0Q71pU0Q<1pWDQ>1pU4Q@1").
Proof.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. exact HB.
Qed.
Section SE.
Local Abbreviation SEC_T_lor_land_2048_4064 := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "C'=&QIzr1%3221'9&QJ&QHr2+_ooooooooonP0%3221+So0%6221+_ooooooooolP0%7261%9214%;3@41p0=1pWDB1")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_lor_land_2048_4064) 0%nat 0%nat).
Lemma lor_land_2048_4064 : ltac:(sec_stmt2 constr:(SEC_T_lor_land_2048_4064) 1%nat 0%nat).
Proof using Type x.
intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
{ change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
rewrite T4064.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.
End SE.
#[using="Type"] Lemma rbig_word_eq : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "Q3'<'='8&QIzr1%3221&QK&QM+2+Q0%3221%5271%;271'9&QJ&QH&QGr2+So0%3221+QC%5221+_ooooooooonP0%8221%:216&G&Cr3%221;%411%A3N61p0C1pU:Q01pUFQ21").
Proof. intros rid n.
intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
replace (n + 4064 + 51) with (n + 4115) by lia.
assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
destruct (Z.lt_ge_cases i 12).
- rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma le4_sxv_succ : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "Q2'=&QIzr1%3221'9'2'S>y8%211%411&Q7&S=yR0&QG&S@&I&Er2%211%411%6281+1%9221%<2;1%>11&QE%=295%211%=11%C11%J3E61p0L1pTDQ11").
Proof. intros c.
intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma le4_swrap_succ : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "Q8'='8&QIzr1%3221&QK&QM+2+Q0%3221%5271%;271'9'2'S>y8%211%411&Q7&S=yR0&QG&S?yQ0r2%3221+1%6221%9281%;11&I&QE%;286%211%411%A11%H3C71p0J1pTFQ71").
Proof. intros c0.
intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rbig_fail1_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "U6'S>yR0%211&Ay5%2213yQ0%711&K'=&Q:&Q;r2&QG&S@rQ6%22?1-Q@%5221(1'N(Mr5%211r6%411r7%611r8%811r9%:11r:%<11(4%11?%A3@31%B3A61%C3B91%D3C<1%E3D?1%F3EB1%Q04ONH1&Q2r3rQ7%Q02Q=1%Q221N%54Q54Q41&QI&QNrQ8%Q62QC1+Q@%4221%62;1rQ9%Q;2QH1%9251&O'@'8'9r1&Q4&Q0r?rQ;rQ:r>r=&Iz%211rQ5rQ4rQ3rQ2rQ1rQ0rOr<r;rLrKrJrIrHrGrFrErDrCrB%MOLKJQ6Q;QAR?IHEDCBA@?>=<QN;:987654321&Q5%11N(0%11S0&QF%11RI%Q577R75R93R;1%Q83Q:Q71%RI2S6Q4%QM4RMR>R@1%Q<231qU8Q>1r@&S=%RO2S<Q9%S121RM%32S>1&Q>%52S@1-1%72SB1rNrMrA%QFO<8QOR4R:S8Q=QE64Q<Q;Q:Q9Q8Q7342Q4Q3Q2Q1Q0ONMLKJ1+c]mL%=2SH1%QJ73RN1S0HS2F%R03S@A1p0R21p0R61p0R>1p0RE1pU2SG1pU4SI1pTHSK1pNSN1pV<T21pV8T31pV4T41pUNT51pUHT61pUDT71pU>T81pUBT91pW@T:1pW>T;1pW<T<1pW:T=1pULT>1pUJT?1pVFT@1pVDTA1pVBTB1pV@TC1pV>TD1pV:TE1pV6TF1pTBTG1pT@TH1pT>TI1pT<TJ1pT:TK1pT8TL1pT4TM1pW8TN1pW6TO1pW4U01pWBU11pTLU21pVHU31").
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.
#[using="Type"] Lemma rbig_fail2b_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "U8'S>yR0%211&Ay5%2213yQ0%711&K'=&Q:&Q;r2&QG&S@rQ9%22?1-Q@%5221(1'N(Mr5%211r6%411r7%611r8%811r9%:11r:%<11(4%11?%A3@31%B3A61%C3B91%D3C<1%E3D?1%F3EB1%Q04ONH1&Q2r3rQ:%Q02Q=1%Q221N%54Q54Q41&QI&QNrQ;%Q62QC1+Q@%4221%62;1rQ<%Q;2QH1%9251&O'@'8'9r1&Q4&Q0r?rQ>rQ=r>r=&Iz%211rQ7rQ6rQ5rQ4rQ3rQ2rQ1r<r;rMrLrKrJrIrHrGrFrErDrC%MOLKJQ6Q;QAR?IHEDCBA@?>=<QN;:987654321&Q5%11N(0%11S0&QF%11RI%Q577R75R93R;1%Q83Q:Q71%RI2S6Q4%QM4RMR>R@1%Q<231qU8Q>1rA&S=%RO2S<Q9%S121RM%32S>1rQ8r@rQ0rOrNrB%QEO;7QNR3R9S765QDQ<Q;Q:Q9Q8Q7Q6432Q3Q2Q1Q0ONMLKJI1+c^\8%<2SG1%QI73RM1ROGS1E%QO3S?@1p0R11p0R51p0R=1p0RD1pU2SF1pU4SH1pTHSJ1pNSM1pV<T11pV8T21pV4T31pUNT41pUHT51pUDT61pV0T71pU>T81pUBT91pW@T:1pW>T;1pW<T<1pW:T=1pULT>1pUJT?1pVFT@1pVDTA1pVBTB1pV@TC1pV>TD1pV:TE1pV6TF1pV2TG1pTBTH1pT@TI1pT>TJ1pT<TK1pT:TL1pT8TM1pT4TN1pT0TO1pW8U01pW6U11pW4U21pWBU31pTLU41pVHU51").
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.
#[using="Type"] Lemma rbig_fail2a_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "SK'S>yR0%211&Ay5%2213yQ0%711&K&Q:&Q;r1&Q>(1'N(L&Iz%211%411(4%117%93831%>4=<;1&O'@'9&Q4&Q0&S=+c^\8%22N1&QG&S@rQ2%22Q21-Q@%5221%92Q51rQ1rQ0rOrNrMr8%@2Q<Q1r7r6rKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:%Q6OQ3LKJIHGFEDCBA@?>=<CD;:987654321r5&Q@%Q82R41r4(0%11R6r3&QF%11R1%QA7:976431%QC3QDR21qU8QE1%Q>2R>Q8%Q@21Q<%QD2R@1rLr9%QHOQ83Q<Q;Q:Q92Q6Q7R2Q4Q3Q2Q1Q0ONMAQ5LKJIHGFEDC1+c^U@%QI2RE1r2%QM74B2?@1=%R13R?;1p0R31pU4RC1pTHRE1pNRH1pU<RL1pWFRM1pU>RN1pUBRO1pW@S01pW>S11pW<S21pW:S31pULS41pUJS51pVFS61pVDS71pVBS81pV@S91pV>S:1pV2S;1pTBS<1pT@S=1pT>S>1pT<S?1pT:S@1pT8SA1pT4SB1pW8SC1pW6SD1pW4SE1pWBSF1pTLSG1pVHSH1").
Proof.
intros until m. intros LK. unfold RMLOCK in *.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step.
eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x9b97c)) with (Z_to_bv 64 0x9b97c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.
Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists (a0 a1 : word) m',
ms' = MS (mkR (Z_to_bv 64 0x9b8b0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep st' m'.
Section SE.
Local Abbreviation SEC_T_rbig_seq_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "V4'S>yR0%211&Ay5%2213yQ0%711&K'='QC&Q?vBr1r4%43321'8&QIz&QA&QBr2%211%411%7261&QK+X0%2241%<241&;'9&S@r?%22Q01&QN&QM+2+R0%3221+1%6221%;3Q081%=11&Q:&Q;r7&QGrQ;%A2Q?1-Q@%4221(1'N(Mr:%211r;%411r<%611r=%811r>%:11%;1Q0(4%11>%@3?31%A3@51%B3A81%C3B;1%D3C>1%E3DA1%N4MLG1&Q2r8rQ<%Q>2R<1%Q021M%54Q34Q21rQ=%QB2R@1+Q@%QA221%R3291&Q9%11R:r9%R7221&Q8%12Q>Q2&O&Q<rQ@rQ?rQ>rQ2rQ1rQ0rOrNrMrLrQ9rQ8rQ7rQ6rQ5rQ4rKrJrIrHrFrErDrCrBrAr@&QD%11Q2%NQ5MLKJIHGFEDQ:Q>R;CBA@?>=<;:9876543RJQLQNR21R0R4&Q4&Q0rG&S=%S02SNQ2%RB21R?%32T01&Q>%52T21rQ:-1%82T51+D%RJ2RB1%;2T81rQ3%?O>:Q=Q<QKQORLJ8I7Q4Q3Q2Q1Q0O521Q;Q:Q9Q8Q7Q6Q5NMLK+c]mL%?2T<1(0%11T=&QF%11S5%G77RD5RF3RH1%QH3S7I1p0QJ1p0QM1p0R21p0R81p0R?1p0S?1p0SN1p0T<1pVJTB1pU:TD1pU2TE1pU4TG1pTHTI1pNTL1pV<U01pV8U11pV4U21pUNU31pUHU41pUDU51pWFU61pU>U71pUBU81pW@U91pW>U:1pW<U;1pW:U<1pULU=1pUJU>1pVFU?1pVDU@1pVBUA1pV@UB1pV>UC1pV:UD1pTBUE1pT@UF1pT>UG1pT<UH1pT:UI1pT8UJ1pT4UK1pW8UL1pW6UM1pW4UN1pWBUO1pTLV01pVHV11")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 5%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 6%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 7%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 8%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 9%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 10%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 11%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 12%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 13%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 14%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 15%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 16%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 17%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 18%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 19%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 20%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 21%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 22%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 23%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 24%nat 0%nat).
Variable ra' : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 25%nat 0%nat).
Variable nw : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 26%nat 0%nat).
Variable xw : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 27%nat 0%nat).
Variable rav : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 28%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 29%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 30%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 31%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 32%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 33%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 34%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 35%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 36%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 37%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 38%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rbig_seq_walk) 39%nat 0%nat).
Lemma rbig_seq_walk : ltac:(sec_stmt2 constr:(SEC_T_rbig_seq_walk) 40%nat 0%nat).
Proof using Type sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v F fc m lo n st.
intros MR SEQ XNE FR ST LO ILO MI.
pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
(pose_ceil; unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *). unfold ctx_tail_cells in C6.
replace (950384 + 912) with 951296 in C6 by reflexivity. replace (950384 + 848) with 951232 in US by reflexivity.
step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
step. rewrite ?zxb_b8 by lia. step.
assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs mj lo (bv_unsigned sp + -48) -> mem_inv rsegs mj ->
munch [(950384 + 848, 950384 + 880); (950384 + 912, 950384 + 913)]%Z m mj -> wmono rsegs m mj ->
evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 950376)
(Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b8a8) fc None mj (seg_rom rsegs))).
{ intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (950384 + 912) with 951296 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 951296) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
raw_store_finishR (950384 + 912) [b8 ns] FRj STj MUj WMj SOK.
step.
apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
assert (UZ : u8arr rsegs m1 951232 (zeros 32)).
{ apply (u8arr_of_rw_cells rsegs m1 951232 32). apply (rw_cells_congr rsegs m1 951232 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
clear USC.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with MUc : munch _ m m1, WMc : wmono rsegs m m1 |- _ =>
assert (MRz : rmrep stz m1);
[ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold RCTX; replace (950384 + 912) with 951296 by reflexivity;
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
step. step.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX, FRc : rw_cells rsegs ?mX (bv_unsigned sp + -48) _, STc : stk rsegs ?mX _ _, MIc : mem_inv rsegs ?mX |- _ =>
eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.
End SE.
Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.
Section SE.
Local Abbreviation SEC_T_rbig_succ_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_bigw "WG'S>yR0%211&Ay5%2213yQ0%711'9'=&S@r9%22;1v?%63521&Q:&Q;vRA&QGrQ4%:2C1-Q@%4221(1'N(Mr5%211r6%411r7%611r8%811%91Gr4%;11(4%11>%@3?31%A3@61%B3A81%C3B;1%D3C>1%E3DA1%N4MLG1&Q2vR@rQ5%Q72Q@1%Q021M%54Q3Q241&QI&QNrQ6%Q=2QF1+Q@%4221%62;1&Q8%12Q<Q;&O'@':'5y8%R211%311p0R21'8&Q4&Q0rC&S=rQ<%R12R:1%QJ21QG%42R<1rQ;rQ:rQ9rQ8rQ7vRD%;2RC1&Q>%=2RE1r3r2rQ3rQ2rQ1rQ0rB&Iz%211vSI%411rNrMrLrKrJrIrHrGrFrErD%Q7OQ6Q1Q0ONMLJHGFQNRKEDCBA><;:987654321r;+c^b8%Q82S@1r:(0%11SBr1&QF%11S7%QB7:976431%SA3QKRF1&Q1'7%12SCSC(6+Q8%S=2SB1%34SGSGSC1+8%S@2Q11%64SJSJQ21&Q=+<%SD221+@%SF241%<4T0T031%S51>%SD3?21%SE3@91%SF3A=1%D31SMI&Q3%13T0SOK%RF2T1L%S44T2MS3R6r=%SK11r>%SM11r?%SO11r@%T111rA%T311r<%T511%T83T71SI%T93T841%T:3T971%T;3T::1%T<3T;=1%T=3T<@1%TF4TEQ@RI1&Q?vB&DvS<vR<vRJ&QEvR9+1%TM221%411%95876RN1%<3;1QM&H%113%S@231%SA2A1%SB2Q51%SC2Q71%SD2Q91%SE2Q<1%SF2R21qU6SH1%SN2SI1qT6UL1%T02UM1qT2UN1%T22UO1qU8T41%UI2V2SB%UB21U?%SL2V41rO+D%UF2SE1%T02V81%T3OQC5SHTDTJUGSASFSDQES@S?S>4S7S6S5S41S8S3S2S1S0RORNRMT2S=Q?QA+c^U@%T32V;1%T773U?1UARIULRF%TA3UN<1p0TC1p0TF1p0TN1p0U51p0V51pTHV=1pNV@1pUDVD1pV<VE1pV8VF1pV4VG1pUNVH1pUHVI1pTNVJ1pUBVK1pW@VL1pW>VM1pW<VN1pW:VO1pULW01pUJW11pVFW21pVDW31pVBW41pV@W51pV>W61pV2W71pTBW81pT@W91pT>W:1pT<W;1pT:W<1pT8W=1pT4W>1pW8W?1pW6W@1pW4WA1pWBWB1pTLWC1pVHWD1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 5%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 6%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 7%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 8%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 9%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 10%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 11%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 12%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 13%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 14%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 15%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 16%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 17%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 18%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 19%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 20%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 21%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 22%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 23%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 24%nat 0%nat).
Variable ra' : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 25%nat 0%nat).
Variable gw : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 26%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 27%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 28%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 29%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 30%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 31%nat 0%nat).
Variable rav : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 32%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 33%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rbig_succ_walk) 34%nat 0%nat).
Lemma rbig_succ_walk : ltac:(sec_stmt2 constr:(SEC_T_rbig_succ_walk) 35%nat 0%nat).
Proof using MR TK G0 MSL RR GN AN SHN HC CR NR CLO sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav F fc.
intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
change (meta_word meta0) with 0 in CH.
destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
assert (HDR : rw_cells rsegs m x [C8 (wz 0); C1 (b8 0)]).
{ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
- cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
apply rzeros_bytes_at; [lia| cbn; pose_ceil; lia|].
intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
- cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
rewrite <- HG in CH.
(pose_ceil; unfold RCTX, RMLOCK in *).
step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
unfold ctx_head_cells in CX1. rewrite HC in CX1.
pose proof (rw_cells_prefix rsegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
step. step.
pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
step.
assert (PWX : pw st (Some (rid, 0)) = wz x).
{ unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHA : rw_cells rsegs mX (conc st g) (meta_cells st (big_metaA rid)));
[ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
| pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
clear MUa WMa CHA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
cbv delta [wz]. step.
set (stA := put_meta g (big_metaA rid) st) in MRA.
destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
{ eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
+ rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- unfold RGOT_SSP in R5. lia.
- unfold RSSP_GUARD in R6. lia. }
clear MRB0 MUb WMb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
{ eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
clear MRB1.
step. step. step. step. step. step.
rewrite (unsigned_lit (n + 4115)) by lia.
assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
step. step. step.
set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHC : rw_cells rsegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
[ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
| pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
clear MUc WMc CHC MRB.
step. rewrite (sx32_wz_sxv c) by lia. step.
lazymatch goal with H : rw_cells rsegs ?mX 950384 _ |- _ =>
pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 950396) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
clear H end.
step_ref; MallocKit_B.fix_lit_store; try MallocKit_B.nrm. rewrite le4_swrap_succ by lia.
set (stC := put_meta g (big_meta rid n) stB) in MRC.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
clear MRC.
raw_store_finishR (950384 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
step.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [exact MRD| exact TKB].
Qed.
End SE.
End SUCC.
End CEIL_WRAP_1.
