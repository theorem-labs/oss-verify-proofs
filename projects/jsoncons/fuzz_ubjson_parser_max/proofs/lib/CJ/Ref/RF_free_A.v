(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_free_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_free_A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_free_A.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2or"; "3N"; "3Z"; "0E"; "0F"]; ["4bvmap"; "0RUNp"; "5mw_ok"; "6b8"; "6meta_slot"; "6meta_word"; "6ticks_ok"; "6wz"; "7C8"; "7CB"; "7cell"; "8evt"; "9mkR"; "9stk"; "9wmono"; ":MS"]; [";bytes_at"; ";mem_inv"; ";zx32"; "<alloc_ceiling"; "=rw_cells"; ">rsegs"; "?rfhead_post"; "@rfree_fp"; "Armrep"; "Brpres_except"; "CKnown"; "CRKGroup"; "Caadd"; "Captr"; "Ccell_read"; "Ccellval"]; ["Cconc"; "Cget_meta_rec"; "Cget_shadow"; "Cghdr"; "Cm_freeable"; "Cm_last_idx"; "Cm_maplen"; "Cm_sizeclass"; "Cmeta"; "Cmstate"; "Cr_base"; "Cr_kind"; "Cr_len"; "Cregion"; "Crkind"; "Cround_up_pg"]; ["Cs_groups"; "Cs_regions"; "Cwr16"; "Cwr8"; "Dseg_rom"; "Eadd"; "Eland"; "Ele"; "Elt"; "Emodulo"; "Emul"; "Epow"; "Eshiftr"; "Esub"; "0a0"; "0a3"]; ["0a5"; "0a6"; "0a7"; "0b"; "0b3"; "0fc"; "0g"; "0gh'"; "0gp"; "0hi"; "0idx"; "0junk"; "0lo"; "0lo8"; "0m"; "0m0"]; ["0mr"; "0p"; "0po"; "0r"; "0ra"; "0rsv"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"]; ["0s8"; "0s9"; "0sp"; "0st"; "0st1"; "Flookup"; "GZ_to_bv"; "Gbv"; "Gbv_unsigned"; "HN_countable"; "HZ_countable"; "Hprod_countable"; "Iprod_eq_dec"; "Jgmap"; "Jgmap_lookup"; "Keq_dec"]; ["Leq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := (pose_ceil; unfold UNIT, IB in *); lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma zx32_wz : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_A "I'='9&R7zr1%3221&R8&R;+2+Q0%3221%5271%;271':'SGyR0%211&Q2&Gr2%211%411%93612p0;1pXDH1").
Proof. intros x. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma meta_word_sc2 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_A "G'QH&Br1%211':'=&R6&R<&Er2%211+5%5221+SN%8221&R:+2&QG%119%4231%@3?61p0B1pV2F1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_pg : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_A "E'QH&Br1%211':'=&R=&Er2%211&R9+TP0%2231%7241&R:&QF%118%3261%>3=51p0@1pV2D1").
Proof. intros mr.
intros (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
fun ms' => exists x1 x5 x6 x7 junk m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0xe7e98) x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ae9c) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rmrep st1 m'.
Section SE.
Local Abbreviation SEC_T_rfree_head3 := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_free_A "\M'SGyR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'4%114'='QI&Q='QM&8'<r8%33271&R6r6+O%3221'QH&QAr;%2219&R2&Q<-2%2251z&R3-3%6291+WOr<%53321%;3871&Q8vAr=r@%43321&Q1&Q5rA%3221&Fr?%211&MrC&R5&SHrQB%22QK1-Q@%5221%84>7=1&R7&Q3%11FrB%4221&R=rQD%=2R61+Q@%4221%:2B1&Q4rFrQE%D2R=1%F21B(2'J(Iu8rE%3221(HrQ7%211rQ8%411rQ>%611rQ?%811rQF%:11(5%11A%C3B31%D3C61%E3D91%F3E<1%G3F?1%H3GC1%N4QHMJ1&Q9&Q7rD%QC2S<>%332J1rHrG%73321&NrI%23R315':%S>1S4&SE'SM&SO&SI%34S721S9&SN%14S943S;&3%13S;S@Q;&R1%11QE%;6S>S@7531(1%12SBH%@3?31'QN&QK%11QD(Q;%E3421&QJ%11R0%RD21RH%I3SORB1&R9+@%22S31%M3T31S?%RC23S1%RK2RA4&QO&QL%11Q4%311%RI251&DrL%221Q9'Q?&Q>&QBrM%Q33T=TB6%3221+3%RO2QH1%7231(Q:%11QD%QC3;31rN%Q<3TFTK:%<221+2%S82RI1%@231%QJ3B18rO%QC3TMU28%C221+1%S?2S81%G231%R13I1?'9&QE%11S5%SJ2TG1&R8+Q0%2241%7241&QD%11SD%T12TN1%722F%<221&QG%11RE%T62U31+R0%=231%B231&QF%11RL%T<2U91&R;+Q8%22Q31%E251%J251rQ0%TC2U@1+X0%J231%O231rQ3%R=11%U021QN%TJ21QA%U22Q;Q8rQ4%RB11%R812%R:11%U7231%U1261%U22UOQBrQ5%RI11%U<21QL%U12D1%U72QG1%QA261&Q0rQ;rQ1%U721J&C%11V;%T>1W5%U03W621%84V0751rQ<rQ2%;4V3214'7%12W2W7'QC%W@11&SL&T0%24W7T2W<1&SK&SJ%26W:T5T4W?41%T74W>418%T44W?529r2&R0%11A%T=6>=5431r1%T32?1%TB3?31r3%T;3WEWJ1%T<3WFWKH%TF3WG21';r4%WK3WJWO1%V?2Q<1%VG22T0%VA21Q>%6231p081p0=1pU@N1pU8Q01&K&Q6rR>rR=rR<rR;rR7rR6rR0rQOrQNrQMrQLrQKrQJrQIrQHrQGrR:rR9rR8rQCrR5rQArQ@%SH1RN%IQ1HGFEDCBA@?>=<;:9876VBW4W;5432QOR7VDT1VHR61&O&L&SF%WK2YDK%WM21WI%32YF1%42YGR=&G&Q@%12RAW2%311&E%11S<%611%<2YOS4rR4%91S;rR3rR2rR1%COX;?Q;Q:MLK>I:7654321Q7Q6Q5Q4Q3Q2Q1Q0ONW7WIX0J+c[b<%D2Z71(0%11Z8&R4%11XK%K77O5N3WB1%QG3XMM1p0QI1p0RL1p0S01p0S:1p0SB1p0SJ1p0SO1p0T51p0T>1p0TE1p0TK1p0U41p0U<1p0UD1p0V11p0V51p0V<1p0V>1p0VC1p0VH1p0VN1p0W@1p0WD1p0WM1p0XM1p0Y41p0Y:1p0YD1p0YH1p0YM1tW:ZMZ31tV2ZCZ@1tUF[0ZE1tV6[1ZJ1pV<[21pN[31pUD[41pUL[51pU:[61pU>[51pV8[51pV4[71pW8[91pUJ[;1pUH[=1pV0[@1pUN[A1pU<[G1pQ0[J1pXF[N1pX@[O1pX>\01pX<\11pX:\21pVD\31pVB\41pW4\51pW2\61pW0\71pVN\81pVL\91pVJ\:1pVH\;1pVF\<1pU6\=1pU4\>1pU2\?1pU0\@1pTN\A1pV@\B1pV>\C1pX8\D1pX6\E1pX4\F1pXB\G1pUB\H1pW6\I1pV:\J1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 27%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 28%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 29%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 30%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 31%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 32%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 34%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 35%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 36%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 37%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 38%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 39%nat 0%nat).
Variable lo8 : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 40%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 41%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 42%nat 0%nat).
Variable rsv : ltac:(sec_ty2 constr:(SEC_T_rfree_head3) 43%nat 0%nat).
Lemma rfree_head3 : ltac:(sec_stmt2 constr:(SEC_T_rfree_head3) 44%nat 0%nat).
Proof.
intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
(pose_ceil; unfold UNIT, IB in *).
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).
pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (SOK3 : store_ok rsegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
st1.
pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
cbn [aadd snd] in MR2. fold po in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
store_done.
pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
assert (SOK2 : store_ok rsegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
st1.
pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
by (f_equal; unfold wa; f_equal; lia) end.
store_done. clear MR2 TK2 HWr HWr2.
st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
st1.
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact I].
intros x Hx. right. right. exists (fst p), r.
assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
apply evt_done. unfold rfhead_post.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
do 6 eexists.
split; [reflexivity|].
split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.
End SE.
Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 -> idx <= m_last_idx mr ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ae04) fc None m0 (seg_rom rsegs)).
Proof.
intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
(pose_ceil; unfold UNIT, IB in *).
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
fold rsv0.
st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
-
destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read rsegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).
st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
st1.
rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.
Section SE.
Local Abbreviation SEC_T_rfree_head := (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z), let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m -> mem_inv rsegs m -> ticks_ok st ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 34%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 35%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 36%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 37%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 38%nat 0%nat).
Variable gh : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 39%nat 0%nat).
Variable ar : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 40%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 41%nat 0%nat).
Variable lo8 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 42%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 43%nat 0%nat).
Variable r32 : ltac:(sec_ty2 constr:(SEC_T_rfree_head) 44%nat 0%nat).
Lemma rfree_head : ltac:(sec_stmt2 constr:(SEC_T_rfree_head) 45%nat 0%nat).
Proof.
intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl rsegs m) as WM.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (FB : fst base = fst p) by reflexivity.
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).
revert BIG RB0r RE0.
(pose_ceil; unfold rfree_entry, UNIT, IB in *). intros BIG RB0r RE0.
st1. if_cases K0; zify_cond K0. { exfalso. lia. }
carve_frame 48%nat ST.
st1. st1. st1. st1. st1. st1. st1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; pose_ceil; lia) end.
eapply evt_cut.
{ eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
all: try eassumption. all: try lia. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0x9adbc)) with (Z_to_bv 64 0x9adbc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (MW : mw_ok mr) by (unfold mw_ok; lia).
pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (K2 : forall a4v a5v a6v, evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0x9adbc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ae04) fc None mX (seg_rom rsegs))) end.
{ intros a4v a5v a6v.
lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
lazymatch type of MUs with munch ?W m ?mY =>
assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
subst rsv rsv0 E stride mr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
[exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
| exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
| intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
(eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
| ulia
| exact RB0r
| exact RE0
| exact HCLR]. }
st1. st1. st1. st1. fold idx. rewrite MW12.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0x9adbc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ade8) fc None mX (seg_rom rsegs))) end.
{ intros a2v a4v COND. specialize (SC48 COND).
assert (STR : stride = 16 * size_class (m_sizeclass mr)).
{ unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
replace (110048 + m_sizeclass mr * 2) with (110048 + 2 * m_sizeclass mr) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (RS' : ov_read_bytes rsegs mX (Z_to_bv 64 (110048 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
{ replace (Z_to_bv 64 (110048 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
rewrite Egw. apply K2. }
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply KS. left. exact Km.
-
st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+ apply KS. right. exact Kl.
+
st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
rewrite Egw. apply K2.
Qed.
End SE.
End CEIL_WRAP_1.
