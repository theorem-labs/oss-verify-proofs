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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RASlot_W2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_W4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W6."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W4.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W4.CEIL_WRAP_1.T1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "0F"]; ["0G"; "4machine_state"; "5bvmap"; "0RUNp"; "6clr"; "7full_skip"; "8sxv"; "9meta_slot"; "9pw"; "9wz"; ":evt"; ";munch"; ";wmono"; "<MS"; "=mem_inv"; ">rsegs"]; ["@rt1_regs"; "?rt1_regs"; "ARCTX"; "Armrep"; "Baptr"; "Bconc"; "Bget_meta_rec"; "Bm_avail"; "Bm_freed"; "Bm_next"; "Bm_prev"; "Bm_set_next"; "Bm_set_prev"; "Bmstate"; "Boptr"; "Bput_meta"]; ["Bset_active"; "Cseg_rom"; "Dadd"; "Dle"; "Dlt"; "Dmul"; "Dpow"; "0a0"; "0a1"; "0a1'"; "0a2"; "0a2'"; "0a3"; "0a4"; "0a5"; "0a6"]; ["0a7"; "0f"; "0fc"; "0g"; "0gp"; "0m"; "0m'"; "0mn"; "0mr"; "0ms'"; "0nx"; "0pv"; "0ra"; "0s1"; "0s10"; "0s11"]; ["0s2"; "0s3"; "0s8"; "0s9"; "0sc"; "0sp"; "0st"; "0st1"; "0st2"; "0st3"; "0st4"; "EZ_to_bv"; "Ebv"; "0t0"; "0t1"; "0t2"]; ["0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.
Section SE.
Local Abbreviation SEC_T_ras_entry_walk := (forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc, a0 = Z_to_bv 64 sc ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' : word) m' junk,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz canary_val) a1' (pw st (active st sc)) a3 a4 a5 a6 a7
a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (match active st sc with None => 0x9bc74 | Some _ => 0x9baf8 end)) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ stk rsegs m' lo (bv_unsigned sp + -144)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep st m')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs))) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ras_entry_walk) 32%nat 0%nat).
Lemma ras_entry_walk : ltac:(sec_stmt2 constr:(SEC_T_ras_entry_walk) 33%nat 0%nat).
Proof.
intros HA ST LO MI. subst a0.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & _) & _). unfold wz in G4.
(pose_ceil; unfold ralloc_slot_entry, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD in *).
step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step.
rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; pose_ceil; lia]) end.
pose proof (rmrep_active_read st _ sc (wa (950384 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
step. clear RDA.
step.
replace (950376 + sc * 8 + 88) with (950384 + 80 + 8 * sc) by lia.
replace (950376 + sc * 8) with (950376 + 8 * sc) by lia.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
step. if_cases K; zify_cond K.
- destruct (active st sc) as [g|] eqn:HA.
{ exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _). pose_ceil.
unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
- destruct (active st sc) as [g|] eqn:HA.
2:{ exfalso. apply K. reflexivity. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End SE.
End ENTRY.
Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.
Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.
Lemma rt1_fin_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "S9'RLyR0%211&By5%2213yQ0%711&=';'>&Q7vR8%211z%63521%811&N&OvR5%3221&J'Ar1&M&Q0rNrMrLrKrJrIrHrG&RKv@%22Q31&I&F%11J%311rDrCrBrAr@r?r>r=r<r;r:r9r8r7r6%OJNMLKJIHGD@D?>=<;:987654321r5+c_QD%I2QJ1r4(0%11QL&QA%11Q>%Q9798653Q>1%QI3Q<Q;1qTDQ=1rFrE%Q=JQ;Q:Q9Q8Q7Q6Q521MQ2LKJIHGFEDCBA@?=+c^gH%Q62R71r3%QB74>21<QG:%QF3QI81p0QH1p0QM1pT6R71pQ0R:1pV8R>1pV6R?1pV4R@1pV2RA1pU0RB1pTNRC1pU8RD1pU6RE1pU4RF1pU2RG1pT2RH1pT0RI1pSNRJ1pSLRK1pSJRL1pSBRM1pS@RN1pTLRO1pV0S01pUNS11pULS21pV:S31pT:S41pU<S51pTJS61").
Proof.
intros until fc. intros AVNZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
pose proof (sxv_range (m_avail mr)) as RA.
step. rewrite sx32_wz_sxv by lia.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
{ exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
step. step.
apply evt_done. reflexivity.
Qed.
Lemma rt1_deq_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "S>'RLyR0%211&By5%2213yQ0%711';'>&Q7vR8%211z%63521&Q8%115%93814&N&OvR5%3221&J'Ar1&M&Q0rOrNrMrLrKrJrIrH&HvRF&Q9%11K%4231&I%11L&RKv@%22Q;1rErDrCrBrAr@r?r>r=r<r;r:r9r8r7%Q2JQ1Q0ONMLKJEC@?>=<;:987654321r6+c^hL%E2QN1r5(0%11R0&QA%11QA%Q<798653QA1%QN3Q?Q>1qTDQ@1rGrF%Q@JQ>Q=Q<Q;Q:Q9Q821MNLKJIHGFEDCBA@?=+c^gH%Q22R;1r4%QE74>21<QJ:%QI3QL81p0QK1p0R01p0R41pT6R<1pQ0R?1pV8RC1pV6RD1pV4RE1pV2RF1pU0RG1pTNRH1pU8RI1pU6RJ1pU4RK1pU2RL1pT2RM1pT0RN1pSNRO1pSLS01pSJS11pSBS21pS@S31pTLS41pV0S51pUNS61pULS71pV:S81pT:S91pU<S:1pTJS;1").
Proof.
intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. unfold pw, wz. reflexivity.
Qed.
Lemma rt1_next_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "TM'RLyR0%211&By5%2213yQ0%711';'>&Q7vR8%211z%63521&=&Q8%116%:3915%411&N&OvR5%3221&J'A'<'6y8%M11%311p0M1':r2&M&Q0rQ0rOrNrMrLrKrJrI&HvRF&Q9%11Q4%4231&I&F%11Q2%311&RKv@%22QF1rFrErDrCrBrAr@r?r>r=r<r;r:r9r8%Q4JQ3Q2Q1Q0ONMLGC@?>=<;:987654321r7+c^jL%E2R91r6(0%11R;r1&QA%11QK%Q?7:976431%R:3QIQA1&K(3'8%12R=R=(7&QB&Q2+R@%3221&QE+8vRD%3221%8251%9214%;4RIRI21(5%11>%A3?31%C31R@H&L%13RCRBJ%RE2RDK&Q3vC&Q@%13?QNR0%4331Q0%R?261%R@281%RA2;1%RB2Q01qT>RD1%RJ2RE1qTDRL1rHrG%REJRBRAR@R?R>R=21R0QOR1QNQMQLQKQJQIQHQGQFQEQDQCQBQ@Q=r5+c^gH%R62SJ1r4%RK75421Q@S7Q=%S63S991p0S81p0S=1p0SC1pT6SK1pQ0SN1pV8T21pV6T31pV4T41pV2T51pU0T61pTNT71pU8T81pU6T91pU4T:1pU2T;1pT2T<1pT0T=1pSNT>1pSLT?1pSJT@1pSBTA1pS@TB1pTLTC1pV0TD1pUNTE1pULTF1pV:TG1pT:TH1pU<TI1pTJTJ1").
Proof.
intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
pose proof (sxv_range (m_freed mr)) as RF.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. step.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
{ exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.
clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (950384 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (950384 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.
step.
apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.
Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.
Lemma rdeq_self_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "TO'RLyR0%211&By5%2213yQ0%711';&Q>&Q9vR8%211(1&Q4vR3%3221%93851&N&OvR5%3221&J'A'<'6y8%K11%311p0K1':r2&M&Q1vRDrNrMrLrKrJrIrHrG&Iz%211rF&RKv@%22Q@1rErDrCrBrAr@r?r>r=r<r;r:r9r8r7%Q0KONMLKJIHGDC@?>=<;:987654321r6+c_SD%E2R31r5(0%11R5r1&QA%11QG%Q;7:976431%R43QEQ=1&K(3'8'>%2211(7&QB&Q2+R@%3221&QE+8%221QG%7241%8213%:4<<21+Q8%;2Q>1%=4??Q?1(5%11@%D3A31%E3B71%G31R@L&L%13RCRBN%RE2RDO&Q3vC&Q?&D%11S1&Q@%Q81S0vRF%33R>21%73S251%:391Q:%RE2<1%RF2>1%RG2A1%RH2Q:1qT>RJ1%S02RK1qTDS21&H%12<S?%RKKRJRGRFRERDRCRBR>R:1R9R;R8R7R6R5R4R3R2R1R0QOQNQMQLQJQGr4+c^hL%R@2SN1r3%S175421QJS=QG%S<3S?91p0S>1p0SC1pT6SN1pQ0T11pV8T51pV6T61pV4T71pV2T81pU0T91pTNT:1pU8T;1pU6T<1pU4T=1pU2T>1pT2T?1pT0T@1pSNTA1pSLTB1pSJTC1pSBTD1pTLTE1pV0TF1pUNTG1pULTH1pV:TI1pT:TJ1pU<TK1pTJTL1").
Proof.
intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (950384 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (950384 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
set (st1 := set_active sc None st) in MR1.
assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).
rmeta_open G MUg WMg.
rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
st1. st1.
rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.
pose proof (rmrep_active_read _ _ sc (wa (950384 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. unfold wz.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
Section SE.
Local Abbreviation SEC_T_rdeq_other_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "V>'RLyR0%211&By5%2213yQ0%711&Q4';&Q>&Q9vR8%211(1r2%2281%83741&Q:%117%;3:14&=r4vR3%?3@21%411&GvRFr6%3221&N&OvR5%3221'Q=&Q?r8&Q;r9%I2O1&Q6%12>5%5231%8371@r:&Q<r1%7213%3291%>3513&Q@vRDr;%Q72Q=1%43318&D%11Q<%F3Q21;&J'A'<'6y8%QO11%311p0QO1':r3&M&Q1rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3&RK&Q5r@%22QF1%42RA1v@%62RC1rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrC%OKQANMLKJIHGBRE@?>=<;:987654321rB+c^jL%I2S61rA(0%11S8&QA%11R=%Q9798653QO1%S53QCQ;1&K(3'8'>%2211(7&QB&Q2+R@%3221&QE+8%221R8%7241%8213%:4<<21+Q8%;2Q=1%=4??Q>1r?%QD2S81%?215%A4CC21%A2QE7%C4EEQF1(5%11F%J3G31%K3H61%L3I;1%M3J?1%O31S>S0&L%13SAS@S2%SC2SBS3&Q3vC%231SNS6%RC241%RD261%RE291%RF2Q:1qT>RH1%RN2RI1qSDTI1%S02TJ1qTDS21rQ2&H%12T5TC%RLKS>RHRGRFRERD3R<R;1R:R=R9R8R7R6R5R4R3R2R1R0QOQNQLQIRA+c^hL%RE2U21r>%S174Q321QKT5QI%S<3T791tUFT5S>1tUDT6SB1tUBT7SH1tU@T8SO1p0T:1p0T?1p0T@1p0TE1p0TF1p0TL1p0U01pTHU:1pTFU;1pT6U=1pQ0U@1pV8UD1pV6UE1pV4UF1pV2UG1pU0UH1pTNUI1pU8UJ1pU6UK1pU4UL1pU2UM1pT2UN1pT0UO1pSNV01pSLV11pSJV21pSBV31pTLV41pV0V51pUNV61pULV71pV:V81pT:V91pU<V:1pTJV;1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 15%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 16%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 17%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 18%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 19%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 20%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 21%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 22%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 23%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 24%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 25%nat 0%nat).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 26%nat 0%nat).
Variable pv : ltac:(sec_ty2 constr:(SEC_T_rdeq_other_walk) 27%nat 0%nat).
Lemma rdeq_other_walk : ltac:(sec_stmt2 constr:(SEC_T_rdeq_other_walk) 28%nat 0%nat).
Proof.
intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _). pose_ceil.
pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _). pose_ceil.
assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
unfold RCTX, RMLOCK, RSSP_GUARD in *.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
step. clear CH.
rmeta_open (conc st pv) MUp WMp.
rmchunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. step. clear CH.
rmeta_open (conc st nx) MUn WMn.
rmchunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
pose proof (rmrep_active_read st2 _ sc (wa (950384 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.
step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. clear CH. step.
pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (wa (950384 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
rraw_store_finish0 (950384 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
fold st3 in MR3.
assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).
rmeta_open G MUg WMg.
rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
replace (get_meta_rec st3 g) with mr in CH.
2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.
pose proof (rmrep_active_read _ _ sc (wa (950384 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End SE.
End DEQ.
Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Lemma rm_act_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "SD'RLyR0%211&By5%2213yQ0%711';'2&EvRFvR3%3221(4%73621&N&OvR5%3221&J'A'<r3&M&Q1vRDrQ0rOrNrMrLrKrJrI&RKv@%22Q41r2r1&I&FvR1%211%411+2%;2Q=1rDrCrBrAr@r?r>r=r<r;r:r9r8%Q3KQ2Q1Q0ONMLKJGFE@>=<;:987654321r7+c^l8%L2QN1r6(0%11R0&QA%11QC%Q=798653QC1%QN3QAQ?1qSHR51%QB2R61qSDR71%QD2R81qTDQF1rHrGrFrEr5%QHKQGQCQBQAQ@Q?543Q<2Q2Q1Q0ONMLKJIHGFDA1r4+c^jL%QA2RC1%QM7431QNCR3A%R23R5;1p0R41p0R91pT6RB1pQ0RE1pV8RI1pV6RJ1pV4RK1pV2RL1pU0RM1pTNRN1pU8RO1pU6S01pU4S11pU2S21pT2S31pT0S41pSNS51pSLS61pSJS71pSFS81pSBS91pTLS:1pV0S;1pUNS<1pULS=1pV:S>1pT:S?1pU<S@1pTJSA1").
Proof.
intros until fc. intros NSK MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ apply evt_done. do 2 eexists. reflexivity. }
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
{ apply evt_done. do 2 eexists. reflexivity. }
exfalso. unfold full_skip in NSK. fold mr f in NSK.
assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rm_skip_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W4 "UO'RLyR0%211&By5%2213yQ0%711&Q4';'2&EvRFvR3%3221(9%73621&Q>&Q9vR8%211(1r2%22?1%?3741&Gr3%22?1':&QCz&Q8&Q6r4%22F1%411%7261&QD&QF+2+Q0%3221%5271%?271&N&OvR5%3221&J'A'<'6y8%QE11%311p0QE1&M&Q1vRDrQ5rQ4rQ3rQ2rQ1rQ0rOrN&RK&Q5r:%22QJ1%42R61&I&F%Q:2QN5%Q<11%311%511%;2R=Q7rIrHrGrFrErDrCrBrAr@r?r>r=%Q3KQ2Q1Q0ONMLKJER2R6?>=<;:987654321r<+c^l8%L2RN1r;(0%11S0r1&QA%11QH%Q>7:976431%RN3QFR61&K(3'8'>%2211(7&QB&Q2+R@%3221&QE+8%221QJ%7241%8213%:4<<21(5%11=%A3>31%C31R=H&L%13R@R?J%RB2RAK&Q3vC&Q@%S=2SJQM%23R91SG%5341Q1%S9271%S:291%S;2<1%S<2Q11qT>RB1%RH2RC1qSHT91%RJ2T:1qSDT;1%RL2T<1qTDRN1rMrLrKrJv@%RB2TD1r9%RNKRMRHRGRFRE76542R8R7R6R5R4R3R2R1R0QOQNQMQLQJQGRB1r8+c^jL%RG2TI1r7%S475421QJS>QG%S=3S@>1p0S?1p0SD1p0T51p0T91p0TB1pT@TK1pT6TM1pQ0U01pV8U41pV6U51pV4U61pV2U71pU0U81pTNU91pU8U:1pU6U;1pU4U<1pU2U=1pT2U>1pT0U?1pSNU@1pSLUA1pSJUB1pSFUC1pSBUD1pTLUE1pV0UF1pUNUG1pULUH1pV:UI1pT:UJ1pU<UK1pTJUL1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 14%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 15%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 16%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 17%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 18%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 19%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 20%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 21%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 22%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 23%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 24%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 25%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 26%nat 0%nat).
Variable mn : ltac:(sec_ty2 constr:(SEC_T_rm_skip_walk) 27%nat 0%nat).
Lemma rm_skip_walk : ltac:(sec_stmt2 constr:(SEC_T_rm_skip_walk) 28%nat 0%nat).
Proof.
intros FSK GN MSn FNR MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). pose_ceil. fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _). pose_ceil.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.
step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.
step. clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (950384 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (950384 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
step. rewrite sx32_wz_sxv by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End SE.
End M.
End CEIL_WRAP_1.
