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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W3 ASlot_W14.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_W14 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W14."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W14.CEIL_WRAP_1.TAIL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "0G"; "4machine_state"; "5bvmap"; "0P"; "0RUNp"; "6stFin"; "7sxv"; "8ticks_ok"; "8wz"]; ["9evt"; ":mkR"; ":munch"; ":wmono"; ";MS"; "<mem_inv"; "<sx32"; "=rsegs"; ">rtailW"; "?RCTX"; "?RMLOCK"; "?rmrep"; "@seg_rom"; "Aadd"; "Aland"; "Ale"]; ["Alt"; "Alxor"; "Amodulo"; "Amul"; "Apow"; "Asub"; "0a"; "0a1'"; "0a2'"; "0a3"; "0a3'"; "0a4"; "0a4'"; "0a5"; "0a6"; "0a7"]; ["0ai"; "0b"; "0cnt"; "0fc"; "0gp"; "0m'"; "0mC"; "0ml"; "0ms'"; "0mt"; "0p"; "0ra"; "0s0'"; "0s10"; "0s11"; "0s2"]; ["0s3"; "0s4"; "0s6"; "0s8"; "0sc"; "0sp"; "0stT"; "BZ_to_bv"; "Bbv"; "Bbv_swrap"; "Bbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"]; ["0t5"; "0t6"; "0tp"; "0x"; "0y"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma sx32_congr : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "L'R8yR0%211'5'3&Q2&R:r2%2271&Q4+2+Q0%3221%8251r1%:213%<3=31&Fr3%211&?&=%11?%311%D3F51p091pS4G1pR>I1").
Proof. intros a b.
intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.
#[using="Type"] Lemma unsigned_mod32_pred_sxv : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "L'5'3&Q2&R:yR0&R7&M&?&=r1%211%411%9281-1%8221%:2;1%=2<1&Q4+2+Q0%3221%C251&Q5+1%22?1%G215%I3J51pU:K1").
Proof. intros y.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
rewrite (mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed.
#[using="Type"] Lemma unsigned_mod32_add_not : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "Q9'5'2&Ozr1%3221&Q0&Q4+2+R0%3221%5271%;271'3&Q2&M&R:yR0&?&=r3%211%411%7261&Q1r2+_oooooooooooO%3221%=251+Q0%G2F1%A231&Q5+1%22>1%321:%F216%H3Q561p0J1pS4Q71pR>Q81").
Proof. intros a b.
intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
#[using="Type"] Lemma unsigned_mod32_swrap_add_not : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "Q4'5'3&Q2&R:yR0&R7&M&R9yQ0r2%3221&Q1&?&=r1%211%411%>2=1+_oooooooooooO%8221%>2:1%@2A1%C2B1&Q4+2+Q0%3221%I251&Q5+1%22E1%321A%N216%Q03Q161pS4Q21pR>Q31").
Proof. intros a b.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
pose proof (sxv_range b) as RB.
rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia.
unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
clearbody x y. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma land224_m32 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "D'5'2&Ozr1%3221&Q0+X0%2241%8241'3&Nr2+W0%3221+_ooooooooooo0%5241%73A31p091pU8C1").
Proof. intros x.
intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.
Definition rtailW : list (Z * Z) :=
[(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.
Section SE.
Local Abbreviation SEC_T_rtail_walk := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W14 "U5'R8yR0%211&9y5%2213yQ0%711'1y8%:11%311p0:1&Kv;vR6r1%43321&E&Gr2%3221&@'8'4'2'3r7&D&ArQ3rQ2rQ1rQ0rOrNrMr6&R7v7%22Q71z%42Q91r5r4r3rJrIrHrGrFrE&M&I+R@%3221&Q3+8vR4%3221%8251%G2QL1rD&J%<215%K2R01rCvQB%N2R31rBrAr@r?r>r=%Q>OQ=Q<Q;Q:Q9Q8Q7Q6Q3Q1Q0ONQGMLKJIH>=:97654321r<+c`gD%Q82R=1r;(0%11R?&L%11R0%QH798653R41%QK3QNQJ1&B&Hr:%3321R9&C%13R83R;%R:2R9R<&<vQ@vQGvQIvQJ%57RCQ8O4321%RF3RE1RC&>%113%R=231%R>2;1%R?2=1%R@2@1%RA2E1qS<RO1%RD2S01qRJS;1%RF2S<1qRFS=1%RH2S>1qRBS?1%RJ2S@1qR@SA1%RL2SB1qSJSC1%RN2SD1qSBS01rLrK%RD2SIR0v:%RF2SK1&Q5+1%22QL1%RJ2SO1%RK2T0Q3r9r8%S7O<;RFRERDRCRB:RL843RAR6R2QOQNQMQLQKR7QJR3QHR0QEQ<21S9RO+c`\L%S02T51%S;73RL1RKQFRJQD%SB3SEA1p0SD1p0SI1pS>SO1pS8T51p>T81pU4T<1pU2T=1pU0T>1pTNT?1pSNT@1pSLTA1pT8TB1pT6TC1pT4TD1pT2TE1pT0TF1pS0TG1pRNTH1pRLTI1pRHTJ1pRDTK1pTLTL1pTJTM1pTHTN1pU6TO1pS:U01pT<U11pSHU21")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 6%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 7%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 8%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 9%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 10%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 11%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 12%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 13%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 14%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 15%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 16%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 17%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 18%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 19%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 20%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 21%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 22%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 24%nat 0%nat).
Variable mC : ltac:(sec_ty2 constr:(SEC_T_rtail_walk) 25%nat 0%nat).
Lemma rtail_walk : ltac:(sec_stmt2 constr:(SEC_T_rtail_walk) 26%nat 0%nat).
Proof using r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 F fc mC.
intros MR MI.
pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold rtailW in MU.
pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). pose_ceil. fold G in Gpos, GC, GI, G4.
pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). pose_ceil.
assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
(pose_ceil; unfold RCTX, RMLOCK in *).
pose proof (rmrep_usage_read (stA stT p) mC sc (wa (950384 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
change (usage (stA stT p) sc) with (usage stT sc) in RDU.
replace (wa (950384 + 464 + 8 * sc)) with (Z_to_bv 64 (950376 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
step. clear RDU.
step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
pose proof MRA as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (usages (stA stT p)) sc (wa (950384 + 464 + 8 * sc)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
replace (wa (950384 + 464 + 8 * sc)) with (Z_to_bv 64 (950376 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
rraw_store_finish0 (950384 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRA TKA.
step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
step.
set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
rmeta_open G MUa WMa.
step. step.
assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
{ subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
rewrite (sx32_congr v3 AV V3).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
step. step.
set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
{ subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
step. step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
| clear MUa WMa; rename H into CH1 ] end.
assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRB TKB MSTB.
pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
[ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
| clear HB LHB ] end.
pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
step.
step.
pose proof (byte_range y8) as Y8.
step. unfold zxb.
step. rewrite ?(unsigned_lit ai) by lia.
replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
step.
pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
rewrite (land224_m32 (bv_unsigned y8)) by lia.
pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
rename H into HDR2;
assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
| assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
[ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
| rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
| ] ] end.
{
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
- unfold RCTX in X1. lia.
- unfold RMLOCK in X2. lia.
- unfold RNEED_LOCKS in X3. lia.
- unfold RPAGE_SIZE in X4. lia.
- change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
- change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
+ rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
+ pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
- change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
destruct (N.eq_dec q (fst p)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
- unfold RGOT_SSP in X5. lia.
- unfold RSSP_GUARD in X6. lia. }
clear MRC MRC2 MUb WMb HDR2.
assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear TKC MSTC.
pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
rmchunk MRD MSTD CH.
change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
rmeta_open G MUc WMc.
step. step. step. step. step.
rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
rewrite (unsigned_lit W), EW, land_pg_mask by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
step. rewrite ?unsigned_lit by lia.
step. step. step. step.
rewrite ?(unsigned_lit (mask_upto ai)) by lia.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_read rsegs mX (950384 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (950384 + 80 + 8 * sc)) H
(actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
replace (wa (950384 + 80 + 8 * sc)) with (Z_to_bv 64 (950464 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]
| clear MUc WMc; rename H into CH3 ] end.
{ unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
unfold wz. rewrite !app_nil_r.
rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
fold AV. Z.div_mod_to_equations. lia. }
do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
{ reflexivity. }
{ cbn. tauto. }
assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
clear MRD TKD MSTD.
clear CH3.
lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_store_ok rsegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (950384 + 80 + 8 * sc)) H
ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
replace (wa (950384 + 80 + 8 * sc)) with (Z_to_bv 64 (950464 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
st1.
replace (Z_to_bv 64 (950464 + 8 * sc + 0)) with (Z_to_bv 64 (950464 + 8 * sc)) in SOK by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
rraw_store_finish0 (950384 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
step.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MRF| exact TKE].
Qed.
End SE.
End TAIL.
End CEIL_WRAP_1.
