(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B F_ntf_C MallocKit_B MallocKit_B3 F_am_A F_am_D.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C RF_am_A.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_D () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "0RUNp"; "6am_took"; "7meta_slot"; "8evt"]; ["9mkR"; "9stk"; ":MS"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">LFree"; ">aptr"; ">c_avail_meta"; ">c_avail_meta_count"; ">c_free_meta_head"; ">conc"; ">ctx"; ">dequeue"; ">get_meta_rec"; ">m_next"]; [">m_prev"; ">mstate"; ">optr"; "?rsegs"; "@ram_frame"; "@ram_ret_post"; "ARMLOCK"; "ARSSP_GUARD"; "Armrep"; "Bseg_rom"; "Cadd"; "Cle"; "Clt"; "Cpow"; "Csub"; "0a0"]; ["0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0gp"; "0h"; "0junk"; "0lo"; "0m"; "0ms'"; "0nx"; "0pv"]; ["0q"; "0raw"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2"; "0s2o"; "0s3o"; "0s4"; "0s4o"; "0s5"; "0s6"; "0s7"]; ["0s8"; "0s9"; "0sp"; "0st"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_ram_deq := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_D "VA'REyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'8'Q1&G&Q8v<r4r7%43321&C&Q3r8%3221'5&Q2&J&Lr6%211%411(1r5%22C1%:3941&>%12B8&O&N%12AE%311%:2K=%B3A21&Q0r9%721G%311%G3F16r:%>21Kr;%@21M&6%M3Q753%N3Q8:4%3221&Er@&Q:&RFrQE%22QO1-R0%5221&Q4r?rCrDrErFrGrH%88QH7654321%A4QD@:1&ArArQF%B2R?1%D21@%54QJ4>1&Q;&D%11R2%321J&Q>rQH%K2RH1+R0%4221%92>1&?&Q5rLrQIrQGrKrJrIrQ8rQ7rQ6rQ5rQ4rQ3rQ2rB&M(F%231QCQ1&RD&K%12Q4QF%32SB1%FHS1EDLCBA@Q:Q;?>=<;:9Q<Q=8Q6Q>51&B&@rM%QJ2SGH%QL21QH%:2SI1rQDrQCrQBrQArQ@rQ?rQ>rQ=rQ<rQ;rQ:&Q7%G2T61&Q6%I2T81rQ9rQ1rQ0rOrN%IOHEQGQ>R0R@DCBA@?>=<;:865Q:Q9Q8Q7Q6Q5Q44321+caZD%Q12T@1(0%11TA&Q9%11SM%Q177R>5R?3R@1%QJ3SOQ31p0QL1p0R31p0R81p0R?1p0S21p0S71p0S:1p0S=1p0SC1p0SJ1p0SM1p0T91p0T>1pT0TD1pSNTE1pSDTF1pU8TH1pSHTJ1pSFTL1pSJTO1pS@U51pDU81pTJU<1pTFU=1pTDU>1pT@U?1pT8U@1pT4UA1pV0UB1pULUC1pUJUD1pUHUE1pUFUF1pT>UG1pT<UH1pU4UI1pU2UJ1pU0UK1pTNUL1pTLUM1pTHUN1pS>UO1pS<V01pS:V11pS8V21pS6V31pS4V41pS2V51pS0V61pT:V71pT6V81pUDV91pUBV:1pU@V;1pUNV<1pSBV=1pU6V>1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 7%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 8%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 9%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 10%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 11%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 12%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 13%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 14%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 27%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 28%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 29%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 30%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 31%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 32%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 33%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 34%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 35%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 36%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 37%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 38%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 39%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 40%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 41%nat 0%nat).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 42%nat 0%nat).
Variable pv : ltac:(sec_ty2 constr:(SEC_T_ram_deq) 43%nat 0%nat).
Lemma ram_deq : ltac:(sec_stmt2 constr:(SEC_T_ram_deq) 44%nat 0%nat).
Proof.
intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _). pose_ceil.
pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _). pose_ceil.
pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _). pose_ceil.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (954560, 954560 + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
st1. if_cases K; zify_cond K.
-
assert (Enx : nx = h).
{ rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells rsegs ?mX 954560 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
[exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
-
assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).
rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. st1. clear CH.
rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
st1. st1.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.
rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
{ eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells rsegs ?mX 954560 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
[exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End SE.
Lemma ram_take_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_D "VD'REyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'8'Q1&G&Q8v<r2r5%43321&C&Q3r6%3221'5&Q2&J&Lr4%211%411(0%11B%93831&7&I%91B%211z%?3K21%611'4&Q;%@1E%911%3271&Q<&Q=+2+R0%3221%5271%;271&Hr7%L11%311(1%12Q<Q4%Q33Q231&>r8%2218&Er<&Q:&RFrQA%22R61-R0%5221&Q4r;r?r@rArBrCrD%88QO7654321%A4QK@:1&Ar=rQB%B2RF1%D21@%54R14>1&D%11R8%Q?21I&Q>rQD%J2RN1%321Q<%QD2<1&?&Q5rHrQErQCrGrFrErQ4rQ3rQ2rQ1rQ0rOrNr>&=%RE1N%R>11+1%I221%53Q2QD1&RD&K%12Q5QG%32SJ1%IHS9HGNFEDCQ;Q<BA@?>=<Q=Q>;Q7Q?51&B&@rI%QK2SOK%QM21QI%:2T11rQ@rQ?rQ>rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6&Q7%G2T>1&Q6%I2T@1rQ5rMrLrKrJ%IOHEQIQAR1RADCBA@?>=<;:865Q=Q<Q;Q:Q9Q8Q74321+caZD%Q12TH1%SH1TH&Q9%11T4%Q076R>4R?3R@1%QL3T6Q21p0QN1p0R41p0R81p0R?1p0S21p0S61p0S>1p0SK1p0T31p0T>1p0TC1pT2TI1pU8TK1pSHTM1pSFTO1pSJU21pS@U81pDU;1pTJU?1pTFU@1pTDUA1pT@UB1pT8UC1pT4UD1pV0UE1pULUF1pUJUG1pUHUH1pUFUI1pT>UJ1pT<UK1pU4UL1pU2UM1pU0UN1pTNUO1pTLV01pTHV11pS>V21pS<V31pS:V41pS8V51pS6V61pS4V71pS2V81pS0V91pT:V:1pT6V;1pUDV<1pUBV=1pU@V>1pUNV?1pSBV@1pU6VA1").
Proof.
intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _). pose_ceil.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
st1. st1.
rewrite bv_eqb_refl. cbv iota.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
rewrite CF; clear CF.
st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 954552) with (Z_to_bv 64 RMLOCK).
eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
[exact MR | exact MI | exact MSq | lia | exact FR | exact ST | pose_ceil; lia | lia].
Qed.
Lemma ram_disp0 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_D "T2'REyR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'Q1&Q8v<r1r2%43321'5&Q2&J&L%116%311(0&G%211%93841'8&Ir3%:11%311z%@3621&?&Q3':&B&@r9rQ6rQ5rQ4rQ3rQ2rQ1rQ0rO&RD%12QBArLrKrJrIrHrGrF&Q6%:2QK1rErDrCrBrAr@r?r>r=r<r;r:%Q1OQ0ONMLKJIHFFEDCBA@?=<;:987654321r8+ca]8%J2R;1r7%QE1R<r6&Q9%11Q<%Q;79865431%R03Q=R31qSLQ>1rNrM%Q?O=Q<Q;Q:Q9Q8Q7Q621Q3Q2Q1Q0ONMJKIHGFEDCBA@?Q>+caZD%Q72RH1r5%QD74>2<=1:%QH3QG81p0QJ1p0R21p0R=1pU8RC1pSJRE1pS@RK1pDRN1pV0S21pULS31pUJS41pUHS51pUFS61pT>S71pT<S81pU4S91pU2S:1pU0S;1pTNS<1pTLS=1pTHS>1pTBS?1pS>S@1pS<SA1pS:SB1pS8SC1pS6SD1pS4SE1pS2SF1pS0SG1pT:SH1pT6SI1pUDSJ1pUBSK1pU@SL1pUNSM1pSBSN1pU6SO1").
Proof.
intros until st. intros MR FMH CNT.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
st1. st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.
