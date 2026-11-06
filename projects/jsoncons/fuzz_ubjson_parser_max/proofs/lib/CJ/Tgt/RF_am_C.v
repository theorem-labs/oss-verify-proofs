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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A RF_am_K.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1snd"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "0F"; "4bvmap"; "0RUNp"]; ["5am_took"; "6pgal"; "7carve_st"; "8lr_lo"; "8wz"; "8zeros"; "9C4"; "9C8"; "9CB"; "9cell"; ":evt"; ";mkR"; ";stk"; ";wmono"; "<MS"; "=bytes_at"]; ["=mem_inv"; "=wr_at"; ">alloc_ceiling"; "?rw_cells"; "@AREA_HDR"; "@META_SIZE"; "@NSLOTS"; "@RKGroup"; "@aadd"; "@aptr"; "@area"; "@c_avail_meta_area_count"; "@c_meta_area_tail"; "@c_secret"; "@conc"; "@ctx"]; ["@meta"; "@mkArea"; "@mstate"; "@optr"; "@r_base"; "@r_kind"; "@r_len"; "@region"; "@rkind"; "@round_up_pg"; "@s_areas"; "@s_metas"; "@s_regions"; "@set_areas"; "@set_meta_area_tail"; "@upd_ctx"]; ["Arsegs"; "Bram_fp"; "Bram_frame"; "Bram_ret_post"; "CRMLOCK"; "CRSSP_GUARD"; "Crmrep"; "Drpres_except"; "Eseg_rom"; "Fadd"; "Fle"; "Flt"; "Fmul"; "Fpow"; "Fsub"; "0a0"]; ["0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0gp"; "0junk"; "0k"; "0lo"; "0m"; "0m0"; "0p"; "0r"]; ["0raw"; "0s0"; "0s0o"; "0s10"; "0s11"; "0s1o"; "0s2o"; "0s3o"; "0s4"; "0s4o"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"]; ["0st"; "0st0"; "0stC"; "0stD"; "Ginsert"; "Gis_Some"; "Glookup"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "IN_countable"; "IZ_countable"; "Iprod_countable"; "Jprod_eq_dec"; "Kmap_insert"; "Lgmap"]; ["Lgmap_lookup"; "Lgmap_partial_alter"; "Meq_dec"; "Neq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tl"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_ram_carve2 := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_C "[6'SHyR0%211&>y5%2213yQ0%711'6y8%:11%311p0:1'4%114'<'QB&Q9'QG&R6v?r3r7%43321&Q0&R0r8%3221'9'SO';&T2&SJ%44321?&QLr5%211r6%411%;3631%Q01F&SF&T0%14=<;I&3%13?N:%56@L=318(1r4%22O1%F3:41&:'QH&QE%11C(Q7%L3421%611&R:z&7%13OQ>Q7%4231&R9%43Q2QAQ6+TP0%3221&QI&QF%11Q?%311%=251&Ar9%>3Q<QK1%311&C%114&QD%116r:%E3QCR21%C231%I261'Q:%R=11&SM&T3%24QJQIR91&SL&SK%26QMQLQKR<41%QO4R;418%QC4R<529r;&QJr<%211%QI6RA>6541(0%11@%R93@31'8r1%Q>2Q=1&R;&Q6%2241%6241'Q@%S611%RB4RNGD2%R64ROHE3&Q8r>&Q4&R<&Q5r2%3221%QI251%8271&QKr?%211%RD6S<@>=41%K1A%S33A21p0D1pUFSB1&Q=&Q?%11B%311%R<2R;1&R=+2+R0%3221%Q2261%Q6261&Q3rC&Q>%12EN(2'I(G&D%11RJ%311(F%113(5%118%:3931%;3:41%<3;71%=3<81%B4T6A?1rDr@%C21Q7+H%S5221(HuSo8&E%112%4231%I3H1@%N4TB;71&R7&R1rB&SIrQJ%22U@1%534Q41rFrE%93321&MrG%23TO15rQL%;2UI1-R0%SM221&R2rKrLrMrNrOrQ0%78U@A654321%QH4U<>91&LrHrQM%J2V81%T;21?%54UB4H1&Q2%11UI%TD21G&R>rQO%Q22V@1%321R9%TI2<1&QO&QN%U72V5Q3%211%421Q1&QM&SD&SN&T1%14V<T5T2T9%34V=T:T21(QA%RM1I%RO11%SO1VA%4321SI%T51SM%;7VDTAT97Q>21%=21SO&J&R3rQ6rR2rR1rR0rQ5rQ4rQ3rQ2rQ1rQBrQArQ@rQ?rQ>rQ=rQ<rJ&@%T:2QDT8+S4%33TF21&SGrI%SA21QI%V221RN%42X11%KHW?JIHGFEDCBA@?>=<;R0R1R5:R261&N&KrQ7%RH2X6M%V921R=%;2X81rQN%=2X:;rQKrQIrQHrQGrQFrQErQD&R5%F2XC1&R4%H2XE1rQCrQ;rQ:rQ9rQ8%GOFCQAQ@R<BRDS3A@S<?>=<;:865Q:Q9Q8Q7Q6Q5Q44321+cag4%Q02XM1%UL1XM&R8%11X8%N76RO4S03S21%QL3X:Q01tW8XDQN1tW6XER=1p0RC1p0RI1p0RM1p0S41p0SB1p0SF1p0T11p0T>1p0U21p0U>1p0V;1p0VN1p0W71p0W<1p0WF1p0WL1p0X41p0X@1p0XM1p0Y21pV0Y81pUNY:1pW2Y<1pW4Y=1pUHY?1pUDYA1pUJYD1pULYE1pU@YK1pLYN1pVDZ21pV@Z31pV>Z41pV<Z51pV6Z61pV2Z71pXLZ81pXFZ91pXDZ:1pXBZ;1pX@Z<1pV:Z=1pV8Z>1pVNZ?1pVLZ@1pVJZA1pVHZB1pVFZC1pVBZD1pU>ZE1pU<ZF1pU:ZG1pU8ZH1pU6ZI1pU4ZJ1pU2ZK1pU0ZL1pV4ZM1pX>ZN1pX<ZO1pX:[01pXJ[11pUB[21pW0[31")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 6%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 14%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 15%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 16%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 17%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 18%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 19%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 26%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 27%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 28%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 29%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 30%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 31%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 32%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 33%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 34%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 35%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 36%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 37%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 38%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 39%nat 0%nat).
Variable st0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 40%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 41%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 42%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_ram_carve2) 43%nat 0%nat).
Lemma ram_carve2 : ltac:(sec_stmt2 constr:(SEC_T_ram_carve2) 44%nat 0%nat).
Proof using Type sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo st0 st p r.
intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). pose_ceil.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
assert (PD : conc st p + 4096 <= 0xb0000 \/ 0xea000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
{ eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl rsegs mX) as WMp end.
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
{ eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
clear MUp WMp MRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
{ unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
- exact SAL.
- change (conc stC p) with (conc st p). exact HDR0.
- intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
- change (conc stC p) with (conc st p).
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
clear MRC3 HDR0 REST.
assert (MSq : meta_slot stD (aadd p AREA_HDR)).
{ exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
{ change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
rewrite CQ. change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 954552) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
[exact MRD | assumption | exact MSq | lia | | | pose_ceil; lia | lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
- cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
pose proof (lr_lo_ge r). lia. }
split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_ram_carve_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_C "Z4'SHyR0%211&>y5%2213yQ0%711'6y8%:11%311p0:1'4%114'<'QB&Q9'QG&R6v?r3r6%43321&Q0&R0r7%3221'9%E1;&SF';'SO&T2&SJ%34421A&T0%14643C&3r4%239I1&QLr5%211%>6=J9741(1%12LI%C3B31&:'QH&QE%11<(Q7%I3421%611&R:z&7%13KQ;Q4%4231&R9%43NQ>Q3+TP0%3221&QI&QF%11Q<%311%=251&Ar8%>3Q8QH1%311&C%114&QD%116r9%E3Q?QO1%C231%I261'Q:%R:11&SM&T3%24QFQDR61&SL&SK%26QIQGQFR941%QI4R8418%QF4R9529r:&QJr;%211%R16R>>6541(0%11@%R63@31'8r1%Q>2Q=1&R;&Q6%2241%6241'Q@%S311%R<4RKGD2%R94RLHE3&Q8r=&Q4&R<&Q5r2%3221%QI251%8271&QKr>%211%RL6S9@>=41%K1A%S03A21p0D1pUFS?1&QC&Q<&Q?%11:%311%RG2SCQ0%S93621&SEr?%Q<11%S;6SHQHQ@Q?F1%42QI1p061pXHSK1+1&Q;%11=%RI231&R=+2+R0%3221%Q?261%QC261&Q=%G1A%211%S32S21%QE227%QI221&OrC&Q>r@%221J&EuTP0%211%84T<741&Q1rDrA%:219%44TA31S<&Q3rE&SIrQI%22U>1-R0%SE221&R2rHrIrJrKrLrM%78U5B654321%?4U1>91&LrFrQJ%A2UM1%T321?%54U74I1&Q2%11U>%T<21G&R>rQL%I2V51%321QD%TA2<1&J&R3rQ1rQMrQKrQ0rOrNrQ=rQ<rQ;rQ:rQ9rQ8rQ7rG&B%12NQ>&@%S>2Q@S<+S4%33421&SG%R12Q4QD+H%U6221%42W21%JHV@IHOGFEDQ<Q=CBA@?>=Q>Q?<:Q@61&N&KrQ2%QK2W7L%U=21QI%;2W91rQHrQG%>2W<=rQFrQErQDrQCrQBrQArQ@rQ?&R5%H2WF1&R4%J2WH1rQ>rQ6rQ5rQ4rQ3%IOHEQJQBR2RADCBA@?>=<;:865Q>Q=Q<Q;Q:Q9Q84321+caeH%Q22X01%U21X0&R8%11W;%Q076R?4R@3RA1%QM3W=Q21p0QO1p0R51p0R91p0R@1p0S11p0S71p0SA1p0SH1p0T31p0TB1p0U?1p0V21p0V;1p0V@1p0VJ1p0W01p0W81p0WM1p0X21pV0X81pUNX:1pW2X<1pUHX>1pUDX@1pUJXC1pU@XI1pLXL1pVDY01pV@Y11pV>Y21pV<Y31pV6Y41pV2Y51pXLY61pXFY71pXDY81pXBY91pX@Y:1pV:Y;1pV8Y<1pVNY=1pVLY>1pVJY?1pVHY@1pVFYA1pVBYB1pU>YC1pU<YD1pU:YE1pU8YF1pU6YG1pU4YH1pU2YI1pU0YJ1pV4YK1pX>YL1pX<YM1pX:YN1pXJYO1pUBZ01pW0Z11")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 6%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 14%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 15%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 16%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 17%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 18%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 19%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 20%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 21%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 22%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 23%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 24%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 25%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 26%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 27%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 28%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 29%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 30%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 31%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 32%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 33%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 34%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 35%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 36%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 37%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 38%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 39%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 40%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_ram_carve_walk) 41%nat 0%nat).
Lemma ram_carve_walk : ltac:(sec_stmt2 constr:(SEC_T_ram_carve_walk) 42%nat 0%nat).
Proof using Type sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m junk lo st p r.
intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). pose_ceil.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.
assert (HDR0 : rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
{ rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
assert (REST : rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
{ eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
clear ZB ZW.
(pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
assert (PD : conc st p + 4096 <= 0xb0000 \/ 0xea000 <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RF DR1 DR23 DR2 RU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
pose proof (wmono_refl rsegs m) as WM0. unfold RCTX in MU0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1. st1. st1. st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
lazymatch goal with H : rw_cells rsegs ?mX 954560 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.
st1.
destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
-
destruct (TL tl eq_refl) as [ar Har].
destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). pose_ceil.
pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
assert (TD : conc st tl + 4096 <= 0xb0000 \/ 0xea000 <= conc st tl) by lia.
assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
{ destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
- rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
- destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
unfold pw. cbn [oconc]. unfold wz.
assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF. clear CF.
pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
change (conc st1 tl) with (conc st tl) in ARh.
apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl rsegs mX) as WMa end.
st1. st1.
set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
clear MUa WMa ARh MR1.
rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 954552) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
- pose_ceil; lia.
- lia. }
intros ms' RP. exact RP.
-
unfold pw. cbn [oconc]. unfold wz.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1.
set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
lazymatch goal with H : rw_cells rsegs ?mX 954560 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc MR1.
rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 954144) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 954552) with (Z_to_bv 64 RMLOCK).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact WM0 | idtac].
- lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
- lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
- pose_ceil; lia.
- lia. }
intros ms' RP. exact RP.
Qed.
End SE.
End CEIL_WRAP_1.
