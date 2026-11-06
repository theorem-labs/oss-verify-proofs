(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10, for omx-clap-core/fuzz_state's ASan build (image A, fuzz_state.asan sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0): fs's instance of the ONE strcmp text.
   1. fs_strcmp_U: AStrcmpDefU.astrcmp_realizesU (Reusable/AStrcmpDefU.v:27, a Theorem Labs lane's registry text) at FSH_Base.PC_strcmp
      = 0x4265c (__wrap_strcmp, `j 0x42c10` into ___interceptor_strcmp), from the walk relocated from libreac/fuzz_grant
      (Strcmp.v, StrcmpLoop.v, StrcmpChkX.v, StrcmpChkY.v, StrcmpTbl.v; unchanged). The walk's phase lemmas take AR over
      the memory of the config they run, which is false at U <> [] (FSupoison.block_granule0: shadow 0 on a live block's
      user granule; upoisoned: 0xf7), so the phases are restated over FSupoison.ARU: StrcmpU_X.scx_check_srr,
      StrcmpU_Y.scy_check_srr (the ChkX / ChkY Section-f glue with HAR -> ARU), and here sc_tailU and strcmp_srrU
      (Strcmp.v's sc_tail and strcmp_srr with the same change: the entry's rodata cells and AR frame read on unpoison U
      mem, the stack window [sp - 2264, sp) above kHighMemBeg and so off U's shadow bytes; the strings, the loop, the
      range checks and the frame/presence posts stay on mem, as the U text states). a Theorem Labs lane 2026-10-29T09:53Z: fs-local
      copies, no upstream change.
   2. fs_strcmp_contract: fs's own contract (FSH_Gen.v:426-432 astrcmp_realizesU) derived from (1) with k = the first
      index where l1 ++ [0] and l2 ++ [0] differ or l1's byte is NUL, and one EXPLICIT extra premise
      `Z.of_nat (length l1) + 1 < 2 ^ 32`: the U text asks k + 1 < 2 ^ 32 (AStrcmpDefU.v:32), and at l1 = l2 of length
      2 ^ 32 - 1 str_meet forces k = 2 ^ 32 - 1.
   3. fs_strcmp_realizesU: FSH_Gen.astrcmp_realizesU at FSH_Base.PC_strcmp exactly. cstr_ok's fourth conjunct is
      `Z.of_nat (length l) + 1 < 2 ^ 32` (FSH_Gen.v:302; a Theorem Labs lane 2026-10-29T09:53Z, a working branch 40390baa3df),
      which is (2)'s extra premise for l1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 AStrcmpDef.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Rt Require Import StrcmpTbl StrcmpLoop Strcmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Rt Require StrcmpChkX StrcmpChkY StrcmpU_X StrcmpU_Y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require UPoison AStrcmpDefU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSuwalk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Gen FSH_Base ACem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16 YK06.
Import ListNotations.
(* SINK GUARD (FSH_Gen.v:50-52): a SUCCESS here means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* Phase 5 over ARU: Strcmp.sc_tail with ecall_preU (its AR only gives the layout) and ARU at the tail's memory memR. *)
Lemma sc_tailU : forall B, AR_laws tfibsegs B ->
forall ly S (U : list (Z * Z)) (W : world tfibsegs) regs mem md (regsR : bvmap 5 word) (memR : word -> option byte) mdR c1 c2,
UPoison.ecall_preU tfibsegs B ly S U W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
0 <= c1 < 256 -> 0 <= c2 < 256 ->
FSP.ARU tfibsegs B ly S U W memR mdR -> same_but_materialized md mdR ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) memR a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memR a) ->
getr regsR 25 = w64 c1 -> getr regsR 26 = w64 c2 ->
getr regsR 2 = w64 (spZ regs - SC_FRAME) -> getr regsR 3 = getr regs 3 -> getr regsR 4 = getr regs 4 ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 104) 8 (bv_unsigned (getr regs 27)) ->
SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 SC_TAIL) memR (seg_rom tfibsegs)) mdR)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
UPoison.ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (strcmp_res c1 c2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS ly S U W regs mem md regsR memR mdR c1 c2 HPRE Hslo2 Hc1 Hc2 HARR HsbmR AVR PMR G25 G26 G2 G3 G4
V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12.
pose proof HPRE as ((HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & _ & _).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK, SC_SCR, SC_FRAME in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
set (E4 := Ereg regsR [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2192).
{ subst E4. rewrite (ew_Ereg_nat regsR _ 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regsR (Z_to_bv 64 SC_TAIL) memR (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regsR [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, SC_FRAME. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2192) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (rq : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rq -> Z.of_nat j < 13 ->
val_mem tfibsegs (mrestrict H memR) (sp0 - 2192 + off) 8 (bv_unsigned (getr regs rq)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H memR) (sp0 - 2192) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j rq off Hnth Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2192) off 8 _ (bv_unsigned (getr regs rq))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regsR _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs rq)). zside.
- zside.
- exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv 2184); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2184) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv 2176); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2176) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv 2168); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2168) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv 2160); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2160) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv 2152); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2152) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv 2144); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2144) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv 2136); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2136) with (sp0 - 56) by lia; exact V6].
+ apply (CK 7%nat 22%bv 2128); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2128) with (sp0 - 64) by lia; exact V7].
+ apply (CK 8%nat 23%bv 2120); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2120) with (sp0 - 72) by lia; exact V8].
+ apply (CK 9%nat 24%bv 2112); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2112) with (sp0 - 80) by lia; exact V9].
+ apply (CK 10%nat 25%bv 2104); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2104) with (sp0 - 88) by lia; exact V10].
+ apply (CK 11%nat 26%bv 2096); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2096) with (sp0 - 96) by lia; exact V11].
+ apply (CK 12%nat 27%bv 2088); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2088) with (sp0 - 104) by lia; exact V12].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2192) with (spZ regs + (-137) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply SRr_bind; [apply (sc_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 cf4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_sc tbl_sc_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = memR z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23.
rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (Q10 : getr (ms_regs ms4) 10 = sv_denot E4 RES) by (rewrite (st_ok_reg_denot H E4 epi_e ms4 10%bv HS4), res_reg; reflexivity).
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regsR _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regsR rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regsR _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regsR _ 0)). rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy mdR) mat' mdR).
pose proof (same_but_materialized_frame mdR _ (with_vm_backing_same mdR mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H memR a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split]]]].
+ (* the tail writes nothing: ARU of memR carries over to the returned memory and model *)
assert (MEQ4U : forall z, FSP.unpoison U (ms_mem ms4) z = FSP.unpoison U memR z) by (intros z; apply unp_same; apply MEQ4).
assert (AV4U : forall a, aview tfibsegs H (FSP.unpoison U (ms_mem ms4)) a = aview tfibsegs H (FSP.unpoison U memR) a)
by (intros a; apply aview_same; apply MEQ4U).
change (FSP.ARU tfibsegs B ly S U W (ms_mem ms4) (with_vm_backing (m_vm_lazy mdR) mat' mdR)).
apply (ARU_intro tfibsegs B ly S S U W memR (ms_mem ms4) mdR _ HARR eq_refl); [intros s _; apply AV4|].
apply (al_frame _ _ LAWS ly S W (FSP.unpoison U memR) mdR (FSP.unpoison U (ms_mem ms4)) _ (FSP.ARU_AR tfibsegs B ly S U W memR mdR HARR)).
* intros a Hr Hown. apply AV4U.
* intros a Hv. rewrite AV4U. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ4U).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl). exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl). exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 7%nat 22%bv eq_refl).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 8%nat 23%bv eq_refl).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24. exact (X 9%nat 24%bv eq_refl).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25. exact (X 10%nat 25%bv eq_refl).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26. exact (X 11%nat 26%bv eq_refl).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27. exact (X 12%nat 27%bv eq_refl).
+ eapply same_but_materialized_trans; [exact HsbmR | apply with_vm_backing_same].
+ rewrite Q10. apply res_ok; [rewrite (Y 25%nat 25%bv eq_refl); exact G25 | rewrite (Y 26%nat 26%bv eq_refl); exact G26 | exact Hc1 | exact Hc2].
+ intros a Hr Hs. rewrite AV4. apply AVR; [exact Hr | unfold sp0 in *; lia].
+ intros a Hp. apply (apresent_same H memR (ms_mem ms4) a (MEQ4 _)). apply PMR. exact Hp.
Qed.
(* The walk over ARU: Strcmp.strcmp_srr with the phases of StrcmpU_X / StrcmpU_Y and sc_tailU. *)
Lemma strcmp_srrU : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall pc0, RUNTOL (ssA pc0) = (eA, RS_running) -> AStrcmpDefU.astrcmp_realizesU tfibsegs B pc0.
Proof.
intros B LAWS TB pc0 RA. unfold AStrcmpDefU.astrcmp_realizesU.
intros ly S U W regs mem md x y k c1 c2 HPRE Hslo2 Hpres2 G10 G11 Hx Hy Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby
Hamx Hamy Hrax Hhx Hray Hhy.
(* the donor invariant on unpoison U mem (FSupoison's reading of the U text's ecall_preU); the strings, the stack window
   and the walk stay on mem *)
assert (HARU : FSP.ARU tfibsegs B ly S U W mem md) by (destruct HPRE as (HE & HOK & HPO); exact (conj (proj1 HE) (conj HOK HPO))).
pose proof (FSP.ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HPRE as ((_ & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & _ & _). unfold ESTACK in Hslo, HpresE, Hbx, Hby, Hpres2.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof AF0x.Hwx_tfa as Hwx.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (unfold ESTACK in Hslo2; lia).
assert (Hsl2 : ly_stk_lo ly + 8192 <= sp0) by (unfold ESTACK in Hslo2; exact Hslo2).
destruct Hmeet as (Hk0 & Hbef & Hc1v & Hc2v & Hstop).
assert (Hamr : x + (k + 1) <= 2 ^ 47 - 1 /\ y + (k + 1) <= 2 ^ 47 - 1)
by (pose proof Hamx as X1; pose proof Hamy as Y1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1, Y1; lia).
destruct (aview_byte_ex H mem (x + k) c1 Hc1v) as (bc1 & _ & _ & Rc1).
destruct (aview_byte_ex H mem (y + k) c2 Hc2v) as (bc2 & _ & _ & Rc2).
assert (VT : forall (m m' : word -> option byte) a v, val_mem tfibsegs (mrestrict H m) a 8 v ->
(forall b, a <= b < a + 8 -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a 8 v).
{ intros m m' a v Hv Hf. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
(* phase 1: entry *)
unfold cfg_at. change (w64 pc0) with (Z_to_bv 64 pc0).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (HS0 : st_ok tfibsegs EE (ssA pc0) (restrict H (mkst regs (Z_to_bv 64 pc0) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (region_ok_unp tfibsegs B ly S U W mem md H EE (map ro_region icpt_rodata) HARU ltac:(vm_compute; reflexivity)
(rodata_ok B TB icpt_rodata ly S H (FSP.unpoison U mem) EE (icpt_rodata_chk ly) (proj1 HAR)))].
unfold stkA, SC_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2208)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Hpres2. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, icpt_rodata, ro_region, extent_of_region, SC_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; first [exact Hal16 | lia]. }
eapply SRr_bind; [apply (sc_phase_to W EE SL_HEAD _ _ _ _ _ HS0 RA)|].
cbv beta. intros W1 cf1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2208 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SC_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold SC_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R2].
apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j v off, nth_error SAVEDA j = Some (v, off) -> forall z, sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros j v off Hj z Hz Hrg. rewrite forallb_forall in HSV. specialize (HSV (v, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 v _ Hck Hz); zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q18 : getr regs1 18 = w64 x) by (rewrite (RD 18%bv (SOff 10 0) R18); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q9 : getr regs1 9 = w64 y) by (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q20 : getr regs1 20 = w64 0) by (rewrite (RD 20%bv (SLit 0) R20); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2192)) by (rewrite (RD 2%bv (SOff 2 (- SC_FRAME)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 2192) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2208 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold SC_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2208)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
(* ARU after the entry: AR moves on unpoison U (the entry writes only [sp0 - 2208, sp0), above kHighMemBeg, off U's
   shadow bytes), and U's shadow bytes keep 0xf7 *)
assert (AV1U : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0) ->
aview tfibsegs H (FSP.unpoison U (ms_mem ms1)) a = aview tfibsegs H (FSP.unpoison U mem) a).
{ intros a Hr Ha. apply aview_same. apply unp_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (MEQ1U : forall z : word, ~ (sp0 - 2208 <= bv_unsigned z < sp0) -> FSP.unpoison U (ms_mem ms1) z = FSP.unpoison U mem z).
{ intros z Hz. apply unp_same. apply MEQ1. exact Hz. }
assert (HAR1 : FSP.ARU tfibsegs B ly S U W (ms_mem ms1) md1).
{ apply (ARU_intro tfibsegs B ly S S U W mem (ms_mem ms1) md md1 HARU eq_refl).
- intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S U W mem md s HARU Hs) as (_ & Hs1 & Hs2). unfold kHighMemBeg in Hs2.
apply AV1; [exact (FSP.ush_range tfibsegs B ly S U W mem md s HARU Hs) | unfold sp0 in *; lia].
- apply (al_frame _ _ LAWS ly S W (FSP.unpoison U mem) md (FSP.unpoison U (ms_mem ms1)) _ HAR).
+ intros a Hr Hown. apply AV1U; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W (FSP.unpoison U mem) md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (FSP.unpoison U (ms_mem ms1)) a). rewrite (AE2y.aview_mod _ (FSP.unpoison U mem) a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2208)) as [L1|L1]; [rewrite AV1U by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1U by lia; exact Hv].
apply aview_some_of_apresent. apply apresent_unp. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1U HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
(* phase 2: the byte loop *)
assert (AVS : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * 4096 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a)
by (intros a Hr Ha; apply AV1; [exact Hr | lia]).
assert (LB : forall j, 0 <= j < k -> exists b, 0 < b < 256 /\
rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (x + j)) 1 = Some [Z_to_bv 8 b] /\
rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (y + j)) 1 = Some [Z_to_bv 8 b]).
{ intros j Hj. destruct (Hbef j Hj) as (b & Bx & By & Bnz).
destruct (aview_byte_ex H mem (x + j) b Bx) as (bb & _ & _ & Rb).
exists b. split; [lia|]. split; apply aview_rdn1.
- rewrite AVS; [exact Bx | lia | apply Hbx; lia].
- rewrite AVS; [exact By | lia | apply Hby; lia]. }
assert (LX : rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (x + k)) 1 = Some [Z_to_bv 8 c1])
by (apply aview_rdn1; rewrite AVS; [exact Hc1v | lia | apply Hbx; lia]).
assert (LY : rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (y + k)) 1 = Some [Z_to_bv 8 c2])
by (apply aview_rdn1; rewrite AVS; [exact Hc2v | lia | apply Hby; lia]).
destruct (strcmp_loop (mrestrict H (ms_mem ms1)) (seg_rom tfibsegs) x y k c1 c2 ltac:(lia) ltac:(lia) Hxk Hyk LB Rc1 Rc2 LX LY Hstop Hk0
regs1 Q18 Q9 Q20) as (regs2 & Hms & L20 & L25 & L26 & LK).
assert (Hms' : msteps tfibsegs (restrict H ms1) (mkst regs2 (Z_to_bv 64 SL_EXIT) (mrestrict H (ms_mem ms1)) (seg_rom tfibsegs)))
by (rewrite Hshape at 1; rewrite restrict_mkst_fx; exact Hms).
eapply (SRr_msteps tfibsegs Hwx W ms1 _ md1 _ Hms').
intros model' Hsbm _. fold H. rewrite unrestrict_mkst_mrestrict.
assert (HAR2 : FSP.ARU tfibsegs B ly S U W (ms_mem ms1) model').
{ apply (ARU_intro tfibsegs B ly S S U W (ms_mem ms1) (ms_mem ms1) md1 model' HAR1 eq_refl); [intros s _; reflexivity|].
apply (al_frame _ _ LAWS ly S W (FSP.unpoison U (ms_mem ms1)) md1 (FSP.unpoison U (ms_mem ms1)) _ (FSP.ARU_AR tfibsegs B ly S U W (ms_mem ms1) md1 HAR1));
[intros a _ _; reflexivity | intros a Hv; exact Hv | | | | exact (AE2y.hs_kept_eq _ _ _ (fun z => eq_refl))];
apply (same_but_materialized_frame md1 _ Hsbm). }
assert (Hsp1 : spZ regs2 = sp0 - 2192) by (unfold spZ; rewrite (LK 2%bv) by discriminate; exact R1sp).
(* phase 3: the s1 range check *)
change (mkCfg (mkst regs2 (Z_to_bv 64 SL_EXIT) (ms_mem ms1) (seg_rom tfibsegs)) model')
with (cfg_at tfibsegs StrcmpChkX.RC_ENTRY regs2 (ms_mem ms1) model').
eapply SRr_bind.
{ apply (StrcmpU_X.scx_check_srr B LAWS TB ly S U W regs2 (ms_mem ms1) model' x (k + 1) HAR2).
- rewrite Hsp1. replace (sp0 - 2192) with (sp0 + (-137) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite Hsp1. unfold StrcmpChkX.RC_SCR. lia.
- rewrite Hsp1. lia.
- intros a Ha. rewrite Hsp1 in Ha. unfold StrcmpChkX.RC_SCR in Ha. apply PM1. apply Hpres2. lia.
- exact L20.
- rewrite (LK 18%bv) by discriminate. exact Q18.
- lia.
- lia.
- lia.
- exact Hamx.
- eapply range_addressable_agree; [|exact Hrax]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AV1; lia.
- intros s' Hs. rewrite AV1; [exact (Hhx s' Hs) | |];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (x + (k + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + (k + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + (k + 1) - 1)) 8 ltac:(lia)); lia. }
cbv beta. intros W2 cf2 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & (X20 & X21 & X22 & X24) & Hfr3 & Hpm3).
rewrite Hsp1 in Hfr3. unfold StrcmpChkX.RC_SCR in Hfr3.
assert (KK3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 20 -> z <> 21 -> z <> 22 -> z <> 24 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H4 H5. exact (K3 z H1 H2 H3 H4 H5). }
assert (Hsp3 : spZ regs3 = sp0 - 2192)
by (unfold spZ; rewrite (KK3 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Hsp1).
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2192 - 72 <= a < sp0 - 2192) -> aview tfibsegs H mem3 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Ha; exact (Hfr3 a Hr Ha)).
(* phase 4: the s2 range check *)
change (cfg_at tfibsegs StrcmpChkX.RC_END regs3 mem3 md3) with (cfg_at tfibsegs StrcmpChkY.RC_ENTRY regs3 mem3 md3).
eapply SRr_bind.
{ apply (StrcmpU_Y.scy_check_srr B LAWS TB ly S U W regs3 mem3 md3 y (k + 1) HAR3).
- rewrite Hsp3. replace (sp0 - 2192) with (sp0 + (-137) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite Hsp3. unfold StrcmpChkY.RC_SCR. lia.
- rewrite Hsp3. lia.
- intros a Ha. rewrite Hsp3 in Ha. unfold StrcmpChkY.RC_SCR in Ha. apply Hpm3. apply PM1. apply Hpres2. lia.
- exact X20.
- rewrite (KK3 9 9%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (LK 9%bv) by discriminate. exact Q9.
- exact X21.
- exact X24.
- lia.
- lia.
- lia.
- exact Hamy.
- eapply range_addressable_agree; [|exact Hray]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
rewrite AV3 by lia. apply AV1; lia.
- intros s' Hs. rewrite AV3, AV1; [exact (Hhy s' Hs) | | | |];
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (y + (k + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (y + (k + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + (k + 1) - 1)) 8 ltac:(lia)); lia. }
cbv beta. intros W3 cf3 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & K4 & Hsbm4 & (Y20 & Y24) & Hfr4 & Hpm4).
rewrite Hsp3 in Hfr4. unfold StrcmpChkY.RC_SCR in Hfr4.
assert (KK4 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 20 -> z <> 21 -> z <> 24 -> getr regs4 rr = getr regs3 rr).
{ intros z rr -> H1 H2 H3 H4. exact (K4 z H1 H2 H3 H4). }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2192 - 72 <= a < sp0 - 2192) -> aview tfibsegs H mem4 a = aview tfibsegs H mem3 a)
by (intros a Hr Ha; exact (Hfr4 a Hr Ha)).
assert (AVT : forall b, sp0 - 104 <= b < sp0 -> aview tfibsegs H mem4 b = aview tfibsegs H (ms_mem ms1) b)
by (intros b Hb; rewrite AV4, AV3 by lia; reflexivity).
assert (KS : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 10 -> z <> 20 -> z <> 21 -> z <> 22 -> z <> 24 -> z <> 25 -> z <> 26 ->
getr regs4 rr = getr regs1 rr).
{ intros z rr Hrr Hcs H10 H20 H21 H22 H24 H25 H26. rewrite (KK4 z rr Hrr Hcs H20 H21 H24), (KK3 z rr Hrr Hcs H20 H21 H22 H24). subst rr.
unfold acallee_saved in Hcs.
assert (Hz : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 23 \/ z = 27) by lia.
destruct Hz as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
apply LK; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E. }
(* phase 5: the tail *)
change (cfg_at tfibsegs StrcmpChkY.RC_END regs4 mem4 md4) with (mkCfg (mkst regs4 (Z_to_bv 64 SC_TAIL) mem4 (seg_rom tfibsegs)) md4).
apply (sc_tailU B LAWS ly S U W regs mem md regs4 mem4 md4 c1 c2 HPRE Hslo2 Rc1 Rc2 HAR4).
all: try change (spZ regs) with sp0.
- eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm|].
eapply same_but_materialized_trans; [exact Hsbm3 | exact Hsbm4].
- intros a Hr Ha. unfold SC_SCR in Ha. rewrite AV4, AV3; [apply AV1; [exact Hr | lia] | exact Hr | lia | exact Hr | lia].
- intros a Hp. apply Hpm4. apply Hpm3. apply PM1. exact Hp.
- rewrite (KK4 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia).
rewrite (KK3 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact L25.
- rewrite (KK4 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia).
rewrite (KK3 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact L26.
- rewrite (KS 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). unfold SC_FRAME. exact Q2.
- rewrite (KS 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q3.
- rewrite (KS 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q4.
- apply (VT (ms_mem ms1)); [exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 1))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 8))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 9))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 18))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 4%nat (SOff 19 0) (-40) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 19))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 5%nat (SOff 20 0) (-48) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 20))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 6%nat (SOff 21 0) (-56) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 21))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 7%nat (SOff 22 0) (-64) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 22))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 8%nat (SOff 23 0) (-72) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 23))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 9%nat (SOff 24 0) (-80) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 24))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 10%nat (SOff 25 0) (-88) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 25))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 11%nat (SOff 26 0) (-96) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 26))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 12%nat (SOff 27 0) (-104) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 27))) | intros b Hb; apply AVT; lia].
Qed.
(* (1) fs's instance of the ONE strcmp text, at the trampoline FSH_Base.PC_strcmp = STRCMP_TRAMP = 0x4265c. *)
Theorem fs_strcmp_U : forall B, AR_laws tfibsegs B -> TfibSyms B -> AStrcmpDefU.astrcmp_realizesU tfibsegs B FSH_Base.PC_strcmp.
Proof. intros B LAWS TB. exact (strcmp_srrU B LAWS TB STRCMP_TRAMP r_A_tramp). Qed.
(* ---- (2) fs's own contract from (1) ---- *)
Lemma least_nat : forall (P : nat -> Prop), (forall n, P n \/ ~ P n) ->
  forall N, P N -> exists k, P k /\ (k <= N)%nat /\ (forall i, (i < k)%nat -> ~ P i).
Proof.
intros P D.
assert (G : forall n, (exists k, (k <= n)%nat /\ P k /\ forall i, (i < k)%nat -> ~ P i) \/ (forall i, (i <= n)%nat -> ~ P i)).
{ induction n as [|n IH].
  - destruct (D 0%nat) as [H0|H0].
    + left. exists 0%nat. split; [lia|]. split; [exact H0|]. intros i Hi. lia.
    + right. intros i Hi. replace i with 0%nat by lia. exact H0.
  - destruct IH as [(k & Hk & Pk & Mk)|Hn].
    + left. exists k. split; [lia|]. split; [exact Pk | exact Mk].
    + destruct (D (S n)) as [HS|HS].
      * left. exists (S n). split; [lia|]. split; [exact HS|]. intros i Hi. apply Hn. lia.
      * right. intros i Hi. destruct (Nat.eq_dec i (S n)) as [->|Hne]; [exact HS|]. apply Hn. lia. }
intros N HN. destruct (G N) as [(k & Hk & Pk & Mk)|Hn].
- exists k. split; [exact Pk|]. split; [exact Hk | exact Mk].
- exfalso. exact (Hn N (le_n N) HN).
Qed.
Lemma w64_mod : forall z, w64 (z mod 2 ^ 64) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma strcmp_res_zero : forall c1 c2, strcmp_res c1 c2 mod 2 ^ 64 = 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold strcmp_res. destruct (Z.eqb_spec c1 c2) as [e|ne]; [split; [intros _; exact e | intros _; reflexivity]|].
assert (M1 : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by reflexivity. assert (P1 : 1 mod 2 ^ 64 = 1) by reflexivity.
destruct (c1 <? c2); [rewrite M1 | rewrite P1]; split; intros C; first [lia | exfalso; exact (ne C)].
Qed.
(* A string pair meeting FSH_Gen's premises meets the U text's at k = the first index where l1 ++ [0] and l2 ++ [0]
   differ or l1's byte is NUL; the U text's CharCmpX result is 0 exactly when l1 = l2. *)
Lemma fs_strcmp_of_U : forall B pc, AStrcmpDefU.astrcmp_realizesU tfibsegs B pc ->
  forall ly S (U : list (Z * Z)) W regs mem md x y (l1 l2 : list Z),
  FSH_Gen.ecall_preU_k tfibsegs B FSH_Gen.STK_RT_STR ly S U W regs mem md -> rom_view tfibsegs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  FSH_Gen.cstr_ok tfibsegs W mem x l1 -> FSH_Gen.cstr_ok tfibsegs W mem y l2 ->
  Z.of_nat (length l1) + 1 < 2 ^ 32 ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
    (FSH_Gen.rt_post_roU tfibsegs B FSH_Gen.STK_RT_STR ly S U W regs mem md (fun v => v = 0 <-> FSH_Gen.str_eq l1 l2)).
Proof.
intros B pc HU ly S U W regs mem md x y l1 l2 (HPU & Hslo2 & Hpres2) _ G10 G11 C1 C2 Hl1.
unfold FSH_Gen.STK_RT_STR in Hslo2, Hpres2.
destruct C1 as ((GA1 & NZ1) & X4 & Xc & Xl & Xam & Xra & Xhu & _).
destruct C2 as ((GA2 & NZ2) & Y4 & Yc & Yl & Yam & Yra & Yhu & _).
pose proof HPU as ((HAR0 & _) & _ & _).
pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR0))) as SC. unfold ASAN_CEIL in SC.
pose proof (@alloc_ceiling_value _) as ACV. pose proof (@alloc_ceiling_lt _) as ACL.
try (rewrite YK06.alloc_ceiling_val in Xc). try (rewrite YK06.alloc_ceiling_val in Yc).
pose proof Hslo2 as Hsl. cbv [ESTACK] in Hsl.
(* the bytes *)
assert (AV1 : forall j, (j <= length l1)%nat -> aview tfibsegs (w_H W) mem (x + Z.of_nat j) = Some (nth j (l1 ++ [0]) 0)).
{ intros j Hj. destruct (GA1 j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
  exact (ACem.aview_of_val_mem1 tfibsegs (w_H W) mem _ _ Hv Hr). }
assert (AV2 : forall j, (j <= length l2)%nat -> aview tfibsegs (w_H W) mem (y + Z.of_nat j) = Some (nth j (l2 ++ [0]) 0)).
{ intros j Hj. destruct (GA2 j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
  exact (ACem.aview_of_val_mem1 tfibsegs (w_H W) mem _ _ Hv Hr). }
assert (NZ1' : forall j, (j < length l1)%nat -> nth j (l1 ++ [0]) 0 <> 0).
{ intros j Hj. rewrite app_nth1 by exact Hj. rewrite Forall_forall in NZ1. apply NZ1. apply nth_In. exact Hj. }
assert (NZ2' : forall j, (j < length l2)%nat -> nth j (l2 ++ [0]) 0 <> 0).
{ intros j Hj. rewrite app_nth1 by exact Hj. rewrite Forall_forall in NZ2. apply NZ2. apply nth_In. exact Hj. }
assert (E1 : nth (length l1) (l1 ++ [0]) 0 = 0) by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
assert (E2 : nth (length l2) (l2 ++ [0]) 0 = 0) by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
(* k: the first index where the bytes differ or l1's is NUL *)
set (P := fun i => nth i (l1 ++ [0]) 0 <> nth i (l2 ++ [0]) 0 \/ nth i (l1 ++ [0]) 0 = 0).
assert (DP : forall i, P i \/ ~ P i).
{ intros i. unfold P; cbv beta. destruct (Z.eq_dec (nth i (l1 ++ [0]) 0) (nth i (l2 ++ [0]) 0)) as [e|ne]; [|left; left; exact ne].
  destruct (Z.eq_dec (nth i (l1 ++ [0]) 0) 0) as [z|nz]; [left; right; exact z|].
  right. intros [C|C]; [exact (C e) | exact (nz C)]. }
destruct (least_nat P DP (length l1) (or_intror E1)) as (k0 & Pk & Hk1 & Mk).
assert (Hk2 : (k0 <= length l2)%nat).
{ destruct (Nat.le_gt_cases k0 (length l2)) as [L|L]; [exact L|]. exfalso. apply (Mk (length l2) L). unfold P; cbv beta.
  destruct (Z.eq_dec (nth (length l2) (l1 ++ [0]) 0) 0) as [z|nz]; [right; exact z | left; rewrite E2; exact nz]. }
assert (BEF : forall i, (i < k0)%nat -> nth i (l1 ++ [0]) 0 = nth i (l2 ++ [0]) 0 /\ nth i (l1 ++ [0]) 0 <> 0).
{ intros i Hi. pose proof (Mk i Hi) as NP. unfold P in NP; cbv beta in NP. split.
  - destruct (Z.eq_dec (nth i (l1 ++ [0]) 0) (nth i (l2 ++ [0]) 0)) as [e|ne]; [exact e | exfalso; apply NP; left; exact ne].
  - intros Z0. apply NP. right. exact Z0. }
unfold P in Pk; cbv beta in Pk.
(* the U text's premises at k = k0 *)
assert (Hmeet : str_meet tfibsegs W mem x y (Z.of_nat k0) (nth k0 (l1 ++ [0]) 0) (nth k0 (l2 ++ [0]) 0)).
{ split; [lia|]. split; [|split; [apply AV1; lia | split; [apply AV2; lia | exact Pk]]].
  intros i Hi. destruct (BEF (Z.to_nat i) ltac:(lia)) as [Be Bn].
  exists (nth (Z.to_nat i) (l1 ++ [0]) 0). split; [|split; [|exact Bn]].
  - replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply AV1. lia.
  - replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia. rewrite Be. apply AV2. lia. }
assert (STK1 : forall a, a < x + Z.of_nat (length l1) + 1 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; cbv [ESTACK]; lia).
assert (STK2 : forall a, a < y + Z.of_nat (length l2) + 1 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; cbv [ESTACK]; lia).
assert (Hsx : src_ok tfibsegs W regs mem x (Z.of_nat k0 + 1)).
{ intros a Ha. split.
  - replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite AV1 by lia. discriminate.
  - cbv [ESTACK]. lia. }
assert (Hsy : src_ok tfibsegs W regs mem y (Z.of_nat k0 + 1)).
{ intros a Ha. split.
  - replace a with (y + Z.of_nat (Z.to_nat (a - y))) by lia. rewrite AV2 by lia. discriminate.
  - cbv [ESTACK]. lia. }
assert (Hbx : forall a, x <= a <= x + Z.of_nat k0 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; apply STK1; lia).
assert (Hby : forall a, y <= a <= y + Z.of_nat k0 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; apply STK2; lia).
assert (Hamx : amem_range x (Z.of_nat k0 + 1)) by (unfold amem_range in Xam |- *; lia).
assert (Hamy : amem_range y (Z.of_nat k0 + 1)) by (unfold amem_range in Yam |- *; lia).
assert (Hrax : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat k0 + 1))
by (unfold range_addressable in Xra |- *; intros z Hz; apply Xra; lia).
assert (Hray : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat k0 + 1))
by (unfold range_addressable in Yra |- *; intros z Hz; apply Yra; lia).
assert (HUL : forall p n n', 1 <= n' <= n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) p n').
{ intros p n n' Hn Hh. unfold shadow_hull_vis in Hh |- *. intros s Hs. apply Hh. split; [lia|].
  assert (M : shadow_addr (p + n' - 1) / 8 * 8 <= shadow_addr (p + n - 1) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l.
    apply Z.div_le_mono; lia. }
  lia. }
assert (Hhx : shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat k0 + 1)) by (apply (HUL x (Z.of_nat (length l1) + 1)); [lia | exact Xhu]).
assert (Hhy : shadow_hull_vis (aview tfibsegs (w_H W) mem) y (Z.of_nat k0 + 1)) by (apply (HUL y (Z.of_nat (length l2) + 1)); [lia | exact Yhu]).
specialize (HU ly S U W regs mem md x y (Z.of_nat k0) (nth k0 (l1 ++ [0]) 0) (nth k0 (l2 ++ [0]) 0) HPU Hslo2 Hpres2 G10 G11
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hmeet Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
eapply SRr_mono; [exact HU|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU' & Hap & Hsbm & G10' & Hfr & Hpm).
destruct HARU' as (HAR' & _ & HPO').
split; [exact EW|].
exists regs', mem', md', (strcmp_res (nth k0 (l1 ++ [0]) 0) (nth k0 (l2 ++ [0]) 0) mod 2 ^ 64).
split; [exact Ec|]. split; [exact HAR'|]. split; [exact HPO'|]. split; [exact Hap|]. split; [exact Hsbm|].
split; [rewrite w64_mod; exact G10'|].
split; [apply Z.mod_pos_bound; lia|].
split; [|split; [exact Hfr | exact Hpm]].
unfold FSH_Gen.str_eq. split.
- intros H0. apply (proj1 (strcmp_res_zero _ _)) in H0.
  assert (Z1 : nth k0 (l1 ++ [0]) 0 = 0) by (destruct Pk as [C|C]; [exfalso; exact (C H0) | exact C]).
  assert (K1 : k0 = length l1).
  { destruct (Nat.eq_dec k0 (length l1)) as [e|ne]; [exact e|]. exfalso. exact (NZ1' k0 ltac:(lia) Z1). }
  assert (K2 : k0 = length l2).
  { destruct (Nat.eq_dec k0 (length l2)) as [e|ne]; [exact e|]. exfalso. apply (NZ2' k0 ltac:(lia)). rewrite <- H0. exact Z1. }
  apply (nth_ext l1 l2 0 0); [lia|].
  intros i Hi. destruct (BEF i ltac:(lia)) as [Be _]. rewrite !app_nth1 in Be by lia. exact Be.
- intros Eq. apply (proj2 (strcmp_res_zero _ _)). rewrite Eq. reflexivity.
Qed.
(* (2) fs's own contract, FSH_Gen.astrcmp_realizesU at FSH_Base.PC_strcmp, with the one explicit premise on l1's length
   (see the header); the rest of the statement is FSH_Gen.v:426-432 word for word. *)
Theorem fs_strcmp_contract : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall ly S (U : list (Z * Z)) W regs mem md x y (l1 l2 : list Z),
  FSH_Gen.ecall_preU_k tfibsegs B FSH_Gen.STK_RT_STR ly S U W regs mem md -> rom_view tfibsegs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  FSH_Gen.cstr_ok tfibsegs W mem x l1 -> FSH_Gen.cstr_ok tfibsegs W mem y l2 ->
  Z.of_nat (length l1) + 1 < 2 ^ 32 ->
  SRr tfibsegs W (cfg_at tfibsegs FSH_Base.PC_strcmp regs mem md)
    (FSH_Gen.rt_post_roU tfibsegs B FSH_Gen.STK_RT_STR ly S U W regs mem md (fun v => v = 0 <-> FSH_Gen.str_eq l1 l2)).
Proof. intros B LAWS TB. exact (fs_strcmp_of_U B FSH_Base.PC_strcmp (fs_strcmp_U B LAWS TB)). Qed.
(* (3) FSH_Gen.astrcmp_realizesU (FSH_Gen.v:426-432) exactly, at FSH_Base.PC_strcmp: since S0's cstr_ok carries
   `Z.of_nat (length l) + 1 < 2 ^ 32` as its fourth conjunct (a working branch 40390baa3df, a Theorem Labs lane 09:53Z),
   fs_strcmp_contract's extra premise is that conjunct of l1's cstr_ok. *)
Theorem fs_strcmp_realizesU : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  FSH_Gen.astrcmp_realizesU tfibsegs B FSH_Base.PC_strcmp.
Proof.
intros B LAWS TB. unfold FSH_Gen.astrcmp_realizesU.
intros ly S U W regs mem md x y l1 l2 Hpre Hrom G10 G11 Hc1 Hc2.
apply (fs_strcmp_contract B LAWS TB ly S U W regs mem md x y l1 l2 Hpre Hrom G10 G11 Hc1 Hc2).
destruct Hc1 as (_ & _ & _ & H32 & _). exact H32.
Qed.
End d.
