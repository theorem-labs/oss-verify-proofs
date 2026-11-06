(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: Sections g and h of A/AE6x.v (the memchr interceptor) on the path where REAL memchr finds no 0 byte among the first n, stated over Poison's ARU (any U) in place of AR; the prologue run is A/AE6x.v's with 1 <= n in place of 8 <= n, REAL memchr through FMsnprintfSnN3a.v, the range check through FMsnprintfSnN6y.v; theorem memchr0_icpt_realizesNU (FMsnprintfSnc.v amemchr0N_realizesU). *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE39 AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AE3a AE6y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AE6x.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfSnc FMsnprintfSnN3a FMsnprintfSnN6y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* AE6x's prologue entry state with the memchr length only bounded by 1 <= n < 2 ^ 31 (the found case has 8 <= n). *)
Definition factsAN : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 (2^47) 0); (12%nat, mkAF 1 (2^31 - 1) 0)].
Definition ssAN : sstate := mkSS MCH_ENTRY sr_atoms (stkA :: map ro_region mchr_rodata) None (mkFacts factsAN [] []).
Definition eAN : sstate := Eval vm_compute in fst (RUNTOR ssAN).
Lemma r_AN : RUNTOR ssAN = (eAN, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma shapeAN_ok : shapeA eAN = true. Proof. vm_compute. reflexivity. Qed.
(* s1 = x9 holds the byte count n when REAL memchr is called; the found path recomputes it from the result. *)
Lemma reg9_AN : reg_is eAN 9 (SOff 12 0) = true. Proof. vm_compute. reflexivity. Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma mchr_tailNU : forall ly S U (W : world tfibsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 x n,
ecall_preU tfibsegs B ly S U W regs mem md ->
1 <= n < 2 ^ 31 -> 0 < x -> x + n <= 2 ^ 63 ->
first_byte tfibsegs W mem x n 0 n ->
src_ok tfibsegs W regs mem x n -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x n ->
mconsts_view W mem ->
getr regs1 9 = w64 n ->
getr regs1 10 = w64 x -> getr regs1 11 = w64 0 -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MCH_RET -> getr regs1 2 = w64 (spZ regs - 2128) -> getr regs1 18 = w64 x -> getr regs1 20 = w64 1 ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 ->
getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MCH_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MCH_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MCH_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S U W regs mem md regs1 mem1 mat1 x n HPRE Hn Hx Hxk Hfb Hsrc Ham Hra Hhull Hrom
G9 G10 G11 G12 G1 G2 G18 G20 G3 G4 G22 G23 G24 G25 G26 G27 MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6.
pose proof (ecall_preU_parts B ly S U W regs mem md HPRE) as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK, MCH_WIN in *.
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
assert (Hamr : x + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfibsegs H mem1 a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (SRCW : forall a, x <= a < x + n -> ~ (sp0 - 2144 <= a < sp0)) by (intros a Ha; destruct (Hsrc a Ha) as [_ Hns]; unfold ESTACK in Hns; unfold sp0 in *; lia).
destruct Hfb as (Hkn & Hbef & Hlast).
destruct (bytes_of_str H mem1 x n ltac:(lia)) as (bs & LEN & NONUL & BS).
{ intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hb0). exists b. split; [|exact Hb0]. rewrite AV1; [exact Hb | lia | apply SRCW; lia]. }
assert (KLEN : Z.of_nat (length bs) = n) by lia.
destruct (tfib_memchrN bs (w64 x) (w64 n) (mrestrict H mem1) (seg_rom tfibsegs) regs1 NONUL) as (regs2 & Hms & A10 & KEEP).
- unfold w64. rewrite unsigned_lit_small by lia. exact KLEN.
- unfold w64. rewrite unsigned_lit_small by lia. lia.
- unfold w64. rewrite !unsigned_lit_small by lia. lia.
-
intros j Hj. unfold w64. rewrite unsigned_lit_small by lia.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
rewrite (BS j Hj). reflexivity.
-
intros a Ha.
assert (Hin : MC_LO <= a < MC_HI) by (unfold MC_LO, MC_HI; unfold tfib_D_const_HIGHS_0x8080808080808080, tfib_D_const_ONES_0x0101010101010100 in *; lia).
pose proof (Hrom a Hin) as Hv. fold H in Hv. rewrite <- (AV1 a) in Hv by (unfold tfib_D_const_HIGHS_0x8080808080808080, tfib_D_const_ONES_0x0101010101010100 in Ha; lia).
rewrite !rdn1_mbyte. unfold aview in Hv.
change (mbyte tfibsegs (fun _ : word => None) a) with (seg_rom tfibsegs (Z_to_bv 64 a)).
destruct (mbyte tfibsegs (mrestrict H mem1) a) as [b|], (seg_rom tfibsegs (Z_to_bv 64 a)) as [b'|]; cbn in Hv; try discriminate; [|reflexivity].
injection Hv as Hv. do 2 f_equal. apply bv_eq. exact Hv.
- exact G10.
- exact G11.
- exact G12.
-
rewrite G1 in Hms. replace (v_jalr (w64 MCH_RET) 0) with (Z_to_bv 64 MCH_RET : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_musl_memchr) with (Z_to_bv 64 MCH_REAL) in Hms.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb _ model' Hsbm). rewrite ?wvb_wvb.
cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H mem1 (mrestrict H mem1)).
assert (M2 : forall z, mem2 z = mem1 z) by (intros z; subst mem2; apply munrestrict_mrestrict_same).
assert (AV2 : forall a, aview tfibsegs H mem2 a = aview tfibsegs H mem1 a) by (intros a; apply aview_same; apply M2).
assert (KEEPr : forall r : bv 5, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs2 r = getr regs1 r) by (intros r; apply KEEP).
assert (R2sp : spZ regs2 = sp0 - 2128).
{ unfold spZ. rewrite KEEPr by (intros H'; discriminate H'). rewrite G2. unfold w64. apply unsigned_lit_small. lia. }
eapply SRr_bind.
{ apply (mchr_checkN_srrU B LAWS TB ly S U W regs2 mem2 (with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md) x n).
-
apply (ARU_frame _ _ LAWS ly S U W mem md mem2 _ HAR).
+ intros a Hr Hown. rewrite AV2. apply AV1; [exact Hr|]. intros Hs. exact (ARU_stack _ _ LAWS ly S U W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
rewrite AV2. destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(lia) ltac:(lia)) (AE2y.hs_kept_eq _ _ _ M2)).
- rewrite R2sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R2sp. unfold FMsnprintfSnN6y.RC_SCR. unfold sp0 in *. lia.
- rewrite R2sp. unfold sp0 in *. lia.
- intros a Ha. rewrite R2sp in Ha. unfold FMsnprintfSnN6y.RC_SCR in Ha.
apply (apresent_same H mem1 mem2 a (M2 _)).
destruct (Z_lt_le_dec a (sp0 - 2144)) as [L1|L1].
+ apply (apresent_same H mem mem1 a). { apply MEQ1. rewrite unsigned_lit_small by lia. lia. } apply HpresE. unfold sp0 in *. lia.
+ apply PRS1. lia.
- rewrite A10. reflexivity.
- rewrite KEEPr by (intros H'; discriminate H'). exact G9.
- rewrite KEEPr by (intros H'; discriminate H'). exact G18.
- rewrite KEEPr by (intros H'; discriminate H'). exact G20.
- lia.
- lia.
- lia.
- lia.
- exact Ham.
- eapply range_addressable_agree; [|exact Hra]. intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. rewrite AV2. apply AV1; unfold sp0 in *; lia.
- intros s Hs. rewrite AV2, AV1; [exact (Hhull s Hs) | |];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia));
unfold sp0 in *; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
rewrite R2sp in Hfr3. unfold FMsnprintfSnN6y.RC_SCR in Hfr3.
set (E4 := Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (K3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 18 -> z <> 20 -> z <> 21 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5 H6. exact (KEPT3 z H1 H2 H3 H5 H6). }
assert (R3sp : getr regs3 2 = w64 (sp0 - 2128)).
{ rewrite (K3 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ subst E4. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R3sp. unfold w64. apply unsigned_lit_small. lia. }
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2200 <= a < sp0 - 2128) -> mbyte tfibsegs (mrestrict H mem3) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. apply mbyte_of_aview. rewrite <- (AV2 a). apply Hfr3; [exact Hr | clear -Ha; lia]. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem3) a 8 v).
{ intros a v Hv Hlo Hhi. apply (AF0x.val_mem_ext (mrestrict H mem1)); [|exact Hv]. intros j Hj. apply MB3; lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs3 (w64 FMsnprintfSnN6y.RC_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2128) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem3) (sp0 - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs3 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VM; [exact Hv | lia | lia]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact V6].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
unfold cfg_at.
eapply SRr_bind; [apply (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21.
rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23. rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs3 _ 0)).
rewrite X32 in Q1.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs3 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs3 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs3 _ ii rr Hnth)).
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem3 a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split]]]].
+   apply (ARU_frame _ _ LAWS ly S U W mem3 md3 (ms_mem ms4) _ HAR3).
* intros a Hr Hown. apply AV4.
* intros a Hv. rewrite AV4. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ4).
+
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl), (K3 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl), (K3 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22, (Y 22%nat 22%bv eq_refl), (K3 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G22.
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23, (Y 23%nat 23%bv eq_refl), (K3 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G23.
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (Y 24%nat 24%bv eq_refl), (K3 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G24.
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl), (K3 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G25.
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl), (K3 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G26.
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl), (K3 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G27.
+ eapply same_but_materialized_trans; [exact Hsbm3 | apply with_vm_backing_same].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl), A10'. reflexivity.
+ intros a Hr Hs. rewrite AV4. rewrite Hfr3 by (unfold sp0 in *; lia). rewrite AV2. apply AV1; [exact Hr | unfold sp0 in *; lia].
+ intros a Hp. pose proof Hp as [Hh [b Hb]]. apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). apply Hpres3.
apply (apresent_same H mem1 mem2 a (M2 _)).
rewrite (AE2y.apresent_mod _ mem1 a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [apply (apresent_same H mem mem1 a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem mem1 a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp].
Qed.
End g.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x n : Z).
Hypothesis HPRE : ecall_preU tfibsegs B ly S U W regs mem md.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 0.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 1 <= n < 2 ^ 31.
Hypothesis Hx : 0 < x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis Hfb : first_byte tfibsegs W mem x n 0 n.
Hypothesis Hsrc : src_ok tfibsegs W regs mem x n.
Hypothesis Ham : amem_range x n.
Hypothesis Hra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis Hhull : shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Hypothesis Hrom : mconsts_view W mem.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Theorem memchr0_icpt_srrNU : SRr tfibsegs W (cfg_at tfibsegs MCH_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof (ecall_preU_parts B ly S U W regs mem md HPRE) as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
assert (Hamr : x + n <= 2 ^ 47 - 1) by (pose proof Ham as Ham'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'; lia).
unfold cfg_at. change (w64 MCH_ENTRY) with (Z_to_bv 64 MCH_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HS0 : st_ok tfibsegs EE ssAN (restrict H (mkst regs (Z_to_bv 64 MCH_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssAN. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_okU B TB mchr_rodata ly S U W mem md EE (mchr_rodata_chk ly) ltac:(vm_compute; reflexivity) HAR)].
unfold stkA, MCH_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2144)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply HpresE. subst sp0. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, mchr_rodata, icpt_rodata, ro_region, extent_of_region, MCH_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsAN]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia]. }
eapply SRr_bind; [apply (icpt_phase_to W EE MCH_REAL _ _ _ _ _ HS0 r_AN)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MCH_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MCH_WIN) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MCH_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeAN_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R18].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eAN) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eAN (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eAN ms1 r HS1). }
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is eAN (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hr. rewrite (RD r _ Hr). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. apply (RA r i Hi). rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK. rewrite <- Hi. exact HK. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eAN _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
apply (mchr_tailNU B LAWS TB ly S U W regs mem md (ms_regs ms1) (ms_mem ms1) mat1 x n HPRE Hn Hx Hxn Hfb Hsrc Ham Hra Hhull Hrom).
- rewrite (RD 9%bv (SOff 12 0) reg9_AN). cbn [sv_denot]. rewrite EE12, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. exact eq_refl.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G11.
- rewrite (RD 12%bv (SOff 12 0) R12). cbn [sv_denot]. rewrite EE12, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 1%bv (SLit MCH_RET) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 (-2128)) R2). cbn [sv_denot]. rewrite EE2. reflexivity.
- rewrite (RD 18%bv (SOff 10 0) R18). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 20%bv (SLit 1) R20). reflexivity.
- exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia)). - exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia)).
- exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)). - exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)). - exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
- exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)). - exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)). - exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)).
- exact MEQ1.
- intros a Ha. unfold MCH_WIN in Ha.
apply (st_ok_window_apresent H EE eAN ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold MCH_WIN. lia.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (CK 0%nat 1 (-8) eq_refl).
- replace (sp0 - 16) with (sp0 + -16) by lia. exact (CK 1%nat 8 (-16) eq_refl).
- replace (sp0 - 24) with (sp0 + -24) by lia. exact (CK 2%nat 9 (-24) eq_refl).
- replace (sp0 - 32) with (sp0 + -32) by lia. exact (CK 3%nat 18 (-32) eq_refl).
- replace (sp0 - 40) with (sp0 + -40) by lia. exact (CK 4%nat 19 (-40) eq_refl).
- replace (sp0 - 48) with (sp0 + -48) by lia. exact (CK 5%nat 20 (-48) eq_refl).
- replace (sp0 - 56) with (sp0 + -56) by lia. exact (CK 6%nat 21 (-56) eq_refl).
Qed.
End h.
Theorem memchr0_icpt_realizesNU : forall B, AR_laws tfibsegs B -> TfibSyms B -> amemchr0N_realizesU B 0x412ec.
Proof.
intros B LAWS TB ly S U W regs mem md x n HPRE G10 G11 G12 Hn Hx Hxn Hfb Hsrc Ham Hra Hhull Hrom.
exact (memchr0_icpt_srrNU B LAWS TB ly S U W regs mem md x n HPRE G10 G11 G12 Hn Hx Hxn Hfb Hsrc Ham Hra Hhull Hrom).
Qed.
Lemma amemchrNU_of_icpt : forall B, AR_laws tfibsegs B -> TfibSyms B -> amemchr0N_realizesU B (pc_wrap_memchr (as_code B)).
Proof. intros B LAWS TB. rewrite (ts_code B TB). exact (memchr0_icpt_realizesNU B LAWS TB). Qed.
End f.
