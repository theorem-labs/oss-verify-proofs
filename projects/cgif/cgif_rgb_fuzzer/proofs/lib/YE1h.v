(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE1n YE1q YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE0w YE1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition SNL_ENTRY {imgk : img} : Z := (0x420c8 + D_2c4).
Definition SNL_REAL {imgk : img} : Z := (0x9bd1c + D_10ec).
Definition SNL_RET {imgk : img} : Z := (0x42440 + D_2c4).
Definition SNL_END {imgk : img} : Z := (0x424b4 + D_2c4).
Definition SNL_FRAME : Z := 2144.
Definition SNL_WIN : Z := 2160.
Definition snlA_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [((0xa3fa8 + D_10f0), 8, [(0, 8%N, (0x9bd1c + D_10ec))])].
Lemma snlA_rodata_chk {imgk : img} : forall ly, rodata_chk ly snlA_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- SNL_WIN) 0 (- SNL_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 (2^47) 0); (11%nat, mkAF 8 (2^63 - 1) 0)].
Definition ssA {imgk : img} : sstate := mkSS SNL_ENTRY sr_atoms (stkA :: map ro_region snlA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_icpt FUEL SNL_REAL s.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssA)))).
Lemma r_A {imgk : img} : RUNTOR ssA = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition epi_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 2136 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 2128 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 2120 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 2112 (CVal 8 (SOff 35 0));
YQ0b.mkChunk 2104 (CVal 8 (SOff 36 0));
YQ0b.mkChunk 2096 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 2088 (CVal 8 (SOff 38 0));
YQ0b.mkChunk 2080 (CVal 8 (SOff 39 0))].
Definition ss_epi {imgk : img} : sstate := mkSS SNL_END sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 2144 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition chunk_is (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk {imgk : img} (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64)].
Definition KEPTA : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? SNL_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - SNL_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 1 (SLit SNL_RET) && reg_is ss 2 (SOff 2 (-2144)) &&
reg_is ss 8 (SOff 2 0) && reg_is ss 9 (SLit 1) && reg_is ss 18 (SOff 10 0) && reg_is ss 19 (SOff 11 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound {imgk : img} : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.

Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); img_refl. Qed.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Hypothesis TL : TfxSyms B.
Lemma amemchr_of_icpt : amemchr0_realizesM B (pc_wrap_memchr (as_code B)).
Proof. rewrite (ts_code B TB). img_exact (memchr0_icpt_contractM B LAWS TB). Qed.
Lemma snl_tail : forall ly S (W : world tfxsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 x n k,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n < 2 ^ 63 -> 0 < x -> 0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfxsegs W mem x n 0 k ->
src_ok tfxsegs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
getr regs1 10 = w64 x -> getr regs1 11 = w64 n ->
getr regs1 1 = w64 SNL_RET -> getr regs1 2 = w64 (spZ regs - 2144) -> getr regs1 8 = w64 (spZ regs) -> getr regs1 9 = w64 1 ->
getr regs1 18 = w64 x -> getr regs1 19 = w64 n ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 20 = getr regs 20 -> getr regs1 21 = getr regs 21 -> getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 ->
getr regs1 24 = getr regs 24 -> getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - SNL_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - SNL_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
SRr tfxsegs W (mkCfg (mkst regs1 (Z_to_bv 64 SNL_REAL) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 x n k HPRE Hslo2 Hpres2 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hsband Ham Hra Hhull Htail Hrom
G10 G11 G1 G2 G8 G9 G18 G19 G3 G4 G20 G21 G22 G23 G24 G25 G26 G27 MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6 V7.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx. unfold ESTACK, SNL_WIN in *.
assert (HSTK : STRNLEN_STK = 4128) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by img_lia.
set (H := w_H W) in *.
assert (Hamr : x + k + 1 <= 2 ^ 47 - 1) by (img_try (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; img_lia)).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2160 <= a < sp0) -> aview tfxsegs H mem1 a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PR1 : forall a, sp0 - 8192 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2160)) as [L1|L1]; [|img_try (img_apply PRS1; img_lia)].
img_apply (apresent_same H mem mem1 a). { img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_lia. } img_apply Hpres2. img_lia. }
assert (R1sp : spZ regs1 = sp0 - 2144) by (img_try (unfold spZ; rewrite G2; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (R1ra : raZ regs1 = SNL_RET) by (img_try (unfold raZ; rewrite G1; unfold w64; img_apply unsigned_lit_small; unfold SNL_RET; img_lia)).
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (MF1 : same_but_materialized md md1) by (img_try ((subst md1; cbv beta); img_apply with_vm_backing_same)).
assert (HAR1 : AR tfxsegs B ly S W mem1 md1).
{ img_apply (al_frame _ _ LAWS ly S W mem md mem1 _ HAR).
+ intros a Hr Hown. img_apply AV1; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ mem1 a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2160)) as [L1|L1]; [img_try (rewrite AV1 by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV1 by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRS1. img_lia.
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 Hpres2 ltac:(img_lia) ltac:(img_lia)). }
assert (HPRE1 : ecall_pre tfxsegs B ly S W regs1 mem1 md1).
{ split; [img_try (img_exact HAR1)|]. split; [img_try (rewrite G1; img_apply (ret_ok_lit SNL_RET); [unfold SNL_RET; img_lia | img_refl])|].
split; [img_try (rewrite R1sp; replace (sp0 - 2144) with (sp0 + (-134) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16)|].
split; [img_try (rewrite R1sp; unfold ESTACK; unfold sp0 in *; img_lia)|]. split; [img_try (rewrite R1sp; unfold sp0 in *; img_lia)|].
split; [img_try (intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; img_apply PR1; img_lia)|].
split; [img_try (rewrite G3; img_exact Hgp) | img_try (rewrite G4; img_exact Htp)]. }
img_change (mkCfg (mkst regs1 (Z_to_bv 64 SNL_REAL) mem1 (seg_rom tfxsegs)) md1) with (cfg_at tfxsegs tfx_A_musl_strnlen regs1 mem1 md1).
eapply SRr_bind.
{ img_apply (tfx_strnlen_at B TL LAWS amemchr_of_icpt ly S W regs1 mem1 md1 x n k HPRE1).
- rewrite R1sp, HSTK. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R1sp, HSTK in Ha. img_apply PR1. img_lia.
- img_exact G10.
- img_exact G11.
- img_exact Hn.
- img_exact Hx.
- img_exact Hk0.
- img_exact Hk8.
- img_exact Hk32.
- unfold kHighMemEnd. img_lia.
-
destruct Hfb as (Hkn & Hbef & Hlast). split; [img_try (img_exact Hkn)|]. split.
+ intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hb0). exists b. split; [|img_try (img_exact Hb0)]. fold H. rewrite AV1; [img_try (img_exact Hb) | img_lia | img_try (pose proof (Hsband (x + i) ltac:(img_lia)); unfold sp0 in *; img_lia)].
+ intros Hlt. fold H. rewrite AV1; [img_try (img_exact (Hlast Hlt)) | img_lia | img_try (pose proof (Hsband (x + k) ltac:(img_lia)); unfold sp0 in *; img_lia)].
- intros a Ha. rewrite R1sp, HSTK. split.
+ fold H. rewrite AV1; [img_try (img_exact (proj1 (Hsrc a Ha))) | img_lia | img_try (pose proof (Hsband a ltac:(img_lia)); unfold sp0 in *; img_lia)].
+ pose proof (Hsband a ltac:(img_lia)). unfold sp0 in *. img_lia.
- img_exact Ham.
- eapply range_addressable_agree; [|img_try (img_exact Hra)]. intros y Hy. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (shadow_addr_bounds y ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. fold H. img_apply AV1; unfold sp0 in *; img_lia.
- intros s Hs. fold H. rewrite AV1; [img_try (img_exact (Hhull s Hs)) | |];
pose proof (shadow_addr_bounds x ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (x + (k + 1) - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia));
unfold sp0 in *; img_lia.
- intros a Ha. fold H. rewrite AV1; [img_try (img_exact (Htail a Ha)) | img_try (pose proof (Z.mod_pos_bound (x + k) 8 ltac:(img_lia)); img_lia) |].
pose proof (Z.mod_pos_bound (x + k) 8 ltac:(img_lia)). pose proof (proj2 (Hsrc (x + k) ltac:(img_lia))) as Hnk. unfold ESTACK in Hnk. unfold sp0 in *. img_lia.
- intros a Hin. pose proof mc_bounds as [MB1 MB2]. fold H. rewrite AV1; [img_try (img_exact (Hrom a Hin)) | img_lia | img_lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & AP2 & Hsbm2 & A10 & Hfr2 & Hpres2').
rewrite R1ra. rewrite R1sp, HSTK in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr).
{ intros rr z -> Hcs. img_exact (AP2 z Hcs). }
assert (R2sp : spZ regs2 = sp0 - 2144).
{ unfold spZ. rewrite (K2 2%bv 2 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact R1sp. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 - 4128 <= a < sp0 - 2144) -> aview tfxsegs H mem2 a = aview tfxsegs H mem1 a).
{ intros a Hr Ha. img_exact (Hfr2 a Hr Ha). }
unfold cfg_at. eapply SRr_bind.
{ eapply (snl_check_srr B LAWS TB ly S W regs2 mem2 md2 x (k + 1) HAR2).
- rewrite R2sp. replace (sp0 - 2144) with (sp0 + (-134) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- rewrite R2sp. unfold YE1i.RC_SCR. unfold sp0 in *. img_lia.
- rewrite R2sp. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R2sp in Ha. unfold YE1i.RC_SCR in Ha. img_apply Hpres2'. img_apply PR1. img_lia.
-   rewrite A10. unfold w64. f_equal; img_lia.
- rewrite (K2 18%bv 18 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G18.
- rewrite (K2 9%bv 9 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G9.
- rewrite (K2 19%bv 19 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G19.
- img_lia.
- img_lia.
- img_lia.
- img_lia.
- img_lia.
- img_exact Ham.
- eapply range_addressable_agree; [|img_try (img_exact Hra)]. intros y Hy. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (shadow_addr_bounds y ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. rewrite AV2 by (img_try (unfold sp0 in *; img_lia)). img_apply AV1; unfold sp0 in *; img_lia.
- intros s Hs. rewrite AV2, AV1; [img_try (img_exact (Hhull s Hs)) | | | |];
pose proof (shadow_addr_bounds x ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (x + (k + 1) - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia));
unfold sp0 in *; img_lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
rewrite R2sp in Hfr3. unfold YE1i.RC_SCR in Hfr3.
set (E4 := Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22]).
assert (K3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 18 -> z <> 20 -> z <> 21 -> z <> 22 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5 H6 H7. img_exact (KEPT3 z H1 H2 H3 H5 H6 H7). }
assert (R3sp : getr regs3 2 = w64 (sp0 - 2144)).
{ rewrite (K3 2 2%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 2%bv 2 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2144).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R3sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> sp0 - 64 <= a < sp0 -> mbyte tfxsegs (mrestrict H mem3) a = mbyte tfxsegs (mrestrict H mem1) a).
{ intros a Hr Ha. img_apply mbyte_of_aview. rewrite <- (AV2 a) by img_lia. img_apply Hfr3; [img_try (img_exact Hr) | img_lia]. }
assert (VM : forall a v, val_mem tfxsegs (mrestrict H mem1) a 8 v -> sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfxsegs (mrestrict H mem3) a 8 v).
{ intros a v Hv Hlo Hhi. img_apply (YF8r.val_mem_ext (mrestrict H mem1)); [|img_try (img_exact Hv)]. intros j Hj. img_apply MB3; img_lia. }
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs3 (w64 YE1i.RC_END) mem3 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2144) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22] (Z_to_bv 64 0) = getr regs r ->
off = 2136 - 8 * Z.of_nat j -> Z.of_nat j < 8 ->
val_mem tfxsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem3) (sp0 - 2144) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 2144) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs3 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- (subst off; cbv beta). replace (sp0 - 2144 + (2136 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by img_lia. img_apply VM; [img_try (img_exact Hv) | img_lia | img_lia]. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK 0%nat 1%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by img_lia; img_exact V0)].
+ img_apply (CK 1%nat 8%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by img_lia; img_exact V1)].
+ img_apply (CK 2%nat 9%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by img_lia; img_exact V2)].
+ img_apply (CK 3%nat 18%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by img_lia; img_exact V3)].
+ img_apply (CK 4%nat 19%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by img_lia; img_exact V4)].
+ img_apply (CK 5%nat 20%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by img_lia; img_exact V5)].
+ img_apply (CK 6%nat 21%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by img_lia; img_exact V6)].
+ img_apply (CK 7%nat 22%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 7) with (sp0 - 64) by img_lia; img_exact V7)].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 2144) with (spZ regs + (-134) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply SRr_bind; [img_norm_st HSe r_epi; img_try (img_apply (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfxsegs tbl_icpt tbl_icpt_ok Hwx W E4); [img_try (img_exact HS4) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (img_try (intros z; img_apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22.
rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (23%bv : bv 5) Q23. rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X32 : ew E4 32 = getr regs 1) by (img_try ((subst E4; cbv beta); img_exact (ew_Ereg_extra regs3 _ 0))).
rewrite X32 in Q1.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (img_try (intros jj rr Hnth; (subst E4; cbv beta); rewrite (ew_Ereg_extra regs3 _ jj); img_exact Hnth)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs3 rr) by (img_try (intros ii rr Hnth; (subst E4; cbv beta); img_exact (ew_Ereg_nat regs3 _ ii rr Hnth))).
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra')).
split; [img_refl|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
assert (AV4 : forall a, aview tfxsegs H (ms_mem ms4) a = aview tfxsegs H mem3 a) by (img_try (intros a; img_apply aview_same; img_apply MEQ4)).
split; [img_refl|].
split; [|img_try (split; [|split; [|split; [|split]]])].
+   img_apply (al_frame _ _ LAWS ly S W mem3 md3 (ms_mem ms4) _ HAR3).
* intros a Hr Hown. img_apply AV4.
* intros a Hv. rewrite AV4. img_exact Hv.
* img_apply MF. * img_apply MF. * img_apply MF.
* img_exact (YE0v.hs_kept_eq _ _ _ MEQ4).
+
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q2. img_apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by img_lia. img_lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q3, (Y 3%nat 3%bv eq_refl), (K3 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 3%bv 3 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q4, (Y 4%nat 4%bv eq_refl), (K3 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 4%bv 4 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q8. img_exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q9. img_exact (X 2%nat 9%bv eq_refl).
* assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q18. img_exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q19. img_exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q20. img_exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q21. img_exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q22. img_exact (X 7%nat 22%bv eq_refl).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q23, (Y 23%nat 23%bv eq_refl), (K3 23 23%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 23%bv 23 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G23.
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q24, (Y 24%nat 24%bv eq_refl), (K3 24 24%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 24%bv 24 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G24.
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q25, (Y 25%nat 25%bv eq_refl), (K3 25 25%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 25%bv 25 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G25.
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q26, (Y 26%nat 26%bv eq_refl), (K3 26 26%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 26%bv 26 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G26.
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q27, (Y 27%nat 27%bv eq_refl), (K3 27 27%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (K2 27%bv 27 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G27.
+ eapply same_but_materialized_trans; [img_try (img_exact MF1)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm2)|].
eapply same_but_materialized_trans; [img_try (img_exact Hsbm3) | img_try (img_apply with_vm_backing_same)].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl), A10'. unfold w64. f_equal; img_lia.
+ intros a Hr Hs. rewrite AV4. rewrite Hfr3 by (img_try (unfold sp0 in *; img_lia)). rewrite AV2 by (img_try (unfold sp0 in *; img_lia)). img_apply AV1; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia)].
+ intros a Hp. img_apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). img_apply Hpres3. img_apply Hpres2'.
pose proof Hp as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ mem1 a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2160)) as [L1|L1]; [img_try (img_apply (apresent_same H mem mem1 a'); [img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRS1; img_lia)|].
img_apply (apresent_same H mem mem1 a'); [img_try (img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)].
Qed.
End f.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Hypothesis TL : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x n k : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis Hslo2 : ly_stk_lo ly + 2 * ESTACK <= spZ regs.
Hypothesis Hpres2 : forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis Hx : 0 < x.
Hypothesis Hk0 : 0 <= k.
Hypothesis Hk8 : k + 8 <= n.
Hypothesis Hk32 : k + 1 < 2 ^ 32.
Hypothesis Hxk : x + k + 1 <= 2 ^ 63.
Hypothesis Hfb : first_byte tfxsegs W mem x n 0 k.
Hypothesis Hsrc : src_ok tfxsegs W regs mem x (k + 1).
Hypothesis Hsband : forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs).
Hypothesis Ham : amem_range x (k + 1).
Hypothesis Hra : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1).
Hypothesis Hhull : shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1).
Hypothesis Htail : forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None.
Hypothesis Hrom : mconsts_view W mem.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Theorem strnlen_icpt_srr : SRr tfxsegs W (cfg_at tfxsegs SNL_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof Hslo2 as Hslo2'. pose proof Hpres2 as Hpres2'. unfold ESTACK in Hslo2', Hpres2'.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
assert (Hamr : x + k + 1 <= 2 ^ 47 - 1) by (img_try (pose proof Ham as Ham'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'; img_lia)).
unfold cfg_at. img_change (w64 SNL_ENTRY) with (Z_to_bv 64 SNL_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl); img_exact G10)).
assert (EE11 : ew EE 11 = Z_to_bv 64 n) by (img_try (rewrite (EEreg 11%nat 11%bv eq_refl); img_exact G11)).
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 SNL_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_exact (rodata_ok B TB snlA_rodata ly S H mem EE (snlA_rodata_chk ly) (proj1 HAR)))].
unfold stkA, SNL_WIN. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2160)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply HpresE. (subst sp0; cbv beta). img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, snlA_rodata, icpt_rodata, ro_region, extent_of_region, SNL_WIN.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; first [img_exact Hal16 | img_apply Z.mod_1_r | (subst sp0; cbv beta); img_lia]. }
eapply SRr_bind; [img_norm_st HS0 r_A; img_try (img_apply (icpt_phase_to W EE SNL_REAL _ _ _ _ _ HS0 r_A))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - SNL_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. img_apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SNL_WIN) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]. unfold SNL_WIN in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK].
apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is eA (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hr. rewrite (RD r _ Hr). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. img_apply (RA r i Hi). rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK. rewrite <- Hi. img_exact HK. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfxsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (img_try (do 8 (destruct j as [|j]; [img_try (cbn in Hj; injection Hj as <- <-; img_lia)|]); destruct j; discriminate)).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. (subst c; cbv beta).
pose proof (st_ok_mem_ok tfxsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
img_apply (val_of_chunk_ok tfxsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [img_refl|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 5) with 32. rewrite Z.mod_small by img_lia. img_lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
pose proof (st_ok_restrict_mkst tfxsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
img_apply (snl_tail B LAWS TB TL ly S W regs mem md (ms_regs ms1) (ms_mem ms1) mat1 x n k HPRE Hslo2 Hpres2 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hsband Ham Hra Hhull Htail Hrom).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_exact eq_refl.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
- rewrite (RD 1%bv (SLit SNL_RET) R1). img_refl.
- rewrite (RD 2%bv (SOff 2 (-2144)) R2). cbn [sv_denot]. rewrite EE2. img_refl.
- rewrite (RD 8%bv (SOff 2 0) R8). cbn [sv_denot]. rewrite EE2, Z.add_0_r. img_refl.
- rewrite (RD 9%bv (SLit 1) R9). img_refl.
- rewrite (RD 18%bv (SOff 10 0) R18). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
- rewrite (RD 19%bv (SOff 11 0) R19). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
- img_exact (RK 3%bv 3%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 4%bv 4%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact (RK 20%bv 20%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 21%bv 21%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 22%bv 22%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact (RK 23%bv 23%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 24%bv 24%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact (RK 25%bv 25%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 26%bv 26%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 27%bv 27%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact MEQ1.
- intros a Ha. unfold SNL_WIN in Ha.
img_apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold SNL_WIN. img_lia.
- replace (sp0 - 8) with (sp0 + -8) by img_lia. img_exact (CK 0%nat 1 (-8) eq_refl).
- replace (sp0 - 16) with (sp0 + -16) by img_lia. img_exact (CK 1%nat 8 (-16) eq_refl).
- replace (sp0 - 24) with (sp0 + -24) by img_lia. img_exact (CK 2%nat 9 (-24) eq_refl).
- replace (sp0 - 32) with (sp0 + -32) by img_lia. img_exact (CK 3%nat 18 (-32) eq_refl).
- replace (sp0 - 40) with (sp0 + -40) by img_lia. img_exact (CK 4%nat 19 (-40) eq_refl).
- replace (sp0 - 48) with (sp0 + -48) by img_lia. img_exact (CK 5%nat 20 (-48) eq_refl).
- replace (sp0 - 56) with (sp0 + -56) by img_lia. img_exact (CK 6%nat 21 (-56) eq_refl).
- replace (sp0 - 64) with (sp0 + -64) by img_lia. img_exact (CK 7%nat 22 (-64) eq_refl).
Qed.
End g.
Theorem strnlen_icpt_realizes {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B -> TfxSyms B ->
forall ly S (W : world tfxsegs) regs mem md x n k,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfxsegs W mem x n 0 k ->
src_ok tfxsegs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfxsegs W (cfg_at tfxsegs (0x420c8 + D_2c4) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB TL ly S W regs mem md x n k HPRE Hslo2 Hpres2 G10 G11 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hsband Ham Hra Hhull Htail Hrom.
img_exact (strnlen_icpt_srr B LAWS TB TL ly S W regs mem md x n k HPRE Hslo2 Hpres2 G10 G11 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hsband Ham Hra Hhull Htail Hrom).
Qed.
Corollary strnlen_icpt_contractM {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B -> TfxSyms B -> astrnlen_realizesM B (0x420c8 + D_2c4).
Proof. intros B LAWS TB TL. img_exact (strnlen_icpt_realizes B LAWS TB TL). Qed.

End d.
