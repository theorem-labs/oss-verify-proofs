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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE1n YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF61 YE0x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition MCH_ENTRY {imgk : img} : Z := (0x420dc + D_2c4).
Definition MCH_REAL {imgk : img} : Z := (0x9b394 + D_10ec).
Definition MCH_RET {imgk : img} : Z := (0x43904 + D_2c4).
Definition MCH_END {imgk : img} : Z := (0x43964 + D_2c4).
Definition MCH_WIN : Z := 2144.
Definition MCH_SCR : Z := 2200.
Definition mchr_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [((0xa3eb0 + D_10f0), 8, [(0, 8%N, (0x9b394 + D_10ec))])].
Lemma mchr_rodata_chk {imgk : img} : forall ly, rodata_chk ly mchr_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- MCH_WIN) 0 (- MCH_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 (2^47) 0); (12%nat, mkAF 8 (2^63 - 1) 0)].
Definition ssA {imgk : img} : sstate := mkSS MCH_ENTRY sr_atoms (stkA :: map ro_region mchr_rodata) None (mkFacts factsA [] []).
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_icpt FUEL MCH_REAL s.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssA)))).
Lemma r_A {imgk : img} : RUNTOR ssA = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition epi_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 2120 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 2112 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 2104 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 2096 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 2088 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 2080 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi {imgk : img} : sstate := mkSS MCH_END sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition chunk_is {imgk : img} (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk {imgk : img} (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? MCH_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - MCH_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 1 (SLit MCH_RET) && reg_is ss 2 (SOff 2 (-2128)) &&
reg_is ss 18 (SOff 10 0) && reg_is ss 20 (SLit 1) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound {imgk : img} : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Lemma bytes_of_str {imgk : img} : forall (H : word -> bool) (mem : word -> option byte) x k,
0 <= k -> (forall i, 0 <= i < k -> exists b, aview tfxsegs H mem (x + i) = Some b /\ b <> 0) ->
exists bs : list byte, length bs = Z.to_nat k /\ ~ In NUL bs /\
forall j, (j < length bs)%nat -> mbyte tfxsegs (mrestrict H mem) (x + Z.of_nat j) = Some (nth j bs NUL).
Proof.
intros H mem x k Hk Hs.
set (bs := map (fun j : nat => match mbyte tfxsegs (mrestrict H mem) (x + Z.of_nat j) with Some b => b | None => NUL end) (seq 0 (Z.to_nat k))).
assert (L : length bs = Z.to_nat k) by (img_try ((subst bs; cbv beta); rewrite length_map, length_seq; img_refl)).
assert (B : forall j, (j < length bs)%nat -> mbyte tfxsegs (mrestrict H mem) (x + Z.of_nat j) = Some (nth j bs NUL) /\ nth j bs NUL <> NUL).
{ intros j Hj. rewrite L in Hj. destruct (Hs (Z.of_nat j) ltac:(img_lia)) as (b & Hb & Hb0).
apply aview_some in Hb as (bb & E & Ev).
assert (NE : nth_error bs j = Some bb).
{ (subst bs; cbv beta). rewrite nth_error_map, nth_error_seq. replace (j <? Z.to_nat k)%nat with true by (img_try (symmetry; img_apply Nat.ltb_lt; img_exact Hj)).
cbn. rewrite E. img_refl. }
rewrite (nth_error_nth _ _ _ NE). split; [img_try (img_exact E)|]. intros Hn. img_apply Hb0. rewrite <- Ev, Hn. img_refl. }
exists bs. split; [img_try (img_exact L)|]. split.
- intros Hin. apply In_nth with (d := NUL) in Hin as (j & Hj & Hnj). img_exact (proj2 (B j Hj) Hnj).
- intros j Hj. img_exact (proj1 (B j Hj)).
Qed.

Lemma rdn1_mbyte {imgk : img} : forall (m : word -> option byte) a,
rdn tfxsegs m (Z_to_bv 64 a) 1 = match mbyte tfxsegs m a with Some b => Some [b] | None => None end.
Proof.
intros m a. cbn [rdn]. img_change (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom tfxsegs (Z_to_bv 64 a) end) with (mbyte tfxsegs m a).
destruct (mbyte tfxsegs m a); img_refl.
Qed.
Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); img_refl. Qed.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Lemma mchr_tail : forall ly S (W : world tfxsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 x n k,
ecall_pre tfxsegs B ly S W regs mem md ->
0 <= n < 2 ^ 63 -> 0 < x -> 0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfxsegs W mem x n 0 k ->
src_ok tfxsegs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
getr regs1 10 = w64 x -> getr regs1 11 = w64 0 -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MCH_RET -> getr regs1 2 = w64 (spZ regs - 2128) -> getr regs1 18 = w64 x -> getr regs1 20 = w64 1 ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 ->
getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MCH_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MCH_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfxsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
SRr tfxsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MCH_REAL) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 x n k HPRE Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom
G10 G11 G12 G1 G2 G18 G20 G3 G4 G22 G23 G24 G25 G26 G27 MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx. unfold ESTACK, MCH_WIN in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by img_lia.
set (H := w_H W) in *.
assert (Hamr : x + k + 1 <= 2 ^ 47 - 1) by (img_try (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; img_lia)).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfxsegs H mem1 a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (SRCW : forall a, x <= a < x + (k + 1) -> ~ (sp0 - 2144 <= a < sp0)) by (img_try (intros a Ha; destruct (Hsrc a Ha) as [_ Hns]; unfold ESTACK in Hns; unfold sp0 in *; img_lia)).
destruct Hfb as (Hkn & Hbef & Hlast).
destruct (bytes_of_str H mem1 x k Hk0) as (bs & LEN & NONUL & BS).
{ intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hb0). exists b. split; [|img_try (img_exact Hb0)]. rewrite AV1; [img_try (img_exact Hb) | img_lia | img_try (img_apply SRCW; img_lia)]. }
assert (KLEN : Z.of_nat (length bs) = k) by img_lia.
destruct (tfx_memchr bs (w64 x) (w64 n) (mrestrict H mem1) (seg_rom tfxsegs) regs1 NONUL) as (regs2 & Hms & A10 & A11 & A12 & A13 & KEEP).
- unfold w64. rewrite unsigned_lit_small by img_lia. img_lia.
- unfold w64. rewrite unsigned_lit_small by img_lia. img_lia.
-
intros j Hj. unfold w64. rewrite unsigned_lit_small by img_lia.
img_apply (proj2 (rdn_mbytes tfxsegs _ 1 _ _)). split; [img_refl|]. intros i Hi. replace i with 0%nat by img_lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
destruct (Nat.lt_ge_cases j (length bs)) as [Hlt|Hge].
+ rewrite (BS j Hlt), app_nth1 by img_lia. img_refl.
+ assert (Hj' : j = length bs) by img_lia. (subst j; cbv beta). rewrite app_nth2 by img_lia. rewrite Nat.sub_diag. cbn [nth].
rewrite KLEN. rewrite (YF8r.aview_byte H mem1 _ 0); [img_refl|]. rewrite AV1; [img_try (img_exact (Hlast ltac:(img_lia))) | img_lia | img_try (img_apply SRCW; img_lia)].
-
intros a Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by img_lia. rewrite KLEN in Ha.
pose proof (Z.mod_pos_bound (x + k) 8 ltac:(img_lia)) as Hm8. pose proof (proj2 (Hsrc (x + k) ltac:(img_lia))) as Hnk. unfold ESTACK in Hnk.
intros Hnone.
assert (Hv : aview tfxsegs H mem1 a <> None) by (img_try (rewrite (AV1 a) by (unfold sp0 in *; img_lia); img_apply (Htail a); img_lia)).
apply (proj1 (aview_vis H mem1 a)) in Hv.
destruct (mbyte tfxsegs (mrestrict H mem1) a) as [b|] eqn:Eb; [|img_try (img_exact (Hv eq_refl))].
assert (E : rdn tfxsegs (mrestrict H mem1) (Z_to_bv 64 a) 1 = Some [b]).
{ img_apply (proj2 (rdn_mbytes tfxsegs (mrestrict H mem1) 1 a [b])). split; [img_refl|]. intros i Hi. destruct i; [|img_lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. img_exact Eb. }
rewrite E in Hnone. discriminate.
-
intros a Ha.
assert (Hin : MC_LO <= a < MC_HI) by (img_try (unfold MC_LO, MC_HI; unfold tfx_D_const_HIGHS_0x8080808080808080, tfx_D_const_ONES_0x0101010101010100 in *; img_lia)).
pose proof (Hrom a Hin) as Hv. fold H in Hv. rewrite <- (AV1 a) in Hv by (img_try (unfold tfx_D_const_HIGHS_0x8080808080808080, tfx_D_const_ONES_0x0101010101010100 in Ha; img_lia)).
rewrite !rdn1_mbyte. unfold aview in Hv.
change (mbyte tfxsegs (fun _ : word => None) a) with (seg_rom tfxsegs (Z_to_bv 64 a)).
destruct (mbyte tfxsegs (mrestrict H mem1) a) as [b|], (seg_rom tfxsegs (Z_to_bv 64 a)) as [b'|]; cbn in Hv; try discriminate; [|img_refl].
injection Hv as Hv. do 2 f_equal. img_apply bv_eq. img_exact Hv.
- img_exact G10.
- img_exact G11.
- img_exact G12.
-
rewrite G1 in Hms. replace (v_jalr (w64 MCH_RET) 0) with (Z_to_bv 64 MCH_RET : word) in Hms by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
img_change (Z_to_bv 64 tfx_A_musl_memchr) with (Z_to_bv 64 MCH_REAL) in Hms.
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb _ model' Hsbm). rewrite ?wvb_wvb.
cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H mem1 (mrestrict H mem1)).
assert (M2 : forall z, mem2 z = mem1 z) by (img_try (intros z; (subst mem2; cbv beta); img_apply munrestrict_mrestrict_same)).
assert (AV2 : forall a, aview tfxsegs H mem2 a = aview tfxsegs H mem1 a) by (img_try (intros a; img_apply aview_same; img_apply M2)).
assert (KEEPr : forall r : bv 5, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs2 r = getr regs1 r) by (img_try (intros r; img_apply KEEP)).
assert (R2sp : spZ regs2 = sp0 - 2128).
{ unfold spZ. rewrite KEEPr by (img_try (intros H'; discriminate H')). rewrite G2. unfold w64. img_apply unsigned_lit_small. img_lia. }
eapply SRr_bind.
{ img_apply (mchr_check_srr B LAWS TB ly S W regs2 mem2 (with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md) x (k + 1)).
-
img_apply (al_frame _ _ LAWS ly S W mem md mem2 _ HAR).
+ intros a Hr Hown. rewrite AV2. img_apply AV1; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ mem2 a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
rewrite AV2. destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [img_try (rewrite AV1 by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV1 by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRS1. img_lia.
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ img_exact (YE0v.hs_kept_trans _ _ _ _ (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(img_lia) ltac:(img_lia)) (YE0v.hs_kept_eq _ _ _ M2)).
- rewrite R2sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- rewrite R2sp. unfold YE0x.RC_SCR. unfold sp0 in *. img_lia.
- rewrite R2sp. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R2sp in Ha. unfold YE0x.RC_SCR in Ha.
img_apply (apresent_same H mem1 mem2 a (M2 _)).
destruct (Z_lt_le_dec a (sp0 - 2144)) as [L1|L1].
+ img_apply (apresent_same H mem mem1 a). { img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_lia. } img_apply HpresE. unfold sp0 in *. img_lia.
+ img_apply PRS1. img_lia.
-   rewrite A10. unfold w64. rewrite unsigned_lit_small by img_lia. rewrite KLEN. f_equal. img_lia.
- rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G18.
- rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G20.
- img_lia.
- img_lia.
- img_lia.
- img_lia.
- img_exact Ham.
- eapply range_addressable_agree; [|img_try (img_exact Hra)]. intros y Hy. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (shadow_addr_bounds y ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. rewrite AV2. img_apply AV1; unfold sp0 in *; img_lia.
- intros s Hs. rewrite AV2, AV1; [img_try (img_exact (Hhull s Hs)) | |];
pose proof (shadow_addr_bounds x ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (x + (k + 1) - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + (k + 1) - 1)) 8 ltac:(img_lia));
unfold sp0 in *; img_lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
rewrite R2sp in Hfr3. unfold YE0x.RC_SCR in Hfr3.
set (E4 := Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (K3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 18 -> z <> 20 -> z <> 21 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5 H6. img_exact (KEPT3 z H1 H2 H3 H5 H6). }
assert (R3sp : getr regs3 2 = w64 (sp0 - 2128)).
{ rewrite (K3 2 2%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R3sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2200 <= a < sp0 - 2128) -> mbyte tfxsegs (mrestrict H mem3) a = mbyte tfxsegs (mrestrict H mem1) a).
{ intros a Hr Ha. img_apply mbyte_of_aview. rewrite <- (AV2 a). img_apply Hfr3; [img_try (img_exact Hr) | img_try (clear -Ha; img_lia)]. }
assert (VM : forall a v, val_mem tfxsegs (mrestrict H mem1) a 8 v -> sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfxsegs (mrestrict H mem3) a 8 v).
{ intros a v Hv Hlo Hhi. img_apply (YF8r.val_mem_ext (mrestrict H mem1)); [|img_try (img_exact Hv)]. intros j Hj. img_apply MB3; img_lia. }
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs3 (w64 YE0x.RC_END) mem3 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2128) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfxsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem3) (sp0 - 2128) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs3 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- (subst off; cbv beta). replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by img_lia. img_apply VM; [img_try (img_exact Hv) | img_lia | img_lia]. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK 0%nat 1%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by img_lia; img_exact V0)].
+ img_apply (CK 1%nat 8%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by img_lia; img_exact V1)].
+ img_apply (CK 2%nat 9%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by img_lia; img_exact V2)].
+ img_apply (CK 3%nat 18%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by img_lia; img_exact V3)].
+ img_apply (CK 4%nat 19%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by img_lia; img_exact V4)].
+ img_apply (CK 5%nat 20%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by img_lia; img_exact V5)].
+ img_apply (CK 6%nat 21%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by img_lia; img_exact V6)].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
unfold cfg_at.
eapply SRr_bind; [img_norm_st HSe r_epi; img_try (img_apply (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfxsegs tbl_icpt tbl_icpt_ok Hwx W E4); [img_try (img_exact HS4) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (img_try (intros z; img_apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21.
rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23. rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X32 : ew E4 32 = getr regs 1) by (img_try ((subst E4; cbv beta); img_exact (ew_Ereg_extra regs3 _ 0))).
rewrite X32 in Q1.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
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
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q3, (Y 3%nat 3%bv eq_refl), (K3 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q4, (Y 4%nat 4%bv eq_refl), (K3 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q8. img_exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q9. img_exact (X 2%nat 9%bv eq_refl).
* assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q18. img_exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q19. img_exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q20. img_exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q21. img_exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q22, (Y 22%nat 22%bv eq_refl), (K3 22 22%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G22.
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q23, (Y 23%nat 23%bv eq_refl), (K3 23 23%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G23.
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q24, (Y 24%nat 24%bv eq_refl), (K3 24 24%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G24.
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q25, (Y 25%nat 25%bv eq_refl), (K3 25 25%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G25.
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q26, (Y 26%nat 26%bv eq_refl), (K3 26 26%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G26.
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q27, (Y 27%nat 27%bv eq_refl), (K3 27 27%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite KEEPr by (img_try (intros H'; discriminate H')). img_exact G27.
+ eapply same_but_materialized_trans; [img_try (img_exact Hsbm3) | img_try (img_apply with_vm_backing_same)].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl), A10', A10. unfold w64. rewrite unsigned_lit_small by img_lia. rewrite KLEN. img_refl.
+ intros a Hr Hs. rewrite AV4. rewrite Hfr3 by (img_try (unfold sp0 in *; img_lia)). rewrite AV2. img_apply AV1; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia)].
+ intros a Hp. pose proof Hp as [Hh [b Hb]]. img_apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). img_apply Hpres3.
img_apply (apresent_same H mem1 mem2 a (M2 _)).
rewrite (YE0v.apresent_mod _ mem1 a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [img_try (img_apply (apresent_same H mem mem1 a'); [img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRS1; img_lia)|].
img_apply (apresent_same H mem mem1 a'); [img_try (img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)].
Qed.
End g.
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x n k : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 0.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis Hx : 0 < x.
Hypothesis Hk0 : 0 <= k.
Hypothesis Hk8 : k + 8 <= n.
Hypothesis Hk32 : k + 1 < 2 ^ 32.
Hypothesis Hxk : x + k + 1 <= 2 ^ 63.
Hypothesis Hfb : first_byte tfxsegs W mem x n 0 k.
Hypothesis Hsrc : src_ok tfxsegs W regs mem x (k + 1).
Hypothesis Ham : amem_range x (k + 1).
Hypothesis Hra : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1).
Hypothesis Hhull : shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1).
Hypothesis Htail : forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None.
Hypothesis Hrom : mconsts_view W mem.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Theorem memchr0_icpt_srr : SRr tfxsegs W (cfg_at tfxsegs MCH_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
assert (Hamr : x + k + 1 <= 2 ^ 47 - 1) by (img_try (pose proof Ham as Ham'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'; img_lia)).
unfold cfg_at. img_change (w64 MCH_ENTRY) with (Z_to_bv 64 MCH_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl); img_exact G10)).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (img_try (rewrite (EEreg 12%nat 12%bv eq_refl); img_exact G12)).
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 MCH_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_exact (rodata_ok B TB mchr_rodata ly S H mem EE (mchr_rodata_chk ly) (proj1 HAR)))].
unfold stkA, MCH_WIN. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2144)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply HpresE. (subst sp0; cbv beta). img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, mchr_rodata, icpt_rodata, ro_region, extent_of_region, MCH_WIN.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; first [img_exact Hal16 | img_apply Z.mod_1_r | (subst sp0; cbv beta); img_lia]. }
eapply SRr_bind; [img_norm_st HS0 r_A; img_try (img_apply (icpt_phase_to W EE MCH_REAL _ _ _ _ _ HS0 r_A))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MCH_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. img_apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MCH_WIN) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]. unfold MCH_WIN in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R18].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
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
assert (Hrz : 0 <= rz < 32) by (img_try (do 7 (destruct j as [|j]; [img_try (cbn in Hj; injection Hj as <- <-; img_lia)|]); destruct j; discriminate)).
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
img_apply (mchr_tail B LAWS TB ly S W regs mem md (ms_regs ms1) (ms_mem ms1) mat1 x n k HPRE Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_exact eq_refl.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact G11.
- rewrite (RD 12%bv (SOff 12 0) R12). cbn [sv_denot]. rewrite EE12, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
- rewrite (RD 1%bv (SLit MCH_RET) R1). img_refl.
- rewrite (RD 2%bv (SOff 2 (-2128)) R2). cbn [sv_denot]. rewrite EE2. img_refl.
- rewrite (RD 18%bv (SOff 10 0) R18). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
- rewrite (RD 20%bv (SLit 1) R20). img_refl.
- img_exact (RK 3%bv 3%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 4%bv 4%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact (RK 22%bv 22%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 23%bv 23%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 24%bv 24%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact (RK 25%bv 25%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 26%bv 26%nat eq_refl ltac:(img_try (cbn; img_lia))). - img_exact (RK 27%bv 27%nat eq_refl ltac:(img_try (cbn; img_lia))).
- img_exact MEQ1.
- intros a Ha. unfold MCH_WIN in Ha.
img_apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold MCH_WIN. img_lia.
- replace (sp0 - 8) with (sp0 + -8) by img_lia. img_exact (CK 0%nat 1 (-8) eq_refl).
- replace (sp0 - 16) with (sp0 + -16) by img_lia. img_exact (CK 1%nat 8 (-16) eq_refl).
- replace (sp0 - 24) with (sp0 + -24) by img_lia. img_exact (CK 2%nat 9 (-24) eq_refl).
- replace (sp0 - 32) with (sp0 + -32) by img_lia. img_exact (CK 3%nat 18 (-32) eq_refl).
- replace (sp0 - 40) with (sp0 + -40) by img_lia. img_exact (CK 4%nat 19 (-40) eq_refl).
- replace (sp0 - 48) with (sp0 + -48) by img_lia. img_exact (CK 5%nat 20 (-48) eq_refl).
- replace (sp0 - 56) with (sp0 + -56) by img_lia. img_exact (CK 6%nat 21 (-56) eq_refl).
Qed.
End h.
Theorem memchr0_icpt_realizes {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B ->
forall ly S (W : world tfxsegs) regs mem md x n k,
ecall_pre tfxsegs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfxsegs W mem x n 0 k ->
src_ok tfxsegs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfxsegs W (cfg_at tfxsegs (0x420dc + D_2c4) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md x n k HPRE G10 G11 G12 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom.
img_exact (memchr0_icpt_srr B LAWS TB ly S W regs mem md x n k HPRE G10 G11 G12 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom).
Qed.
Corollary memchr0_icpt_contractM {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B -> amemchr0_realizesM B (0x420dc + D_2c4).
Proof. intros B LAWS TB. img_exact (memchr0_icpt_realizes B LAWS TB). Qed.

End f.
