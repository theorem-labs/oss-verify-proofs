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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1o YE09 YE0t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FW_ENTRY {imgk : img} : Z := (0x420e8 + D_2c4).
Definition FW_REAL {imgk : img} : Z := (0x97a04 + D_10ec).
Definition FW_RET {imgk : img} : Z := (0x440bc + D_2c4).
Definition FW_B {imgk : img} : Z := (0x440c8 + D_2c4).
Definition FW_END {imgk : img} : Z := (0x44120 + D_2c4).
Definition FW_FRAME : Z := 2128.
Definition FW_WIN : Z := 2144.
Definition FWI_STK : Z := 6224.
Definition fwA_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [((0xa3ec8 + D_10f0), 8, [(0, 8%N, (0x97a04 + D_10ec))])].
Lemma fwA_rodata_chk {imgk : img} : forall ly, rodata_chk ly fwA_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- FW_WIN) 0 (- FW_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 1 (2^25) 0); (12%nat, mkAF 1 1 0)].
Definition ssA {imgk : img} : sstate := mkSS FW_ENTRY sr_atoms (stkA :: map ro_region fwA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_icpt FUEL FW_REAL s.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssA)))).
Lemma r_A {imgk : img} : RUNTOR ssA = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_icpt FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition epi_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 2120 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 2112 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 2104 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 2096 (CVal 8 (SOff 35 0));
YQ0b.mkChunk 2088 (CVal 8 (SOff 36 0));
YQ0b.mkChunk 2080 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi {imgk : img} : sstate := mkSS FW_END sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? FW_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - FW_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 13 (SOff 13 0) &&
reg_is ss 1 (SLit FW_RET) && reg_is ss 2 (SOff 2 (-2128)) &&
reg_is ss 9 (SOff 11 0) && reg_is ss 18 (SOff 10 0) && reg_is ss 19 (SOff 13 0) && reg_is ss 20 (SOff 12 0) && reg_is ss 21 (SLit 1) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Lemma lk_ret0 {imgk : img} : clookup tbl_icpt (0x440bc + D_2c4) = Some 0x060a8263. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma lk_ret1 {imgk : img} : clookup tbl_icpt (0x440c0 + D_2c4) = Some 0x06050063. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma lk_ret2 {imgk : img} : clookup tbl_icpt (0x440c4 + D_2c4) = Some 0x029504b3. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma fw_mid3 {imgk : img} : forall (W : world tfxsegs) regs mem md,
getr regs 21 = w64 1 -> getr regs 10 = w64 1 ->
SRr tfxsegs W (mkCfg (mkst regs (Z_to_bv 64 FW_RET) mem (seg_rom tfxsegs)) md)
(fun W' c' => W' = W /\ exists md', c' = mkCfg (mkst (regupd regs 9%bv (getr regs 9%bv)) (Z_to_bv 64 FW_B) mem (seg_rom tfxsegs)) md' /\
same_but_materialized md md').
Proof.
intros W regs mem md G21 G10. pose proof YF8r.Hwx_tfa as Hwx.
eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
{ rewrite restrict_mkst_fx. img_apply (step_beq_ft tfxsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret0) eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)); replace r0 with (0%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)) end.
rewrite G21. img_case; vm_compute. all: img_refl. }
intros md1 Hs1. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 (0x440bc + D_2c4)) 4) with (Z_to_bv 64 (0x440c0 + D_2c4) : word) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
{ rewrite restrict_mkst_fx. img_apply (step_beq_ft tfxsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret1) eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (10%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)); replace r0 with (0%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)) end.
rewrite G10. img_case; vm_compute. all: img_refl. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 (0x440c0 + D_2c4)) 4) with (Z_to_bv 64 (0x440c4 + D_2c4) : word) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
{ rewrite restrict_mkst_fx. img_apply (step_mul tfxsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret2) eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))). }
intros md3 Hs3. rewrite unrestrict_mkst_mrestrict.
match goal with |- SRr _ _ (mkCfg (mkst (if bv_eqb ?rd _ then _ else regupd _ _ (v_mul (getr _ ?a) (getr _ ?b))) _ _ _) _) _ =>
replace rd with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)); replace a with (10%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)) end.
replace (bv_eqb (9%bv : bv 5) 0) with false by img_refl. cbn iota.
replace (v_addi (Z_to_bv 64 (0x440c4 + D_2c4)) 4) with (Z_to_bv 64 FW_B : word) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
replace (v_mul (getr regs 10) (getr regs 9)) with (getr regs 9).
2:{ unfold v_mul. rewrite G10. unfold w64. rewrite unsigned_lit_small by img_lia. rewrite Z.mul_1_l, Z_to_bv_bv_unsigned. img_refl. }
img_apply SRr_ret. split; [img_refl|]. exists md3. split; [img_refl|].
eapply same_but_materialized_trans; [img_try (img_exact Hs1)|]. eapply same_but_materialized_trans; [img_try (img_exact Hs2) | img_try (img_exact Hs3)].
Qed.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Theorem tfx_fwrite_icpt : forall ly S (W : world tfxsegs) regs mem md ch p size cval (msg : list byte) T,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + FWI_STK <= spZ regs ->
(forall a, spZ regs - FWI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 p -> getr regs 11 = w64 size -> getr regs 12 = w64 1 -> getr regs 13 = w64 F_STDERR ->
1 <= size -> size <= 2 ^ 25 ->
0 <= p -> p + size <= kHighMemEnd ->
(p + size <= spZ regs - FWI_STK \/ spZ regs <= p) ->
(p + size <= F_STDERR \/ F_STDERR + FILE_SZ <= p) ->
rdn tfxsegs (mrestrict (w_H W) mem) (Z_to_bv 64 p) (Z.to_nat size) = Some msg ->
stderr_pristine (mrestrict (w_H W) mem) ->
(forall a, F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
amem_range p size ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF p size ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) p size ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 1 ->
stderr_written (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FWI_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs FW_ENTRY regs mem md) (t_emit (map (WriteEv ch) msg) T).
Proof.
intros ly S W regs mem md ch p size cval msg T HPRE Hstk Hpres G10 G11 G12 G13 Hsz Hszhi Hp0 Hphi Hpband HpF Hmsg HFP HFown Hgot Hcan Hcv
Ham Hra Hhull Hch HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold FWI_STK in *.
assert (HFS : FILE_SZ = 232) by img_refl. assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (0xa2e10 + D_10f0)) by img_refl. assert (HCA : A_canary = (0x5fd190 + D_10c0)) by img_refl.
assert (HFWS : FW_STK = 176) by img_refl. assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
assert (Hamr : p + size <= 2 ^ 47 - 1) by (img_try (pose proof Ham as X1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1; img_lia)).
pose proof YF8r.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfxsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfxsegs H m' b = aview tfxsegs H m b) -> val_mem tfxsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. img_apply (YF8r.val_mem_ext (mrestrict H m)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply Hf. img_lia. }
assert (FT : forall flds (m m' : word -> option byte),
Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) flds ->
file_is flds (mrestrict H m) ->
(forall b, F_STDERR <= b < F_STDERR + FILE_SZ -> aview tfxsegs H m' b = aview tfxsegs H m b) -> file_is flds (mrestrict H m')).
{ intros flds m m' Hwf Hf Hb. unfold file_is in *. img_apply Forall_forall. intros [[o nn] v] Hin.
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. pose proof (proj1 (Forall_forall _ _) Hwf _ Hin) as Ho. cbn beta iota in Hv, Ho |- *.
img_apply (VT m); [img_try (img_exact Hv)|]. intros b Hbb. img_apply Hb. pose proof (N_nat_Z nn). img_lia. }
assert (WF1 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields) by (img_try (unfold stderr_fields, FILE_SZ; repeat constructor; cbn; img_lia)).
assert (WF2 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields_after) by (img_try (unfold stderr_fields_after, FILE_SZ; repeat constructor; cbn; img_lia)).
unfold cfg_at. img_change (w64 FW_ENTRY) with (Z_to_bv 64 FW_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE10 : ew EE 10 = Z_to_bv 64 p) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl); img_exact G10)).
assert (EE11 : ew EE 11 = Z_to_bv 64 size) by (img_try (rewrite (EEreg 11%nat 11%bv eq_refl); img_exact G11)).
assert (EE12 : ew EE 12 = Z_to_bv 64 1) by (img_try (rewrite (EEreg 12%nat 12%bv eq_refl); img_exact G12)).
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FW_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_exact (rodata_ok B TB fwA_rodata ly S H mem EE (fwA_rodata_chk ly) (proj1 HAR)))].
unfold stkA, FW_WIN. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2144)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YE0v.apresent_writable. img_apply HpresE. (subst sp0; cbv beta). img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, fwA_rodata, icpt_rodata, ro_region, extent_of_region, FW_WIN.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; first [img_exact Hal16 | img_apply Z.mod_1_r | (subst sp0; cbv beta); img_lia]. }
eapply (SRr_srealizes tfxsegs W _ _ _ (icpt_phase_to W EE FW_REAL _ _ _ _ _ HS0 r_A) HAI0).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2144 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. img_apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FW_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((img_case; vm_compute); img_refl)|]. unfold FW_WIN in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R21]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R13]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact HK')]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
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
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). img_zside.
- img_zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 p) by (img_try (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q11 : getr regs1 11 = w64 size) by (img_try (rewrite (RD 11%bv (SOff 11 0) R11); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q12 : getr regs1 12 = w64 1) by (img_try (rewrite (RD 12%bv (SOff 12 0) R12); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by img_lia; img_refl)).
assert (Q13 : getr regs1 13 = w64 F_STDERR) by (img_try (rewrite (RD 13%bv (SOff 13 0) R13); cbn [sv_denot]; rewrite (EEreg 13%nat 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_exact G13)).
assert (Q1 : getr regs1 1 = w64 FW_RET) by (img_try (rewrite (RD 1%bv (SLit FW_RET) R1); img_refl)).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2128)) by (img_try (rewrite (RD 2%bv (SOff 2 (-2128)) R2); cbn [sv_denot]; rewrite EE2; img_refl)).
assert (Q9 : getr regs1 9 = w64 size) by (img_try (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q18 : getr regs1 18 = w64 p) by (img_try (rewrite (RD 18%bv (SOff 10 0) R18); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q21 : getr regs1 21 = w64 1) by (img_try (rewrite (RD 21%bv (SLit 1) R21); img_refl)).
assert (Q3 : getr regs1 3 = getr regs 3) by (img_try (img_exact (RK 3%bv 3%nat eq_refl ltac:(cbn; img_lia)))).
assert (Q4 : getr regs1 4 = getr regs 4) by (img_try (img_exact (RK 4%bv 4%nat eq_refl ltac:(cbn; img_lia)))).
assert (R1sp : spZ regs1 = sp0 - 2128) by (img_try (unfold spZ; rewrite Q2; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (R1ra : raZ regs1 = FW_RET) by (img_try (unfold raZ; rewrite Q1; unfold w64; img_apply unsigned_lit_small; unfold FW_RET; img_lia)).
pose proof (st_ok_restrict_mkst tfxsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (img_try ((subst md1; cbv beta); img_apply with_vm_backing_same)).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfxsegs H (ms_mem ms1) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PRS1 : forall a, sp0 - 2144 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. img_apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold FW_WIN. img_lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ (ms_mem ms1) a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [img_try (img_apply (apresent_same H mem (ms_mem ms1) a'); [img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRS1; img_lia)|].
img_apply (apresent_same H mem (ms_mem ms1) a'); [img_try (img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)]. }
assert (HAR1 : AR tfxsegs B ly S W (ms_mem ms1) md1).
{ img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. img_apply AV1; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ (ms_mem ms1) a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [img_try (rewrite AV1 by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV1 by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRS1. img_lia.
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(img_try (unfold sp0 in *; img_lia)) ltac:(img_lia)). }
assert (HPRE1 : ecall_pre tfxsegs B ly S W regs1 (ms_mem ms1) md1).
{ split; [img_try (img_exact HAR1)|]. split; [img_try (rewrite Q1; img_apply (ret_ok_lit FW_RET); [unfold FW_RET; img_lia | img_refl])|].
split; [img_try (rewrite R1sp; replace (sp0 - 2128) with (sp0 + (-133) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16)|].
split; [img_try (rewrite R1sp; unfold ESTACK; unfold sp0 in *; img_lia)|]. split; [img_try (rewrite R1sp; unfold sp0 in *; img_lia)|].
split; [img_try (intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; img_apply PM1; img_apply Hpres; unfold sp0 in *; img_lia)|].
split; [img_try (rewrite Q3; img_exact Hgp) | img_try (rewrite Q4; img_exact Htp)]. }
img_change (mkCfg (mkst regs1 (Z_to_bv 64 FW_REAL) (ms_mem ms1) (seg_rom tfxsegs)) md1) with (cfg_at tfxsegs A_fwrite regs1 (ms_mem ms1) md1).
img_apply (tfx_fwrite_at B LAWS ly S W regs1 (ms_mem ms1) md1 ch p size 1 cval msg T HPRE1).
- rewrite R1sp, HFWS. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R1sp, HFWS in Ha. img_apply PM1. img_apply Hpres. unfold sp0 in *. img_lia.
- img_exact Q10.
- img_exact Q11.
- img_exact Q12.
- img_exact Q13.
- img_exact Hsz.
- img_lia.
- rewrite Z.mul_1_r. img_exact Hszhi.
- img_exact Hp0.
- rewrite Z.mul_1_r. img_exact Hphi.
- rewrite Z.mul_1_r, R1sp, HFWS. unfold sp0 in *. img_lia.
- rewrite Z.mul_1_r. img_exact HpF.
- rewrite Z.mul_1_r. pose proof (proj1 (rdn_mbytes tfxsegs _ _ _ _) Hmsg) as [Hlen Hby].
img_apply (proj2 (rdn_mbytes tfxsegs _ _ _ _)). split; [img_try (img_exact Hlen)|]. intros i Hi. rewrite <- (Hby i Hi).
img_apply mbyte_of_aview. img_apply AV1; [img_lia | img_try (unfold sp0 in *; img_lia)].
- img_apply (FT stderr_fields mem); [img_try (img_exact WF1) | img_try (img_exact HFP) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_exact HFown.
- img_apply (VT mem); [img_try (img_exact Hgot) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_apply (VT mem); [img_try (img_exact Hcan) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_exact Hcv.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_exact MF1)].
- img_exact HAI1.
-
intros regs2 mem2 md2 HAR2 AP2 Hsbm2 A10_2 HFW2 Hfr2 Hpm2 HAI2.
rewrite R1ra. rewrite R1sp, HFWS in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (img_try (intros rr z -> Hcs; img_exact (AP2 z Hcs))).
assert (G21_2 : getr regs2 21 = w64 1) by (img_try (rewrite (K2 21%bv 21 ltac:(img_apply bv_eq; img_refl)) by (unfold acallee_saved; img_lia); img_exact Q21)).
unfold cfg_at. img_change (w64 FW_RET) with (Z_to_bv 64 FW_RET).
eapply (SRr_srealizes tfxsegs W _ _ T (fw_mid3 W regs2 mem2 md2 G21_2 A10_2) HAI2).
intros W3' c3 _ HAI3 (-> & md3 & -> & Hsbm3). cbn [cfg_model] in HAI3.
set (regs3 := regupd regs2 9%bv (getr regs2 9%bv)).
assert (R3 : forall rr : bv 5, getr regs3 rr = getr regs2 rr).
{ intros rr. (subst regs3; cbv beta). destruct (bv_eq_dec _ rr 9%bv) as [->|Hne]; [img_try (img_apply getr_same; intros X0; discriminate X0) | img_try (img_apply getr_other; img_exact Hne)]. }
assert (R3sp : spZ regs3 = sp0 - 2128) by (img_try (unfold spZ; rewrite R3, (K2 2%bv 2 ltac:(img_apply bv_eq; img_refl)) by (unfold acallee_saved; img_lia); img_exact R1sp)).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 176 <= a < sp0 - 2128) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> aview tfxsegs H mem2 a = aview tfxsegs H (ms_mem ms1) a)
by (img_try (intros a Hr Ha Hf; img_exact (Hfr2 a Hr Ha Hf))).
assert (HAR3 : AR tfxsegs B ly S W mem2 md3).
{ img_apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | | | | img_try (img_exact (YE0v.hs_kept_refl _ _))]; img_apply (same_but_materialized_frame md2 _ Hsbm3). }
eapply (SRr_srealizes tfxsegs W _ _ T); [| img_try (img_exact HAI3) |].
{ img_apply (fwr_check_srr B LAWS TB ly S W regs3 mem2 md3 p size HAR3).
- rewrite R3sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- rewrite R3sp. unfold YE0t.RC_SCR. unfold sp0 in *. img_lia.
- rewrite R3sp. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R3sp in Ha. unfold YE0t.RC_SCR in Ha. img_apply Hpm2; [img_lia | img_lia |]. img_apply PM1. img_apply Hpres. unfold sp0 in *. img_lia.
- rewrite R3, (K2 9%bv 9 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q9.
- rewrite R3, (K2 18%bv 18 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q18.
- rewrite R3. img_exact A10_2.
- img_lia.
- img_exact Hp0.
- img_lia.
- img_exact Ham.
- eapply range_addressable_agree; [|img_try (img_exact Hra)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
rewrite AV2 by (img_try (unfold sp0 in *; img_lia)). img_apply AV1; unfold sp0 in *; img_lia.
- intros s' Hs. rewrite AV2, AV1; [img_try (img_exact (Hhull s' Hs)) | | | | | ];
pose proof (shadow_addr_bounds p ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (p + size - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr p) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (p + size - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (p + size - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia. }
intros W4' c4 _ HAI4 (-> & regs4 & mem4 & md4 & -> & HAR4 & K4 & Hsbm4 & A10_4 & Hfr4 & Hpm4). cbn [cfg_model] in HAI4.
rewrite R3sp in Hfr4. unfold YE0t.RC_SCR in Hfr4.
assert (KK4 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs3 rr).
{ intros z rr -> H1 H2 H3 H5. img_exact (K4 z H1 H2 H3 H5). }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 72 <= a < sp0 - 2128) -> aview tfxsegs H mem4 a = aview tfxsegs H mem2 a) by (img_try (intros a Hr Ha; img_exact (Hfr4 a Hr Ha))).
set (E4 := Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (R4sp : getr regs4 2 = w64 (sp0 - 2128)).
{ rewrite (KK4 2 2%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite R3, (K2 2%bv 2 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), R4sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfxsegs (mrestrict H mem4) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. assert (Hoff : -56 <= off <= -8) by (img_try (do 7 (destruct j as [|j]; [img_try (cbn in Hj; injection Hj as <- <-; img_lia)|]); destruct j; discriminate)).
img_apply (VT mem2); [img_try (img_apply (VT (ms_mem ms1)); [img_exact (CK j rz off Hj) | intros b Hb; img_apply AV2; unfold sp0 in *; img_lia]) | img_try (intros b Hb; img_apply AV4; unfold sp0 in *; img_lia)]. }
pose proof (WS 0%nat 1%Z (-8)%Z eq_refl) as W0. replace (sp0 + -8) with (sp0 - 8) in W0 by img_lia.
pose proof (WS 1%nat 8%Z (-16)%Z eq_refl) as W1. replace (sp0 + -16) with (sp0 - 16) in W1 by img_lia.
pose proof (WS 2%nat 9%Z (-24)%Z eq_refl) as W2. replace (sp0 + -24) with (sp0 - 24) in W2 by img_lia.
pose proof (WS 3%nat 18%Z (-32)%Z eq_refl) as W3. replace (sp0 + -32) with (sp0 - 32) in W3 by img_lia.
pose proof (WS 4%nat 19%Z (-40)%Z eq_refl) as W4. replace (sp0 + -40) with (sp0 - 40) in W4 by img_lia.
pose proof (WS 5%nat 20%Z (-48)%Z eq_refl) as W5. replace (sp0 + -48) with (sp0 - 48) in W5 by img_lia.
pose proof (WS 6%nat 21%Z (-56)%Z eq_refl) as W6. replace (sp0 + -56) with (sp0 - 56) in W6 by img_lia.
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs4 (w64 YE0t.RC_END) mem4 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2128) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfxsegs (mrestrict H mem4) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem4) (sp0 - 2128) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs4 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). img_zside.
- img_zside.
- (subst off; cbv beta). replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by img_lia. img_exact Hv. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK4 0%nat 1%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by img_lia; img_exact W0)].
+ img_apply (CK4 1%nat 8%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by img_lia; img_exact W1)].
+ img_apply (CK4 2%nat 9%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by img_lia; img_exact W2)].
+ img_apply (CK4 3%nat 18%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by img_lia; img_exact W3)].
+ img_apply (CK4 4%nat 19%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by img_lia; img_exact W4)].
+ img_apply (CK4 5%nat 20%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by img_lia; img_exact W5)].
+ img_apply (CK4 6%nat 21%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by img_lia; img_exact W6)].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply (SRr_srealizes tfxsegs W _ _ T (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI4).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem4 z) by (img_try (intros z; img_apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md4) mat' md4)) T); [ | img_try (img_exact HAI5) | ].
{ eapply (SRr_ret_at tfxsegs tbl_icpt tbl_icpt_ok Hwx W E4); [img_try (img_exact HS5) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (img_try (intros jj rr Hnth; (subst E4; cbv beta); rewrite (ew_Ereg_extra regs4 _ jj); img_exact Hnth)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs4 rr) by (img_try (intros ii rr Hnth; (subst E4; cbv beta); img_exact (ew_Ereg_nat regs4 _ ii rr Hnth))).
assert (X32 : ew E4 32 = getr regs 1) by (img_try ((subst E4; cbv beta); img_exact (ew_Ereg_extra regs4 _ 0))). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra')).
assert (SBM56 : same_but_materialized (with_vm_backing (m_vm_lazy md4) mat5 md4) (with_vm_backing (m_vm_lazy md4) mat6 md4))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md4) mat6 mat5 md4); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBM56) as MF.
assert (AV5 : forall a, aview tfxsegs H (ms_mem ms5) a = aview tfxsegs H mem4 a) by (img_try (intros a; img_apply aview_same; img_apply MEQ5)).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs1 rr).
{ intros z rr Hrr H1 H2 H3 H5. rewrite (KK4 z rr Hrr H1 H2 H3 H5), R3. (subst rr; cbv beta). img_exact (K2 _ z eq_refl H1). }
img_apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md4) mat6 md4)).
+ img_apply (al_frame _ _ LAWS ly S W mem4 (with_vm_backing (m_vm_lazy md4) mat5 md4) (ms_mem ms5) _).
* img_apply (al_frame _ _ LAWS ly S W mem4 md4 mem4 _ HAR4); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | | | | img_try (img_exact (YE0v.hs_kept_refl _ _))]; img_apply (same_but_materialized_frame md4 _ (with_vm_backing_same md4 mat5)).
* intros a Hr Hown. img_apply AV5.
* intros a Hv. rewrite AV5. img_exact Hv.
* img_apply MF. * img_apply MF. * img_apply MF.
* img_exact (YE0v.hs_kept_eq _ _ _ MEQ5).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P2. img_apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by img_lia. img_lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P3, (Y 3%nat 3%bv eq_refl), (GG 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P4, (Y 4%nat 4%bv eq_refl), (GG 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P8. img_exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P9. img_exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P18. img_exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P19. img_exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P20. img_exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P21. img_exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 22%bv 22%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 23%bv 23%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 24%bv 24%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 25%bv 25%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 26%bv 26%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 27%bv 27%nat eq_refl ltac:(img_try (cbn; img_lia))).
+ eapply same_but_materialized_trans; [img_try (img_exact MF1)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm2)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm3)|].
eapply same_but_materialized_trans; [img_try (img_exact Hsbm4)|]. img_apply with_vm_backing_same.
+ rewrite P10, (Y 10%nat 10%bv eq_refl). img_exact A10_4.
+ img_apply (FT stderr_fields_after mem2); [img_try (img_exact WF2) | img_try (img_exact HFW2) | img_try (intros b Hb; rewrite AV5; img_apply AV4; img_lia)].
+ intros a Hr Hs Hf. rewrite AV5. rewrite AV4 by (img_try (unfold sp0 in *; img_lia)). rewrite AV2; [| img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia) | img_try (img_exact Hf)]. img_apply AV1; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia)].
+ intros a Hr Hf Hp. img_apply (apresent_same H mem4 (ms_mem ms5) a (MEQ5 _)). img_apply Hpm4. img_apply Hpm2; [img_try (img_exact Hr) | img_try (img_exact Hf)|]. img_apply PM1. img_exact Hp.
+ img_exact HAI6.
Qed.
End g.
End d.
