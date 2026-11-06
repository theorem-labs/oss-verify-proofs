(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF0q YF0o YF1g YF2n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize, kChunkHeaderSize in *.
Definition rT : nat := 32.
Definition rC : nat := 33.
Definition rSB : nat := 34.
Definition rM : nat := 35.
Definition rCL : nat := 36.
Definition rBASE : nat := 37.
Definition rHW : nat := 38.
Definition rN : nat := 39.
Definition rSHB : nat := 40.
Definition rSP : nat := 41.
Definition rN8 : nat := 42.
Definition rCNT8 : nat := 43.
Definition rCBP : nat := 44.
Definition rMU : nat := 45.
Definition rRG : nat := 46.
Definition rRI : nat := 47.
Definition rSZ : nat := 48.
Definition rJ1 : nat := 49.   Definition rJ2 : nat := 50.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c base rz nn hb1 cbp muc j1 j2 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33b74 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2.
Local Notation Mv := (YF2n.Mv base rz).
Local Notation Uv := (YF2n.Uv base rz).
Local Notation HWv := (YF2n.HWv hb1).
Local Notation SPv := (YF2n.SPv base rz).
Local Notation N8v := (YF2n.N8v nn).
Local Notation CNT8v := (YF2n.CNT8v nn).
Local Notation RIv := (YF2n.RIv ly).
Local Notation RGv := (YF2n.RGv ly c).
Local Notation SZv := (YF2n.SZv c).
Local Notation RELv := (YF2n.RELv ly c base).
Local Notation OFFv := (YF2n.OFFv ly base).
Local Notation XW := (YF2n.XW ly c base rz nn hb1 cbp muc j1 j2).
Local Notation E0 := (YF2n.E0 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation Er := (YF2n.Er ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation E2 := (YF2n.E2 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation E1 := (YF2n.E1 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqT := (YF2n.EqT ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqC := (YF2n.EqC ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqSB := (YF2n.EqSB ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqM := (YF2n.EqM ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqCL := (YF2n.EqCL ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqBASE := (YF2n.EqBASE ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqHW := (YF2n.EqHW ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqN := (YF2n.EqN ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqSHB := (YF2n.EqSHB ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqSP := (YF2n.EqSP ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqN8 := (YF2n.EqN8 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqCNT8 := (YF2n.EqCNT8 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqCBP := (YF2n.EqCBP ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqMU := (YF2n.EqMU ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqRG := (YF2n.EqRG ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqRI := (YF2n.EqRI ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqSZ := (YF2n.EqSZ ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqJ1 := (YF2n.EqJ1 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation EqJ2 := (YF2n.EqJ2 ly regs0 c base rz nn hb1 cbp muc j1 j2).
Local Notation R_STK := YF2n.R_STK.
Local Notation R_CB := YF2n.R_CB.
Local Notation R_HDR := YF2n.R_HDR.
Local Notation R_RGMU := YF2n.R_RGMU.
Local Notation R_CTX := YF2n.R_CTX.
Local Notation R_JST := YF2n.R_JST.
Local Notation REG0 := YF2n.REG0.
Local Notation R_MAG := YF2n.R_MAG.
Local Notation FFR := YF2n.FFR.
Local Notation SR0 := YF2n.SR0.
Local Notation SS0 := YF2n.SS0.
Local Notation LYB := (YF2n.LYB W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation class_facts := (YF2n.class_facts W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation derived_ranges := (YF2n.derived_ranges W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WINF := (YF2n.WINF ly base rz).
Local Notation WINS := (YF2n.WINS base rz nn).
Local Notation WIN := (YF2n.WIN ly regs0 base rz nn).
Local Notation win_sub := YF2n.win_sub.
Local Notation win_sub_sound := (YF2n.win_sub_sound ly regs0).
Local Notation WSK0 := YF2n.WSK0.
Local Notation WSKM := YF2n.WSKM.
Local Notation sk_ok := (YF2n.sk_ok ly regs0 base rz nn).
Local Notation WSK0_ok := (YF2n.WSK0_ok W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WSKM_ok := (YF2n.WSKM_ok W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation windows_WIN := (YF2n.windows_WIN ly regs0 base rz nn).
Local Notation WIN_zone := (YF2n.WIN_zone W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WIN_off := (YF2n.WIN_off W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation MEQ := (YF2n.MEQ ly regs0 mem0 base rz nn).
Local Notation MEQ_frame := (YF2n.MEQ_frame ly regs0 mem0 base rz nn).
Local Notation MEQ_0 := (YF2n.MEQ_0 ly regs0 mem0 base rz nn).
Local Notation st_ok_forget_reg := (YF2n.st_ok_forget_reg ly regs0).
Local Notation within := YF2n.within.
Local Notation within_mono := YF2n.within_mono.
Local Notation windows_within := (YF2n.windows_within ly regs0).
Local Notation frame_within := (YF2n.frame_within ly regs0).
Local Notation MEQP := (YF2n.MEQP mem0).
Local Notation MEQP_frame := (YF2n.MEQP_frame ly regs0 mem0).
Local Notation MEQP_weaken := (YF2n.MEQP_weaken mem0).
Local Notation MEQP_0 := (YF2n.MEQP_0 mem0).
Local Notation MEQ_of_MEQP := (YF2n.MEQ_of_MEQP ly regs0 mem0 base rz nn).
Local Notation WIN0 := (YF2n.WIN0 ly regs0 base rz).
Local Notation WINX := (YF2n.WINX ly regs0 base rz).
Local Notation MAGR := (YF2n.MAGR base rz).
Local Notation WIN0_WINX := (YF2n.WIN0_WINX ly regs0 base rz).
Local Notation WINX_WIN := (YF2n.WINX_WIN ly regs0 base rz nn).
Local Notation WINS_WIN := (YF2n.WINS_WIN ly regs0 base rz nn).
Local Notation MAGR_WINX := (YF2n.MAGR_WINX ly regs0 base rz).
Local Notation WINX_not_WINS := (YF2n.WINX_not_WINS W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WIN0_not_MAGR := (YF2n.WIN0_not_MAGR W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WSK0_within := (YF2n.WSK0_within W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation WSKM_within := (YF2n.WSKM_within W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation MAG := (YF2n.MAG W base rz).
Local Notation MAG_frame := (YF2n.MAG_frame W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation SHD := (YF2n.SHD base rz nn).
Local Notation SHD_frame := (YF2n.SHD_frame W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Local Notation all_disjoint_of_forall := YF2n.all_disjoint_of_forall.
Local Notation SREGS := YF2n.SREGS.
Local Notation at_CD := (YF2n.at_CD W ly regs0 mem0 md0 c base rz nn hb1).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hcb Hc Hbase Hrz Hnn Hhb1 Hhdr Hmag Hsh_pres Hrg Hjunk SEED].
Local Notation off_T := (YF2n.off_T W ly regs0 mem0 c base rz nn hb1 cbp muc j1 j2 FH).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, t_stats; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Ltac meq_acc KW :=
match goal with
| M : MEQP ?D ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQP_frame D E _ rs ma mb KW ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac mag_acc K0 :=
match goal with
| MG : MAG ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MG" in
pose proof (MAG_frame E _ rs ma mb K0 ltac:(img_try ((img_case; vm_compute); img_refl)) HFx MG) as M2; clear MG; rename M2 into MG
end.
Ltac shd_acc K0 :=
match goal with
| SH : SHD ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "SH" in
pose proof (SHD_frame E _ rs ma mb K0 ltac:(img_try ((img_case; vm_compute); img_refl)) HFx SH) as M2; clear SH; rename M2 into SH
end.
Ltac drop_frame := match goal with HFx : frame_of ?E ?rs ?ma ?mb |- _ => clear HFx end.
Ltac acc2 KW K0 := meq_acc KW; mag_acc K0; drop_frame.
Ltac acc3 KW K0 := meq_acc KW; mag_acc K0; shd_acc K0; drop_frame.
Ltac acc1 KW := meq_acc KW; drop_frame.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac pin_norm :=
pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end.
Definition SUBT : sv := SAlu ALU_ADD (SMd M_MUL (SOff 34%nat 0) (SLit (-1))) (SOff 35%nat 0).
Definition A4T : sv := SMd M_MUL (SOff 48%nat 0) (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_DIVU SUBT (SOff 48%nat 0)) (SLit 32)) (SLit 32)).
Lemma A4_val : forall (rho : nat -> Z) (sb m sz q r cc : Z),
rho 34%nat = sb -> rho 35%nat = m -> rho 48%nat = sz ->
0 <= sb <= m -> m < 2 ^ 64 -> m - sb = cc * 2 ^ 32 + (q * sz + r) -> 0 <= cc ->
0 <= q < 2 ^ 31 -> 0 <= r < sz -> 1 <= sz <= 2 ^ 31 -> q * sz + sz <= 2 ^ 32 ->
zev rho A4T = q * sz.
Proof.
intros rho sb m sz q r cc H34 H35 H48 Hsm Hm Hd Hcc Hq Hr Hsz Hqs.
unfold A4T, SUBT. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw, zmd_raw. rewrite H34, H35, H48, !Z.add_0_r.
rewrite (zcanon_id sb), (zcanon_id m), (zcanon_id sz) by (img_try (unfold M64; zlia)).
rewrite zcanon_negadd by (img_try (unfold M64; zlia)).
replace ((m - sb) mod 2 ^ 32) with (q * sz + r).
2:{ rewrite Hd. rewrite (Z.add_comm (cc * 2 ^ 32) (q * sz + r)), Z_mod_plus_full. symmetry. img_apply Z.mod_small. nia. }
rewrite (Z.mod_small sz) by zlia.
replace (sz =? 0) with false by (img_try (symmetry; img_apply Z.eqb_neq; zlia)).
replace ((q * sz + r) / sz) with q by (img_try (img_apply (Z.div_unique_pos _ _ q r); zlia)).
rewrite bv_swrap_small by (img_try (unfold bv_half_modulus, bv_modulus; img_change (2 ^ Z.of_N 32 / 2) with (2 ^ 31); zlia)).
rewrite (bv_wrap_small 64 q) by (img_try (unfold bv_modulus; img_change (2 ^ Z.of_N 64) with (2 ^ 64); zlia)).
img_change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by zlia.
rewrite (zcanon_id (q * 2 ^ 32)) by (img_try (unfold M64; zlia)). rewrite Z_div_mult by zlia. rewrite (zcanon_id q) by (img_try (unfold M64; zlia)).
rewrite Z.mul_comm. img_apply zcanon_id. unfold M64; nia.
Qed.
Definition SZH : sv :=
SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 36 0) (SLit 63)) (SLit 63)) (SAlu ALU_SRL (SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))) (SLit 1)))
(SAlu ALU_SLL (SLit 512) (SAlu ALU_SRL (SOff 36 (-16)) (SLit 1))).
Lemma SZ_hi_val : forall (rho : nat -> Z) cl, 17 <= cl <= 30 -> rho 36%nat = cl -> zev rho SZH = class_size cl.
Proof.
intros rho cl Hcl Hr. rewrite (zev_only 36 rho SZH eq_refl). rewrite Hr.
assert (C : forallb (fun i => zev (fun _ => 17 + Z.of_nat i) SZH =? class_size (17 + Z.of_nat i)) (seq 0 14) = true) by (img_try ((img_case; vm_compute); img_refl)).
pose proof (forallb_seq_In _ 14 (Z.to_nat (cl - 17)) C ltac:(img_try (zlia))) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by zlia.
replace (17 + (cl - 17)) with cl in Hx by zlia. apply Z.eqb_eq in Hx. img_exact Hx.
Qed.
Lemma SLLW_lit : forall (rho : nat -> Z) v X, 0 <= v < 2 ^ 31 -> Z.land (zev rho X mod 2 ^ 32) 31 = 0 -> zev rho (SAluw ALU_SLL (SLit v) X) = v.
Proof.
intros rho v X Hv HX. cbn [zev zalu_raw]. unfold zalu_raw. rewrite HX. rewrite (zcanon_id v) by (img_try (unfold M64; zlia)).
rewrite (Z.mod_small v) by zlia. rewrite Z.shiftl_0_r.
rewrite bv_swrap_small by (img_try (unfold bv_half_modulus, bv_modulus; img_change (2 ^ Z.of_N 32 / 2) with (2 ^ 31); zlia)).
img_apply bv_wrap_small. unfold bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). zlia.
Qed.
Lemma low5_M8 : forall x, x mod 4 = 0 -> Z.land (zcanon (Z.shiftl x (Z.land (zcanon 3) 63)) mod 2 ^ 32) 31 = 0.
Proof.
intros x Hx. img_change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by zlia. img_change 31 with (Z.ones 5).
rewrite land_ones_mod by (img_try (try zlia; img_apply Z.mod_pos_bound; zlia)). unfold zcanon, M64. img_change (2 ^ 3) with 8. img_change (2 ^ 5) with 32. zlia.
Qed.
Definition T0T : sv := SAlu ALU_XOR (SOff 38%nat 0) (SAlu ALU_AND (SAlu ALU_XOR (SOff 38%nat 0) (SLit 0)) (SLit 255)).
Lemma T0_val : forall (rho : nat -> Z) hb, 0 <= hb < 256 -> rho 38%nat = 3 + 256 * hb -> zev rho T0T = 256 * hb.
Proof.
intros rho hb Hb Hr. rewrite (zev_only 38 rho T0T eq_refl). rewrite Hr.
assert (C : forallb (fun i => zev (fun _ => 3 + 256 * Z.of_nat i) T0T =? 256 * Z.of_nat i) (seq 0 256) = true) by (img_try ((img_case; vm_compute); img_refl)).
pose proof (forallb_seq_In _ 256 (Z.to_nat hb) C ltac:(img_try (zlia))) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by zlia.
apply Z.eqb_eq in Hx. img_exact Hx.
Qed.
Definition A1T : sv :=
SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_SLL (SExt false 16 (SAlu ALU_SRL (SOff 38%nat (-3)) (SLit 16))) (SLit 32)) (SOff 39%nat 0)) (SLit 7)) (SLit (-8)).
Lemma A1_val : forall (rho : nat -> Z) hw n hb, rho 38%nat = hw -> rho 39%nat = n -> hw = 3 + 256 * hb -> 0 <= hb < 256 -> 1 <= n < 2 ^ 28 ->
zev rho A1T = (n + 7) / 8 * 8.
Proof.
intros rho hw n hb H38 H39 Hhw Hhb Hn. unfold A1T. cbn [zev zalu_raw]. unfold zalu_raw. rewrite H38, H39, Hhw, Z.add_0_r.
replace (3 + 256 * hb + -3) with (256 * hb) by zlia. rewrite (zcanon_id (256 * hb)) by (img_try (unfold M64; zlia)).
img_change (Z.land (zcanon 16) 63) with 16. img_change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftr_div_pow2 by zlia. rewrite (Z.div_small (256 * hb) (2 ^ 16)) by zlia.
img_change (zcanon (zcanon 0 mod 2 ^ Z.of_N 16)) with 0. rewrite Z.shiftl_0_l. img_change (zcanon 0) with 0. rewrite Z.lor_0_l.
rewrite (zcanon_id n), (zcanon_id 7) by (img_try (unfold M64; zlia)). rewrite (zcanon_id n) by (img_try (unfold M64; zlia)). rewrite (zcanon_id (n + 7)) by (img_try (unfold M64; zlia)).
img_change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite zcanon_id by (img_try (unfold M64; zlia)). zlia.
Qed.
Definition A2T : sv := SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 34%nat 0) (SLit 2475880078570760549664030720)) (SAlu ALU_SLL (SOff 37%nat 0) (SLit 27))) (SLit 59).
Lemma A2_val : forall (rho : nat -> Z) sb b cc rel, rho 34%nat = sb -> rho 37%nat = b -> b - sb = cc * 2 ^ 32 + rel -> 0 <= rel < 2 ^ 32 -> 0 <= cc < 32 ->
0 <= sb -> sb <= b < 2 ^ 64 -> zev rho A2T = cc.
Proof.
intros rho sb b cc rel H34 H37 Hd Hrel Hcc Hsb Hb. unfold A2T. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw, zmd_raw. rewrite H34, H37, !Z.add_0_r.
img_change (Z.land (zcanon 27) 63) with 27. img_change (Z.land (zcanon 59) 63) with 59. img_change (zcanon 2475880078570760549664030720) with (2 ^ 64 - 2 ^ 27).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by zlia. rewrite (zcanon_id sb), (zcanon_id b) by (img_try (unfold M64; zlia)). unfold zcanon, M64. nia.
Qed.
Lemma segRC : SRr tfxsegs W cfg0 at_CD.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_within E0 HE0) as K00. pose proof (within_mono _ _ E0 _ WIN0_WINX K00) as KW0.
pose proof (MEQP_0 WINX) as MQ.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dCB1 & dCB2 & dCBal & dB1 & dB2 & dBal & dBeq & dM1 & dU1 & dMal & dUal & dBM & dUN &
dHW1 & dHW2 & dN1 & dRZ & dSP1 & dSP2 & dN8 & dN8b & dC8 & dI1 & dG0 & dG1 & dG2 & dI2 & dMU & dX1 & dX2 & dOFF & dCc1 & dCc2 & dJ1 & dJ2).
pose proof Hcb as (C1 & C2 & C3 & C4 & C5).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18 & L19 & L20 & L21 & L22).
assert (dM4 : Mv mod 4 = 0) by (img_try (clear - dMal; img_apply (mod0_factor _ 4 4); [img_try (zlia) | img_try (img_exact dMal)])).
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - dT1 dT2; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = SB) by (img_try (unfold rho_of; rewrite EqSB; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2; numconst; zlia)).
assert (R35 : rho_of E0 35%nat = Mv) by (img_try (unfold rho_of; rewrite EqM; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2 dM1 dBM dUN dRZ dN1 K1; numconst; zlia)).
assert (R36 : rho_of E0 36%nat = c) by (img_try (unfold rho_of; rewrite EqCL; unfold w64; img_apply unsigned_lit_small; clear - Hc; zlia)).
assert (R37 : rho_of E0 37%nat = base) by (img_try (unfold rho_of; rewrite EqBASE; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2 K1; numconst; zlia)).
assert (R38 : rho_of E0 38%nat = HWv) by (img_try (unfold rho_of; rewrite EqHW; unfold w64; img_apply unsigned_lit_small; clear - dHW1; zlia)).
assert (R39 : rho_of E0 39%nat = nn) by (img_try (unfold rho_of; rewrite EqN; unfold w64; img_apply unsigned_lit_small; clear - dN1; zlia)).
assert (R40 : rho_of E0 40%nat = SHADOW_OFF) by (img_try (unfold rho_of; rewrite EqSHB; unfold w64; img_apply unsigned_lit_small; numconst; zlia)).
assert (R41 : rho_of E0 41%nat = SPv) by (img_try (unfold rho_of; rewrite EqSP; unfold w64; img_apply unsigned_lit_small; clear - dSP1 dSP2 dC8; numconst; zlia)).
assert (R42 : rho_of E0 42%nat = N8v) by (img_try (unfold rho_of; rewrite EqN8; unfold w64; img_apply unsigned_lit_small; clear - dN8 dN8b dN1 dC8; zlia)).
assert (R43 : rho_of E0 43%nat = CNT8v) by (img_try (unfold rho_of; rewrite EqCNT8; unfold w64; img_apply unsigned_lit_small; clear - dSP1 dSP2 dC8; numconst; zlia)).
assert (R44 : rho_of E0 44%nat = cbp) by (img_try (unfold rho_of; rewrite EqCBP; unfold w64; img_apply unsigned_lit_small; clear - dK1 dCB1 dCB2; numconst; zlia)).
assert (R45 : rho_of E0 45%nat = muc) by (img_try (unfold rho_of; rewrite EqMU; unfold w64; img_apply unsigned_lit_small; clear - dMU; numconst; zlia)).
assert (R46 : rho_of E0 46%nat = RGv) by (img_try (unfold rho_of; rewrite EqRG; unfold w64; img_apply unsigned_lit_small; clear - dS1 dI1 dG0 dG1 dG2 dI2; numconst; zlia)).
assert (R47 : rho_of E0 47%nat = RIv) by (img_try (unfold rho_of; rewrite EqRI; unfold w64; img_apply unsigned_lit_small; clear - dS1 dI1 dI2; numconst; zlia)).
assert (R48 : rho_of E0 48%nat = SZv) by (img_try (unfold rho_of; rewrite EqSZ; unfold w64; img_apply unsigned_lit_small; clear - K1; numconst; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV32 : bv_unsigned (ew E0 32) = T) by img_exact R32.
assert (BV33 : bv_unsigned (ew E0 33) = ly_C ly) by (img_try (rewrite EqC; unfold w64; img_apply unsigned_lit_small; clear - dCc1 dCc2; numconst; zlia)).
assert (BV35 : bv_unsigned (ew E0 35) = Mv) by img_exact R35.
assert (BV37 : bv_unsigned (ew E0 37) = base) by img_exact R37.
assert (BV44 : bv_unsigned (ew E0 44) = cbp) by img_exact R44.
assert (BV46 : bv_unsigned (ew E0 46) = RGv) by img_exact R46.
assert (QC : (Mv - SB) / 2 ^ 32 = c).
{ symmetry. img_apply (Z.div_unique_pos _ _ _ (RELv + rz - 16)); clear - dBeq dM1 dRZ dX1 dX2 dMU dUN dU1 dN1 K3 Hc; numconst; zlia. }
assert (A4V : zev (rho_of E0) A4T = RELv).
{ destruct Hbase as (X1 & X2 & X3 & X4 & X5).
assert (HQ : SZv * (RELv / SZv) = RELv) by (img_try (clear - X3 K1; symmetry; img_apply Znumtheory.Zdivide_Zdiv_eq; [img_try (zlia)|]; img_apply Z.mod_divide; zlia)).
rewrite (A4_val (rho_of E0) SB Mv SZv (RELv / SZv) (rz - 16) c R34 R35 R48).
- clear - HQ. zlia.
- clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; numconst; zlia.
- clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; numconst; zlia.
- clear - dBeq dM1 HQ K3. rewrite (Z.mul_comm (RELv / SZv) SZv), HQ. zlia.
- clear - Hc; zlia.
- clear - X1 X2 dMU K1. split; [img_try (img_apply Z.div_pos; zlia)|]. img_apply Z.div_lt_upper_bound; [img_try (zlia)|]. numconst. zlia.
- clear - dRZ dUN dU1 dN1. zlia.
- clear - K1. numconst. zlia.
- clear - X1 X2 dMU K1 HQ. rewrite (Z.mul_comm (RELv / SZv) SZv), HQ. numconst. zlia. }
eassert (TAIL : forall (E' : env) (ms' : machine_state) (mat' : list word),
(forall k, (k < aHAVf)%nat -> ew E' k = ew E0 k) ->
st_ok tfxsegs E' _ (restrict (w_H W) ms') ->
MEQP WINX (ms_mem ms') -> MAG (ms_mem ms') ->
SRr tfxsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy md0) mat' md0)) at_CD).
2:{
destruct (Z.eq_dec rz 16) as [HRZ|HRZ].
-
pose proof KW0 as KW.
assert (MG : forall m : word -> option byte, MAG m) by (img_try (intros m Hne; exfalso; img_exact (Hne HRZ))).
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R35 R34 dS1 dS2 dB1 dB2 dM1 dRZ K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R35 R34 dS1 dS2 dB1 dB2 dM1 dRZ K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33bc4 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 36%nat 0)) in HS; [ | img_try (intros X; discriminate) | img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia;
rewrite (zcanon_id SB) by (clear - dS1 dS2; unfold M64; numconst; zlia); rewrite (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia);
rewrite zcanon_negadd by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); rewrite QC;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia); img_refl) ]. unpin HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 36%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia;
rewrite (zcanon_id SB) by (clear - dS1 dS2; unfold M64; numconst; zlia); rewrite (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia);
rewrite zcanon_negadd by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); rewrite QC;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia); rewrite (zcanon_id 31) by (unfold M64; zlia);
img_change 31 with (Z.ones 5); rewrite land_ones_mod by (clear - Hc; zlia); rewrite Z.mod_small by (clear - Hc; zlia); rewrite zcanon_id by (clear - Hc; unfold M64; zlia); img_refl) ].
unpin HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
+
match goal with Hb : branch_taken _ _ _ = true |- _ =>
assert (HC17 : 17 <= c) by (img_try (clear - Hb R36 Hc; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia)); clear Hb end.
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c24 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 48%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 48%nat 0) = zev (rho_of E0) SZH); rewrite (SZ_hi_val (rho_of E0) c) by (first [img_exact R36 | clear - HC17 Hc; zlia]);
cbn [zev]; rewrite R48, Z.add_0_r; img_apply zcanon_id; clear - K1; unfold YF2n.SZv in K1; unfold M64; numconst; zlia) ].
unpin HS.
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 46%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 7) with 128; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.RGv; clear - Hc dG0 dG1 dG2 dI1 dI2 dS1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c54 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 0) = zcanon (if zev (rho_of E0) (SOff 45%nat 0) <? zcanon (zev (rho_of E0) A4T + zev (rho_of E0) (SOff 48%nat 0)) then 1 else 0));
rewrite A4V; cbn [zev]; rewrite R45, R48, !Z.add_0_r; rewrite (zcanon_id muc), (zcanon_id SZv), (zcanon_id (RELv + SZv)) by (clear - dMU dX1 dX2 K1; unfold M64; numconst; zlia);
destruct (Z.ltb_spec muc (RELv + SZv)); [exfalso; clear - dX2 H; zlia | img_refl]) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c58 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 37%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 37%nat 0) = zcanon (zev (rho_of E0) (SAlu ALU_ADD (SOff 34%nat 0) (SAlu ALU_SLL (SOff 36%nat 0) (SLit 32))) + zev (rho_of E0) A4T));
rewrite A4V; cbn [zev zalu_raw]; unfold zalu_raw; rewrite R34, R36, R37, !Z.add_0_r; img_change (Z.land (zcanon 32) 63) with 32; rewrite Z.shiftl_mul_pow2 by zlia;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
clear - dS1 dS2 dB1 dB2 dBeq K1 K3 Hc dX1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c60 + D_150). acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
2:{ exfalso. match goal with Hb : branch_taken _ _ _ = false |- _ => clear - Hb R37 R35 dS1 dS2 dB1 dB2 dM1 dRZ K1 HRZ; zbranch Hb; apply Z.eqb_neq in Hb; zlia end. }
match goal with Hb : branch_taken _ _ _ = true |- _ => clear Hb end. uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c9c + D_150). acc1 KW.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => specialize (MG (ms_mem msx)) end.
apply (st_ok_pin_regU _ _ _ 13%bv (SLit 3)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 3) = zev (rho_of E0) (SAluw ALU_SLL (SLit 3) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 3); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 255)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 255) = zev (rho_of E0) (SAluw ALU_SLL (SLit 255) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 255); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS.
apply (st_ok_forget_reg _ _ _ 17%bv 54%nat) in HS; [ | img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl) ].
evalS HS.
eapply TAIL; [ | img_try (img_exact HS) | img_try (img_exact MQ) | img_try (img_exact MG) ]. intros k Hk; img_apply ew_havoc_old; img_exact Hk.
+
match goal with Hb : branch_taken _ _ _ = false |- _ =>
assert (HC17 : c <= 16) by (img_try (clear - Hb R36 Hc; zbranch Hb; apply Bool.negb_false_iff in Hb; apply Z.ltb_lt in Hb; zlia)); clear Hb end.
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c24 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 48%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 5) with 32; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.SZv, class_size; replace (c =? 31) with false by (symmetry; img_apply Z.eqb_neq; clear - Hc; zlia);
replace (c <=? 16) with true by (symmetry; img_apply Z.leb_le; img_exact HC17); rewrite !zcanon_id by (clear - Hc; unfold M64; zlia); clear - Hc; zlia) ].
unpin HS.
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 46%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 7) with 128; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.RGv; clear - Hc dG0 dG1 dG2 dI1 dI2 dS1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c54 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 0) = zcanon (if zev (rho_of E0) (SOff 45%nat 0) <? zcanon (zev (rho_of E0) A4T + zev (rho_of E0) (SOff 48%nat 0)) then 1 else 0));
rewrite A4V; cbn [zev]; rewrite R45, R48, !Z.add_0_r; rewrite (zcanon_id muc), (zcanon_id SZv), (zcanon_id (RELv + SZv)) by (clear - dMU dX1 dX2 K1; unfold M64; numconst; zlia);
destruct (Z.ltb_spec muc (RELv + SZv)); [exfalso; clear - dX2 H; zlia | img_refl]) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c58 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 37%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 37%nat 0) = zcanon (zev (rho_of E0) (SAlu ALU_ADD (SOff 34%nat 0) (SAlu ALU_SLL (SOff 36%nat 0) (SLit 32))) + zev (rho_of E0) A4T));
rewrite A4V; cbn [zev zalu_raw]; unfold zalu_raw; rewrite R34, R36, R37, !Z.add_0_r; img_change (Z.land (zcanon 32) 63) with 32; rewrite Z.shiftl_mul_pow2 by zlia;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
clear - dS1 dS2 dB1 dB2 dBeq K1 K3 Hc dX1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c60 + D_150). acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
2:{ exfalso. match goal with Hb : branch_taken _ _ _ = false |- _ => clear - Hb R37 R35 dS1 dS2 dB1 dB2 dM1 dRZ K1 HRZ; zbranch Hb; apply Z.eqb_neq in Hb; zlia end. }
match goal with Hb : branch_taken _ _ _ = true |- _ => clear Hb end. uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c9c + D_150). acc1 KW.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => specialize (MG (ms_mem msx)) end.
apply (st_ok_pin_regU _ _ _ 13%bv (SLit 3)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 3) = zev (rho_of E0) (SAluw ALU_SLL (SLit 3) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 3); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 255)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 255) = zev (rho_of E0) (SAluw ALU_SLL (SLit 255) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 255); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS.
apply (st_ok_forget_reg _ _ _ 17%bv 54%nat) in HS; [ | img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl) ].
evalS HS.
eapply TAIL; [ | img_try (img_exact HS) | img_try (img_exact MQ) | img_try (img_exact MG) ]. intros k Hk; img_apply ew_havoc_old; img_exact Hk.
-
pose proof (WSKM_within E0 HE0 HRZ) as KW.
assert (R32z : 32 <= rz). { destruct Hrz as (Q1 & Q2 & Q3). apply Z.mod_divide in Q2 as [q Hq]; [|img_try (zlia)]. assert (Hq1 : q <> 1) by (img_try (intros ->; img_apply HRZ; zlia)). clear - Hq Hq1 Q1. zlia. }
apply (st_ok_add_region _ _ _ R_MAG) in HS;
[ | img_refl
| img_try (unfold YF2n.R_MAG, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst]; rewrite BV37;
split; [clear - dS1 dS2 dB1 dB2 K1; numconst; zlia|]; split; [clear - dS1 dS2 dB1 dB2 K1; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - dS1 dS2 dB1 dB2 K1 Ho; numconst; zlia) | img_apply (proj2 (proj2 Hhdr)); clear - Ho K1; zlia]|];
img_apply Forall_cons; [eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia | rewrite Z.add_0_r; img_exact (Hmag HRZ)] | img_apply Forall_nil])
| img_try (unfold YF2n.R_MAG; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?BV2, ?BV32, ?BV33, ?BV35, ?BV37, ?BV44, ?BV46;
unfold T, SB, sp0 in *;
clear - L1 L2 L3 L4 L5 L6 L10 L11 L12 L14 L16 L17 L20 dT1 dT2 dS1 dS2 dK1 dK2 dCB1 dCB2 dB1 dB2 dM1 dI1 dI2 dG0 dG1 dG2 dCc1 dCc2 K1 R32z Hlo Hhi Hc C2;
numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R35 R34 dS1 dS2 dB1 dB2 dM1 dRZ K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R35 R34 dS1 dS2 dB1 dB2 dM1 dRZ K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33bc4 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 36%nat 0)) in HS; [ | img_try (intros X; discriminate) | img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia;
rewrite (zcanon_id SB) by (clear - dS1 dS2; unfold M64; numconst; zlia); rewrite (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia);
rewrite zcanon_negadd by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); rewrite QC;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia); img_refl) ]. unpin HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 36%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia;
rewrite (zcanon_id SB) by (clear - dS1 dS2; unfold M64; numconst; zlia); rewrite (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia);
rewrite zcanon_negadd by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); rewrite QC;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia); rewrite (zcanon_id 31) by (unfold M64; zlia);
img_change 31 with (Z.ones 5); rewrite land_ones_mod by (clear - Hc; zlia); rewrite Z.mod_small by (clear - Hc; zlia); rewrite zcanon_id by (clear - Hc; unfold M64; zlia); img_refl) ].
unpin HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
+
match goal with Hb : branch_taken _ _ _ = true |- _ =>
assert (HC17 : 17 <= c) by (img_try (clear - Hb R36 Hc; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia)); clear Hb end.
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c24 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 48%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 48%nat 0) = zev (rho_of E0) SZH); rewrite (SZ_hi_val (rho_of E0) c) by (first [img_exact R36 | clear - HC17 Hc; zlia]);
cbn [zev]; rewrite R48, Z.add_0_r; img_apply zcanon_id; clear - K1; unfold YF2n.SZv in K1; unfold M64; numconst; zlia) ].
unpin HS.
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 46%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 7) with 128; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.RGv; clear - Hc dG0 dG1 dG2 dI1 dI2 dS1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c54 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 0) = zcanon (if zev (rho_of E0) (SOff 45%nat 0) <? zcanon (zev (rho_of E0) A4T + zev (rho_of E0) (SOff 48%nat 0)) then 1 else 0));
rewrite A4V; cbn [zev]; rewrite R45, R48, !Z.add_0_r; rewrite (zcanon_id muc), (zcanon_id SZv), (zcanon_id (RELv + SZv)) by (clear - dMU dX1 dX2 K1; unfold M64; numconst; zlia);
destruct (Z.ltb_spec muc (RELv + SZv)); [exfalso; clear - dX2 H; zlia | img_refl]) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c58 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 37%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 37%nat 0) = zcanon (zev (rho_of E0) (SAlu ALU_ADD (SOff 34%nat 0) (SAlu ALU_SLL (SOff 36%nat 0) (SLit 32))) + zev (rho_of E0) A4T));
rewrite A4V; cbn [zev zalu_raw]; unfold zalu_raw; rewrite R34, R36, R37, !Z.add_0_r; img_change (Z.land (zcanon 32) 63) with 32; rewrite Z.shiftl_mul_pow2 by zlia;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
clear - dS1 dS2 dB1 dB2 dBeq K1 K3 Hc dX1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c60 + D_150). acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R35 dS1 dS2 dB1 dB2 dM1 dRZ K1 HRZ; zbranch Hb; apply Z.eqb_eq in Hb; zlia end. }
match goal with Hb : branch_taken _ _ _ = false |- _ => clear Hb end. uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c9c + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SLit 3)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 3) = zev (rho_of E0) (SAluw ALU_SLL (SLit 3) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 3); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 255)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 255) = zev (rho_of E0) (SAluw ALU_SLL (SLit 255) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 255); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (MG : MAG (ms_mem msx)) by
(img_try (intros _; split;
[ img_try (memv HS 0%nat 0%nat; [rewrite BV37; zlia | img_refl | zlia])
| img_try (intros a Ha; eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
[img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV37; clear - Ha; zlia | off_by ltac:(clear - Ha dS1 dS2 dB1 dB2 K1; numconst; zlia) ]) ])) end.
lazymatch type of HS with st_ok _ _ ?ss _ => let rs := img_ev (ss_mem ss) in
lazymatch rs with ?r0 :: ?rest => apply (st_ok_submem tfxsegs _ _ _ rest) in HS; [ | img_try (img_apply submem_drop; img_apply submem_refl) | img_try ((img_case; vm_compute); img_refl) ] end end.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS.
apply (st_ok_forget_reg _ _ _ 17%bv 54%nat) in HS; [ | img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl) ].
evalS HS.
eapply TAIL; [ | img_try (img_exact HS) | img_try (img_exact MQ) | img_try (img_exact MG) ]. intros k Hk; img_apply ew_havoc_old; img_exact Hk.
+
match goal with Hb : branch_taken _ _ _ = false |- _ =>
assert (HC17 : c <= 16) by (img_try (clear - Hb R36 Hc; zbranch Hb; apply Bool.negb_false_iff in Hb; apply Z.ltb_lt in Hb; zlia)); clear Hb end.
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c24 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 48%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 5) with 32; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.SZv, class_size; replace (c =? 31) with false by (symmetry; img_apply Z.eqb_neq; clear - Hc; zlia);
replace (c <=? 16) with true by (symmetry; img_apply Z.leb_le; img_exact HC17); rewrite !zcanon_id by (clear - Hc; unfold M64; zlia); clear - Hc; zlia) ].
unpin HS.
srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 46%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 7) with 128; rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold YF2n.RGv; clear - Hc dG0 dG1 dG2 dI1 dI2 dS1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c54 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 0) = zcanon (if zev (rho_of E0) (SOff 45%nat 0) <? zcanon (zev (rho_of E0) A4T + zev (rho_of E0) (SOff 48%nat 0)) then 1 else 0));
rewrite A4V; cbn [zev]; rewrite R45, R48, !Z.add_0_r; rewrite (zcanon_id muc), (zcanon_id SZv), (zcanon_id (RELv + SZv)) by (clear - dMU dX1 dX2 K1; unfold M64; numconst; zlia);
destruct (Z.ltb_spec muc (RELv + SZv)); [exfalso; clear - dX2 H; zlia | img_refl]) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c58 + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SOff 37%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SOff 37%nat 0) = zcanon (zev (rho_of E0) (SAlu ALU_ADD (SOff 34%nat 0) (SAlu ALU_SLL (SOff 36%nat 0) (SLit 32))) + zev (rho_of E0) A4T));
rewrite A4V; cbn [zev zalu_raw]; unfold zalu_raw; rewrite R34, R36, R37, !Z.add_0_r; img_change (Z.land (zcanon 32) 63) with 32; rewrite Z.shiftl_mul_pow2 by zlia;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
clear - dS1 dS2 dB1 dB2 dBeq K1 K3 Hc dX1; numconst; zcanon_simp; zlia) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c60 + D_150). acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc1 KW.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. match goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb R37 R35 dS1 dS2 dB1 dB2 dM1 dRZ K1 HRZ; zbranch Hb; apply Z.eqb_eq in Hb; zlia end. }
match goal with Hb : branch_taken _ _ _ = false |- _ => clear Hb end. uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33c9c + D_150). acc1 KW.
apply (st_ok_pin_regU _ _ _ 13%bv (SLit 3)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 3) = zev (rho_of E0) (SAluw ALU_SLL (SLit 3) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 3); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 255)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit 255) = zev (rho_of E0) (SAluw ALU_SLL (SLit 255) (SAlu ALU_SLL (SOff 35%nat 0) (SLit 3))));
rewrite (SLLW_lit (rho_of E0) 255); [img_refl | zlia | cbn [zev]; rewrite R35, Z.add_0_r, (zcanon_id Mv) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia); img_apply low5_M8; img_exact dM4]) ].
unpin HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (MG : MAG (ms_mem msx)) by
(img_try (intros _; split;
[ img_try (memv HS 0%nat 0%nat; [rewrite BV37; zlia | img_refl | zlia])
| img_try (intros a Ha; eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
[img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV37; clear - Ha; zlia | off_by ltac:(clear - Ha dS1 dS2 dB1 dB2 K1; numconst; zlia) ]) ])) end.
lazymatch type of HS with st_ok _ _ ?ss _ => let rs := img_ev (ss_mem ss) in
lazymatch rs with ?r0 :: ?rest => apply (st_ok_submem tfxsegs _ _ _ rest) in HS; [ | img_try (img_apply submem_drop; img_apply submem_refl) | img_try ((img_case; vm_compute); img_refl) ] end end.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS.
apply (st_ok_forget_reg _ _ _ 17%bv 54%nat) in HS; [ | img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl) ].
evalS HS.
eapply TAIL; [ | img_try (img_exact HS) | img_try (img_exact MQ) | img_try (img_exact MG) ]. intros k Hk; img_apply ew_havoc_old; img_exact Hk. }
clear HS MQ. intros E' ms' mat' HE' HS MQ MG.
assert (HR : forall k, (k < aHAVf)%nat -> rho_of E' k = rho_of E0 k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE' k Hk); img_refl)).
assert (Q32 : rho_of E' 32%nat = T) by (img_try (rewrite (HR 32%nat ltac:((img_case; cbv); zlia)); img_exact R32)).
assert (Q34 : rho_of E' 34%nat = SB) by (img_try (rewrite (HR 34%nat ltac:((img_case; cbv); zlia)); img_exact R34)).
assert (Q35 : rho_of E' 35%nat = Mv) by (img_try (rewrite (HR 35%nat ltac:((img_case; cbv); zlia)); img_exact R35)).
assert (Q36 : rho_of E' 36%nat = c) by (img_try (rewrite (HR 36%nat ltac:((img_case; cbv); zlia)); img_exact R36)).
assert (Q37 : rho_of E' 37%nat = base) by (img_try (rewrite (HR 37%nat ltac:((img_case; cbv); zlia)); img_exact R37)).
assert (Q38 : rho_of E' 38%nat = HWv) by (img_try (rewrite (HR 38%nat ltac:((img_case; cbv); zlia)); img_exact R38)).
assert (Q39 : rho_of E' 39%nat = nn) by (img_try (rewrite (HR 39%nat ltac:((img_case; cbv); zlia)); img_exact R39)).
assert (Q40 : rho_of E' 40%nat = SHADOW_OFF) by (img_try (rewrite (HR 40%nat ltac:((img_case; cbv); zlia)); img_exact R40)).
assert (Q41 : rho_of E' 41%nat = SPv) by (img_try (rewrite (HR 41%nat ltac:((img_case; cbv); zlia)); img_exact R41)).
assert (Q42 : rho_of E' 42%nat = N8v) by (img_try (rewrite (HR 42%nat ltac:((img_case; cbv); zlia)); img_exact R42)).
assert (Q43 : rho_of E' 43%nat = CNT8v) by (img_try (rewrite (HR 43%nat ltac:((img_case; cbv); zlia)); img_exact R43)).
assert (Q44 : rho_of E' 44%nat = cbp) by (img_try (rewrite (HR 44%nat ltac:((img_case; cbv); zlia)); img_exact R44)).
assert (Q48 : rho_of E' 48%nat = SZv) by (img_try (rewrite (HR 48%nat ltac:((img_case; cbv); zlia)); img_exact R48)).
assert (PV2 : bv_unsigned (ew E' 2) = sp0) by (img_try (rewrite (HE' 2%nat ltac:((img_case; cbv); zlia)); img_exact BV2)).
assert (PV32 : bv_unsigned (ew E' 32) = T) by img_exact Q32.
assert (PV35 : bv_unsigned (ew E' 35) = Mv) by img_exact Q35.
assert (PV37 : bv_unsigned (ew E' 37) = base) by img_exact Q37.
assert (PV44 : bv_unsigned (ew E' 44) = cbp) by img_exact Q44.
assert (PV33 : bv_unsigned (ew E' 33) = ly_C ly) by (img_try (rewrite (HE' 33%nat ltac:((img_case; cbv); zlia)); img_exact BV33)).
assert (PV46 : bv_unsigned (ew E' 46) = RGv) by (img_try (rewrite (HE' 46%nat ltac:((img_case; cbv); zlia)); img_exact BV46)).
pose proof (WSK0_within E' HE') as K0. pose proof (within_mono _ _ E' _ WIN0_WINX K0) as KW.
clear R32 R34 R35 R36 R37 R38 R39 R40 R41 R42 R43 R44 R45 R46 R47 R48 BV2 BV32 BV33 BV35 BV37 BV44 BV46 KW0 K00 HE0.
srr_run_sh tfxtbl_rtK_ok HS. acc2 KW K0.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb Q38 dHW1 dHW2 Hhb1; zbranch Hb;
apply Bool.negb_true_iff in Hb; apply Z.eqb_neq in Hb; img_apply Hb;
rewrite dHW2; img_change 255 with (Z.ones 8); rewrite land_ones_mod by zlia; img_change (2 ^ 8) with 256;
rewrite (Z.mul_comm 256 hb1), Z_mod_plus_full; img_refl end. }
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33cb4 + D_150). acc2 KW K0.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 38%nat (-3))) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E') (SOff 38%nat (-3)) = zev (rho_of E') T0T); rewrite (T0_val (rho_of E') hb1 Hhb1) by (rewrite Q38; img_exact dHW2);
cbn [zev]; rewrite Q38, dHW2; replace (3 + 256 * hb1 + -3) with (256 * hb1) by zlia; img_apply zcanon_id; clear - Hhb1; unfold M64; zlia) ].
unpin HS. srr_run_sh tfxtbl_rtK_ok HS. acc2 KW K0.
assert (A1V : zev (rho_of E') A1T = N8v) by (img_try (unfold YF2n.N8v; img_exact (A1_val (rho_of E') HWv nn hb1 Q38 Q39 dHW2 Hhb1 dN1))).
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E') (SLit 0) = zcanon (Z.land (zev (rho_of E') A1T) (zev (rho_of E') (SLit 7)))); rewrite A1V; cbn [zev];
rewrite (zcanon_id 7) by (unfold M64; zlia); rewrite land_7_mod by (clear - dN8 dC8; zlia); unfold YF2n.N8v; rewrite Z_mod_mult; img_refl) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 42%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E') (SOff 42%nat 0) = zev (rho_of E') A1T); rewrite A1V; cbn [zev]; rewrite Q42, Z.add_0_r; img_apply zcanon_id; clear - dN8 dN8b dN1 dC8; unfold M64; zlia) ].
unpin HS. srr_run_sh tfxtbl_rtK_ok HS. acc2 KW K0.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
clear - Hb Q35 Q42 dS1 dS2 dB1 dB2 dM1 dU1 dUN dN8 dN8b dC8 dN1 dRZ K1; zbranch Hb end. all: zlia. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc2 KW K0.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 41%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
rewrite (zcanon_id (Mv + 16)) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1; unfold M64; numconst; zlia);
unfold YF2n.SPv, YF2n.Uv; rewrite dM1; replace (base + rz - 16 + 16) with (base + rz) by zlia;
clear - dSP1 dSP2 dC8 dU1 dM1 dS1 dS2 dB1 dB2 dRZ K1; unfold YF2n.SPv, YF2n.Uv in *; numconst; zcanon_simp; zlia) ].
unpin HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 43%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_norm; rewrite ?Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
rewrite (zcanon_id (Mv + 16)), (zcanon_id (Mv + 8)), (zcanon_id N8v), (zcanon_id (Mv + 8 + N8v)) by (clear - dS1 dS2 dB1 dB2 dM1 dRZ K1 dN8 dN8b dN1 dC8; unfold M64; numconst; zlia);
rewrite ?(zcanon_id 1), ?(zcanon_id 0) by (unfold M64; zlia);
clear - dS1 dS2 dB1 dB2 dM1 dMal dRZ K1 dN8 dN8b dN1 dC8 dSP1 dSP2; unfold YF2n.CNT8v in *; numconst; zcanon_simp;
first [nia | zlia]) ].
unpin HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha dSP1 dSP2 dC8; numconst; zlia)).
img_apply (apresent_same (w_H W) mem0).
- img_apply MQ. rewrite unsigned_lit_small by img_exact Ra. intros Hx. img_exact (WINX_not_WINS a Hx Ha).
- img_apply Hsh_pres. img_exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch W 55%nat E' _ _ _ SPv CNT8v (0x33ce0 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R, (HE' 41%nat ltac:((img_case; cbv); zlia)), EqSP; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R, (HE' 43%nat ltac:((img_case; cbv); zlia)), EqCNT8; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - dC8; zlia) | img_try (clear - dSP1; numconst; zlia) | img_try (clear - dSP1 dSP2 dC8; numconst; zlia) | img_refl | img_try (zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem In] in Hr; repeat (destruct Hr as [<-|Hr];
[ img_try (cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?PV2, ?PV32, ?PV33, ?PV35, ?PV44, ?PV46;
unfold T, SB, sp0 in *; clear - dK1 dK2 C1 C2 dS1 dS2 dB1 dB2 dM1 dRZ K1 dSP1 dSP2 dC8 dI1 dI2 dG0 dG1 dG2 dCc1 dCc2 dT1 dT2 Hlo Hhi L1 L16 L10 L11; numconst;
zlia) |]); destruct Hr.
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS. evalS HS.
lazymatch type of HS with st_ok _ ?E _ _ => set (E5 := E) in HS end.
assert (HE5 : forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) by (img_try (intros k Hk; (subst E5; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; img_apply HE'; img_exact Hk)).
pose proof (WSK0_within E5 HE5) as K05. pose proof (within_mono _ _ E5 _ (fun a Ha => WINX_WIN a (WIN0_WINX a Ha)) K05) as KW5.
assert (MQ5 : MEQP WIN mem5).
{ intros x Hx. rewrite (Hfr5 x) by (img_try (intros Hs; img_apply Hx; img_apply WINS_WIN; img_exact Hs)). img_apply MQ. intros Hw; img_apply Hx; img_exact (WINX_WIN _ Hw). }
assert (MG5 : MAG mem5).
{ intros Hne. destruct (MG Hne) as [V P].
assert (EQ : forall a, base <= a < base + 8 -> mem5 (Z_to_bv 64 a) = ms_mem msM (Z_to_bv 64 a)).
{ intros a Ha. img_apply Hfr5. rewrite unsigned_lit_small by (img_try (clear - Ha dS1 dS2 dB1 dB2 K1; numconst; zlia)).
intros Hs. img_apply (WINX_not_WINS a); [img_try (img_apply MAGR_WINX; split; [img_exact Hne | img_exact Ha]) | img_try (img_exact Hs)]. }
split; [img_try (eapply val_mem_frame; [|img_exact V]; intros k Hk; img_apply EQ; zlia) | img_try (intros a Ha; img_apply (apresent_same (w_H W) (ms_mem msM)); [img_apply EQ; img_exact Ha | img_apply P; img_exact Ha])]. }
assert (SH5 : SHD mem5).
{ intros i Hi. unfold w64. rewrite (Hfill (Z_to_bv 64 (SPv + i))) by (img_try (rewrite unsigned_lit_small by (clear - Hi dSP1 dSP2 dC8; numconst; zlia); zlia)).
rewrite RA1m. img_refl. }
clear MQ MG Hfr5 Hfill SHPRES. rename MQ5 into MQ. rename MG5 into MG. rename SH5 into SH.
srr_run_sh tfxtbl_rtK_ok HS. acc3 KW5 K05.
assert (HR5 : forall k, (k < aHAVf)%nat -> rho_of E5 k = rho_of E' k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE5 k Hk), (HE' k Hk); img_refl)).
assert (S32 : rho_of E5 32%nat = T) by (img_try (rewrite (HR5 32%nat ltac:((img_case; cbv); zlia)); img_exact Q32)).
assert (S34 : rho_of E5 34%nat = SB) by (img_try (rewrite (HR5 34%nat ltac:((img_case; cbv); zlia)); img_exact Q34)).
assert (S35 : rho_of E5 35%nat = Mv) by (img_try (rewrite (HR5 35%nat ltac:((img_case; cbv); zlia)); img_exact Q35)).
assert (S36 : rho_of E5 36%nat = c) by (img_try (rewrite (HR5 36%nat ltac:((img_case; cbv); zlia)); img_exact Q36)).
assert (S37 : rho_of E5 37%nat = base) by (img_try (rewrite (HR5 37%nat ltac:((img_case; cbv); zlia)); img_exact Q37)).
assert (S44 : rho_of E5 44%nat = cbp) by (img_try (rewrite (HR5 44%nat ltac:((img_case; cbv); zlia)); img_exact Q44)).
clear Q32 Q34 Q35 Q36 Q37 Q38 Q39 Q40 Q41 Q42 Q43 Q44 Q48.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb S37 S34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Z.ltb_lt in Hb; zlia end. }
uncond HS. srr_run_sh tfxtbl_rtK_ok HS. acc3 KW5 K05.
srr_branch_sh tfxtbl_rtK_ok HS.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => clear - Hb S37 S34 dS1 dS2 dB1 dB2 K1; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; zlia end. }
uncond HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33d30 + D_150). acc3 KW5 K05.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 36%nat 0)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E5) (SOff 36%nat 0) = zev (rho_of E5) A2T);
rewrite (A2_val (rho_of E5) SB base c RELv S34 S37); [cbn [zev]; rewrite S36, Z.add_0_r; img_apply zcanon_id; clear - Hc; unfold M64; zlia
| clear - dBeq K3; zlia | clear - dX1 dX2 dMU K1; numconst; zlia | clear - Hc; zlia | clear - dS1; numconst; zlia | clear - dS1 dS2 dB1 dB2 K1; numconst; zlia ]) ].
unpin HS. srr_run_to_sh tfxtbl_rtK_ok HS (0x33f78 + D_150). acc3 KW5 K05.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msF end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E5 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape.
img_apply SRr_ret. split; [img_refl|].
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msF), (ms_mem msF), mt end.
split; [img_try (rewrite Hshape at 1; img_refl)|].
Ltac reg_atom HS HE5 r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q, (HE5 k ltac:(img_try ((img_case; cbv); zlia))); img_exact (Er k r eq_refl).
split; [img_try (reg_atom HS HE5 (2%bv : bv 5) 2%nat)|].
split; [img_try (reg_atom HS HE5 (1%bv : bv 5) 1%nat)|].
split. { intros r Hr. cbn [YF2n.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_atom HS HE5 (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl
| reg_atom HS HE5 (8%bv : bv 5) 8%nat | reg_atom HS HE5 (9%bv : bv 5) 9%nat | reg_atom HS HE5 (18%bv : bv 5) 18%nat
| reg_atom HS HE5 (19%bv : bv 5) 19%nat | reg_atom HS HE5 (20%bv : bv 5) 20%nat | reg_atom HS HE5 (21%bv : bv 5) 21%nat
| reg_atom HS HE5 (22%bv : bv 5) 22%nat | reg_atom HS HE5 (23%bv : bv 5) 23%nat | reg_atom HS HE5 (24%bv : bv 5) 24%nat
| reg_atom HS HE5 (25%bv : bv 5) 25%nat | reg_atom HS HE5 (26%bv : bv 5) 26%nat | reg_atom HS HE5 (27%bv : bv 5) 27%nat
]. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite (HE5 32%nat ltac:(img_try ((img_case; cbv); zlia))), EqT; unfold w64; rewrite Zbv_add_unsigned; unfold t_cache; img_refl. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; unfold A_ALLOCATOR; img_refl. }
split. { rreg HS (12%bv : bv 5) Q; rewrite Q; first [rewrite (HE5 36%nat ltac:(img_try ((img_case; cbv); zlia))), EqCL; img_refl | cbn [sv_denot]; rewrite (HE5 36%nat ltac:(img_try ((img_case; cbv); zlia))), EqCL; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl]. }
split. { rreg HS (13%bv : bv 5) Q; rewrite Q; first [rewrite (HE5 37%nat ltac:(img_try ((img_case; cbv); zlia))), EqBASE; img_refl | cbn [sv_denot]; rewrite (HE5 37%nat ltac:(img_try ((img_case; cbv); zlia))), EqBASE; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl]. }
split. { img_exact (MEQ_of_MEQP _ MQ). }
assert (PV2' : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite (HE5 2%nat ltac:((img_case; cbv); zlia)); rewrite E2; img_refl)).
assert (PV32' : bv_unsigned (ew E5 32) = T) by img_exact S32.
assert (PV35' : bv_unsigned (ew E5 35) = Mv) by img_exact S35.
split. { intros a Ha. unfold YF2n.WIN, YF2n.WINF, YF2n.WINS in Ha.
destruct Ha as [Ha|[[Ha|[[Hne Ha]|Ha]]|Ha]].
- eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV2'; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo L11; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV35'; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha dS1 dS2 dB1 dB2 dM1 dRZ K1; numconst; zlia)) ].
- img_exact (proj2 (MG Hne) a Ha).
- eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 5 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV32'; clear - Ha; numconst; zlia) | img_try (off_by ltac:(clear - Ha dT1 dT2; numconst; zlia)) ].
- destruct (Hsh_pres a Ha) as [Hh _]. split; [img_try (img_exact Hh)|]. exists (Z_to_bv 8 250). replace a with (SPv + (a - SPv)) by zlia. img_apply SH. clear - Ha; zlia. }
cbv zeta. split. { memv HS 2%nat 0%nat; [img_try (rewrite PV35'; zlia) | img_try (cbn [sv_denot]; rewrite (HE5 38%nat ltac:((img_case; cbv); zlia)), EqHW; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - dHW1 dHW2 Hhb1; zlia)]. }
split. { intros Hne. img_exact (proj1 (MG Hne)). }
img_exact SH.
Qed.
End WK.
End d.
