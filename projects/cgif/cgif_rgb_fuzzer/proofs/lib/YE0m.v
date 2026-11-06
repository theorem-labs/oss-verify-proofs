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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF64 YE04 YE0v YE0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfxsegs B ly S W regs mem d n.
Hypothesis HRA : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n.
Hypothesis HAM : amem_range d n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := d / 8.
Let g1 : Z := (d + n - 1) / 8.
Let du : Z := (d + 7) / 8 * 8.
Let de : Z := (d + n) / 8 * 8.
Let gu : Z := (d + 7) / 8.
Let ge : Z := (d + n) / 8.
Local Notation Env := (YE0v.Env regs).
Local Notation Env_reg := (YE0v.Env_reg regs).
Local Notation Env_x := (YE0v.Env_x regs).
Local Notation Env2 := (YE0k.Env2 regs).
Local Notation Env10 := (YE0k.Env10 regs d G10).
Local Notation Env12 := (YE0k.Env12 regs n G12).
Local Notation POSTm := (YE0k.POSTm B ly S W regs mem md d x n).
Local Notation basics := (YE0k.basics B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation finish := (YE0k.finish B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent_stk := (YE0k.ent_stk B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation ent_ro := (YE0k.ent_ro B TB ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation path0 := (YE0k.path0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent1_0 := (YE0k.ent1_0 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HAM).
Local Notation ent1_1 := (YE0k.ent1_1 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_2 := (YE0k.ent1_2 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_3 := (YE0k.ent1_3 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_4 := (YE0k.ent1_4 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_5 := (YE0k.ent1_5 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_6 := (YE0k.ent1_6 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_7 := (YE0k.ent1_7 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_8 := (YE0k.ent1_8 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) hyp(MEQp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MS_STK, MS_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MS_STK, MS_SCR in *; img_lia | ];
    clear HFk HFrk.

Lemma path1_5 : 1 <= n <= 64 -> g1 - g0 = 5 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p1_5_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_5_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p1_5_e0 13) (RG p1_5_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p1_5_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_5_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p1_5_e1 14) (RG p1_5_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p1_5_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_5_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (p1_5_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (img_try (intros z Hz; rewrite HM4; img_apply MEQ3; img_exact Hz)).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450885 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450885) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc p1_5_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_5_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (img_try (intros z Hz; rewrite HM5; img_apply MEQ4; img_exact Hz)).
clear HM5 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_p1_5_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_5_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG p1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_5z_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_5z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
img_apply (finish EE p1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms7) a); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG p1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_5n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_5n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 5%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_p1_5n_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_5n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 MEQ7 EE EE2.
img_apply (finish EE p1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms8) a); [img_try (img_apply MEQ8; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
Qed.
Lemma path1_6 : 1 <= n <= 64 -> g1 - g0 = 6 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p1_6_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_6_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p1_6_e0 13) (RG p1_6_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p1_6_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_6_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p1_6_e1 14) (RG p1_6_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p1_6_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_6_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (p1_6_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (img_try (intros z Hz; rewrite HM4; img_apply MEQ3; img_exact Hz)).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450886 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450886) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc p1_6_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_6_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (img_try (intros z Hz; rewrite HM5; img_apply MEQ4; img_exact Hz)).
clear HM5 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_p1_6_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_6_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG p1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_6z_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_6z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
img_apply (finish EE p1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms7) a); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG p1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_6n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_6n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 6%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_p1_6n_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_6n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 MEQ7 EE EE2.
img_apply (finish EE p1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms8) a); [img_try (img_apply MEQ8; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
Qed.
Lemma path1_7 : 1 <= n <= 64 -> g1 - g0 = 7 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p1_7_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_7_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p1_7_e0 13) (RG p1_7_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p1_7_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_7_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p1_7_e1 14) (RG p1_7_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p1_7_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_7_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (p1_7_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (img_try (intros z Hz; rewrite HM4; img_apply MEQ3; img_exact Hz)).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450887 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450887) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc p1_7_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_7_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (img_try (intros z Hz; rewrite HM5; img_apply MEQ4; img_exact Hz)).
clear HM5 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_p1_7_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_7_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG p1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_7z_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_7z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
img_apply (finish EE p1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms7) a); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG p1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_7n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_7n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 7%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_p1_7n_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_7n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 MEQ7 EE EE2.
img_apply (finish EE p1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms8) a); [img_try (img_apply MEQ8; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
Qed.
Lemma path1_8 : 1 <= n <= 64 -> g1 - g0 = 8 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1 < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (Env_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (Env_x _ 4); img_refl)).
pose proof (ent1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p1_8_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_8_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p1_8_e0 13) (RG p1_8_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p1_8_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_8_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p1_8_e1 14) (RG p1_8_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p1_8_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_8_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (p1_8_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (img_try (intros z Hz; rewrite HM4; img_apply MEQ3; img_exact Hz)).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450888 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0 + 2147450888) with (g1 + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MS_STK, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc p1_8_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_8_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (img_try (intros z Hz; rewrite HM5; img_apply MEQ4; img_exact Hz)).
clear HM5 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_p1_8_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_8_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG p1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_8z_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_8z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
img_apply (finish EE p1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms7) a); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG p1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p1_8n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_8n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 8%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_p1_8n_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_8n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 MEQ7 EE EE2.
img_apply (finish EE p1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; img_apply (apresent_same H mem (ms_mem ms8) a); [img_try (img_apply MEQ8; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_apply Bpres; img_lia)].
Qed.
End c.
End b.
