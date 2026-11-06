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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF63 YE04 YE0v YE11.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
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
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfxsegs W regs mem x n.
Hypothesis HDISJ : d + n <= x \/ x + n <= d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0s : Z := x / 8.
Let g1s : Z := (x + n - 1) / 8.
Let dus : Z := (x + 7) / 8 * 8.
Let des : Z := (x + n) / 8 * 8.
Let gus : Z := (x + 7) / 8.
Let ges : Z := (x + n) / 8.
Let g0d : Z := d / 8.
Let g1d : Z := (d + n - 1) / 8.
Let dud : Z := (d + 7) / 8 * 8.
Let ded : Z := (d + n) / 8 * 8.
Let gud : Z := (d + 7) / 8.
Let ged : Z := (d + n) / 8.
Local Notation Env := (YE0v.Env regs).
Local Notation POSTc := (YE11.POSTc B ly S W regs mem md d x n).
Local Notation SV := (YE11.SV regs).
Local Notation MIDP := (YE11.MIDP W regs mem d x n).
Local Notation MIDQ := (YE11.MIDQ W regs mem md d x n).
Local Notation basics := (YE11.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (YE11.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (YE11.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (YE11.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (YE11.EnvS_reg regs).
Local Notation EnvS_x := (YE11.EnvS_x regs).
Local Notation EnvS2 := (YE11.EnvS2 regs).
Local Notation EnvS10 := (YE11.EnvS10 regs d G10).
Local Notation EnvS11 := (YE11.EnvS11 regs x G11).
Local Notation EnvS12 := (YE11.EnvS12 regs n G12).
Local Notation entS_stk := (YE11.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (YE11.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (YE11.EnvD regs).
Local Notation EnvD_reg := (YE11.EnvD_reg regs).
Local Notation EnvD_sv := (YE11.EnvD_sv regs d x).
Local Notation EnvD_x := (YE11.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (YE11.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (YE11.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (YE11.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (YE11.EnvD12 W regs mem d x n).
Local Notation entD_stk := (YE11.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (YE11.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (YE11.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Lemma entS2L : forall b1, 64 < n -> x + n <= kLowMemEnd - 1 -> aview tfxsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfxsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2L (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (img_try (img_apply (EnvS_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (img_try (img_apply (EnvS_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (img_try (img_apply (EnvS_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (img_try (img_apply (EnvS_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (img_try (img_apply (EnvS_x _ 8); img_refl)).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (img_try ((subst gus dus; cbv beta); pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (img_try ((subst ges des; cbv beta); pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssS2L. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply entS_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply entS_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) x n g0s HRAX ltac:(img_lia) Hx0). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Nat.add].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1s _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsS2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by img_lia. pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by img_lia. pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
Lemma entS2H : forall b1, 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> aview tfxsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfxsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2H (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (img_try (img_apply (EnvS_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (img_try (img_apply (EnvS_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (img_try (img_apply (EnvS_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (img_try (img_apply (EnvS_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (img_try (img_apply (EnvS_x _ 8); img_refl)).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (img_try ((subst gus dus; cbv beta); pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (img_try ((subst ges des; cbv beta); pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssS2H. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply entS_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply entS_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) x n g0s HRAX ltac:(img_lia) Hx0). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Nat.add].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1s _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsS2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by img_lia. pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by img_lia. pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MC_STK, MC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    clear HFk HFrk.
  Tactic Notation "icpt_l1t_1" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MC_STK, MC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    clear HFk HFrk.

Lemma pathS2L : 64 < n -> x + n <= kLowMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1s < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) x n HRAX ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (img_try ((subst gus dus; cbv beta); pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (img_try ((subst ges des; cbv beta); pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply EnvS_reg; assumption)).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (img_try (img_apply (EnvS_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (img_try (img_apply (EnvS_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (img_try (img_apply (EnvS_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (entS2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfxsegs EE q2L_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfxsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [img_norm_st HSc r_q2L_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HSc r_q2L_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q2L_e0 13) (RG q2L_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_q2L_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2L_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (SLit 2147450879) (RG q2L_e1 18) HS2 (br_end_low EE 11 12 x n EE11 EE12 Hx0 ltac:(img_lia) ltac:(img_try (unfold kLowMemEnd in *; img_lia)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2L_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2L_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2L_e2 8) (RG q2L_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q2L_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2L_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_q2Lz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Lz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2Lz_e0 19) (RG q2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_q2Lz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Lz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) x n (a - SB) HRAX); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hx0)]. }
assert (R10 : sv_denot EE (RG q2Lz_e1 10) = Z_to_bv 64 (gus + SB)).
{ img_change (sv_denot EE (RG q2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG q2Lz_e1 11) = Z_to_bv 64 (ges - gus)).
{ img_change (sv_denot EE (RG q2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG q2Lz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ img_change (sv_denot EE (RG q2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG q2Lz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG q2Lz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem q2Lz_e1)).
{ cbn [ss_mem q2Lz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE q2Lz_e1 ms6 _ 56 (ss_mem q2Lz_e1) (gus + SB) (ges - gus) (sp0 - 2224) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ6. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_q2Lz_2; img_try (img_apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Lz_2))|].
icpt_l1t_1 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply SRr_ret. split; [img_refl|]. exists ms8, mat8. split; [img_refl|].
img_apply (midS EE' q2Lz_e2 ms8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_q2Ln_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Ln_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(img_lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_q2Ln_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Ln_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2Ln_e1 19) (RG q2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q2Ln_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Ln_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) x n (a - SB) HRAX); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hx0)]. }
assert (R10 : sv_denot EE (RG q2Ln_e2 10) = Z_to_bv 64 (gus + SB)).
{ img_change (sv_denot EE (RG q2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG q2Ln_e2 11) = Z_to_bv 64 (ges - gus)).
{ img_change (sv_denot EE (RG q2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG q2Ln_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ img_change (sv_denot EE (RG q2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG q2Ln_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG q2Ln_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem q2Ln_e2)).
{ cbn [ss_mem q2Ln_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE q2Ln_e2 ms7 _ 56 (ss_mem q2Ln_e2) (gus + SB) (ges - gus) (sp0 - 2224) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_q2Ln_3; img_try (img_apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Ln_3))|].
icpt_l1t_1 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply SRr_ret. split; [img_refl|]. exists ms9, mat9. split; [img_refl|].
img_apply (midS EE' q2Ln_e3 ms9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
}
eapply SRr_bind; [img_norm_st HS0 r_q2Lo_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Lo_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
assert (Hdx : d <> x) by img_lia.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q2Lo_e0 10) (RG q2Lo_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
img_change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [img_norm_st HS1n r_q2LoA_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1n r_q2LoA_0))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2LoB_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2LoB_0))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q2LoB_e0 10) (RG q2LoB_e0 19) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(img_lia)))) as HS3'.
img_change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q2LoB_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2LoB_1))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q2LoB_canon in HSq. img_exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2LoA_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2LoA_1))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q2LoA_canon in HSq. img_exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS2H : 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1s < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) x n HRAX ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (img_try ((subst gus dus; cbv beta); pose proof (Z.div_mod (x + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (img_try ((subst ges des; cbv beta); pose proof (Z.div_mod (x + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply EnvS_reg; assumption)).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (img_try (img_apply (EnvS_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (img_try (img_apply (EnvS_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (img_try (img_apply (EnvS_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (entS2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfxsegs EE q2H_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfxsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [img_norm_st HSc r_q2H_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HSc r_q2H_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q2H_e0 13) (RG q2H_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_q2H_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2H_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (SLit 140737488355327) (RG q2H_e1 18) HS2 (br_end_high EE 11 12 x n EE11 EE12 Hx0 ltac:(img_lia) ltac:(img_try (unfold kHighMemEnd in *; img_lia)))) as HS2'.
img_change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2H_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2H_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2H_e2 8) (RG q2H_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q2H_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2H_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_q2Hz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2Hz_e0 19) (RG q2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_q2Hz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) x n (a - SB) HRAX); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hx0)]. }
assert (R10 : sv_denot EE (RG q2Hz_e1 10) = Z_to_bv 64 (gus + SB)).
{ img_change (sv_denot EE (RG q2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG q2Hz_e1 11) = Z_to_bv 64 (ges - gus)).
{ img_change (sv_denot EE (RG q2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG q2Hz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ img_change (sv_denot EE (RG q2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG q2Hz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG q2Hz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem q2Hz_e1)).
{ cbn [ss_mem q2Hz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE q2Hz_e1 ms6 _ 56 (ss_mem q2Hz_e1) (gus + SB) (ges - gus) (sp0 - 2224) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ6. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_q2Hz_2; img_try (img_apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Hz_2))|].
icpt_l1t_1 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply SRr_ret. split; [img_refl|]. exists ms8, mat8. split; [img_refl|].
img_apply (midS EE' q2Hz_e2 ms8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_q2Hn_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hn_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(img_lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_q2Hn_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hn_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2Hn_e1 19) (RG q2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q2Hn_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Hn_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) x n (a - SB) HRAX); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hx0)]. }
assert (R10 : sv_denot EE (RG q2Hn_e2 10) = Z_to_bv 64 (gus + SB)).
{ img_change (sv_denot EE (RG q2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG q2Hn_e2 11) = Z_to_bv 64 (ges - gus)).
{ img_change (sv_denot EE (RG q2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG q2Hn_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ img_change (sv_denot EE (RG q2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG q2Hn_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG q2Hn_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem q2Hn_e2)).
{ cbn [ss_mem q2Hn_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE q2Hn_e2 ms7 _ 56 (ss_mem q2Hn_e2) (gus + SB) (ges - gus) (sp0 - 2224) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try ((subst EE'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact EE2)).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_q2Hn_3; img_try (img_apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Hn_3))|].
icpt_l1t_1 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply SRr_ret. split; [img_refl|]. exists ms9, mat9. split; [img_refl|].
img_apply (midS EE' q2Hn_e3 ms9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
}
eapply SRr_bind; [img_norm_st HS0 r_q2Ho_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Ho_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
assert (Hdx : d <> x) by img_lia.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q2Ho_e0 10) (RG q2Ho_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
img_change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [img_norm_st HS1n r_q2HoA_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1n r_q2HoA_0))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2HoB_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2HoB_0))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q2HoB_e0 10) (RG q2HoB_e0 19) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(img_lia)))) as HS3'.
img_change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q2HoB_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2HoB_1))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q2HoB_canon in HSq. img_exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q2HoA_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2HoA_1))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q2HoA_canon in HSq. img_exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
End e.
End c.
