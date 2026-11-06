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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF63 YE04 YE0v YE0a.
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
Local Notation POSTc := (YE0a.POSTc B ly S W regs mem md d x n).
Local Notation SV := (YE0a.SV regs).
Local Notation MIDP := (YE0a.MIDP W regs mem d x n).
Local Notation MIDQ := (YE0a.MIDQ W regs mem md d x n).
Local Notation basics := (YE0a.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (YE0a.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (YE0a.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (YE0a.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (YE0a.EnvS_reg regs).
Local Notation EnvS_x := (YE0a.EnvS_x regs).
Local Notation EnvS2 := (YE0a.EnvS2 regs).
Local Notation EnvS10 := (YE0a.EnvS10 regs d G10).
Local Notation EnvS11 := (YE0a.EnvS11 regs x G11).
Local Notation EnvS12 := (YE0a.EnvS12 regs n G12).
Local Notation entS_stk := (YE0a.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (YE0a.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (YE0a.EnvD regs).
Local Notation EnvD_reg := (YE0a.EnvD_reg regs).
Local Notation EnvD_sv := (YE0a.EnvD_sv regs d x).
Local Notation EnvD_x := (YE0a.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (YE0a.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (YE0a.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (YE0a.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (YE0a.EnvD12 W regs mem d x n).
Local Notation entD_stk := (YE0a.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (YE0a.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (YE0a.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Lemma entS1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 0 -> aview tfxsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfxsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 0) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply entS_stk) | img_try (img_apply Forall_cons; [| img_apply entS_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) x n (g0s + i) HRAX ltac:(img_lia) Hx0); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0s _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 0 E32) by img_lia. (subst g0s g1s; cbv beta). img_lia.
Qed.
Lemma entS1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 1 -> aview tfxsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfxsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 1) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply entS_stk) | img_try (img_apply Forall_cons; [| img_apply entS_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) x n (g0s + i) HRAX ltac:(img_lia) Hx0); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0s _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 1 E32) by img_lia. (subst g0s g1s; cbv beta). img_lia.
Qed.
Lemma entS1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 2 -> aview tfxsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfxsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 2) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply entS_stk) | img_try (img_apply Forall_cons; [| img_apply entS_ro])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) x n (g0s + i) HRAX ltac:(img_lia) Hx0); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0s _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by img_lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; img_apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 2 E32) by img_lia. (subst g0s g1s; cbv beta). img_lia.
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
  Tactic Notation "icpt_l1t_1" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HMk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) hyp(CL0) hyp(CL1) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HMk);
    assert (MEQk : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z) by (img_try (intros z Hz; rewrite HMk; img_apply MEQp; img_exact Hz));
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None) by (img_try (intros z Hz; rewrite HMk; img_apply PSLp; img_exact Hz));
    clear CL0 CL1.

Lemma pathS1_0 : 1 <= n <= 64 -> g1s - g0s = 0 -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1s < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) x n HRAX ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULLX ltac:(img_lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0s; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1s; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem x n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply EnvS_reg; assumption)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (EnvS_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (EnvS_x _ 4); img_refl)).
pose proof (entS1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfxsegs EE q1_0_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfxsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [img_norm_st HSc r_q1_0_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_0_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_0_e0 13) (RG q1_0_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_q1_0_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_0_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_0_e1 13) (RG q1_0_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_0_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (q1_0_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450880 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0s + 2147450880) with (g1s + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_0_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_q1_0_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_0_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_0z_0; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_0z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms7, mat7. split; [img_refl|].
img_apply (midS EE q1_0z_e0 ms7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_0n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_0n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG q1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(img_lia) Hxn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_q1_0n_1; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_0n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms8, mat8. split; [img_refl|].
img_apply (midS EE q1_0n_e1 ms8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
}
eapply SRr_bind; [img_norm_st HS0 r_q1_0o_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_0o_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
assert (Hdx : d <> x) by img_lia.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q1_0o_e0 10) (RG q1_0o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
img_change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [img_norm_st HS1n r_q1_0oA_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_0oA_0))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_0oB_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0oB_0))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_0oB_e0 10) (RG q1_0oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(img_lia)))) as HS3'.
img_change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q1_0oB_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_0oB_1))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_0oB_canon in HSq. img_exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_0oA_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0oA_1))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_0oA_canon in HSq. img_exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS1_1 : 1 <= n <= 64 -> g1s - g0s = 1 -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1s < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) x n HRAX ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULLX ltac:(img_lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0s; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1s; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem x n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply EnvS_reg; assumption)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (EnvS_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (EnvS_x _ 4); img_refl)).
pose proof (entS1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfxsegs EE q1_1_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfxsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [img_norm_st HSc r_q1_1_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_1_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_1_e0 13) (RG q1_1_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_q1_1_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_1_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_1_e1 13) (RG q1_1_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_1_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (q1_1_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450881 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0s + 2147450881) with (g1s + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_1_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_q1_1_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_1_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_1z_0; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_1z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms7, mat7. split; [img_refl|].
img_apply (midS EE q1_1z_e0 ms7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_1n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_1n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG q1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(img_lia) Hxn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_q1_1n_1; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_1n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms8, mat8. split; [img_refl|].
img_apply (midS EE q1_1n_e1 ms8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
}
eapply SRr_bind; [img_norm_st HS0 r_q1_1o_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_1o_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
assert (Hdx : d <> x) by img_lia.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q1_1o_e0 10) (RG q1_1o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
img_change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [img_norm_st HS1n r_q1_1oA_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_1oA_0))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_1oB_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1oB_0))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_1oB_e0 10) (RG q1_1oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(img_lia)))) as HS3'.
img_change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q1_1oB_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_1oB_1))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_1oB_canon in HSq. img_exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_1oA_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1oA_1))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_1oA_canon in HSq. img_exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS1_2 : 1 <= n <= 64 -> g1s - g0s = 2 -> SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (img_try ((subst g0s; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod x 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (img_try ((subst g1s; cbv beta); pose proof (Z.div_mod (x + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1s < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) x n HRAX ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULLX ltac:(img_lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0s; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1s; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem x n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply EnvS_reg; assumption)).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (img_try (img_apply (EnvS_x _ 0); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (EnvS_x _ 2); img_refl)).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (img_try (img_apply (EnvS_x _ 3); img_refl)).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (img_try (img_apply (EnvS_x _ 4); img_refl)).
pose proof (entS1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfxsegs EE q1_2_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfxsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [img_norm_st HSc r_q1_2_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_2_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_2_e0 13) (RG q1_2_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_q1_2_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_2_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_2_e1 13) (RG q1_2_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_2_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W EE (q1_2_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450882 E32) by img_lia. f_equal. (subst h2; cbv beta). replace (g0s + 2147450882) with (g1s + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W EE (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_2_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_q1_2_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_2_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 EE EE2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_2z_0; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_2z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms7, mat7. split; [img_refl|].
img_apply (midS EE q1_2z_e0 ms7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_q1_2n_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_2n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG q1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(img_lia) Hxn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_q1_2n_1; img_try (img_apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_2n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE EE2.
img_apply SRr_ret. split; [img_refl|]. exists ms8, mat8. split; [img_refl|].
img_apply (midS EE q1_2n_e1 ms8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EEreg).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
}
eapply SRr_bind; [img_norm_st HS0 r_q1_2o_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_2o_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 EE EE2.
assert (Hdx : d <> x) by img_lia.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG q1_2o_e0 10) (RG q1_2o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
img_change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [img_norm_st HS1n r_q1_2oA_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_2oA_0))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 EE EE2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_2oB_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2oB_0))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG q1_2oB_e0 10) (RG q1_2oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(img_lia)))) as HS3'.
img_change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_q1_2oB_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_2oB_1))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 EE EE2.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_2oB_canon in HSq. img_exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_q1_2oA_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2oA_1))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 EE EE2.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_2oA_canon in HSq. img_exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
End e.
End c.
