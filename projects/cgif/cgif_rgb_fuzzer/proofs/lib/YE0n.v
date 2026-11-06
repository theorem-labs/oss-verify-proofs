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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YF64 YE04 YE0v YE0k YE0l YE0m.
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
Local Notation path1_0 := (YE0l.path1_0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_1 := (YE0l.path1_1 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_2 := (YE0l.path1_2 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_3 := (YE0l.path1_3 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_4 := (YE0l.path1_4 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_5 := (YE0m.path1_5 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_6 := (YE0m.path1_6 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_7 := (YE0m.path1_7 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_8 := (YE0m.path1_8 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Lemma ent2L : forall b1, 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2L (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (img_try (img_apply (Env_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (img_try (img_apply (Env_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss2L. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply ent_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n g0 HRA ltac:(img_lia) Hd). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by img_lia. pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by img_lia. pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
Lemma ent2H : forall b1, 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfxsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2H (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (img_try (img_apply (Env_x _ 5); img_refl)).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (img_try (img_apply (Env_x _ 6); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
rewrite restrict_mkst_fx. unfold ss2H. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply ent_stk) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply ent_ro]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n g0 HRA ltac:(img_lia) Hd). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1 _ 1 (SOff 34 0) b1); [img_try (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by img_lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok facts2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; img_apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by img_lia. pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by img_lia. pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MS_STK, MS_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MS_STK, MS_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MS_STK, MS_SCR in *; img_lia | ];
    clear HFk HFrk.
  Tactic Notation "icpt_l1t_1" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) hyp(MEQp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MS_STK, MS_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MS_STK, MS_SCR in *; img_lia | ];
    clear HFk HFrk.

Lemma path2L : 64 < n -> d + n <= kLowMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (ent2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p2L_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2L_0))|].
icpt_l1t_1 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p2L_e0 13) (RG p2L_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p2L_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2L_1))|].
icpt_l1t_1 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_GEU (SLit 2147450879) (RG p2L_e1 18) HS2 (br_end_low EE 10 12 d n EE10 EE12 Hd ltac:(img_lia) ltac:(img_try (unfold kLowMemEnd in *; img_lia)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p2L_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2L_2))|].
icpt_l1t_1 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2L_e2 8) (RG p2L_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_p2L_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2L_3))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 MEQ3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_p2Lz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Lz_0))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 MEQ4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2Lz_e0 19) (RG p2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_p2Lz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Lz_1))|].
icpt_l1t_1 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply (apresent_same H mem (ms_mem ms6) z); [img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MS_STK; img_lia) | img_try (img_apply Bpres; img_lia)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MS_STK, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot EE (RG p2Lz_e1 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG p2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG p2Lz_e1 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG p2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG p2Lz_e1 2) = Z_to_bv 64 (sp0 - 2192)).
{ img_change (sv_denot EE (RG p2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG p2Lz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG p2Lz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem p2Lz_e1)).
{ cbn [ss_mem p2Lz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE p2Lz_e1 ms6 _ 48 (ss_mem p2Lz_e1) (gu + SB) (ge - gu) (sp0 - 2192) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try (rewrite (EE'reg 2%nat 2%bv eq_refl); img_refl)).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MS_SCR in *; img_lia)). img_apply MEQ6. unfold MS_SCR, MS_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MS_SCR, MS_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_p2Lz_2; img_try (img_apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Lz_2))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply (finish EE' p2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; split; [img_try (img_exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; img_lia)))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; img_lia); img_exact Ha) Eb))].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_p2Ln_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Ln_0))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 MEQ4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG p2Ln_e0 12) (RG p2Ln_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_p2Ln_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Ln_1))|].
icpt_l1t_1 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2Ln_e1 19) (RG p2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p2Ln_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Ln_2))|].
icpt_l1t_1 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply (apresent_same H mem (ms_mem ms7) z); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MS_STK; img_lia) | img_try (img_apply Bpres; img_lia)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MS_STK, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot EE (RG p2Ln_e2 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG p2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG p2Ln_e2 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG p2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG p2Ln_e2 2) = Z_to_bv 64 (sp0 - 2192)).
{ img_change (sv_denot EE (RG p2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG p2Ln_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG p2Ln_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem p2Ln_e2)).
{ cbn [ss_mem p2Ln_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE p2Ln_e2 ms7 _ 48 (ss_mem p2Ln_e2) (gu + SB) (ge - gu) (sp0 - 2192) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try (rewrite (EE'reg 2%nat 2%bv eq_refl); img_refl)).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MS_SCR in *; img_lia)). img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MS_SCR, MS_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_p2Ln_3; img_try (img_apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Ln_3))|].
icpt_l1t_0 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply (finish EE' p2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; split; [img_try (img_exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; img_lia)))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; img_lia); img_exact Ha) Eb))].
Qed.
Lemma path2H : 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by img_refl.
unfold cfg_at. img_change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfxsegs)) z = mem z) by (img_try (intros; img_refl)).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (img_try ((subst gu du; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (img_try ((subst ge de; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply Env_reg; assumption)).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (img_try (img_apply (Env_x _ 0); img_refl)).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (img_try (img_apply (Env_x _ 1); img_refl)).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (img_try (img_apply (Env_x _ 2); img_refl)).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (img_try (img_apply (Env_x _ 7); img_refl)).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (img_try (img_apply (Env_x _ 8); img_refl)).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (img_try (rewrite E32; img_apply unsigned_lit_small; img_lia)).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (img_try (rewrite E33; img_apply unsigned_lit_small; img_lia)).
pose proof (ent2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [img_norm_st HS0 r_p2H_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2H_0))|].
icpt_l1t_1 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 MEQ0 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (RG p2H_e0 13) (RG p2H_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_p2H_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2H_1))|].
icpt_l1t_1 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 MEQ1 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_LTU (SLit 140737488355327) (RG p2H_e1 18) HS2 (br_end_high EE 10 12 d n EE10 EE12 Hd ltac:(img_lia) ltac:(img_try (unfold kHighMemEnd in *; img_lia)))) as HS2'.
img_change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_p2H_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2H_2))|].
icpt_l1t_1 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 MEQ2 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2H_e2 8) (RG p2H_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_p2H_3; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2H_3))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 MEQ3 EE EE2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(img_try (rewrite E34, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_p2Hz_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hz_0))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 MEQ4 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2Hz_e0 19) (RG p2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_p2Hz_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hz_1))|].
icpt_l1t_1 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply (apresent_same H mem (ms_mem ms6) z); [img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MS_STK; img_lia) | img_try (img_apply Bpres; img_lia)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MS_STK, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot EE (RG p2Hz_e1 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG p2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG p2Hz_e1 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG p2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG p2Hz_e1 2) = Z_to_bv 64 (sp0 - 2192)).
{ img_change (sv_denot EE (RG p2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG p2Hz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG p2Hz_e1 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem p2Hz_e1)).
{ cbn [ss_mem p2Hz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE p2Hz_e1 ms6 _ 48 (ss_mem p2Hz_e1) (gu + SB) (ge - gu) (sp0 - 2192) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try (rewrite (EE'reg 2%nat 2%bv eq_refl); img_refl)).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MS_SCR in *; img_lia)). img_apply MEQ6. unfold MS_SCR, MS_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MS_SCR, MS_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_p2Hz_2; img_try (img_apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Hz_2))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 EE' EE'2.
img_apply (finish EE' p2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ8. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; split; [img_try (img_exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; img_lia)))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; img_lia); img_exact Ha) Eb))].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_p2Hn_0; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hn_0))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 MEQ4 EE EE2.
pose proof (st_ok_add_cond tfxsegs EE _ _ BC_LT (RG p2Hn_e0 12) (RG p2Hn_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(img_lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_p2Hn_1; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hn_1))|].
icpt_l1t_1 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 MEQ5 EE EE2.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_GEU (RG p2Hn_e1 19) (RG p2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_p2Hn_2; img_try (img_apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Hn_2))|].
icpt_l1t_1 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 MEQ6 EE EE2.
assert (SLW : forall z, sp0 - 2192 - 8 <= z < sp0 - 2192 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply (apresent_same H mem (ms_mem ms7) z); [img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MS_STK; img_lia) | img_try (img_apply Bpres; img_lia)]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MS_STK, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot EE (RG p2Hn_e2 10) = Z_to_bv 64 (gu + SB)).
{ img_change (sv_denot EE (RG p2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot EE (RG p2Hn_e2 11) = Z_to_bv 64 (ge - gu)).
{ img_change (sv_denot EE (RG p2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). img_exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot EE (RG p2Hn_e2 2) = Z_to_bv 64 (sp0 - 2192)).
{ img_change (sv_denot EE (RG p2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2192))). cbn [sv_denot]. rewrite EE2. f_equal; img_lia. }
assert (R1 : sv_denot EE (RG p2Hn_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot EE (RG p2Hn_e2 1)) with (sv_denot EE (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val EE (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2192 - 8 \/ sp0 - 2192 <= base_val EE (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem p2Hn_e2)).
{ cbn [ss_mem p2Hn_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W EE p2Hn_e2 ms7 _ 48 (ss_mem p2Hn_e2) (gu + SB) (ge - gu) (sp0 - 2192) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. (subst EE'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (img_try (rewrite (EE'reg 2%nat 2%bv eq_refl); img_refl)).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MS_SCR in *; img_lia)). img_apply MEQ7. unfold MS_SCR, MS_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MS_SCR, MS_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_p2Hn_3; img_try (img_apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Hn_3))|].
icpt_l1t_0 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 EE' EE'2.
img_apply (finish EE' p2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EE'reg).
- intros z Hz. img_apply MEQ9. unfold MS_SCR, MS_STK in *. img_lia.
- intros a Ha; split; [img_try (img_exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; img_lia)))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; img_lia); img_exact Ha) Eb))].
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. img_lia. Qed.
Theorem asan_memset_srr : SRr tfxsegs W (cfg_at tfxsegs MS_ENTRY regs mem md) POSTm.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [img_try (img_apply path0; img_exact Hn0)|].
destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by img_lia.
assert (Hg0 : 8 * g0 <= d < 8 * g0 + 8) by (img_try ((subst g0; cbv beta); pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (img_try ((subst g1; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
destruct (t_cases (g1 - g0) ltac:(img_lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[img_try (img_apply path1_0) | img_try (img_apply path1_1) | img_try (img_apply path1_2) | img_try (img_apply path1_3) | img_try (img_apply path1_4) | img_try (img_apply path1_5) | img_try (img_apply path1_6) | img_try (img_apply path1_7) | img_try (img_apply path1_8)]; assumption.
- destruct HAM as [HL|HH]; [img_try (img_apply path2L; [img_lia | img_exact HL]) | img_try (img_apply path2H; [img_lia | img_exact HH])].
Qed.
End e.
Theorem asan_memset_realizes {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B ->
forall ly S (W : world tfxsegs) regs mem md d x n,
ecall_pre tfxsegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfxsegs B ly S W regs mem d n ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) d n) ->
amem_range d n ->
SRr tfxsegs W (cfg_at tfxsegs (0x5224c + D_2c4) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM.
img_exact (asan_memset_srr B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
End c.
