(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y AE30.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfibsegs W regs mem x n.
Hypothesis HDISJ : d + n <= x \/ x + n <= d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
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
Local Notation Env := (AE2y.Env regs).
Local Notation POSTc := (AE30.POSTc B ly S W regs mem md d x n).
Local Notation SV := (AE30.SV regs).
Local Notation MIDP := (AE30.MIDP W regs mem d x n).
Local Notation MIDQ := (AE30.MIDQ W regs mem md d x n).
Local Notation basics := (AE30.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (AE30.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (AE30.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (AE30.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (AE30.EnvS_reg regs).
Local Notation EnvS_x := (AE30.EnvS_x regs).
Local Notation EnvS2 := (AE30.EnvS2 regs).
Local Notation EnvS10 := (AE30.EnvS10 regs d G10).
Local Notation EnvS11 := (AE30.EnvS11 regs x G11).
Local Notation EnvS12 := (AE30.EnvS12 regs n G12).
Local Notation entS_stk := (AE30.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (AE30.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (AE30.EnvD regs).
Local Notation EnvD_reg := (AE30.EnvD_reg regs).
Local Notation EnvD_sv := (AE30.EnvD_sv regs d x).
Local Notation EnvD_x := (AE30.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (AE30.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (AE30.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (AE30.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (AE30.EnvD12 W regs mem d x n).
Local Notation entD_stk := (AE30.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (AE30.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (AE30.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Lemma entS2L : forall b1, 64 < n -> x + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2L (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (apply (EnvS_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (apply (EnvS_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS2L. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply Forall_cons; [| apply entS_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n g0s HRAX ltac:(lia) Hx0). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma entS2H : forall b1, 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2H (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (apply (EnvS_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (apply (EnvS_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS2H. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply Forall_cons; [| apply entS_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n g0s HRAX ltac:(lia) Hx0). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma pathS2L : 64 < n -> x + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (entS2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q2L_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2L_e0 13) (RG q2L_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG q2L_e1 18) HS2 (br_end_low EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2L_e2 8) (RG q2L_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Lz_e0 19) (RG q2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Lz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Lz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Lz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot EE (RG q2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Lz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG q2Lz_e1 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Lz_e1)).
{ cbn [ss_mem q2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Lz_e1 ms6 _ 56 (ss_mem q2Lz_e1) (gus + SB) (ges - gus) (sp0 - 2224) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Lz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Ln_e1 19) (RG q2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Ln_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Ln_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Ln_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot EE (RG q2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Ln_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG q2Ln_e2 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Ln_e2)).
{ cbn [ss_mem q2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Ln_e2 ms7 _ 56 (ss_mem q2Ln_e2) (gus + SB) (ges - gus) (sp0 - 2224) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Ln_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Lo_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
assert (Hdx : d <> x) by lia.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2Lo_e0 10) (RG q2Lo_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q2LoA_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2LoB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2LoB_e0 10) (RG q2LoB_e0 19) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2LoB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q2LoB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q2LoA_e0 11) (RG q2LoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2LoA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q2LoA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS2H : 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (entS2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q2H_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2H_e0 13) (RG q2H_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG q2H_e1 18) HS2 (br_end_high EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2H_e2 8) (RG q2H_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hz_e0 19) (RG q2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot EE (RG q2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG q2Hz_e1 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hz_e1)).
{ cbn [ss_mem q2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hz_e1 ms6 _ 56 (ss_mem q2Hz_e1) (gus + SB) (ges - gus) (sp0 - 2224) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Hz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hn_e1 19) (RG q2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hn_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hn_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hn_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot EE (RG q2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2224))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hn_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG q2Hn_e2 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hn_e2)).
{ cbn [ss_mem q2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hn_e2 ms7 _ 56 (ss_mem q2Hn_e2) (gus + SB) (ges - gus) (sp0 - 2224) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Hn_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Ho_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
assert (Hdx : d <> x) by lia.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2Ho_e0 10) (RG q2Ho_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q2HoA_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
destruct (Z_lt_le_dec x (d + n)) as [Hov|Hov].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2HoB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2HoB_e0 10) (RG q2HoB_e0 19) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2HoB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q2HoB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q2HoA_e0 11) (RG q2HoA_e0 20) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2HoA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q2HoA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
End e.
End c.
