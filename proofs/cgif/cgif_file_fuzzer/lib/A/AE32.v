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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3d AE20 AE2y AE79 AE7a AE7b.
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
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis HAM : amem_range d n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := d / 8.
Let g1 : Z := (d + n - 1) / 8.
Let du : Z := (d + 7) / 8 * 8.
Let de : Z := (d + n) / 8 * 8.
Let gu : Z := (d + 7) / 8.
Let ge : Z := (d + n) / 8.
Local Notation Env := (AE2y.Env regs).
Local Notation Env_reg := (AE2y.Env_reg regs).
Local Notation Env_x := (AE2y.Env_x regs).
Local Notation Env2 := (AE79.Env2 regs).
Local Notation Env10 := (AE79.Env10 regs d G10).
Local Notation Env12 := (AE79.Env12 regs n G12).
Local Notation POSTm := (AE79.POSTm B ly S W regs mem md d x n).
Local Notation basics := (AE79.basics B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation finish := (AE79.finish B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent_stk := (AE79.ent_stk B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation ent_ro := (AE79.ent_ro B TB ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation path0 := (AE79.path0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent1_0 := (AE79.ent1_0 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HAM).
Local Notation ent1_1 := (AE79.ent1_1 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_2 := (AE79.ent1_2 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_3 := (AE79.ent1_3 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_4 := (AE79.ent1_4 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_5 := (AE79.ent1_5 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_6 := (AE79.ent1_6 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_7 := (AE79.ent1_7 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_8 := (AE79.ent1_8 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation path1_0 := (AE7a.path1_0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_1 := (AE7a.path1_1 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_2 := (AE7a.path1_2 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_3 := (AE7a.path1_3 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_4 := (AE7a.path1_4 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_5 := (AE7b.path1_5 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_6 := (AE7b.path1_6 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_7 := (AE7b.path1_7 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Local Notation path1_8 := (AE7b.path1_8 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Lemma ent2L : forall b1, 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2L (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss2L. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0 HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma ent2H : forall b1, 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge]) ss2H (restrict H (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as E12.
fold EE in E2, E10, E12.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ss2H. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0 HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stk, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MS_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok facts2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma path2L : 64 < n -> d + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2216) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p2L_e0 13) (RG p2L_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG p2L_e1 18) HS2 (br_end_low EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2L_e2 8) (RG p2L_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Lz_e0 19) (RG p2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms6) z); [apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Lz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Lz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG p2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Lz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG p2Lz_e1 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Lz_e1)).
{ cbn [ss_mem p2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Lz_e1 ms6 _ 48 (ss_mem p2Lz_e1) (gu + SB) (ge - gu) (sp0 - 2208) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MS_SCR in *; lia). apply MEQ6. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MS_SCR, MS_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE' p2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG p2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG p2Ln_e0 12) (RG p2Ln_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Ln_e1 19) (RG p2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms7) z); [apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Ln_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Ln_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG p2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Ln_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG p2Ln_e2 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Ln_e2)).
{ cbn [ss_mem p2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Ln_e2 ms7 _ 48 (ss_mem p2Ln_e2) (gu + SB) (ge - gu) (sp0 - 2208) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MS_SCR in *; lia). apply MEQ7. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MS_SCR, MS_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF9 HFr9.
apply (finish EE' p2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
Qed.
Lemma path2H : 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2216) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= d + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= d + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE2. pose proof (Env10 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE10. pose proof (Env12 [g0; g1; b1; 0; 0; du; de; gu; ge]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p2H_e0 13) (RG p2H_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG p2H_e1 18) HS2 (br_end_high EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2H_e2 8) (RG p2H_e2 18) HS3 (br_beg_lt_end EE 10 12 d n EE10 EE12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_p2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Hz_e0 19) (RG p2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms6) z); [apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Hz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Hz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG p2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Hz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG p2Hz_e1 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Hz_e1)).
{ cbn [ss_mem p2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Hz_e1 ms6 _ 48 (ss_mem p2Hz_e1) (gu + SB) (ge - gu) (sp0 - 2208) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ7 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MS_SCR in *; lia). apply MEQ6. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MS_SCR, MS_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS7 r_p2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE' p2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG p2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_p2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG p2Hn_e0 12) (RG p2Hn_e0 11) HS5 (rp_blt_last EE 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_p2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p2Hn_e1 19) (RG p2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply (apresent_same H mem (ms_mem ms7) z); [apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK; lia | apply Bpres; lia]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MS_STK, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot EE (RG p2Hn_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG p2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG p2Hn_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG p2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG p2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG p2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG p2Hn_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot EE (RG p2Hn_e2 1)) with (sv_denot EE (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem p2Hn_e2)).
{ cbn [ss_mem p2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MS_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE p2Hn_e2 ms7 _ 48 (ss_mem p2Hn_e2) (gu + SB) (ge - gu) (sp0 - 2208) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 48 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (rewrite (EE'reg 2%nat 2%bv eq_refl); reflexivity).
assert (MEQ8 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MS_SCR in *; lia). apply MEQ7. unfold MS_SCR, MS_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MS_SCR, MS_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W EE' _ _ _ _ _ HS8 r_p2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MS_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MS_SCR <= bv_unsigned z < sp0 - MS_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF9 HFr9.
apply (finish EE' p2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; split; [exact (proj1 (Bpres a ltac:(unfold MS_SCR, MS_STK in *; lia))) |];
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (unfold MS_SCR, MS_STK in *; lia); exact Ha) Eb)].
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.
Theorem memset_icpt_srr : SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [apply path0; exact Hn0|].
destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0 <= d < 8 * g0 + 8) by (subst g0; pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1 - g0) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply path1_0 | apply path1_1 | apply path1_2 | apply path1_3 | apply path1_4 | apply path1_5 | apply path1_6 | apply path1_7 | apply path1_8]; assumption.
- destruct HAM as [HL|HH]; [apply path2L; [lia | exact HL] | apply path2H; [lia | exact HH]].
Qed.
End e.
Theorem memset_icpt_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall ly S (W : world tfibsegs) regs mem md d x n,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
amem_range d n ->
SRr tfibsegs W (cfg_at tfibsegs 0x515d4 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM.
exact (memset_icpt_srr B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
End c.
