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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y AE6k.
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
Local Notation POSTc := (AE6k.POSTc B ly S W regs mem md d x n).
Local Notation SV := (AE6k.SV regs).
Local Notation MIDP := (AE6k.MIDP W regs mem d x n).
Local Notation MIDQ := (AE6k.MIDQ W regs mem md d x n).
Local Notation basics := (AE6k.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation finish0 := (AE6k.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation finishD := (AE6k.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Local Notation midS := (AE6k.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HAM Hx0 HDISJ HAMX).
Local Notation EnvS_reg := (AE6k.EnvS_reg regs).
Local Notation EnvS_x := (AE6k.EnvS_x regs).
Local Notation EnvS2 := (AE6k.EnvS2 regs).
Local Notation EnvS10 := (AE6k.EnvS10 regs d G10).
Local Notation EnvS11 := (AE6k.EnvS11 regs x G11).
Local Notation EnvS12 := (AE6k.EnvS12 regs n G12).
Local Notation entS_stk := (AE6k.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entS_ro := (AE6k.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD := (AE6k.EnvD regs).
Local Notation EnvD_reg := (AE6k.EnvD_reg regs).
Local Notation EnvD_sv := (AE6k.EnvD_sv regs d x).
Local Notation EnvD_x := (AE6k.EnvD_x regs d x n Hn Hd Hx0).
Local Notation EnvD2 := (AE6k.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation EnvD10 := (AE6k.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (AE6k.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (AE6k.EnvD12 W regs mem d x n).
Local Notation entD_stk := (AE6k.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation entD_ro := (AE6k.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HDISJ HAMX).
Local Notation pathS0 := (AE6k.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HDISJ HAMX).
Lemma entS1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 0 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 0) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 0 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 1) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 1 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 2 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 2) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 2 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_0 : 1 <= n <= 64 -> g1s - g0s = 0 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_0_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_0_e0 13) (RG q1_0_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_0_e1 13) (RG q1_0_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_0_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450880 E32) by lia. f_equal. subst h2. replace (g0s + 2147450880) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_0_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_0z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_0n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_0o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
assert (Hdx : d <> x) by lia.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q1_0o_e0 10) (RG q1_0o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_0oA_0)|].
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
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0oB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_0oB_e0 10) (RG q1_0oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_0oB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_0oB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q1_0oA_e0 11) (RG q1_0oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0oA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_0oA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS1_1 : 1 <= n <= 64 -> g1s - g0s = 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_1_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_1_e0 13) (RG q1_1_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_1_e1 13) (RG q1_1_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_1_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450881 E32) by lia. f_equal. subst h2. replace (g0s + 2147450881) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_1_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_1z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_1n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_1o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
assert (Hdx : d <> x) by lia.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q1_1o_e0 10) (RG q1_1o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_1oA_0)|].
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
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1oB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_1oB_e0 10) (RG q1_1oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_1oB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_1oB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q1_1oA_e0 11) (RG q1_1oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1oA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_1oA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
Lemma pathS1_2 : 1 <= n <= 64 -> g1s - g0s = 2 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_2_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_2_e0 13) (RG q1_2_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_2_e1 13) (RG q1_2_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_2_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450882 E32) by lia. f_equal. subst h2. replace (g0s + 2147450882) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_2_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_2z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_2n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_2o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
assert (Hdx : d <> x) by lia.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q1_2o_e0 10) (RG q1_2o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hdx))) as HS1n.
change (neg_bc BC_EQ) with BC_NE in HS1n. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1n r_q1_2oA_0)|].
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
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_lt _ _) Hov)))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2oB_0)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_2oB_e0 10) (RG q1_2oB_e0 21) HS3 (eq_trans (br_ltu_atom_add2 EE 10 11 12 d x n EE10 EE11 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge d (x + n)) ltac:(lia)))) as HS3'.
change (neg_bc BC_LTU) with BC_GEU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q1_2oB_1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
pose proof (st_ok_dropc EE _ _ HS4) as HSq. rewrite q1_2oB_canon in HSq. exact (CONT ms4 mat4 HSq MEQ4 PSL4).
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (RG q1_2oA_e0 11) (RG q1_2oA_e0 19) HS2 (eq_trans (br_geu_atom_add2 EE 11 10 12 x d n EE11 EE10 EE12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) (f_equal negb (proj2 (Z.ltb_ge _ _) Hov)))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2oA_1)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_dropc EE _ _ HS3) as HSq. rewrite q1_2oA_canon in HSq. exact (CONT ms3 mat3 HSq MEQ3 PSL3).
Qed.
End e.
End c.
