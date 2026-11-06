(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build. *)
(* Modified by Theorem Labs, 2026-10: relocated to reac-repacer/fuzz_wire's asan build: addresses and numbers moved by symbol to its asan image; module paths changed; the image end read from TFIB_IMG_END (PcapImgEnd dropped); the symbol record PcapSyms renamed WireSyms. *)
(* Declaration: the structure follows proofs/cgif/cgif_file_fuzzer/lib/A/AE6l.v .. A/AE6s.v (origin/ossv/recipes c8557374ad2e); its image-symbol record TfibSyms is renamed WireSyms, and every numeral is pcap's own, measured on the v1.9.0 asan pin. *)
(* The paths of the walk of __asan_memmove (0x51310): one lemma per shape of the quick shadow check of
   each range (t = g1 - g0 in 0..8 granules for n <= 64) and one per half of the
   __asan_region_is_poisoned path (n > 64, low and high memory), for the source phase (entry -> 0x513a4)
   and for the destination phase (0x513a4 -> the call at 0x513f0).  Ported from the memcpy paths of
   proofs/cgif/cgif_file_fuzzer/lib/A/AE6l.v, AE6m.v, AE6n.v, AE6o.v, AE6p.v, AE6q.v, AE6r.v and AE6s.v:
   the overlap prelude of each source path is dropped (__asan_memmove has none), the two shadow loads
   read into a6 / a7 instead of a5 / a6, the class test reads s3, and the destination-phase atom block
   starts at 40 because only 8 registers are saved. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt Require Import MemmoveIm MemmoveK.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : WireSyms B.
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
Local Notation POSTc := (MemmoveK.POSTc B ly S W regs mem md d x n).
Local Notation SV := (MemmoveK.SV regs).
Local Notation MIDP := (MemmoveK.MIDP W regs mem d x n).
Local Notation MIDQ := (MemmoveK.MIDQ W regs mem md d x n).
Local Notation basics := (MemmoveK.basics B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation finish0 := (MemmoveK.finish0 B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HAMX).
Local Notation finishD := (MemmoveK.finishD B LAWS ly S W regs mem md d x n HPRE Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HAMX).
Local Notation midS := (MemmoveK.midS B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd HAM Hx0 HAMX).
Local Notation EnvS_reg := (MemmoveK.EnvS_reg regs).
Local Notation EnvS_x := (MemmoveK.EnvS_x regs).
Local Notation EnvS2 := (MemmoveK.EnvS2 regs).
Local Notation EnvS10 := (MemmoveK.EnvS10 regs d G10).
Local Notation EnvS11 := (MemmoveK.EnvS11 regs x G11).
Local Notation EnvS12 := (MemmoveK.EnvS12 regs n G12).
Local Notation entS_stk := (MemmoveK.entS_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation entS_ro := (MemmoveK.entS_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation EnvD := (MemmoveK.EnvD regs).
Local Notation EnvD_reg := (MemmoveK.EnvD_reg regs).
Local Notation EnvD_sv := (MemmoveK.EnvD_sv regs d x n Hd Hx0).
Local Notation EnvD_x := (MemmoveK.EnvD_x regs d x n Hd Hx0).
Local Notation EnvD2 := (MemmoveK.EnvD2 B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation EnvD10 := (MemmoveK.EnvD10 W regs mem d x n).
Local Notation EnvD11 := (MemmoveK.EnvD11 W regs mem d x n).
Local Notation EnvD12 := (MemmoveK.EnvD12 W regs mem d x n).
Local Notation entD_stk := (MemmoveK.entD_stk B ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation entD_ro := (MemmoveK.entD_ro B TB ly S W regs mem md d x n HPRE Hn Hd HAM Hx0 HAMX).
Local Notation pathS0 := (MemmoveK.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HAMX).
Lemma entS1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 0 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 0) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
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
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 1) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
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
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 2) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 2 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_0 : 1 <= n <= 64 -> g1s - g0s = 0 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_0_e0 13) (RG q1_0_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_0_e1 13) (RG q1_0_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_0_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450880 E32) by lia. f_equal. subst h2. replace (g0s + 2147450880) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_0_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_0_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_0z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_0n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_1 : 1 <= n <= 64 -> g1s - g0s = 1 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_1_e0 13) (RG q1_1_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_1_e1 13) (RG q1_1_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_1_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450881 E32) by lia. f_equal. subst h2. replace (g0s + 2147450881) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_1_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_1_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_1z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_1n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_2 : 1 <= n <= 64 -> g1s - g0s = 2 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_2_e0 13) (RG q1_2_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_2_e1 13) (RG q1_2_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_2_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450882 E32) by lia. f_equal. subst h2. replace (g0s + 2147450882) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_2_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_2_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_2z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_2n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entS1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 3 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 3) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 3 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 4 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 4) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 4 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 5 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 5) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 5 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_3 : 1 <= n <= 64 -> g1s - g0s = 3 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_3_e0 13) (RG q1_3_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_3_e1 13) (RG q1_3_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_3_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450883 E32) by lia. f_equal. subst h2. replace (g0s + 2147450883) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_3_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_3_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_3z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 3%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_3n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_4 : 1 <= n <= 64 -> g1s - g0s = 4 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_4_e0 13) (RG q1_4_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_4_e1 13) (RG q1_4_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_4_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450884 E32) by lia. f_equal. subst h2. replace (g0s + 2147450884) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_4_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_4_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_4z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 4%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_4n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_5 : 1 <= n <= 64 -> g1s - g0s = 5 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_5_e0 13) (RG q1_5_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_5_e1 13) (RG q1_5_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_5_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450885 E32) by lia. f_equal. subst h2. replace (g0s + 2147450885) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_5_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_5_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_5z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 5%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_5n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entS1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 6 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 6) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 6 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 7 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 7) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 7 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 8 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 8) (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MM_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 8 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_6 : 1 <= n <= 64 -> g1s - g0s = 6 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_6_e0 13) (RG q1_6_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_6_e1 13) (RG q1_6_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_6_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450886 E32) by lia. f_equal. subst h2. replace (g0s + 2147450886) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_6_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_6_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_6z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 6%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_6n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_7 : 1 <= n <= 64 -> g1s - g0s = 7 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_7_e0 13) (RG q1_7_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_7_e1 13) (RG q1_7_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_7_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450887 E32) by lia. f_equal. subst h2. replace (g0s + 2147450887) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_7_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_7_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_7z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 7%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_7n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS1_8 : 1 <= n <= 64 -> g1s - g0s = 8 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
pose proof (entS1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_8_e0 13) (RG q1_8_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_8_e1 13) (RG q1_8_e1 19) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_8_e2) ms3 _ 16%bv 16%bv 538627 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450888 E32) by lia. f_equal. subst h2. replace (g0s + 2147450888) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_8_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc q1_8_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS6' r_q1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_8z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 8%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MM_MID _ _ _ _ _ HS7' r_q1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_8n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entS2L : forall b1, 64 < n -> x + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2L (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MM_STK.
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
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2H (restrict H (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs))).
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
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MM_STK.
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
Lemma pathS2L : 64 < n -> x + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2L_e0 13) (RG q2L_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG q2L_e1 18) HS2 (br_end_low EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2L_e2 8) (RG q2L_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Lz_e0 19) (RG q2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Lz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Lz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Lz_e1 1) = Z_to_bv 64 343188).
{ change (sv_denot EE (RG q2Lz_e1 1)) with (sv_denot EE (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Lz_e1)).
{ cbn [ss_mem q2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Lz_e1 ms6 _ 56 (ss_mem q2Lz_e1) (gus + SB) (ges - gus) (sp0 - 2208) 343188 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MM_SCR in *; lia). apply MEQ6. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MM_SCR, MM_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MM_MID _ _ _ _ _ HS7 r_q2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Lz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Ln_e1 19) (RG q2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Ln_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Ln_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Ln_e2 1) = Z_to_bv 64 343188).
{ change (sv_denot EE (RG q2Ln_e2 1)) with (sv_denot EE (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Ln_e2)).
{ cbn [ss_mem q2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Ln_e2 ms7 _ 56 (ss_mem q2Ln_e2) (gus + SB) (ges - gus) (sp0 - 2208) 343188 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MM_SCR in *; lia). apply MEQ7. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MM_SCR, MM_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MM_MID _ _ _ _ _ HS8 r_q2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Ln_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathS2H : 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MM_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MM_ENTRY) with (Z_to_bv 64 MM_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem (mkst regs (Z_to_bv 64 MM_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MM_SCR, MM_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2H_e0 13) (RG q2H_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG q2H_e1 18) HS2 (br_end_high EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2H_e2 8) (RG q2H_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hz_e0 19) (RG q2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hz_e1 1) = Z_to_bv 64 343188).
{ change (sv_denot EE (RG q2Hz_e1 1)) with (sv_denot EE (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hz_e1)).
{ cbn [ss_mem q2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hz_e1 ms6 _ 56 (ss_mem q2Hz_e1) (gus + SB) (ges - gus) (sp0 - 2208) 343188 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MM_SCR in *; lia). apply MEQ6. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MM_SCR, MM_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MM_MID _ _ _ _ _ HS7 r_q2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Hz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hn_e1 19) (RG q2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hn_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hn_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hn_e2 1) = Z_to_bv 64 343188).
{ change (sv_denot EE (RG q2Hn_e2 1)) with (sv_denot EE (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hn_e2)).
{ cbn [ss_mem q2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hn_e2 ms7 _ 56 (ss_mem q2Hn_e2) (gus + SB) (ges - gus) (sp0 - 2208) 343188 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MM_SCR in *; lia). apply MEQ7. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MM_SCR, MM_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MM_MID _ _ _ _ _ HS8 r_q2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MM_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Hn_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD1_0 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 0 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 0) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 0 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 0)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 0 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_1 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 1) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 1 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 1)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 1 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_2 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 2 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 2) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 2 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 2)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 2 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_0 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 0 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_0 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_0_e0 13) (RG w1_0_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_0_e1 13) (RG w1_0_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_0_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450880 E40) by lia. f_equal. subst h2. replace (g0d + 2147450880) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_0_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_0_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 0%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_1 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_1 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_1_e0 13) (RG w1_1_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_1_e1 13) (RG w1_1_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_1_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450881 E40) by lia. f_equal. subst h2. replace (g0d + 2147450881) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_1_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_1_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 1%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_2 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 2 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_2 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_2_e0 13) (RG w1_2_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_2_e1 13) (RG w1_2_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_2_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450882 E40) by lia. f_equal. subst h2. replace (g0d + 2147450882) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_2_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_2_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 2%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD1_3 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 3 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 3) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 3 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 3)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 3 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_4 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 4 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 4) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 4 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 4)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 4 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_5 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 5 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 5) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 5 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 5)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 5 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_3 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 3 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_3 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_3_e0 13) (RG w1_3_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_3_e1 13) (RG w1_3_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_3_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450883 E40) by lia. f_equal. subst h2. replace (g0d + 2147450883) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_3_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_3_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 3%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_4 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 4 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_4 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_4_e0 13) (RG w1_4_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_4_e1 13) (RG w1_4_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_4_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450884 E40) by lia. f_equal. subst h2. replace (g0d + 2147450884) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_4_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_4_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 4%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_5 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 5 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_5 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_5_e0 13) (RG w1_5_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_5_e1 13) (RG w1_5_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_5_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450885 E40) by lia. f_equal. subst h2. replace (g0d + 2147450885) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_5_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_5_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_5_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 5%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD1_6 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 6 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 6) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 6 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 6)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 6 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_7 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 7 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 7) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 7 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 7)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 7 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_8 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 8 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 8) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shreg1 40 8 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 40 8)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 40 g0d 8 E40) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_6 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 6 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_6 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_6_e0 13) (RG w1_6_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_6_e1 13) (RG w1_6_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_6_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450886 E40) by lia. f_equal. subst h2. replace (g0d + 2147450886) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_6_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_6_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_6_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 6%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_7 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 7 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_7 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_7_e0 13) (RG w1_7_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_7_e1 13) (RG w1_7_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_7_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450887 E40) by lia. f_equal. subst h2. replace (g0d + 2147450887) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_7_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_7_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_7_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 7%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_8 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 8 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_8 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_8_e0 13) (RG w1_8_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_8_e1 13) (RG w1_8_e1 19) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 43))).
{ rewrite E43, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_8_e2) ms3 _ 16%bv 16%bv 538627 h1 43 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 40 g0d 2147450880 E40 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 40 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 40 g0d 2147450888 E40) by lia. f_equal. subst h2. replace (g0d + 2147450888) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 44))).
{ rewrite E44, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MM_STK, MM_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_8_e2 [((16%bv : bv 5), SOff 43 0)] (ss_pc w1_8_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 44 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_8_e3 16) (SLit 0) HS6 (eq_trans (br_hull ED 43 44 q1 q2 E43 E44 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 8%nat 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD2L : forall ms b1, MIDP ms -> 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2L (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E41 : ew EE 41 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E45 : ew EE 45 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E46 : ew EE 46 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shregs2 40 ++ map ro_region icpt_rodata) None (mkFacts factsD2L [] (aliases2 10 40)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 41%nat)) with (bv_unsigned (ew EE 41)). rewrite E41, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, E41, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E41, E42, E45, E46, E47, E48, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 41 g1d E41) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 45 dud E45) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 46 ded E46) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 45 dud E45), (U_atom EE 47 gud E47) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 46 ded E46), (U_atom EE 48 ged E48) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2L. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD2H : forall ms b1, MIDP ms -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2H (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MM_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E40 : ew EE 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E41 : ew EE 41 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E42 : ew EE 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E45 : ew EE 45 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E46 : ew EE 46 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MM_MID sr_atoms (stkD :: shregs2 40 ++ map ro_region icpt_rodata) None (mkFacts factsD2H [] (aliases2 10 40)))
(mkst (ms_regs ms) (Z_to_bv 64 MM_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 40%nat)) with (bv_unsigned (ew EE 40)). rewrite E40, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 41%nat)) with (bv_unsigned (ew EE 41)). rewrite E41, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 42 0) b1); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E40, E41, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E40, E41, E42, E45, E46, E47, E48, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 40 g0d E40) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 41 g1d E41) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 45 dud E45) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 46 ded E46) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 45 dud E45), (U_atom EE 47 gud E47) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 46 ded E46), (U_atom EE 48 ged E48) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2H. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl), M19, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD2L : forall ms0 mat0, MIDP ms0 -> 64 < n -> d + n <= kLowMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E41 : ew ED 41 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E47 : ew ED 47 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E48 : ew ED 48 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 40) = g0d) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 41) = g1d) by (rewrite E41; apply unsigned_lit_small; lia).
pose proof (entD2L ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2L_e0 13) (RG w2L_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_GEU (SLit 2147450879) (RG w2L_e1 18) HS2 (br_end_low ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2L_e2 8) (RG w2L_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_zero ED 42 ltac:(rewrite E42, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Lz_e0 19) (RG w2Lz_e0 10) HS5 (br_sbeg_lt_send ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Lz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Lz_e1 10)) with (sv_denot ED (SOff 47 SB)). cbn [sv_denot]. rewrite E47, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Lz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Lz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 47 0) (SLit (-1))) (SOff 48 0))). exact (U_mz_len ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Lz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Lz_e1 1) = Z_to_bv 64 343188).
{ change (sv_denot ED (RG w2Lz_e1 1)) with (sv_denot ED (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Lz_e1)).
{ cbn [ss_mem w2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Lz_e1 ms6 _ 56 (ss_mem w2Lz_e1) (gud + SB) (ged - gud) (sp0 - 2208) 343188 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 8)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MM_SCR in *; lia). apply MEQ6. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MM_SCR, MM_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 42 b1 E42 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11) HS5 (rp_blt_last ED 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Ln_e1 19) (RG w2Ln_e1 10) HS6 (br_sbeg_lt_send ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Ln_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Ln_e2 10)) with (sv_denot ED (SOff 47 SB)). cbn [sv_denot]. rewrite E47, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Ln_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Ln_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 47 0) (SLit (-1))) (SOff 48 0))). exact (U_mz_len ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Ln_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Ln_e2 1) = Z_to_bv 64 343188).
{ change (sv_denot ED (RG w2Ln_e2 1)) with (sv_denot ED (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Ln_e2)).
{ cbn [ss_mem w2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Ln_e2 ms7 _ 56 (ss_mem w2Ln_e2) (gud + SB) (ged - gud) (sp0 - 2208) 343188 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 8)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MM_SCR in *; lia). apply MEQ7. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MM_SCR, MM_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD2H : forall ms0 mat0, MIDP ms0 -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M3 & M4 & M23 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MM_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MM_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MM_SCR, MM_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 8)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E40 : ew ED 40 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E41 : ew ED 41 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E42 : ew ED 42 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E47 : ew ED 47 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E48 : ew ED 48 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 40) = g0d) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 41) = g1d) by (rewrite E41; apply unsigned_lit_small; lia).
pose proof (entD2H ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2H_e0 13) (RG w2H_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (SLit 140737488355327) (RG w2H_e1 18) HS2 (br_end_high ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2H_e2 8) (RG w2H_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_zero ED 42 ltac:(rewrite E42, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hz_e0 19) (RG w2Hz_e0 10) HS5 (br_sbeg_lt_send ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hz_e1 10)) with (sv_denot ED (SOff 47 SB)). cbn [sv_denot]. rewrite E47, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 47 0) (SLit (-1))) (SOff 48 0))). exact (U_mz_len ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Hz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hz_e1 1) = Z_to_bv 64 343188).
{ change (sv_denot ED (RG w2Hz_e1 1)) with (sv_denot ED (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hz_e1)).
{ cbn [ss_mem w2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hz_e1 ms6 _ 56 (ss_mem w2Hz_e1) (gud + SB) (ged - gud) (sp0 - 2208) 343188 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 8)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MM_SCR in *; lia). apply MEQ6. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MM_SCR, MM_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 42 b1 E42 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11) HS5 (rp_blt_last ED 10 12 42 d n b1 ED10 ED12 E42 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hn_e1 19) (RG w2Hn_e1 10) HS6 (br_sbeg_lt_send ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MM_SCR, MM_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MM_STK, MM_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hn_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hn_e2 10)) with (sv_denot ED (SOff 47 SB)). cbn [sv_denot]. rewrite E47, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hn_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hn_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 47 0) (SLit (-1))) (SOff 48 0))). exact (U_mz_len ED 47 48 gud ged E47 E48 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Hn_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hn_e2 1) = Z_to_bv 64 343188).
{ change (sv_denot ED (RG w2Hn_e2 1)) with (sv_denot ED (SLit 343188)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hn_e2)).
{ cbn [ss_mem w2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MM_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hn_e2 ms7 _ 56 (ss_mem w2Hn_e2) (gud + SB) (ged - gud) (sp0 - 2208) 343188 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 343188 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 8)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MM_SCR in *; lia). apply MEQ7. unfold MM_SCR, MM_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MM_SCR, MM_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MM_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MM_STK, MM_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MM_SCR <= bv_unsigned z < sp0 - MM_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MM_STK, MM_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M23 M24 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MM_SCR, MM_STK in *. lia.
- intros a Ha. unfold MM_SCR, MM_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
End e.
End c.
