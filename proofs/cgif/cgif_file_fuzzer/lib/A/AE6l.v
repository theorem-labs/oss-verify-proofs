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
Lemma entD1_0 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 0 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 0) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 0 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 0)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 0 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_1 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 1) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 1 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 1)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 1 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_2 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 2 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 2) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 2 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 2)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 2 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_0 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 0 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_0 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_0_e0 13) (RG w1_0_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_0_e1 13) (RG w1_0_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_0_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450880 E42) by lia. f_equal. subst h2. replace (g0d + 2147450880) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_0_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_0_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 0%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_1 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_1 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_1_e0 13) (RG w1_1_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_1_e1 13) (RG w1_1_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_1_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450881 E42) by lia. f_equal. subst h2. replace (g0d + 2147450881) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_1_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_1_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 1%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_2 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 2 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_2 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_2_e0 13) (RG w1_2_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_2_e1 13) (RG w1_2_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_2_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450882 E42) by lia. f_equal. subst h2. replace (g0d + 2147450882) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_2_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_2_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 2%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
End e.
End c.
