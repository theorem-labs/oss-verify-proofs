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
Lemma entD2L : forall ms b1, MIDP ms -> 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2L (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
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
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2L [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2160) mod 16 = 0 => replace (a - 2160) with (a + (-135) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2L. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 20 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 20 20%bv eq_refl); exact M20 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD2H : forall ms b1, MIDP ms -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2H (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
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
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2H [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2160) mod 16 = 0 => replace (a - 2160) with (a + (-135) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2H. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 20 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 20 20%bv eq_refl); exact M20 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD2L : forall ms0 mat0, MIDP ms0 -> 64 < n -> d + n <= kLowMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (rewrite E42; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (rewrite E43; apply unsigned_lit_small; lia).
pose proof (entD2L ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2L_e0 13) (RG w2L_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_GEU (SLit 2147450879) (RG w2L_e1 18) HS2 (br_end_low ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2L_e2 8) (RG w2L_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(rewrite E44, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Lz_e0 19) (RG w2Lz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Lz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Lz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Lz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Lz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Lz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot ED (RG w2Lz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Lz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot ED (RG w2Lz_e1 1)) with (sv_denot ED (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Lz_e1)).
{ cbn [ss_mem w2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Lz_e1 ms6 _ 56 (ss_mem w2Lz_e1) (gud + SB) (ged - gud) (sp0 - 2224) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2160)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Ln_e1 19) (RG w2Ln_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Ln_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Ln_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Ln_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Ln_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Ln_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot ED (RG w2Ln_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Ln_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot ED (RG w2Ln_e2 1)) with (sv_denot ED (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Ln_e2)).
{ cbn [ss_mem w2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Ln_e2 ms7 _ 56 (ss_mem w2Ln_e2) (gud + SB) (ged - gud) (sp0 - 2224) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2160)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD2H : forall ms0 mat0, MIDP ms0 -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
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
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (rewrite E42; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (rewrite E43; apply unsigned_lit_small; lia).
pose proof (entD2H ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2H_e0 13) (RG w2H_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (SLit 140737488355327) (RG w2H_e1 18) HS2 (br_end_high ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2H_e2 8) (RG w2H_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(rewrite E44, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hz_e0 19) (RG w2Hz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hz_e1 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot ED (RG w2Hz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hz_e1 1) = Z_to_bv 64 344780).
{ change (sv_denot ED (RG w2Hz_e1 1)) with (sv_denot ED (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hz_e1)).
{ cbn [ss_mem w2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hz_e1 ms6 _ 56 (ss_mem w2Hz_e1) (gud + SB) (ged - gud) (sp0 - 2224) 344780 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2160)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hn_e1 19) (RG w2Hn_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2224 - 8 <= z < sp0 - 2224 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hn_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hn_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hn_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hn_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hn_e2 2) = Z_to_bv 64 (sp0 - 2224)).
{ change (sv_denot ED (RG w2Hn_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hn_e2 1) = Z_to_bv 64 344780).
{ change (sv_denot ED (RG w2Hn_e2 1)) with (sv_denot ED (SLit 344780)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2224 - 8 \/ sp0 - 2224 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hn_e2)).
{ cbn [ss_mem w2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hn_e2 ms7 _ 56 (ss_mem w2Hn_e2) (gud + SB) (ged - gud) (sp0 - 2224) 344780 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 344780 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2160)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
End e.
End c.
