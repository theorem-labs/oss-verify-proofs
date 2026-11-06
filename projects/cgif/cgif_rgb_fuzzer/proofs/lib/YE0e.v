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
Lemma entD2L : forall ms b1, MIDP ms -> 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfxsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2L (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms _ 0); img_refl)).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (img_try (img_apply (EnvD_x ms _ 1); img_refl)).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms _ 2); img_refl)).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (img_try (img_apply (EnvD_x ms _ 5); img_refl)).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (img_try (img_apply (EnvD_x ms _ 6); img_refl)).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (img_try (img_apply (EnvD_x ms _ 7); img_refl)).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (img_try (img_apply (EnvD_x ms _ 8); img_refl)).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (img_try ((subst gud dud; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (img_try ((subst ged ded; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). img_refl. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfxsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2L [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfxsegs))).
{ unfold EE, EnvD, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply (entD_stk ms _ HM)) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply (entD_ro ms _ HM)]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (img_try (unfold kHighMemBeg in *; img_lia)).
fold (mbyte tfxsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n g0d HRA ltac:(img_lia) Hd). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Nat.add].
img_change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1d _ 1 (SOff 44 0) b1); [img_try (cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply (val_mem_frame H mem (ms_mem ms)); [img_try (intros k Hk; img_apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; img_lia); unfold kHighMemBeg in *; img_lia)|].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsD2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; img_apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; img_apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by img_lia end; rewrite Z_mod_plus_full; img_exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by img_lia. pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by img_lia. pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl. }
unfold ssD2L. img_apply (st_ok_regs tfxsegs EE _ _ sr_mid HS0). img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| img_apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by img_lia; symmetry; img_apply (U_atom EE 19 (d + n)); [img_try ((subst EE; cbv beta); rewrite (EnvD_reg ms _ 19 19%bv eq_refl); img_exact M19) | img_lia]
| cbn [sv_denot]; rewrite E12; (subst EE; cbv beta); rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by img_lia; img_refl ] |]).
destruct Hr.
Qed.
Lemma entD2H : forall ms b1, MIDP ms -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfxsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2H (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms _ 0); img_refl)).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (img_try (img_apply (EnvD_x ms _ 1); img_refl)).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms _ 2); img_refl)).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (img_try (img_apply (EnvD_x ms _ 5); img_refl)).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (img_try (img_apply (EnvD_x ms _ 6); img_refl)).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (img_try (img_apply (EnvD_x ms _ 7); img_refl)).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (img_try (img_apply (EnvD_x ms _ 8); img_refl)).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (img_try ((subst gud dud; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (img_try ((subst ged ded; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). img_refl. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfxsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2H [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfxsegs))).
{ unfold EE, EnvD, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply (entD_stk ms _ HM)) | img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply (entD_ro ms _ HM)]])].
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
img_change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (img_try (unfold kHighMemBeg in *; img_lia)).
fold (mbyte tfxsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (YF8r.aview_byte H mem _ 0); [img_refl|].
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n g0d HRA ltac:(img_lia) Hd). unfold SB. f_equal. img_lia.
+ unfold region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Nat.add].
img_change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs EE _ g1d _ 1 (SOff 44 0) b1); [img_try (cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |].
img_apply (val_mem_frame H mem (ms_mem ms)); [img_try (intros k Hk; img_apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; img_lia); unfold kHighMemBeg in *; img_lia)|].
img_apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsD2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. img_change (2 ^ 3) with 8. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; img_apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; img_apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by img_lia end; rewrite Z_mod_plus_full; img_exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|img_try (split; [|split; [|split; [|split; [|split; [|img_exact I]]]]])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by img_lia. img_refl.
* img_apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by img_lia. pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by img_lia. pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)). img_lia.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by img_lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by img_lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by img_lia. img_refl. }
unfold ssD2H. img_apply (st_ok_regs tfxsegs EE _ _ sr_mid HS0). img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| img_apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by img_lia; symmetry; img_apply (U_atom EE 19 (d + n)); [img_try ((subst EE; cbv beta); rewrite (EnvD_reg ms _ 19 19%bv eq_refl); img_exact M19) | img_lia]
| cbn [sv_denot]; rewrite E12; (subst EE; cbv beta); rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by img_lia; img_refl ] |]).
destruct Hr.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MC_STK, MC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    clear HFk HFrk.

Lemma pathD2L : forall ms0 mat0, MIDP ms0 -> 64 < n -> d + n <= kLowMemEnd - 1 ->
SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (img_try (unfold MC_SCR; img_exact MEQ0)).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1d < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (img_try ((subst gud dud; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (img_try ((subst ged ded; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (img_try (intros; img_apply EnvD_reg; assumption)).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros; img_apply EnvD_sv; assumption)).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms0 _ 0); img_refl)).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (img_try (img_apply (EnvD_x ms0 _ 1); img_refl)).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms0 _ 2); img_refl)).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (img_try (img_apply (EnvD_x ms0 _ 7); img_refl)).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (img_try (img_apply (EnvD_x ms0 _ 8); img_refl)).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (img_try (rewrite E42; img_apply unsigned_lit_small; img_lia)).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (img_try (rewrite E43; img_apply unsigned_lit_small; img_lia)).
pose proof (entD2L ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [img_norm_st HS0 r_w2L_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2L_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (RG w2L_e0 13) (RG w2L_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_w2L_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2L_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_GEU (SLit 2147450879) (RG w2L_e1 18) HS2 (br_end_low ED 10 12 d n ED10 ED12 Hd ltac:(img_lia) ltac:(img_try (unfold kLowMemEnd in *; img_lia)))) as HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_w2L_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2L_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2L_e2 8) (RG w2L_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_w2L_3; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2L_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 ED ED2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(img_try (rewrite E44, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_w2Lz_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Lz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2Lz_e0 19) (RG w2Lz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_w2Lz_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Lz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot ED (RG w2Lz_e1 10) = Z_to_bv 64 (gud + SB)).
{ img_change (sv_denot ED (RG w2Lz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot ED (RG w2Lz_e1 11) = Z_to_bv 64 (ged - gud)).
{ img_change (sv_denot ED (RG w2Lz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). img_exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot ED (RG w2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ img_change (sv_denot ED (RG w2Lz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; img_lia. }
assert (R1 : sv_denot ED (RG w2Lz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot ED (RG w2Lz_e1 1)) with (sv_denot ED (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem w2Lz_e1)).
{ cbn [ss_mem w2Lz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W ED w2Lz_e1 ms6 _ 56 (ss_mem w2Lz_e1) (gud + SB) (ged - gud) (sp0 - 2208) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. (subst ED'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EDreg. img_exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (img_try ((subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact ED2)).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros j Hj; (subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_apply EDsv; img_exact Hj)).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ6. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_w2Lz_2; img_try (img_apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Lz_2))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 ED' ED'2.
img_apply (finishD ED' (ms_regs ms0) w2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_w2Ln_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Ln_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(img_lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_w2Ln_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Ln_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2Ln_e1 19) (RG w2Ln_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w2Ln_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Ln_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot ED (RG w2Ln_e2 10) = Z_to_bv 64 (gud + SB)).
{ img_change (sv_denot ED (RG w2Ln_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot ED (RG w2Ln_e2 11) = Z_to_bv 64 (ged - gud)).
{ img_change (sv_denot ED (RG w2Ln_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). img_exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot ED (RG w2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ img_change (sv_denot ED (RG w2Ln_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; img_lia. }
assert (R1 : sv_denot ED (RG w2Ln_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot ED (RG w2Ln_e2 1)) with (sv_denot ED (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem w2Ln_e2)).
{ cbn [ss_mem w2Ln_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W ED w2Ln_e2 ms7 _ 56 (ss_mem w2Ln_e2) (gud + SB) (ged - gud) (sp0 - 2208) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. (subst ED'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EDreg. img_exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (img_try ((subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact ED2)).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros j Hj; (subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_apply EDsv; img_exact Hj)).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_w2Ln_3; img_try (img_apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Ln_3))|].
icpt_l1t_0 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 ED' ED'2.
img_apply (finishD ED' (ms_regs ms0) w2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. img_apply MEQ9. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma pathD2H : forall ms0 mat0, MIDP ms0 -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 ->
SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (img_try (unfold MC_SCR; img_exact MEQ0)).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1d < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (img_try ((subst gud dud; cbv beta); pose proof (Z.div_mod (d + 7) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(img_lia)); img_lia)).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (img_try ((subst ged ded; cbv beta); pose proof (Z.div_mod (d + n) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(img_lia)); img_lia)).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (img_try (intros; img_apply EnvD_reg; assumption)).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros; img_apply EnvD_sv; assumption)).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms0 _ 0); img_refl)).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (img_try (img_apply (EnvD_x ms0 _ 1); img_refl)).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms0 _ 2); img_refl)).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (img_try (img_apply (EnvD_x ms0 _ 7); img_refl)).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (img_try (img_apply (EnvD_x ms0 _ 8); img_refl)).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (img_try (rewrite E42; img_apply unsigned_lit_small; img_lia)).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (img_try (rewrite E43; img_apply unsigned_lit_small; img_lia)).
pose proof (entD2H ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [img_norm_st HS0 r_w2H_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2H_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (RG w2H_e0 13) (RG w2H_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_w2H_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2H_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (SLit 140737488355327) (RG w2H_e1 18) HS2 (br_end_high ED 10 12 d n ED10 ED12 Hd ltac:(img_lia) ltac:(img_try (unfold kHighMemEnd in *; img_lia)))) as HS2'.
img_change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_w2H_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2H_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2H_e2 8) (RG w2H_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(img_lia) ltac:(img_lia))) as HS3'.
img_change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [img_norm_st HS3' r_w2H_3; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2H_3))|].
icpt_l1t_0 W4 c4 ms4 mat4 HS4 HF4 HFr4 MEQ4 PSL4 MEQ3 PSL3 ED ED2.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(img_try (rewrite E44, Hbz; img_refl)))) as HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_w2Hz_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hz_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2Hz_e0 19) (RG w2Hz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS5'.
img_change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_w2Hz_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hz_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfxsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfxsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (img_try (img_apply MEQ6; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot ED (RG w2Hz_e1 10) = Z_to_bv 64 (gud + SB)).
{ img_change (sv_denot ED (RG w2Hz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot ED (RG w2Hz_e1 11) = Z_to_bv 64 (ged - gud)).
{ img_change (sv_denot ED (RG w2Hz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). img_exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot ED (RG w2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ img_change (sv_denot ED (RG w2Hz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; img_lia. }
assert (R1 : sv_denot ED (RG w2Hz_e1 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot ED (RG w2Hz_e1 1)) with (sv_denot ED (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem w2Hz_e1)).
{ cbn [ss_mem w2Hz_e1]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W ED w2Hz_e1 ms6 _ 56 (ss_mem w2Hz_e1) (gud + SB) (ged - gud) (sp0 - 2208) (347624 + D_2c4) HS6 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. (subst ED'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EDreg. img_exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (img_try ((subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact ED2)).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros j Hj; (subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_apply EDsv; img_exact Hj)).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ6. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. img_apply HP7. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [img_norm_st HS7 r_w2Hz_2; img_try (img_apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Hz_2))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 ED' ED'2.
img_apply (finishD ED' (ms_regs ms0) w2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (img_try (destruct Hok as [Hz0 | [Hlt Hb]]; [img_try (exfalso; img_exact (Hbz Hz0)) | img_lia])).
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(img_lia))) as HS4'.
img_change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [img_norm_st HS4' r_w2Hn_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hn_0))|].
icpt_l1t_0 W5 c5 ms5 mat5 HS5 HF5 HFr5 MEQ5 PSL5 MEQ4 PSL4 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(img_lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [img_norm_st HS5' r_w2Hn_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hn_1))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w2Hn_e1 19) (RG w2Hn_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_try (unfold SB; img_lia)))) as HS6'.
img_change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w2Hn_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Hn_2))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfxsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
split; [img_try (img_exact (proj1 (Bpres z ltac:(img_lia)))) | img_try (exists b; img_exact Eb)]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfxsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (img_try (img_apply MEQ7; rewrite unsigned_lit_small by img_lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; img_lia)).
replace a with (SB + (a - SB)) by img_lia. img_apply (ra_granule_zero (aview tfxsegs H mem) d n (a - SB) HRA); [img_try (unfold SB in *; img_lia) | img_try (img_exact Hd)]. }
assert (R10 : sv_denot ED (RG w2Hn_e2 10) = Z_to_bv 64 (gud + SB)).
{ img_change (sv_denot ED (RG w2Hn_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by img_lia. img_refl. }
assert (R11 : sv_denot ED (RG w2Hn_e2 11) = Z_to_bv 64 (ged - gud)).
{ img_change (sv_denot ED (RG w2Hn_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). img_exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(img_lia) ltac:(img_lia)). }
assert (R2 : sv_denot ED (RG w2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ img_change (sv_denot ED (RG w2Hn_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; img_lia. }
assert (R1 : sv_denot ED (RG w2Hn_e2 1) = Z_to_bv 64 (347624 + D_2c4)).
{ img_change (sv_denot ED (RG w2Hn_e2 1)) with (sv_denot ED (SLit (347624 + D_2c4))). img_apply bv_eq. img_case; vm_compute. all: img_refl. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val ED (YQ0b.r_base r) + YQ0b.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) (ss_mem w2Hn_e2)).
{ cbn [ss_mem w2Hn_e2]. repeat (img_apply Forall_cons); try img_apply Forall_nil.
all: cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; img_lia. }
eapply SRr_bind; [img_try (img_exact (icpt_memisz W ED w2Hn_e2 ms7 _ 56 (ss_mem w2Hn_e2) (gud + SB) (ged - gud) (sp0 - 2208) (347624 + D_2c4) HS7 eq_refl eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) (submem_refl _)
R10 R11 R2 R1 ltac:(img_lia) ltac:(unfold SB; img_lia) ltac:(unfold SB, kHighMemBeg in *; img_lia) ltac:(unfold TFX_IMG_END, kHighMemBeg in *; img_lia) ltac:(img_lia)
(ret_ok_lit (347624 + D_2c4) ltac:(img_lia) ltac:(img_eqrefl_m)) ltac:(left; unfold SB, kHighMemBeg in *; img_lia) SLW SZERO HOFF))|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. (subst ED'; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EDreg. img_exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (img_try ((subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_exact ED2)).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros j Hj; (subst ED'; cbv beta); rewrite ew_havoc_old by img_lia; img_apply EDsv; img_exact Hj)).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (img_try (unfold MC_SCR in *; img_lia)). img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. img_apply HP8. unfold MC_SCR, MC_STK in *. img_lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [img_norm_st HS8 r_w2Hn_3; img_try (img_apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Hn_3))|].
icpt_l1t_0 W9 c9 ms9 mat9 HS9 HF9 HFr9 MEQ9 PSL9 MEQ8 PSL8 ED' ED'2.
img_apply (finishD ED' (ms_regs ms0) w2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. img_apply MEQ9. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
End e.
End c.
