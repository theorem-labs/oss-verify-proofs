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
Lemma entD1_3 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 3 -> aview tfxsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 3) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms _ 0); img_refl)).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms _ 2); img_refl)).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). img_refl. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfxsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 3 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 3)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfxsegs))).
{ unfold EE, EnvD, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply (entD_stk ms _ HM)) | img_try (img_apply Forall_cons; [| img_apply (entD_ro ms _ HM)])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (img_try (unfold kHighMemBeg in *; img_lia)); fold (mbyte tfxsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0d + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0d _ 1 (SOff 44 0) b1); [img_try (cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply (val_mem_frame H mem (ms_mem ms)); [img_try (intros k Hk; img_apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; img_lia); unfold kHighMemBeg in *; img_lia)|];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: match goal with |- (?a - 2160) mod 16 = 0 => replace (a - 2160) with (a + (-135) * 16) by img_lia end; rewrite Z_mod_plus_full; img_exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 3 E42) by img_lia. (subst g0d g1d; cbv beta). img_lia. }
unfold ssD1. img_apply (st_ok_regs tfxsegs EE _ _ sr_mid HS0). img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| img_apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by img_lia; symmetry; img_apply (U_atom EE 20 (d + n)); [img_try ((subst EE; cbv beta); rewrite (EnvD_reg ms _ 20 20%bv eq_refl); img_exact M20) | img_lia]
| cbn [sv_denot]; rewrite E12; (subst EE; cbv beta); rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by img_lia; img_refl ] |]).
destruct Hr.
Qed.
Lemma entD1_4 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 4 -> aview tfxsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 4) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms _ 0); img_refl)).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms _ 2); img_refl)).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). img_refl. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfxsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 4 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 4)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfxsegs))).
{ unfold EE, EnvD, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply (entD_stk ms _ HM)) | img_try (img_apply Forall_cons; [| img_apply (entD_ro ms _ HM)])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (img_try (unfold kHighMemBeg in *; img_lia)); fold (mbyte tfxsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0d + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0d _ 1 (SOff 44 0) b1); [img_try (cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply (val_mem_frame H mem (ms_mem ms)); [img_try (intros k Hk; img_apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; img_lia); unfold kHighMemBeg in *; img_lia)|];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: match goal with |- (?a - 2160) mod 16 = 0 => replace (a - 2160) with (a + (-135) * 16) by img_lia end; rewrite Z_mod_plus_full; img_exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 4 E42) by img_lia. (subst g0d g1d; cbv beta). img_lia. }
unfold ssD1. img_apply (st_ok_regs tfxsegs EE _ _ sr_mid HS0). img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| img_apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by img_lia; symmetry; img_apply (U_atom EE 20 (d + n)); [img_try ((subst EE; cbv beta); rewrite (EnvD_reg ms _ 20 20%bv eq_refl); img_exact M20) | img_lia]
| cbn [sv_denot]; rewrite E12; (subst EE; cbv beta); rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by img_lia; img_refl ] |]).
destruct Hr.
Qed.
Lemma entD1_5 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 5 -> aview tfxsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfxsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 5) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms _ 0); img_refl)).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms _ 2); img_refl)).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)). img_refl. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfxsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 5 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 5)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfxsegs))).
{ unfold EE, EnvD, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [img_try (img_apply (entD_stk ms _ HM)) | img_try (img_apply Forall_cons; [| img_apply (entD_ro ms _ HM)])].
unfold shreg1, region_ok, SB. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
img_change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
all: first
[ img_apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (img_try (unfold kHighMemBeg in *; img_lia)); fold (mbyte tfxsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (YF8r.aview_byte H mem _ 0); [img_refl|];
rewrite <- (ra_granule_zero (aview tfxsegs H mem) d n (g0d + i) HRA ltac:(img_lia) Hd); unfold SB; f_equal; img_lia
| eapply (chunk_ok_val tfxsegs EE _ g0d _ 1 (SOff 44 0) b1); [img_try (cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (zside) | img_try (zside) |];
img_apply (val_mem_frame H mem (ms_mem ms)); [img_try (intros k Hk; img_apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; img_lia); unfold kHighMemBeg in *; img_lia)|];
img_apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; img_lia ].
- img_apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; img_lia.
- split; [|img_try (split; [img_exact I|])].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; try img_lia; try img_apply Z.mod_1_r.
all: match goal with |- (?a - 2160) mod 16 = 0 => replace (a - 2160) with (a + (-135) * 16) by img_lia end; rewrite Z_mod_plus_full; img_exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|img_try (split; [|img_exact I])].
* img_apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by img_lia. img_refl.
* img_apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 5 E42) by img_lia. (subst g0d g1d; cbv beta). img_lia. }
unfold ssD1. img_apply (st_ok_regs tfxsegs EE _ _ sr_mid HS0). img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| img_apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by img_lia; symmetry; img_apply (U_atom EE 20 (d + n)); [img_try ((subst EE; cbv beta); rewrite (EnvD_reg ms _ 20 20%bv eq_refl); img_exact M20) | img_lia]
| cbn [sv_denot]; rewrite E12; (subst EE; cbv beta); rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by img_lia; img_refl ] |]).
destruct Hr.
Qed.
  (* [comment removed for export] *)
  Tactic Notation "icpt_l1t_0" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HFk) ident(HFrk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) constr(EE) hyp(EE2) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HFk & HFrk); rewrite ?wvb_wvb in *;
    assert (MEQk : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply MEQp; unfold MC_STK, MC_SCR in *; img_lia)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None);
    [ intros z Hz; rewrite (HFk z); [img_try (img_apply PSLp; img_exact Hz)|]; intros Hin;
      unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (-64) 2160 (sp0 - 2160) _ EE2 Hin) as X; [img_try ((img_case; vm_compute); img_refl)|]; unfold MC_STK, MC_SCR in *; img_lia | ];
    clear HFk HFrk.
  Tactic Notation "icpt_l1t_1" ident(Wk) ident(ck) ident(msk) ident(matk) ident(HSk) ident(HMk) ident(MEQk) ident(PSLk) hyp(MEQp) hyp(PSLp) hyp(CL0) hyp(CL1) :=
    cbv beta; intros Wk ck _ (-> & msk & matk & -> & HSk & HMk);
    assert (MEQk : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem msk z = mem z) by (img_try (intros z Hz; rewrite HMk; img_apply MEQp; img_exact Hz));
    assert (PSLk : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msk z <> None) by (img_try (intros z Hz; rewrite HMk; img_apply PSLp; img_exact Hz));
    clear CL0 CL1.

Lemma pathD1_3 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 3 ->
SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (img_try (unfold MC_SCR; img_exact MEQ0)).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1d < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0d; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1d; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (img_try (intros; img_apply EnvD_reg; assumption)).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros; img_apply EnvD_sv; assumption)).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms0 _ 0); img_refl)).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms0 _ 2); img_refl)).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (img_try (img_apply (EnvD_x ms0 _ 3); img_refl)).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (img_try (img_apply (EnvD_x ms0 _ 4); img_refl)).
pose proof (entD1_3 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [img_norm_st HS0 r_w1_3_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_3_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (RG w1_3_e0 13) (RG w1_3_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_w1_3_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_3_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w1_3_e1 13) (RG w1_3_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_w1_3_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_3_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 ED ED2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W ED (w1_3_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450883 E42) by img_lia. f_equal. (subst h2; cbv beta). replace (g0d + 2147450883) with (g1d + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W ED (set_regs_pc w1_3_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_3_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_w1_3_3; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_3_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_NE (RG w1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_3z_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_NE (RG w1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_3n_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_EQ (RG w1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 3%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_w1_3n_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_3n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma pathD1_4 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 4 ->
SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (img_try (unfold MC_SCR; img_exact MEQ0)).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1d < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0d; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1d; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (img_try (intros; img_apply EnvD_reg; assumption)).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros; img_apply EnvD_sv; assumption)).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms0 _ 0); img_refl)).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms0 _ 2); img_refl)).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (img_try (img_apply (EnvD_x ms0 _ 3); img_refl)).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (img_try (img_apply (EnvD_x ms0 _ 4); img_refl)).
pose proof (entD1_4 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [img_norm_st HS0 r_w1_4_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_4_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (RG w1_4_e0 13) (RG w1_4_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_w1_4_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_4_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w1_4_e1 13) (RG w1_4_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_w1_4_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_4_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 ED ED2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W ED (w1_4_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450884 E42) by img_lia. f_equal. (subst h2; cbv beta). replace (g0d + 2147450884) with (g1d + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W ED (set_regs_pc w1_4_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_4_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_w1_4_3; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_4_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_NE (RG w1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_4z_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_NE (RG w1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_4n_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_EQ (RG w1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 4%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_w1_4n_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_4n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
Lemma pathD1_5 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 5 ->
SRr tfxsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M20 & M22 & M3 & M4 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (img_try (unfold MC_SCR; img_exact MEQ0)).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(img_lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (img_try ((subst g0d; cbv beta); split; [img_try (img_apply Z.div_pos; img_lia) | img_try (pose proof (Z.div_mod d 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound d 8 ltac:(img_lia)); img_lia)])).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (img_try ((subst g1d; cbv beta); pose proof (Z.div_mod (d + n - 1) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
assert (Hg1hi : g1d < 2 ^ 44) by img_lia.
destruct (ra_last (aview tfxsegs H mem) d n HRA ltac:(img_lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (img_try (destruct Hok as [-> | [Hlt Hb]]; [img_lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)); img_lia)).
pose proof (HHULL ltac:(img_lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (img_try ((subst h1; cbv beta); pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (img_try ((subst h2; cbv beta); pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(img_lia)); img_lia)).
assert (Hh12 : h1 <= h2) by (img_try ((subst h1 h2; cbv beta); img_apply Z.mul_le_mono_nonneg_r; [img_lia|]; img_apply Z.div_le_mono; img_lia)).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (img_try ((subst h1; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g0d; cbv beta); f_equal; f_equal; img_lia)).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (img_try ((subst h2; cbv beta); unfold shadow_addr; img_change SHADOW_OFF with SB; unfold SB; (subst g1d; cbv beta); f_equal; f_equal; img_lia)).
destruct (hull_rdword H mem d n h1 HH ltac:(img_lia) ltac:(img_lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(img_lia) ltac:(img_lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (img_try (intros; img_apply EnvD_reg; assumption)).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (img_try (intros; img_apply EnvD_sv; assumption)).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (img_try (img_apply (EnvD_x ms0 _ 0); img_refl)).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (img_try (img_apply (EnvD_x ms0 _ 2); img_refl)).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (img_try (img_apply (EnvD_x ms0 _ 3); img_refl)).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (img_try (img_apply (EnvD_x ms0 _ 4); img_refl)).
pose proof (entD1_5 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [img_norm_st HS0 r_w1_5_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_5_0))|].
icpt_l1t_0 W1 c1 ms1 mat1 HS1 HF1 HFr1 MEQ1 PSL1 MEQ0 PSL0 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_LTU (RG w1_5_e0 13) (RG w1_5_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(img_lia) ltac:(img_lia))) as HS1'.
img_change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [img_norm_st HS1' r_w1_5_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_5_1))|].
icpt_l1t_0 W2 c2 ms2 mat2 HS2 HF2 HFr2 MEQ2 PSL2 MEQ1 PSL1 ED ED2.
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_GEU (RG w1_5_e1 13) (RG w1_5_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
img_change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [img_norm_st HS2' r_w1_5_2; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_5_2))|].
icpt_l1t_0 W3 c3 ms3 mat3 HS3 HF3 HFr3 MEQ3 PSL3 MEQ2 PSL2 ED ED2.
assert (HW4 : rdword (aview tfxsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq1)].
intros i Hi. img_apply aview_same. img_apply MEQ3. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (img_apply (icpt_ld8 W ED (w1_5_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW4))|].
icpt_l1t_1 W4 c4 ms4 mat4 HS4 HM4 MEQ4 PSL4 MEQ3 PSL3 HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450885 E42) by img_lia. f_equal. (subst h2; cbv beta). replace (g0d + 2147450885) with (g1d + 2147450880) by img_lia. img_refl. }
assert (HW5 : rdword (aview tfxsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by img_lia. img_apply (YF8r.rdword_ext (aview tfxsegs H mem)); [|img_try (img_exact Hq2)].
intros i Hi. img_apply aview_same. img_apply MEQ4. rewrite unsigned_lit_small by img_lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. img_lia. }
eapply SRr_bind; [img_try (apply (icpt_ld8 W ED (set_regs_pc w1_5_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_5_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_compute); img_refl) ltac:((img_case; vm_refl_bv)) eq_refl (Hrs2) ltac:(img_lia) ltac:(unfold kHighMemBeg in *; img_lia) HW5))|].
icpt_l1t_1 W5 c5 ms5 mat5 HS5 HM5 MEQ5 PSL5 MEQ4 PSL4 HW5 HS4.
eapply SRr_bind; [img_norm_st HS5 r_w1_5_3; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_5_3))|].
icpt_l1t_0 W6 c6 ms6 mat6 HS6 HF6 HFr6 MEQ6 PSL6 MEQ5 PSL5 ED ED2.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfxsegs ED _ _ BC_NE (RG w1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
img_change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_5z_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5z_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ7. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
+
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_NE (RG w1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [img_norm_st HS6' r_w1_5n_0; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5n_0))|].
icpt_l1t_0 W7 c7 ms7 mat7 HS7 HF7 HFr7 MEQ7 PSL7 MEQ6 PSL6 ED ED2.
pose proof (st_ok_add_cond tfxsegs ED _ _ BC_EQ (RG w1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 5%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(img_lia) Hdn ltac:(img_lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [img_norm_st HS7' r_w1_5n_1; img_try (img_apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_5n_1))|].
icpt_l1t_0 W8 c8 ms8 mat8 HS8 HF8 HFr8 MEQ8 PSL8 MEQ7 PSL7 ED ED2.
img_apply (finishD ED (ms_regs ms0) w1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) EDreg EDsv M2 M10 M11 M12 M3 M4 M25 M26 M27).
- intros z Hz. img_apply MEQ8. unfold MC_SCR, MC_STK in *. img_lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [img_try (img_exact (proj1 (Bpres a ltac:(img_lia))))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [img_try (exists b; img_refl) | img_try (exfalso; img_exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by img_lia; img_lia) Eb))].
Qed.
End e.
End c.
