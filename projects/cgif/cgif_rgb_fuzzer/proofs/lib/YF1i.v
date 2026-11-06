(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0j YF0i YF2j YF2x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d. Context {imgk : img}.
Variables (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte).
Variables (ri c nf j80 j88 : Z).
Let sp : Z := bv_unsigned (getr regs 2).
Let m := mrestrict (w_H W) mem.
Let RGv : Z := ri + 128 * c.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hsp : kHighMemBeg + 80 <= sp /\ sp <= kHighMemEnd.
Hypothesis Hsp_al : sp mod 16 = 0.
Hypothesis Hpres : forall a, sp - 80 <= a < sp -> apresent (w_H W) mem a.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hri : kHighMemBeg <= ri /\ ri + 4096 <= ASAN_CEIL /\ ri mod 4096 = 0.
Hypothesis Hvals : 0 <= nf < 2 ^ 64 /\ 0 <= j80 < 2 ^ 64 /\ 0 <= j88 < 2 ^ 64.
Hypothesis Hdisj : sp <= RGv \/ RGv + 128 <= sp - 80.
Hypothesis Ha0 : getr regs 10 = w64 A_ALLOCATOR.
Hypothesis Ha2 : getr regs 12 = w64 c.
Hypothesis Ha3 : getr regs 13 = w64 0.
Hypothesis V16 : val_mem tfxsegs m (RGv + 16) 8 nf.
Hypothesis V80 : val_mem tfxsegs m (RGv + 80) 8 j80.
Hypothesis V88 : val_mem tfxsegs m (RGv + 88) 8 j88.
Hypothesis VRI : val_mem tfxsegs m (A_ALLOCATOR + 48) 8 ri.
Hypothesis V40 : val_mem tfxsegs m (A_ALLOCATOR + 40) 4 4294967295.
Hypothesis VPG1 : val_mem tfxsegs m (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0).
Hypothesis VPG2 : val_mem tfxsegs m (0x139c60 + D_10c0) 8 4096.
Local Notation E0 := (YF2j.E0 regs ri c nf j80 j88).
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2j.E2 regs ri c nf j80 j88). Qed.
Lemma chunk_lit : forall base a (w : BinNums.N) x, val_mem tfxsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfxsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m base (YQ0b.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac numc := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, A_ALLOCATOR, TFX_IMG_END in *.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m) YF2j.REG0.
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3). pose proof Hvals as (N1 & N2 & N3).
assert (Usp : 0 <= sp < 2 ^ 64) by (img_try (unfold sp; img_apply u64_range)).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (img_try (unfold RGv; img_lia)).
unfold YF2j.REG0, YF2j.R_RGO, fatom8, flit8, flit4. numc.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m 2 sp (- 80)); [img_try (rewrite E2; img_refl) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (numc; img_lia) | img_try (img_apply Hpres; img_exact Ha)]. }
img_apply Forall_cons.
{   reg_intro. rewrite YF2j.EqRG. unfold w64, YF2j.RGv. fold RGv. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
- img_apply (chunk_atom _ _ 8 35%nat nf); [img_refl | img_lia | img_try (img_exact V16) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 36%nat j80); [img_refl | img_lia | img_try (img_exact V80) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 37%nat j88); [img_refl | img_lia | img_try (img_exact V88) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom 0 _ 8 32%nat ri); [img_refl | img_lia | img_try (rewrite Z.add_0_l; img_exact VRI) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_lit 0 _ 4); [img_try (rewrite Z.add_0_l; img_exact V40) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{ reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_lit 0 _ 8); [img_try (rewrite Z.add_0_l; img_exact VPG1) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{ reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_lit 0 _ 8); [img_try (rewrite Z.add_0_l; img_exact VPG2) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2j.REG0.
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3).
assert (Usp : 0 <= sp < 2 ^ 64) by (img_try (unfold sp; img_apply u64_range)).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (img_try (unfold RGv; img_lia)).
img_apply pairwise_disjoint_of_extents. unfold YF2j.REG0, YF2j.R_RGO, fatom8, flit8, flit4, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, YF2j.EqRG. unfold w64, YF2j.RGv. fold sp. fold RGv. numc. rewrite !unsigned_lit_small by img_lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; img_lia.
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2j.FFO).
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3). pose proof Hvals as (N1 & N2 & N3).
assert (Usp : 0 <= sp < 2 ^ 64) by (img_try (unfold sp; img_apply u64_range)).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (img_try (unfold RGv; img_lia)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (E2' : ew E0 2 = w64 sp) by (img_try (rewrite E2; unfold sp, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (RAL : RGv mod 2 ^ 7 = 0).
{ unfold RGv. apply Z.mod_divide in I3 as [q Hq]; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q * 32 + c). img_lia. }
cbn [YF2j.FFO f_atoms atoms_ok]. numc.
split. { img_apply (AF 2%nat sp); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 Hsp_al; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hsp_al]. }
split. { img_apply (AF 32%nat ri); [img_refl| | | |]. all: clear - CR0 I1 I2 I3; first [img_lia | img_change (2 ^ 12) with 4096; img_exact I3]. }
split. { img_apply (AF 33%nat c); [img_refl| | | |]. all: clear - CR0 Hc; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 34%nat RGv); [img_refl| | | |]. all: clear - CR0 I1 I2 G RAL; first [img_lia | img_exact RAL]. }
split. { img_apply (AF 35%nat nf); [img_refl| | | |]. all: clear - CR0 N1; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat j80); [img_refl| | | |]. all: clear - CR0 N2; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 37%nat j88); [img_refl| | | |]. all: clear - CR0 N3; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2j.SS0 (restrict (w_H W) (mkst regs (w64 (0x34958 + D_150)) mem (seg_rom tfxsegs))).
Proof.
rewrite restrict_mkst_fx. unfold YF2j.SS0, YF2j.SR0, sr_set. cbn [bv_eqb]. unfold YF2j.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Ha0] | intros XX; discriminate |]) | img_try (intros XX; discriminate) | img_try (cbn [sv_denot]; img_exact Ha3)].
cbn [sv_denot]. fold (YF2j.E0 regs ri c nf j80 j88). rewrite YF2j.EqC, Ha2. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FHO_ok : YF2j.free_hyps W regs mem ri c nf j80 j88.
Proof.
constructor.
- img_exact Hra.
- img_exact Hsp.
- img_exact Hsp_al.
- img_exact Hpres.
- img_exact Hc.
- img_exact Hri.
- img_exact Hvals.
- img_exact Hdisj.
- img_exact SEED_ok.
Qed.
End d.
End b.
