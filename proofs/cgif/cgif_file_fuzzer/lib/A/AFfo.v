(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgo AFh2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte).
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
Hypothesis V16 : val_mem tfibsegs m (RGv + 16) 8 nf.
Hypothesis V80 : val_mem tfibsegs m (RGv + 80) 8 j80.
Hypothesis V88 : val_mem tfibsegs m (RGv + 88) 8 j88.
Hypothesis VRI : val_mem tfibsegs m (A_ALLOCATOR + 48) 8 ri.
Hypothesis V40 : val_mem tfibsegs m (A_ALLOCATOR + 40) 4 4294967295.
Hypothesis VPG1 : val_mem tfibsegs m 0x9df78 8 0x135aa0.
Hypothesis VPG2 : val_mem tfibsegs m 0x135aa0 8 4096.
Local Notation E0 := (AFgo.E0 regs ri c nf j80 j88).
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgo.E2 regs ri c nf j80 j88). Qed.
Lemma chunk_lit : forall base a (w : BinNums.N) x, val_mem tfibsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac numc := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, A_ALLOCATOR, TFIB_IMG_END in *.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m) AFgo.REG0.
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3). pose proof Hvals as (N1 & N2 & N3).
assert (Usp : 0 <= sp < 2 ^ 64) by (unfold sp; apply u64_range).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (unfold RGv; lia).
unfold AFgo.REG0, AFgo.R_RGO, fatom8, flit8, flit4. numc.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m 2 sp (- 80)); [rewrite E2; reflexivity | lia | lia |].
intros a Ha. apply apresent_writable; [numc; lia | apply Hpres; exact Ha]. }
apply Forall_cons.
{   reg_intro. rewrite AFgo.EqRG. unfold w64, AFgo.RGv. fold RGv. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 8 35%nat nf); [reflexivity | lia | exact V16 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 36%nat j80); [reflexivity | lia | exact V80 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 37%nat j88); [reflexivity | lia | exact V88 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom 0 _ 8 32%nat ri); [reflexivity | lia | rewrite Z.add_0_l; exact VRI | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 4); [rewrite Z.add_0_l; exact V40 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact VPG1 | cbn; lia | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact VPG2 | cbn; lia | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgo.REG0.
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3).
assert (Usp : 0 <= sp < 2 ^ 64) by (unfold sp; apply u64_range).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (unfold RGv; lia).
apply pairwise_disjoint_of_extents. unfold AFgo.REG0, AFgo.R_RGO, fatom8, flit8, flit4, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, AFgo.EqRG. unfold w64, AFgo.RGv. fold sp. fold RGv. numc. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgo.FFO).
Proof.
pose proof Hsp as [S1 S2]. pose proof Hri as (I1 & I2 & I3). pose proof Hvals as (N1 & N2 & N3).
assert (Usp : 0 <= sp < 2 ^ 64) by (unfold sp; apply u64_range).
assert (G : ri + 128 <= RGv /\ RGv + 128 <= ri + 4096) by (unfold RGv; lia).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E0 2 = w64 sp) by (rewrite E2; unfold sp, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (RAL : RGv mod 2 ^ 7 = 0).
{ unfold RGv. apply Z.mod_divide in I3 as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 32 + c). lia. }
cbn [AFgo.FFO f_atoms atoms_ok]. numc.
split. { apply (AF 2%nat sp); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 Hsp_al; first [lia | change (2 ^ 4) with 16; exact Hsp_al]. }
split. { apply (AF 32%nat ri); [reflexivity| | | |]. all: clear - CR0 I1 I2 I3; first [lia | change (2 ^ 12) with 4096; exact I3]. }
split. { apply (AF 33%nat c); [reflexivity| | | |]. all: clear - CR0 Hc; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 34%nat RGv); [reflexivity| | | |]. all: clear - CR0 I1 I2 G RAL; first [lia | exact RAL]. }
split. { apply (AF 35%nat nf); [reflexivity| | | |]. all: clear - CR0 N1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat j80); [reflexivity| | | |]. all: clear - CR0 N2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 37%nat j88); [reflexivity| | | |]. all: clear - CR0 N3; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgo.SS0 (restrict (w_H W) (mkst regs (w64 0x34350) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold AFgo.SS0, AFgo.SR0, sr_set. cbn [bv_eqb]. unfold AFgo.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Ha0] | intros XX; discriminate |] | intros XX; discriminate | cbn [sv_denot]; exact Ha3].
cbn [sv_denot]. fold (AFgo.E0 regs ri c nf j80 j88). rewrite AFgo.EqC, Ha2. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FHO_ok : AFgo.free_hyps W regs mem ri c nf j80 j88.
Proof.
constructor.
- exact Hra.
- exact Hsp.
- exact Hsp_al.
- exact Hpres.
- exact Hc.
- exact Hri.
- exact Hvals.
- exact Hdisj.
- exact SEED_ok.
Qed.
End d.
End b.
