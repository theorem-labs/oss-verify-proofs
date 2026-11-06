(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition shadow_rd (segs : list Segment) (H : word -> bool) (mem : word -> option byte) : Z -> option Z :=
fun a => option_map (fun b : byte => bv_unsigned b) (mbyte segs (mrestrict H mem) a).


Definition zdisj (a b : Z * Z) : Prop := snd a <= fst b \/ snd b <= fst a.
Fixpoint zall_disjoint (a : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: l' => zdisj a b /\ zall_disjoint a l' end.
Fixpoint zpairwise_disjoint (l : list (Z * Z)) : Prop :=
match l with [] => True | a :: l' => zall_disjoint a l' /\ zpairwise_disjoint l' end.
Definition shadow_decl (p b s : nat) : sv * sv :=
(SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0), SOff s 0).
Section d. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Definition extent_of_region (E : env) (r : YQ0b.region) : Z * Z :=
(base_val E (YQ0b.r_base r) + YQ0b.r_lo r, base_val E (YQ0b.r_base r) + YQ0b.r_hi r).
Lemma all_disjoint_of_extents : forall E r rs,
zall_disjoint (extent_of_region E r) (map (extent_of_region E) rs) -> all_disjoint E r rs.
Proof.
intros E r rs. induction rs as [|r' rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)].
unfold extent_of_region, zdisj in H1. cbn in H1. unfold extent_disjoint. lia.
Qed.
Lemma pairwise_disjoint_of_extents : forall E rs,
zpairwise_disjoint (map (extent_of_region E) rs) -> pairwise_disjoint E rs.
Proof.
intros E rs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [exact (all_disjoint_of_extents E r rs H1) | exact (IH H2)].
Qed.



Definition windows (rs : smem) : list (option nat * Z * Z) :=
map (fun r => (YQ0b.r_base r, YQ0b.r_wlo r, YQ0b.r_whi r)) rs.
Lemma in_wrange_windows : forall E rs a,
in_wrange E rs a ->
exists b wlo whi, In (b, wlo, whi) (windows rs) /\ base_val E b + wlo <= a < base_val E b + whi.
Proof.
intros E rs a (r & Hin & Hr). exists (YQ0b.r_base r), (YQ0b.r_wlo r), (YQ0b.r_whi r).
split; [|exact Hr]. unfold windows.
exact (in_map (fun r0 => (YQ0b.r_base r0, YQ0b.r_wlo r0, YQ0b.r_whi r0)) rs r Hin).
Qed.
Definition win_eqb (t u : option nat * Z * Z) : bool :=
match t, u with
| (b1, l1, h1), (b2, l2, h2) => obase_eqb b1 b2 && (l1 =? l2) && (h1 =? h2)
end.
Lemma win_eqb_eq : forall t u, win_eqb t u = true -> t = u.
Proof.
intros [[b1 l1] h1] [[b2 l2] h2] H. cbn in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
destruct b1 as [x|], b2 as [y|]; cbn in H1; try discriminate; [|reflexivity].
apply Nat.eqb_eq in H1. subst. reflexivity.
Qed.
Lemma in_wrange_single_b : forall E rs a n wlo whi spv,
forallb (fun t => win_eqb t (Some n, wlo, whi) || (snd t <=? snd (fst t))) (windows rs) = true ->
bv_unsigned (ew E n) = spv ->
in_wrange E rs a -> spv + wlo <= a < spv + whi.
Proof.
intros E rs a n wlo whi spv Hb Hn Hin.
destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
rewrite forallb_forall in Hb. specialize (Hb _ Ht). apply orb_prop in Hb as [Hb|Hb].
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. rewrite Hn in Hr. exact Hr.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma in_wrange_single : forall E rs a n wlo whi spv,
(forall t, In t (windows rs) -> t = (Some n, wlo, whi) \/ snd t <= snd (fst t)) ->
bv_unsigned (ew E n) = spv ->
in_wrange E rs a -> spv + wlo <= a < spv + whi.
Proof.
intros E rs a n wlo whi spv Hw Hn Hin.
destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
destruct (Hw _ Ht) as [Heq | Hempty].
- injection Heq as -> -> ->. cbn [base_val] in Hr. rewrite Hn in Hr. exact Hr.
- cbn [fst snd] in Hempty. lia.
Qed.
End d.
Ltac simp_off0 v :=
lazymatch v with
| context C [Z_to_bv 64 (bv_unsigned ?w + 0)] => let t := context C [w] in simp_off0 t
| _ => v
end.
Ltac rreg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) _);
change (sv_denot E e = v);
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
end.
Ltac zside := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; lia.
Ltac zdisj_pairwise H :=
cbn [zpairwise_disjoint zall_disjoint] in H |- *; unfold zdisj in H |- *; cbn [fst snd] in H |- *;
let rec par H :=
lazymatch type of H with
| _ /\ _ => let H1 := fresh "D" in let H2 := fresh "D" in destruct H as [H1 H2]; split; [par H1 | par H2]
| True => exact I
| _ => revert H; repeat match goal with K : _ |- _ => clear K end; intros H; lia
end in par H.
