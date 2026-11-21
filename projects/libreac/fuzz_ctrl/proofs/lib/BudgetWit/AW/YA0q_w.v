(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0q.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0q.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition zdisj (a b : Z * Z) : Prop := snd a <= fst b \/ snd b <= fst a.
Fixpoint zall_disjoint (a : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: l' => zdisj a b /\ zall_disjoint a l' end.
Fixpoint zpairwise_disjoint (l : list (Z * Z)) : Prop :=
match l with [] => True | a :: l' => zall_disjoint a l' /\ zpairwise_disjoint l' end.
Section d. 
Definition extent_of_region (E : env) (r : YP09.region) : Z * Z :=
(base_val E (YP09.r_base r) + YP09.r_lo r, base_val E (YP09.r_base r) + YP09.r_hi r).
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
map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs.
Lemma in_wrange_windows : forall E rs a,
in_wrange E rs a ->
exists b wlo whi, In (b, wlo, whi) (windows rs) /\ base_val E b + wlo <= a < base_val E b + whi.
Proof.
intros E rs a (r & Hin & Hr). exists (YP09.r_base r), (YP09.r_wlo r), (YP09.r_whi r).
split; [|exact Hr]. unfold windows.
exact (in_map (fun r0 => (YP09.r_base r0, YP09.r_wlo r0, YP09.r_whi r0)) rs r Hin).
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
