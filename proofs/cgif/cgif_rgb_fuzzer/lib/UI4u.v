(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma U_add2 : forall E n m x y,
bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia). apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_add_shl : forall E n m b x k p,
2 ^ k = p -> bv_unsigned (ew E m) = b -> bv_unsigned (ew E n) = x -> 0 <= b -> 0 <= x < 2 ^ 32 -> 0 <= k <= 4 -> b + x * p < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SLL (SOff n 0) (SLit k))) = Z_to_bv 64 (b + x * p).
Proof.
intros E n m b x k p Hp Hm Hn Hb Hx Hk Hbx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hm, Hn, !Z.add_0_r.
assert (Hk2 : 0 < 2 ^ k <= 16) by (split; [apply Z.pow_pos_nonneg; lia | change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia]).
rewrite (zcanon_id b), (zcanon_id x) by (unfold M64; lia).
replace (Z.land (zcanon k) 63) with k.
2:{ rewrite zcanon_id by (unfold M64; lia). assert (X : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
destruct X as [-> |[-> |[-> |[-> | ->]]]]; reflexivity. }
rewrite Z.shiftl_mul_pow2 by lia. rewrite Hp. rewrite (zcanon_id (x * p)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia.
Qed.
Definition nd_lits (lf : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some lf].
Definition dl_lits (cut : Z) : list (option Z) := [None; None; None; None; None; None; None; Some cut; None; Some 0].
Lemma leaf_facts : forall m u n, tree_at ubs2segs m u -> In n (tree_leaves u) ->
In n (tree_nodes u) /\ length (tn_mean n) = 3%nat /\ exists c0 c1, obj_at ubs2segs m (tn_addr n) LAY_Node (node_vals c0 c1 n 1).
Proof.
intros m u. induction u as [|n0|n0 l IHl rr IHr]; intros n Ht Hin; cbn [tree_leaves tree_at tree_nodes] in *.
- destruct Hin.
- destruct Hin as [<- | []]. destruct Ht as (_ & Hlen & c0 & c1 & Hobj). split; [left; reflexivity|]. split; [exact Hlen|]. exists c0, c1. exact Hobj.
- fold (tree_at ubs2segs) in Ht. destruct Ht as (_ & _ & _ & Hl & Hr). apply in_app_iff in Hin as [Hin|Hin].
+ destruct (IHl n Hl Hin) as (A1 & A2 & A3). split; [right; apply in_app_iff; left; exact A1|]. auto.
+ destruct (IHr n Hr Hin) as (A1 & A2 & A3). split; [right; apply in_app_iff; right; exact A1|]. auto.
Qed.
Lemma root_cases : forall m u, tree_at ubs2segs m u -> tree_full u ->
exists n lf c0 c1, troot u = tn_addr n /\ In n (tree_nodes u) /\ (lf = 0 \/ lf = 1) /\ length (tn_mean n) = 3%nat /\
obj_at ubs2segs m (tn_addr n) LAY_Node (node_vals c0 c1 n lf) /\
(lf = 1 -> u = TLeaf n) /\ (lf = 0 -> exists l rr, u = TNode n l rr).
Proof.
intros m [|n|n l rr] Ht Hf; [destruct Hf| |]; cbn [tree_at] in Ht.
- destruct Ht as (_ & Hlen & c0 & c1 & Hobj). exists n, 1, c0, c1.
split; [reflexivity|]. split; [left; reflexivity|]. split; [right; reflexivity|]. split; [exact Hlen|]. split; [exact Hobj|].
split; [intros _; reflexivity | intros HH0; discriminate HH0].
- fold (tree_at ubs2segs) in Ht. destruct Ht as (_ & Hlen & Hobj & _ & _). exists n, 0, (troot l), (troot rr).
split; [reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Hobj|].
split; [intros HH0; discriminate HH0 | intros _; exists l, rr; reflexivity].
Qed.
