(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition FRAMES_MAX2 : nat := 4096.

Definition e_stack_malloc_1 : Z := 0x66e24.

Definition e_memmove2 : Z := 0x812f0.

Definition e_annotate : Z := 0x850e0.

Definition ann_g1 (n : Z) : Z := - (8 * (n / 16 / 8192)).
Definition ann_g2 (n : Z) : Z := - (8 * ((n / 16) mod 8192)).

Definition ann_block (p n v : Z) : list (Z * Z) :=
  if v =? n then [(p, n)] else [(p, ann_g1 n); (p, ann_g2 n); (p, v)].

Lemma ann_block_plain : forall p n, ann_block p n n = [(p, n)].
Proof. intros p n. unfold ann_block. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma ann_block_fst : forall p n v e, In e (ann_block p n v) -> fst e = p.
Proof.
  intros p n v e H. unfold ann_block in H. destruct (v =? n); cbn in H;
    repeat (destruct H as [<-|H]; [reflexivity|]); destruct H.
Qed.

Lemma ann_block_vis : forall p n v, In (p, v) (ann_block p n v).
Proof.
  intros p n v. unfold ann_block. destruct (Z.eqb_spec v n) as [->|NE]; cbn; [left; reflexivity | right; right; left; reflexivity].
Qed.

Lemma ann_block_sizes : forall p n v e, 0 <= n -> In e (ann_block p n v) -> e = (p, v) \/ snd e <= 0.
Proof.
  intros p n v e Hn H. unfold ann_block in H. destruct (Z.eqb_spec v n) as [->|NE]; cbn in H.
  - destruct H as [<-|[]]. left; reflexivity.
  - destruct H as [<-|[<-|[<-|[]]]]; [right | right | left; reflexivity]; cbn; unfold ann_g1, ann_g2.
    + pose proof (Z.div_pos (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
    + pose proof (Z.mod_pos_bound (n / 16) 8192 ltac:(lia)). lia.
Qed.
Lemma ann_block_length : forall p n v, (length (ann_block p n v) <= 3)%nat.
Proof. intros p n v. unfold ann_block. destruct (v =? n); cbn; lia. Qed.

Lemma live_remove_ann_block : forall p n v l1 l2,
  live_remove p (l1 ++ ann_block p n v ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof.
  intros p n v l1 l2.
  assert (CONS : forall e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l).
  { intros e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. }
  assert (APP : forall l l', live_remove p (l ++ l') = live_remove p l ++ live_remove p l').
  { intros l l'. induction l as [|e l IH]; [reflexivity|]. cbn [app]. rewrite !CONS, IH. destruct (fst e =? p); reflexivity. }
  rewrite APP, APP. replace (live_remove p (ann_block p n v)) with (@nil (Z * Z)); [reflexivity|].
  symmetry. unfold ann_block. destruct (v =? n); rewrite !CONS; cbn [fst]; rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma ann_block_inj : forall p n v n' v', 0 <= v <= n -> 0 <= v' <= n' -> n mod 16 = 0 -> n' mod 16 = 0 -> n < 2 ^ 30 -> n' < 2 ^ 30 ->
  ann_block p n v = ann_block p n' v' -> n = n' /\ v = v'.
Proof.
  intros p n v n' v' Hv Hv' Hn Hn' Bn Bn' E. unfold ann_block, ann_g1, ann_g2 in E.
  destruct (Z.eqb_spec v n) as [->|NE]; destruct (Z.eqb_spec v' n') as [->|NE']; try discriminate E.
  - injection E as <-. split; reflexivity.
  - injection E as E1 E2 <-.
    pose proof (Z.div_mod (n / 16) 8192 ltac:(lia)). pose proof (Z.div_mod (n' / 16) 8192 ltac:(lia)).
    pose proof (Z.div_mod n 16 ltac:(lia)). pose proof (Z.div_mod n' 16 ltac:(lia)). split; [lia | reflexivity].
Qed.

Section Contracts2.
Variable RT : rt_sig.

Definition stack_malloc1_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6a7e68 ->
  (length (rt_frames RT Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_malloc_1 m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size 1 - 8) /\ wr_at asegs m' (shad f) (fs_size 1 / 8)) c
       /\ rt_frames RT Σ' = (f, 1%nat) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size 1 < USTACK_TOP).

Definition memmove_icontract2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memmove2 m)))
    (icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at asegs m' d bs)).

Definition memcmp_wide_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^40 ->
  bytes_at asegs m p bp -> bytes_at asegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)))
    (fun c => exists r : word, (r = Z_to_bv 64 0 <-> bp = bq)
       /\ icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).

Definition memcmp_zero_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)))
    (icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) lo 0 0 m (fun _ => True)).

Definition annotate_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n v v' : Z) (l1 l2 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = l1 ++ ann_block p n v ++ l2 -> Forall (fun e => fst e <> p) l1 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (p + n) -> a2 = Z_to_bv 64 (p + v) -> a3 = Z_to_bv 64 (p + v') ->
  0 <= v <= n -> 0 <= v' <= n -> v mod 8 = 0 -> v' mod 8 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_annotate m)))
    (fun c => exists (Σ' : rts RT) (r : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m') c
       /\ rt_live RT Σ' = l1 ++ ann_block p n v' ++ l2 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

Record rt_contracts2 : Prop := mkRTC2 {
  rc2_rt : rt_contracts RT;
  rc2_stack_malloc_1 : stack_malloc1_contract;
  rc2_memmove2 : memmove_icontract2;
  rc2_memcmp_wide : memcmp_wide_icontract;
  rc2_annotate : annotate_contract;
  rc2_memcmp_zero : memcmp_zero_icontract
}.

End Contracts2.
