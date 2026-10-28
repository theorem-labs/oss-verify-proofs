(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition e_aligned_alloc : Z := 0x835c4.
Definition e_handle_no_return : Z := 0x8a84c.
Definition e_unwind_raise : Z := 0x76944.
Definition real_unwind_raise : Z := 0x1433c4.
Definition e_strncasecmp : Z := 0x6c41c.
Definition e_vsnprintf : Z := 0x71168.
Definition e_frexpl : Z := 0x6e958.
Definition e_tls_get_addr : Z := 0x6c498.

Definition rt_sigW (RT : rt_sig) (W : rts RT -> mem -> Prop) : rt_sig :=
  mkRTS (rts RT) W (ARTM RT) (rt_live RT) (rt_frames RT) (rt_allow RT) (rt_sp0 RT) (fun _ => 0).

Definition tls_get_addr_icontract (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x6a7e68 ->
  0 < p -> p mod 8 = 0 -> bv_unsigned sp <= p -> p + 16 <= USTACK_TOP ->
  rw_cells asegs m p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_tls_get_addr m)))
            (fun c => exists v : word, icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Section Contracts5.
Variable RT : rt_sig.

Definition EXC_SIZE : Z := 144.
Definition aligned_alloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 EXC_SIZE -> tp = Z_to_bv 64 0x6a7e68 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost EXC_SIZE <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_aligned_alloc m)))
            (malloc_postF RT fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 EXC_SIZE lo m).

Definition NORET_DEPTH : Z := 0x40000.
Definition noret_post (Q : rts RT -> mem -> Prop) (Σ : rts RT) (PMc : Model -> Prop) (fc : bv 32)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) : config -> Prop :=
  ASTA RT Σ PMc (fun ms => exists (v : word) (m' : mem), ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
                    /\ Q Σ m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp)
                    /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m').
Definition handle_no_return_contract (P Q : rts RT -> mem -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6a7e68 ->
  P Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> rt_sp0 RT Σ - bv_unsigned sp <= NORET_DEPTH -> bv_unsigned sp + 0xb0 <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_handle_no_return m)))
            (noret_post Q Σ PMc fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m).

Definition unwind_entry_st (Q : rts RT -> mem -> Prop) (Σ : rts RT)
    (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 real_unwind_raise) fc None m' (seg_rom asegs)
    /\ Q Σ m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'.
Definition unwind_raise_stmt (P Q : rts RT -> mem -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6a7e68 ->
  P Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> rt_sp0 RT Σ - bv_unsigned sp <= NORET_DEPTH -> bv_unsigned sp + 0xb0 <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_unwind_raise m)))
            (ASTA RT Σ PMc (unwind_entry_st Q Σ ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)).

Record rt_win : Type := mkRTW {
  ARTW : Z -> rts RT -> mem -> Prop;
  w_enter : forall c, handle_no_return_contract (fun Σ m => ART RT Σ m /\ rt_credit RT Σ = c) (ARTW c);
  w_again : forall c, handle_no_return_contract (ARTW c) (ARTW c);
  w_unwind : forall c, unwind_raise_stmt (ARTW c) (ARTW c);
  w_tls : forall c, tls_get_addr_icontract (rt_sigW RT (ARTW c));
  w_facts : forall c, art_facts (rt_sigW RT (ARTW c));
  w_rc : forall c, rt_contracts (rt_sigW RT (ARTW c));
  w_rc2 : forall c, rt_contracts2 (rt_sigW RT (ARTW c));
  w_exit : forall c Σ m, ARTW c Σ m -> rt_frames RT Σ = [] -> ART RT Σ m /\ rt_credit RT Σ = c
}.

Definition zlower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

Fixpoint scase_idx (bp bq : list Z) (n : nat) : nat :=
  match n, bp, bq with
  | S n', x :: bp', y :: bq' => if (zlower x =? zlower y) && negb (x =? 0) then S (scase_idx bp' bq' n') else O
  | _, _, _ => O
  end.

Definition scase_res (bp bq : list Z) (n : nat) : Z :=
  let i := scase_idx bp bq n in
  if (i <? n)%nat then zlower (nth i bp 0) - zlower (nth i bq 0) else 0.

Definition strncasecmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q n : Z) (bp bq : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n ->
  0 < p <= 2^47 -> 0 < q <= 2^47 -> 0 <= n < 2^26 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) -> Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  let k := Z.min n (Z.of_nat (scase_idx bp bq (Z.to_nat n)) + 1) in
  k <= Z.of_nat (length bp) -> k <= Z.of_nat (length bq) ->
  checked_src RT Σ m sp lo p k -> checked_src RT Σ m sp lo q k ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)))
    (icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (scase_res bp bq (Z.to_nat n))) lo 0 0 m (fun _ => True)).

Definition strncasecmp0_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)))
    (icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) lo 0 0 m (fun _ => True)).

Record rt_contracts5 : Type := mkRTC5 {
  rc5_aligned_alloc : aligned_alloc_contract;
  rc5_strncasecmp : strncasecmp_icontract;
  rc5_strncasecmp0 : strncasecmp0_icontract;
  rc5_win : rt_win
}.

End Contracts5.
