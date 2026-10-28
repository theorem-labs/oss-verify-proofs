(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_asan_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_memcmp : Z := 0x1ac58c.          (* [comment removed for export] *)
Definition e_strcpy : Z := 0x1ac65c.          (* [comment removed for export] *)
Definition e_asan_memmove : Z := 0x1c1ffc.    (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint memcmp_res (b1 b2 : list byte) : Z :=
  match b1, b2 with
  | x :: r1, y :: r2 => if bv_unsigned x =? bv_unsigned y then memcmp_res r1 r2 else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.

(* [comment removed for export] *)
Definition mv_cur (off : nat) (bs : list byte) (i : nat) : list byte := firstn i (skipn off bs) ++ skipn i bs.

Section ContractsPem.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition realloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (p n0 n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (q : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' q n /\ acc asegs m' q n
         /\ (forall bs, bytes_at asegs m p bs -> Z.of_nat (length bs) = Z.min n0 n -> bytes_at asegs m' q bs)) c
    /\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition realloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n0 n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n <= 64512 -> 1 <= n0 <= 64512 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 <= bv_unsigned sp ->
  unwind_ok (rt_cg RT Σ) e_realloc m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_realloc m)))
            (realloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).

(* [comment removed for export] *)
Definition memalign_plain (al n : Z) : Prop :=
  al = 64 /\ 1 <= n /\ n mod al = 0 /\ needed n + al <= 64512 /\ rz_size n mod al = 0
  /\ ClassID (needed n + al) = ClassID (needed n) /\ ClassSize (ClassID (needed n)) mod al = 0.

Definition memalign_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (pp al n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 al -> a2 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 ->
  memalign_plain al n -> 0 <= pp <= 2^47 -> checked_dst RT Σ m sp pp 8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok (rt_cg RT Σ) e_posix_memalign m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_posix_memalign m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) pp 8 m m'
         /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 p)] /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod al = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

(* [comment removed for export] *)
Definition memcmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
  length b1 = length b2 -> Z.of_nat (length b1) < 2^31 -> 0 < p1 <= 2^47 -> 0 < p2 <= 2^47 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 ->
  checked_src RT Σ m sp lo p1 (Z.of_nat (length b1)) -> checked_src RT Σ m sp lo p2 (Z.of_nat (length b1)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_memcmp m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memcmp_res b1 b2)) lo 0 0 m (fun _ => True)).

(* [comment removed for export] *)
Definition strcpy_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^31 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> 0 < d <= 2^47 ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src RT Σ m sp lo s (Z.of_nat (length str) + 1) -> checked_dst RT Σ m sp d (Z.of_nat (length str) + 1) ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strcpy m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length str) + 1) m
               (fun m' => bytes_at asegs m' d (str ++ [Z_to_bv 8 0]))).

(* [comment removed for export] *)
Definition memmove_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d off n : Z) (blk : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (d + off) -> a2 = Z_to_bv 64 n ->
  0 < d <= 2^47 -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length blk) -> 1 <= Z.of_nat (length blk) < 2^40 ->
  bytes_at asegs m d blk ->
  checked_src RT Σ m sp lo (d + off) n -> checked_dst RT Σ m sp d (Z.of_nat (length blk)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length blk)) m
               (fun m' => bytes_at asegs m' d (mv_cur (Z.to_nat off) blk (Z.to_nat n)))).

(* [comment removed for export] *)
Definition acc_global_fact (GOBJ : Z -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (b s a n : Z), ART RT Σ m -> GOBJ b s -> b <= a -> a + n <= b + s -> acc asegs m a n.


(* [comment removed for export] *)
Definition gsh_byte_fact (GOBJ : Z -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (b s g : Z), ART RT Σ m -> GOBJ b s -> b <= g -> g < b + s -> g mod 8 = 0 ->
    ro_cells asegs m (g / 8 + 2147450880) [C1 (Z_to_bv 8 (if b + s - g <? 8 then b + s - g else 0))].

(* [comment removed for export] *)
Definition live_mem_fact : Prop :=
  forall (Σ : rts RT) (m : mem) (p n : Z), ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 1 <= n ->
    (p + n <= 0x7fff8000 \/ 0x10007fff8000 <= p) /\ p + n <= 2^47.
(* [comment removed for export] *)
Definition live_hi_fact : Prop :=
  forall (Σ : rts RT) (m : mem) (p n : Z), ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> 0x10007fff8000 <= p.
Definition frame_mem_fact : Prop :=
  forall (Σ : rts RT) (m : mem) (f : Z) (k : nat), ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
    (f + fs_size k - 8 <= 0x7fff8000 \/ 0x10007fff8000 <= f) /\ f + fs_size k - 8 <= 2^47.

(* [comment removed for export] *)
Record art_facts_pem (GOBJ : Z -> Z -> Prop) : Prop := mkAFP {
  afp_acc_global : acc_global_fact GOBJ;
  afp_gsh_byte : gsh_byte_fact GOBJ;
  afp_live_mem : live_mem_fact;
  afp_live_hi : live_hi_fact;
  afp_frame_mem : frame_mem_fact
}.

Record rt_contracts_pem : Prop := mkRTCP {
  rcp_realloc : realloc_contract;
  rcp_memalign : memalign_contract;
  rcp_memcmp : memcmp_icontract;
  rcp_strcpy : strcpy_icontract;
  rcp_asan_memmove : memmove_icontract e_asan_memmove
}.

End ContractsPem.

(* [comment removed for export] *)
Lemma memalign_plain_ht : memalign_plain 64 32768.
Proof. unfold memalign_plain. repeat split; try (vm_compute; reflexivity); vm_compute; intros; discriminate. Qed.
