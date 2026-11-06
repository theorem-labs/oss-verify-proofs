From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_TABLE_AGE : Z := 0x15b20.
Definition REAC_DISCO_TABLE_AGE_K : Z := 64.
Definition REAC_DISCO_STALE_NS : Z := 5000000000.

Definition disco_stale (T : list byte) (j now : Z) : bool :=
  (last_of T j <? now) && (REAC_DISCO_STALE_NS <? now - last_of T j).

Fixpoint age_loop (fuel : nat) (A : list byte) (now i m r : Z) : list byte * Z * Z :=
  match fuel with
  | O => (A, m, r)
  | S f =>
      if i <? m then
        if disco_stale A i now then age_loop f (upd A (48 * i) (entry_of A (m - 1))) now i (m - 1) (r + 1)
        else age_loop f A now (i + 1) m r
      else (A, m, r)
  end.

Definition age_model (T : list byte) (now : Z) : list byte * Z :=
  let '(A, m, r) := age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 in
  let B := upd A 384 (le4 (Z_to_bv 64 m)) in
  (if 0 <? r then upd B 392 (le4 (Z_to_bv 64 (seq_of T + 1))) else B, r).

Fixpoint age_count (f : Z -> bool) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => age_count f k' + (if f (Z.of_nat k') then 1 else 0)
  end.

Definition age_post (T : list byte) (now : Z) (T' : list byte) (removed : Z) : Prop :=
  length T' = 400%nat /\
  removed = age_count (fun j => disco_stale T j now) (Z.to_nat (n_of T)) /\
  0 <= removed <= n_of T /\
  n_of T' = n_of T - removed /\
  (forall j, 0 <= j < n_of T' -> disco_stale T' j now = false) /\
  seq_of T' = (if 0 <? removed then (seq_of T + 1) mod 2^32 else seq_of T) /\
  table_ok T' /\
  (exists p : Z -> Z,
     (forall j, 0 <= j < n_of T' -> 0 <= p j < n_of T /\ entry_of T' j = entry_of T (p j)) /\
     (forall j1 j2, 0 <= j1 < n_of T' -> 0 <= j2 < n_of T' -> p j1 = p j2 -> j1 = j2)) /\
  (forall k, 48 * n_of T <= k < 384 \/ 388 <= k < 392 \/ 396 <= k < 400 ->
     nth_error T' (Z.to_nat k) = nth_error T (Z.to_nat k)).

Definition reac_disco_table_age_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t now : Z) (T : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 now -> 0 <= now < 2^64 ->
    t <> 0 -> t mod 8 = 0 ->
    rw_cells rsegs m t [CB 400 T] -> length T = 400%nat -> table_ok T ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DISCO_TABLE_AGE_K <= bv_unsigned sp ->
    off_window sp REAC_DISCO_TABLE_AGE_K t 400 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (T' : list byte) (removed : Z),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 removed) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(t, t + 400); (bv_unsigned sp - REAC_DISCO_TABLE_AGE_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' t [CB 400 T'] /\
         age_model T now = (T', removed) /\
         age_post T now T' removed)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DISCO_TABLE_AGE) fc None m (seg_rom rsegs)).
