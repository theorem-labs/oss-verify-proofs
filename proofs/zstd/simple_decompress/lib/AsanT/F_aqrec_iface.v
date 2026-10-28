(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes ARepQ.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_amerge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Fixpoint deq_bq (l : list bq) (bytes min_size : Z) {struct l} : list bq * list bq * Z :=
  match l with
  | [] => ([], [], bytes)
  | b :: l' => if min_size <? bytes
               then let '(taken, rest, bytes') := deq_bq l' (bytes - b_size (fst b)) min_size in (b :: taken, rest, bytes')
               else ([], l, bytes)
  end.

Lemma deq_bq_fst : forall l bytes min_size,
  let '(taken, rest, bytes') := deq_bq l bytes min_size in
  dequeue_while (map fst l) bytes min_size = (map fst taken, map fst rest, bytes').
Proof.
  induction l as [|b l IH]; intros bytes min_size; cbn [deq_bq dequeue_while map]; [reflexivity|].
  destruct (min_size <? bytes); [| reflexivity].
  specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq l (bytes - b_size (fst b)) min_size) as [[tk rs] b2].
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition qrec_mergeb (nb bytes : Z) : bool :=
  (Q_BATCH_BYTES * nb <? bytes) && (bytes * 100 <? Q_BATCH_BYTES * nb * 200).

(* [comment removed for export] *)
Definition qrec_fun (X : list bq) (bytes min_size : Z) : list bq * list bq * Z :=
  let '(gl, ex) := (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) in
  let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
  (rest, ex ++ taken, bytes2).

End CANSEC1.
Notation QREC_FRAME := 80 (only parsing).
Notation QREC_FRONT_STACK := 96 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition qrec_front_post (L : alayout) (X : list bq) (bytes min_size lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a0 a4 a5 a6 a7 t3 t4 t5 t6 tbw : word) m',
    let '(rest, T, bytes2) := qrec_fun X bytes min_size in
    ms' = MS (mkR (Z_to_bv 64 0x35824) (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) gp tp t0 t1 t2 xs0 xs1
                  a0 (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35a1c) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - QREC_FRONT_STACK, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - QREC_FRAME)
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (bv_unsigned sp - QREC_FRAME)
         [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tbw]
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0));
                                    C8 (Z_to_bv 64 bytes2)]
    /\ chain L m' rest 0 /\ chain L m' T 0
    /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= min_size.

Definition qrec_front_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (X : list bq) (bytes min_size lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - QREC_FRONT_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 min_size -> 0 <= min_size < 2^63 ->
  (* [comment removed for export] *)
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 bytes)] ->
  chain L m X 0 ->
  Forall (bgeom L AQ_GCACHE (bv_unsigned sp - QREC_FRAME)) X -> Forall (fun x => 0 <= qb_slot (snd x)) X ->
  NoDup (map (fun x => qb_slot (snd x)) X) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> bytes = batches_bytes (map fst X) -> bytes < 2^56 ->
  Z.of_nat (length X) < 2^40 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X ->
  evtF bsegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x356b4) fc None m (seg_rom bsegs)).
End CANSEC2.
