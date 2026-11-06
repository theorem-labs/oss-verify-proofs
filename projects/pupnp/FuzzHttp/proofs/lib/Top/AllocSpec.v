(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach.
Import ListNotations.
Local Open Scope Z_scope.

Section C.
Context {HC : HasCeiling}.
Variable segs : list Segment.
Variable AI : alloc_if segs.

Let L := ai_L segs AI.
Let K := ai_K segs AI.
Let PS := ai_PS segs AI.
Let BL := list (block K).
Notation mem := (word -> option byte).

Definition client_addr (LB : BL) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (exists lo hi, al_client_static L lo hi /\ lo <= a < hi) \/ in_block LB a.

Definition heap_pres (LB : BL) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> client_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma heap_pres_refl : forall LB SP m, heap_pres LB SP m m.
Proof. intros LB SP m a _ _; auto. Qed.

#[using="Type"] Lemma heap_pres_trans : forall LB SP m1 m2 m3,
  heap_pres LB SP m1 m2 -> heap_pres LB SP m2 m3 -> heap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Definition block_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling
  /\ Forall (fun w => A + n <= fst w \/ snd w <= A) (al_img L).

Definition alloc_frame (sp : word) (lo B : Z) (m m' : mem) (LBkeep : BL) : Prop :=
  mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ RENV segs AI m' B
  /\ (exists errv' : word, rw_cells segs m' (al_errno L) [C4 errv'])
  /\ heap_pres LBkeep (bv_unsigned sp) m m'.

Definition malloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : BL) (n lo B : Z) (m : mem)
    : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ alloc_frame sp lo B m m' LB
    /\ ( (a0 = Z_to_bv 64 0 /\ LB' = LB /\ RHEAP segs AI s' LB m')
       \/ (exists k A junk, a0 = Z_to_bv 64 A /\ LB' = (k, A, n) :: LB /\ block_range A n
             /\ RHEAP segs AI s' LB' m'
             /\ rw_cells segs m' A [CB (Z.to_nat n) junk]) ).

Definition malloc_contract_at (pc : Z) : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (n lo B : Z) (errv : word),
  RHEAP segs AI s LB m ->
  RENV segs AI m B -> bv_unsigned sp <= B ->
  stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
  rw_cells segs m (al_errno L) [C4 errv] ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  SREACH AI (malloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo B m)
    (MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs))
    s LB.

Definition free_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LBrest : BL) (lo B : Z) (m : mem)
    : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ alloc_frame sp lo B m m' LBrest
    /\ LB' = LBrest /\ RHEAP segs AI s' LBrest m'.

Definition free_contract_at (pc : Z) : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (k : K) (A n lo B : Z) (errv : word),
  RHEAP segs AI s LB m -> In (k, A, n) LB ->
  RENV segs AI m B -> bv_unsigned sp <= B ->
  stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
  rw_cells segs m (al_errno L) [C4 errv] ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 A ->
  SREACH AI (free_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (lb_remove (ai_K_eqb segs AI) k LB) lo B m)
    (MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs))
    s LB.

Definition free_null_contract_at (pc : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt segs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m (seg_rom segs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

Definition realloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : BL) (k : K) (A sz n lo B : Z) (old : list byte) (m : mem)
    : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ ( (a0 = Z_to_bv 64 0 /\ LB' = LB /\ alloc_frame sp lo B m m' LB /\ RHEAP segs AI s' LB m')
       \/ (exists k' A' junk, a0 = Z_to_bv 64 A'
             /\ LB' = (k', A', n) :: lb_remove (ai_K_eqb segs AI) k LB
             /\ block_range A' n
             /\ alloc_frame sp lo B m m' (lb_remove (ai_K_eqb segs AI) k LB)
             /\ RHEAP segs AI s' LB' m'
             /\ rw_cells segs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n sz)) old ++ junk)]) ).

Definition realloc_contract_at (pc : Z) : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (k : K) (A sz n lo B : Z)
         (old : list byte) (errv : word),
  RHEAP segs AI s LB m -> In (k, A, sz) LB ->
  rw_cells segs m A [CB (Z.to_nat sz) old] ->
  RENV segs AI m B -> bv_unsigned sp <= B ->
  stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
  rw_cells segs m (al_errno L) [C4 errv] ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  SREACH AI (realloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m)
    (MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs))
    s LB.

Definition realloc_null_contract_at (pc : Z) : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (n lo B : Z) (errv : word),
  RHEAP segs AI s LB m ->
  RENV segs AI m B -> bv_unsigned sp <= B ->
  stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
  rw_cells segs m (al_errno L) [C4 errv] ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  SREACH AI (malloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo B m)
    (MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs))
    s LB.

Record alloc_contracts := mkAC {
  ac_malloc : malloc_contract_at (al_malloc_pc L);
  ac_free : free_contract_at (al_free_pc L);
  ac_free_null : free_null_contract_at (al_free_pc L);
  ac_realloc : realloc_contract_at (al_realloc_pc L);
  ac_realloc_null : realloc_null_contract_at (al_realloc_pc L)
}.

End C.

Arguments client_addr {HC segs} AI LB SP a.
Arguments heap_pres {HC segs} AI LB SP m m'.
Arguments block_range {HC segs} AI A n.
Arguments alloc_frame {HC segs} AI sp lo B m m' LBkeep.
Arguments malloc_post {HC segs} AI.
Arguments free_post {HC segs} AI.
Arguments realloc_post {HC segs} AI.
Arguments malloc_contract_at {HC segs} AI pc.
Arguments free_contract_at {HC segs} AI pc.
Arguments free_null_contract_at segs pc.
Arguments realloc_contract_at {HC segs} AI pc.
Arguments realloc_null_contract_at {HC segs} AI pc.
Arguments alloc_contracts {HC segs} AI.
