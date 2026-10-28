From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_cmp_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.

Definition BX_MPI_CMP_ABS : Z := 0x9d6f4.
Definition MPI_CMP_ABS_STACK_A : Z := 16.

Definition mpi_cmp_abs_raw_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
    (X P n sg : Z) (xs : list word) (pad : word) (Y Q n' sg' : Z) (ys : list word) (pad' : word),
  rw_cells segs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad] ->
  bytes_at segs m P (u32s xs) -> Z.of_nat (length xs) = n -> 0 <= n <= 10000 ->
  (n = 0 \/ (0 < P /\ P mod 4 = 0)) -> 0 < X -> X mod 8 = 0 ->
  rw_cells segs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'] ->
  bytes_at segs m Q (u32s ys) -> Z.of_nat (length ys) = n' -> 0 <= n' <= 10000 ->
  (n' = 0 \/ (0 < Q /\ Q mod 4 = 0)) -> 0 < Y -> Y mod 8 = 0 ->
  mem_inv segs m -> al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m X 16 -> aobj segs AL CS m Y 16 ->
  (1 <= n -> aobj segs AL CS m P (4 * n)) -> (1 <= n' -> aobj segs AL CS m Q (4 * n')) ->
  stk segs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - MPI_CMP_ABS_STACK_A ->
  bv_unsigned sp mod 16 = 0 -> crange CS lo (bv_unsigned sp - lo) ->
  (X + 16 <= lo \/ bv_unsigned sp <= X) -> (Y + 16 <= lo \/ bv_unsigned sp <= Y) ->
  (1 <= n -> P + 4 * n <= lo \/ bv_unsigned sp <= P) -> (1 <= n' -> Q + 4 * n' <= lo \/ bv_unsigned sp <= Q) ->
  a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 Y ->
  evtA segs AL CS
    (mpi_cmp_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (lval xs n - lval ys n')) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Definition mpi_cmp_abs_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (dX dY : mpd) (lo : Z),
  mpd_at segs m LB dX -> mpd_at segs m LB dY ->
  (md_own dX = LHeap -> 0 < md_p dX) -> (md_own dY = LHeap -> 0 < md_p dY) ->
  mem_inv segs m -> al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m (md_addr dX) 16 -> aobj segs AL CS m (md_addr dY) 16 ->
  (1 <= md_n dX -> aobj segs AL CS m (md_p dX) (4 * md_n dX)) ->
  (1 <= md_n dY -> aobj segs AL CS m (md_p dY) (4 * md_n dY)) ->
  stk segs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - MPI_CMP_ABS_STACK_A ->
  bv_unsigned sp mod 16 = 0 -> crange CS lo (bv_unsigned sp - lo) ->
  (md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX) ->
  (md_addr dY + 16 <= lo \/ bv_unsigned sp <= md_addr dY) ->
  (1 <= md_n dX -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX) ->
  (1 <= md_n dY -> md_p dY + 4 * md_n dY <= lo \/ bv_unsigned sp <= md_p dY) ->
  a0 = Z_to_bv 64 (md_addr dX) -> a1 = Z_to_bv 64 (md_addr dY) ->
  evtA segs AL CS
    (mpi_cmp_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
       (Z.sgn (mpd_abs dX - mpd_abs dY)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
        (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).
