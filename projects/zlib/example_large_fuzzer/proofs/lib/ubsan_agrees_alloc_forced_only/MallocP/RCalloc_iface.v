(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocHINV Malloc_iface MallocRep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RCALLOC_SYM : Z := 0x2086c.          (* [comment removed for export] *)
Definition RALLZEROP_SYM : Z := 0x221d8.        (* [comment removed for export] *)
Definition RMEMSET_SYM : Z := 0x27c50.          (* [comment removed for export] *)
Definition RMALLOC_REPLACED : Z := 0x5ae50.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RCALLOC_STACK : Z := 32 + RMALLOC_STACK.

(* [comment removed for export] *)
Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells psegs m' A [CB (Z.to_nat n) (zeros (Z.to_nat n))]
       end.

(* [comment removed for export] *)
Definition rcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  rw_cells psegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 1 -> a1 = Z_to_bv 64 n -> 0 < n < 2^32 ->
  implM psegs (raw_malloc n) s
        (rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom psegs)).
End WithCeiling0.
