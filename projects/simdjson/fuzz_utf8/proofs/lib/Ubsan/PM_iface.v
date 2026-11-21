(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PM_iface.v, UM_fuzz.v and UM_fuzzF.v: the statements of this harness's parts (the fallback validate_utf8 it calls, the harness from its join point, its first call) in place of minify's lambda, vector, string and assign statements. *)
(* The parts of fuzz_utf8's UBSan client proof, as statements: [vutf8_stmt] (the fallback implementation's
   validate_utf8, a leaf whose UBSan checks never fire), [fuzz_join_stmt] (LLVMFuzzerTestOneInput from the point both
   of its paths join after the static vector's guard, to its return) and [fuzz_first_stmt] (its first call). *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessU ProgP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import PAtexit_cells RunDraw PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
(* Code addresses of the ubsan binary, read from its code: the fallback implementation's validate_utf8 is the
   vtable slot the harness calls (PFALLBACK_VT + 0x28, PU_iface.client_img); PJOIN is the instruction after the
   guard test (0x3bcf0, [ld s5, 0x28(s4)]), where the first call rejoins the later ones; PSTATICS is the base the
   harness keeps in s4 ([auipc a0, 0xb0; addi s4, a0, -0x4fc] at 0x3bcdc), the guard is at PSTATICS + 8
   (PVEC_GUARD) and the vector at PSTATICS + 0x28 (PVEC). *)
Definition PVUTF8 : Z := 0x3f130.
Definition VUTF8_STACK : Z := 96.
Definition PJOIN : Z := 0x3bcf0.
Definition PSTATICS : Z := 0xeb7e0.

(* validate_utf8 of the fallback implementation: it returns 0 or 1 to [ra], keeps the callee-saved registers,
   writes nothing outside its frame below [sp] and leaves the stack below [sp] as stack. *)
Definition vutf8_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ (a0' = Z_to_bv 64 0 \/ a0' = Z_to_bv 64 1)
    /\ munch [(bv_unsigned sp - VUTF8_STACK, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Definition vutf8_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z) (pl : list Z) (lo : Z),
    bytes_at usegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
    0 < D -> D + zlength pl <= ATOP -> zlength pl < 2^26 ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - VUTF8_STACK ->
    (D + zlength pl <= lo \/ bv_unsigned sp <= D) ->
    mem_inv usegs m ->
    a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength pl) ->
    evt usegs (vutf8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PVUTF8) fc None m (seg_rom usegs)).

(* What the call has done by the join point, against the state at entry. *)
Definition join_rel (s0 : PState) (LB0 : list block) (m0 : mem) (s : PState) (LB : list block) (m : mem) (SP : Z) : Prop :=
  harness_pres LB0 SP m0 m
  /\ ps_so s = ps_so s0
  /\ (forall b, In b LB0 -> In b LB)
  /\ match ps_fa s0 with
     | Some _ => LB = LB0 /\ ps_fa s = ps_fa s0
     | None => exists p V, LB = (p, V, 8) :: LB0 /\ ps_fa s = Some p
     end.

(* The harness from its join point: the static vector holds the fallback implementation, ra and s0..s9 of the
   caller are saved at sp - 88 (the 112-byte frame), s0 = Size, s1 = Data, s4 = PSTATICS. *)
Definition fuzz_join_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (s s0' : PState) (LB LB0 : list block)
         (D : Z) (pl : list Z) (AB lo : Z) (errv : word) (p : bptr) (V : Z),
    RHEAP s LB m -> In (p, V, 8) LB -> ps_fa s = Some p ->
    join_rel s0' LB0 m0 s LB m (bv_unsigned sp) ->
    bytes_at usegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
    rclient_range LB0 (bv_unsigned sp) D (zlength pl) ->
    0 < D -> D + zlength pl <= ATOP -> zlength pl < 2^26 ->
    client_img m ->
    rw_cells usegs m V [C8 (Z_to_bv 64 PFALLBACK)] ->
    rw_cells usegs m PVEC_GUARD guard1 ->
    rw_cells usegs m PVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
    rw_cells usegs m PFALLBACK [C8 (Z_to_bv 64 PFALLBACK_VT)] ->
    patexit 3 PDTOR_THUNK PVEC m ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    stk usegs m lo (bv_unsigned sp + -88) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
    rw_cells usegs m (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs m (errno_addr tp) [C4 errv] ->
    mem_inv usegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
    implM usegs (mret 0 : Monad.M PState Z) s
          (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' LB0 AB lo m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength pl)) (Z_to_bv 64 D)
                   a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 (Z_to_bv 64 PSTATICS) xs5 xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PJOIN) fc None m (seg_rom usegs)).

(* The first call (the static vector not built yet): fuzz_oneU_stmt's statement for ps_fa s = None. *)
Definition fuzz_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
    ps_fa s = None ->
    RHEAP s LB m ->
    bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
    rclient_range LB (bv_unsigned sp) D (zlength payload) ->
    (forall i, 0 <= i < zlength payload -> outside client_wr (D + i)) ->
    0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
    client_static s LB m ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] ->
    mem_inv usegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) ->
    ra = Z_to_bv 64 PTRUN_RET ->
    implM usegs (ProgP.fuzz_one payload) s
          (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PFUZZ_ENTRY) fc None m (seg_rom usegs)).
End CANSEC1.
