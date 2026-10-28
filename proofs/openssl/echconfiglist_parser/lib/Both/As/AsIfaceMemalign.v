(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame SysStep Exec Arr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition APOSIX_MEMALIGN_STUB : Z := 0x1bf180.   (* [comment removed for export] *)
Definition APOSIX_MEMALIGN_ICPT : Z := 0x1bfaf8.
Definition APC0_POSIX_MEMALIGN : Z := 0x1bfb98.    (* [comment removed for export] *)

Section Sig.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition memalign_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (P al n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (Ab : Z) junk (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                FR (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ apres H LB (bv_unsigned sp) (write_to_mem m (wa P) (le8 (Z_to_bv 64 Ab))) m'
      /\ ablock_range H Ab n /\ Ab mod al = 0 /\ as_RHEAP H s' ((p, Ab, n) :: LB) m'
      /\ rw_cells asegs m' Ab [Cells.CB (Z.to_nat n) junk]
      /\ addressable m' Ab n
      /\ rw_cells asegs m' P [C8 (Z_to_bv 64 Ab)]
      /\ ACONST m'
      /\ (as_AL H s' >= as_AL H s - as_Cm H (n + al))%Z.

  Definition memalign_stmt (entry pc0 : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (P al n lo B : Z) (errv : word) (mo : Model)
           (CH : list (Z * Z)) (pjunk : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          FR (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_alloc_ok H s LB (n + al)%Z -> (as_Cm H (n + al) <= as_AL H s)%Z ->
      as_rauxv_ok H m B -> (bv_unsigned sp <= B)%Z ->
      stk asegs m lo (bv_unsigned sp) -> (aceil <= lo)%Z -> (lo <= bv_unsigned sp - AMALLOC_STACK)%Z ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      (bv_unsigned sp mod 16 = 0)%Z ->
      ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) pc0 (bv_unsigned ra :: map snd CH) ->
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 P -> (P mod 8 = 0)%Z -> rw_cells asegs m P [C8 pjunk] ->
      aclient_write_ok H LB (P, P + 8)%Z -> aconst_ok (P, P + 8)%Z -> (P + 8 <= lo \/ bv_unsigned sp <= P)%Z ->
      (* [comment removed for export] *)
      a1 = Z_to_bv 64 al -> (al = 64)%Z ->
      a2 = Z_to_bv 64 n -> (n = 32768)%Z ->
      as_SR H (memalign_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB P al n lo B m mo) (mkCfg msF mo).
End Sig.
