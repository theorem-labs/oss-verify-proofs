(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_ece : Z := 0x1f4354.
Definition ECE_RA : Z := 0x1ee5f4.
(* [comment removed for export] *)
Definition ECE_STACK : Z := 0x14010.
(* [comment removed for export] *)
Definition ECE_COST : Z := 2048.

Section EceIface.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition ece_postA (COST : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (EA : err_addrs)
      (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ AHEAP Σ' OW LB m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (ea_ES EA <= a < ea_ES EA + 904)) m m'
      /\ rw_cells bsegs m' (ea_ES EA) [CB 904 ES_CLEARED]
      /\ rt_credit RT Σ - COST <= rt_credit RT Σ'.

Definition ERR_clear_error_cpsA_stmt (STACK COST : Z) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (EA : err_addrs) (lo : Z),
    AHEAP Σ OW LB m -> stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - STACK ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv bsegs m -> tp = wz TP_A ->
    ra = wz ECE_RA ->
    (* [comment removed for export] *)
    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
    crypto_statics m -> err_inv m OW EA -> COST <= rt_credit RT Σ ->
    cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz e_ece) fc None m (seg_rom bsegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (ece_postA COST ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB EA lo m Σ') c).

End EceIface.

(* [comment removed for export] *)
Definition ece_cps : Prop := forall AR : ARun, @ERR_clear_error_cpsA_stmt AR ECE_STACK ECE_COST.
