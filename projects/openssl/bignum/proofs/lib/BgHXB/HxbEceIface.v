(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_ece : Z := 0x1f9030.
Definition ECE_RA : Z := 0x1ee258.

Definition ECE_STACK : Z := 0x14010.

Definition ECE_COST : Z := 2048.

Section EceIface.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition ece_postA (COST : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (EA : err_addrs)
      (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bgbsegs)
      /\ AHEAP Σ' OW LB m' /\ mem_inv bgbsegs m' /\ stk bgbsegs m' lo (bv_unsigned sp)
      /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (ea_ES EA <= a < ea_ES EA + 904)) m m'
      /\ rw_cells bgbsegs m' (ea_ES EA) [CB 904 ES_CLEARED]
      /\ rt_credit RT Σ - COST <= rt_credit RT Σ'.

Definition ERR_clear_error_cpsA_stmt (STACK COST : Z) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (EA : err_addrs) (lo : Z),
    AHEAP Σ OW LB m -> stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - STACK ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv bgbsegs m -> tp = wz TP_A ->
    ra = wz ECE_RA ->

    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
    crypto_statics m -> err_inv m OW EA -> COST <= rt_credit RT Σ ->
    cps bgbsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz e_ece) fc None m (seg_rom bgbsegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (ece_postA COST ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB EA lo m Σ') c).

End EceIface.

Definition ece_cps : Prop := forall AR : ARun, @ar_FR AR = [] -> @ERR_clear_error_cpsA_stmt AR ECE_STACK ECE_COST.
