(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition PREFIX_CREATE : Z := 0x294ca4.
Definition PREFIX_DESTROY : Z := 0x294d90.
Definition BIO_SET_DATA : Z := 0x237a9c.
Definition BIO_SET_INIT : Z := 0x237b2c.
Definition BIO_GET_DATA : Z := 0x237ae4.
Definition PREFIX_CREATE_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition PREFIX_DESTROY_STACK : Z := 32 + CRYPTO_FREE_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma zero16_cells : forall m A,
  rw_cells ctasegs m A [CB 16%nat (repeat (Z_to_bv 8 0) 16%nat)] -> rw_cells ctasegs m A [C8 (wz 0); C4 (wz 0); C4 (wz 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; auto| unfold MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

Lemma prefix_ctx_cells_fold : forall m A,
  rw_cells ctasegs m A [C8 (wz 0); C4 (wz 0); C4 (wz 1)] -> rw_cells ctasegs m A (prefix_ctx_cells 0 0 1).
Proof. intros m A H. exact H. Qed.

(* [comment removed for export] *)
Definition apres_but (LB OW : list block) (SP : Z) (bio bsz : Z) (m m' : mem) : Prop :=
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (bio <= a < bio + bsz)) m m'.

(* [comment removed for export] *)
Definition oalloc_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (bio bsz n lo : Z) (m : mem) (rv : Z) (init : Z -> mem -> Prop)
    (p : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' A,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_but LB OW (bv_unsigned sp) bio bsz m m'
    /\ rt_credit RT Σ - mcost n <= rt_credit RT Σ'
    /\ ablock_range A n /\ AHEAP Σ' ((p, A, n) :: OW) LB m' /\ acc ctasegs m' A n /\ init A m'.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free2_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW' LB : list block) (lo : Z) (m : mem) (rv : Z) (fin : mem -> Prop)
    (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres LB OW' (bv_unsigned sp) m m'
    /\ rt_credit RT Σ <= rt_credit RT Σ'
    /\ AHEAP Σ' OW' LB m' /\ fin m'.

(* [comment removed for export] *)


End WithRT.
