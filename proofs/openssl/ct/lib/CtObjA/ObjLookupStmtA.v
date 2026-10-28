(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApCnf ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_obj_lookup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApObjRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Notation zbytes := CtRepP.W_obj_lookup.zbytes.
Import ListNotations.
Open Scope Z_scope.

Notation obj_bsearch_idx := CtRepP.W_obj_lookup.obj_bsearch_idx.

Definition OSSL_BSEARCH_A : Z := 0x2052c0.
Definition OBJ_CMP_FN_A : Z := 0x2220b0.        (* [comment removed for export] *)
Definition OBJ_CMP_A : Z := 0x23b33c.           (* [comment removed for export] *)
Definition OBJ_NID2OBJ_A : Z := 0x21f390.
Definition OSSL_OBJ_OBJ2NID_A : Z := 0x220db0.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OSSL_BSEARCH_STACK_A : Z := 96 + 16 + 16 + RT_STACK.
Definition O2N_STACK_A : Z := 112 + OSSL_BSEARCH_STACK_A.      (* [comment removed for export] *)
Definition N2O_STACK_A : Z := 112 + RT_STACK.                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bsearch_resA (r : option Z) : Z := match r with Some i => A_OBJ_OBJS_VA + 4 * i | None => 0 end.

(* [comment removed for export] *)
Definition ablk (L : list block) (A n : Z) : Prop := exists b, In b L /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b.

Lemma ablk_mono : forall L L' A n, (forall b, In b L -> In b L') -> ablk L A n -> ablk L' A n.
Proof. intros L L' A n H (b & Hb & H1 & H2). exists b. split; [exact (H b Hb)| split; [exact H1| exact H2]]. Qed.
Lemma ablk_sub : forall L A n A' n', ablk L A n -> A <= A' -> A' + n' <= A + n -> ablk L A' n'.
Proof. intros L A n A' n' (b & Hb & H1 & H2) G1 G2. exists b. split; [exact Hb| split; lia]. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition bsearch_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'.

(* [comment removed for export] *)
Definition ossl_bsearch_cpsA : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo KP KA KD : Z) (kb : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + OSSL_BSEARCH_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  ro_cells ctasegs m KP [C8 (wz KA)] -> ablk (OW ++ LB) KP 8 -> KP mod 8 = 0 ->
  ro_cells ctasegs m (KA + 16) [C4 (wz 0); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] -> ablk (OW ++ LB) (KA + 16) 16 -> KA mod 8 = 0 -> 0 < KA ->   (* [comment removed for export] *)
  bytes_at ctasegs m KD kb -> 0 < Z.of_nat (length kb) < 2^31 -> ablk (OW ++ LB) KD (Z.of_nat (length kb)) ->
  a0 = wz KP -> a1 = wz A_OBJ_OBJS_VA -> a2 = wz NUM_OBJ -> a3 = wz 4 -> a4 = wz OBJ_CMP_FN_A -> a5 = wz 0 -> a6 = wz 0 ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz OSSL_BSEARCH_A) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (bsearch_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m
                        (bsearch_resA (obj_bsearch_idx OBJ_BSEARCH_FUEL (zbytes kb) 0 NUM_OBJ)))).

(* [comment removed for export] *)
Definition lk_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (r : Z) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'
    /\ AHEAP Σ' OW LB m' /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition ossl_obj_obj2nid_nid_stmtA : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo KA knid lnlen : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + O2N_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  a0 = wz KA -> KA = A_NID_OBJS_VA + 40 * knid -> 0 < knid < NUM_NID -> static_obj_ok knid lnlen ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz OSSL_OBJ_OBJ2NID_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (lk_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m knid Σ') c
                /\ length (rt_live RT Σ') = length (rt_live RT Σ)).

(* [comment removed for export] *)
Definition ossl_obj_obj2nid_hit_stmtA : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo KA KD : Z) (kb : list byte) (nid lnlen : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + O2N_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  a0 = wz KA -> 0 < KA -> KA mod 8 = 0 ->
  ro_cells ctasegs m (KA + 16) [C4 (wz 0); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] -> ablk (OW ++ LB) (KA + 16) 16 ->
  bytes_at ctasegs m KD kb -> 0 < Z.of_nat (length kb) < 2^31 -> ablk (OW ++ LB) KD (Z.of_nat (length kb)) ->
  obj_lookup (zbytes kb) = Some (nid, lnlen) ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz OSSL_OBJ_OBJ2NID_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (lk_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m nid Σ') c
                /\ length (rt_live RT Σ') = length (rt_live RT Σ)).

(* [comment removed for export] *)
Definition OBJ_nid2obj_stmtA : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo n lnlen : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + N2O_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  0 < n < NUM_NID -> static_obj_ok n lnlen ->
  a0 = wz n ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz OBJ_NID2OBJ_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (lk_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m (A_NID_OBJS_VA + 40 * n) Σ') c
                /\ length (rt_live RT Σ') = length (rt_live RT Σ)).

End WithRT.
