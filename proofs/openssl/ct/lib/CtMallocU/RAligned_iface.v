(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog LibProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RPOSIX_MEMALIGN_SYM : Z := 0x2b4c14.   (* [comment removed for export] *)
Definition raligned_alloc_entry : Z := 0x2b4c78.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RALIGNED_STACK : Z := RMALLOC_STACK + 48.

(* [comment removed for export] *)
Definition rheap_pres_but (LB : list block) (SP : Z) (X : Z * Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (fst X <= a < snd X) ->
    m' (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m' (wa a) <> None).

Lemma rheap_pres_but_of_pres : forall LB SP X m m', rheap_pres LB SP m m' -> rheap_pres_but LB SP X m m'.
Proof. intros LB SP X m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

Lemma rheap_pres_but_trans : forall LB SP X m1 m2 m3,
  rheap_pres_but LB SP X m1 m2 -> rheap_pres_but LB SP X m2 m3 -> rheap_pres_but LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.

Definition rposix_memalign_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (al n mp lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres_but LB (bv_unsigned sp) (mp, mp + 8) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => RHEAP s' LB m' /\ (forall a, mp <= a < mp + 8 -> m' (wa a) = m (wa a))
       | Some p => exists A junk,
           a0 = Z_to_bv 64 0 /\ A mod al = 0 /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells ctusegs m' A [CB (Z.to_nat n) junk]
           /\ rw_cells ctusegs m' mp [C8 (Z_to_bv 64 A)]
       end.

Definition rposix_memalign_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (al n mp lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RALIGNED_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 mp -> bv_unsigned sp <= mp -> mp + 8 <= B -> wr_at ctusegs m mp 8 ->
  a1 = Z_to_bv 64 al -> (al = 32 \/ al = 64) ->
  a2 = Z_to_bv 64 n -> 0 <= n -> aligned_req al n < 2^32 ->
  implM ctusegs (raw_aligned_alloc al n) s
        (rposix_memalign_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB al n mp lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RPOSIX_MEMALIGN_SYM) fc None m (seg_rom ctusegs)).

End WithCeiling0.
