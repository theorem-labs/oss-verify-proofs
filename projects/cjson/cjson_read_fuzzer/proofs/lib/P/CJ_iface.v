(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PMALLOC  : Z := 0x15320.   (* [comment removed for export] *)
Definition PFREE    : Z := 0x151e0.   (* [comment removed for export] *)
Definition PREALLOC : Z := 0x16b8c.   (* [comment removed for export] *)
Definition PTP      : Z := 0x33890.   (* [comment removed for export] *)
Definition PERRNO   : Z := 0x337ec.   (* [comment removed for export] *)
Definition PHOOKS   : Z := 0x23528.   (* [comment removed for export] *)
Definition PGERROR  : Z := 0x337b0.   (* [comment removed for export] *)
Definition PLCONV   : Z := 0x223f8.   (* [comment removed for export] *)
Definition PDOTSTR  : Z := 0x102de.   (* [comment removed for export] *)
Definition PEMPTY   : Z := 0x33790.   (* [comment removed for export] *)
Definition PIMG_LO  : Z := 0x10000.   (* [comment removed for export] *)
Definition PIMG_HI  : Z := 0x55000.
Definition PDATA_LO : Z := 0x22000.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PLIBC    : Z := 0x53b18.
Definition PCTX_END : Z := 0x53b90 + 928.
Definition PSSP     : Z := 0x53af8.   (* [comment removed for export] *)
Definition PGOT_SSP : Z := 0x224e8.   (* [comment removed for export] *)

Definition RMALLOC_STACK : Z := 8192.  (* [comment removed for export] *)

Definition wz (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cblock : Type := (Z * Z)%type.   (* [comment removed for export] *)

Definition in_cblock (LB : list cblock) (a : Z) : Prop :=
  exists A n, In (A, n) LB /\ A <= a < A + n.

Definition palloc_static (a : Z) : Prop :=
  (PLIBC <= a < PCTX_END) \/ (PERRNO <= a < PERRNO + 4) \/ (PSSP <= a < PSSP + 8) \/ (PGOT_SSP <= a < PGOT_SSP + 8).

(* [comment removed for export] *)
Definition cj_client_addr (LB : list cblock) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a) \/ in_cblock LB a.

Definition cj_pres (LB : list cblock) (SP : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> cj_client_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

(* [comment removed for export] *)
Definition cj_write_ok (SPB : Z) (LB : list cblock) (iv : Z * Z) : Prop :=
  snd iv <= fst iv                                                     (* [comment removed for export] *)
  \/ (alloc_ceiling <= fst iv /\ snd iv <= SPB)                        (* [comment removed for export] *)
  \/ (PERRNO <= fst iv /\ snd iv <= PERRNO + 4)                        (* [comment removed for export] *)
  \/ (PGERROR <= fst iv /\ snd iv <= PGERROR + 16)                     (* [comment removed for export] *)
  \/ (exists A n, In (A, n) LB /\ A <= fst iv /\ snd iv <= A + n).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= PIMG_LO \/ PIMG_HI <= A).

Fixpoint cb_remove (A : Z) (LB : list cblock) : list cblock :=
  match LB with
  | [] => []
  | (B, n) :: LB' => if Z.eqb B A then LB' else (B, n) :: cb_remove A LB'
  end.

(* [comment removed for export] *)
Definition CJST (m : word -> option byte) : Prop :=
  rw_cells psegs m PHOOKS [C8 (wz PMALLOC); C8 (wz PFREE); C8 (wz PREALLOC)]
  /\ (exists e1 e2 : word, rw_cells psegs m PGERROR [C8 e1; C8 e2])
  /\ rw_cells psegs m PLCONV [C8 (wz PDOTSTR)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_pres_refl : forall LB SP m, cj_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

Lemma cj_pres_trans : forall LB SP m1 m2 m3,
  cj_pres LB SP m1 m2 -> cj_pres LB SP m2 m3 -> cj_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma cj_pres_weaken : forall LB LB' SP SP' m m',
  cj_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> cj_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(A & n & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

Definition cj_client_range (LB : list cblock) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (PDATA_LO <= A /\ A + n <= PIMG_HI /\ (A + n <= PLIBC \/ PCTX_END <= A) /\ (A + n <= PERRNO \/ PERRNO + 4 <= A)
      /\ (A + n <= PSSP \/ PSSP + 8 <= A) /\ (A + n <= PGOT_SSP \/ PGOT_SSP + 8 <= A))
  \/ (exists B k, In (B, k) LB /\ B <= A /\ A + n <= B + k).

Lemma cj_client_range_addr : forall LB SP A n a,
  cj_client_range LB SP A n -> A <= a < A + n -> cj_client_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha.
  unfold cj_client_range, cj_client_addr, palloc_static, in_cblock, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP, PDATA_LO, PIMG_HI in *.
  destruct HR as [H|[H|(B & k & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists B, k; split; [exact Hb|lia]].
Qed.

Lemma cj_pres_bytes_at : forall LB SP m m' A bs,
  cj_pres LB SP m m' -> bytes_at psegs m A bs -> cj_client_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at psegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply cj_client_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma cj_pres_wr_at : forall LB SP m m' A n,
  cj_pres LB SP m m' -> wr_at psegs m A n -> cj_client_range LB SP A n -> wr_at psegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply cj_client_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma cj_pres_rw_cells : forall LB SP m m' A cs,
  cj_pres LB SP m m' -> rw_cells psegs m A cs -> cj_client_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells psegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply cj_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply cj_pres_wr_at; eauto.
Qed.

Lemma cj_pres_stk : forall LB SP m m' lo hi,
  cj_pres LB SP m m' -> stk psegs m lo hi -> SP <= lo -> stk psegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmts.
Variable LHEAP : Z -> list cblock -> (word -> option byte) -> Model -> Prop.

(* [comment removed for export] *)

Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPB : Z) (LB : list cblock) (n lo : Z) (m : word -> option byte)
    : machine_state -> Model -> Prop :=
  fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' PERRNO [C4 errv']
    /\ cj_pres LB (bv_unsigned sp) m m'
    /\ ( (a0 = wz 0 /\ LHEAP SPB LB m' mo')
         \/ (exists (A : Z) (junk : list byte),
               a0 = wz A /\ cblock_range A n /\ ~ In A (map fst LB)
               /\ LHEAP SPB ((A, n) :: LB) m' mo'
               /\ rw_cells psegs m' A [CB (Z.to_nat n) junk]) ).

Definition malloc_scps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
         (SPB : Z) (LB : list cblock) (n lo : Z) (errv : word),
  LHEAP SPB LB m mo ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] ->
  mem_inv psegs m ->
  tp = wz PTP ->
  a0 = wz n -> 0 <= n < 2^32 ->
  SCPS psegs (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LB n lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz PMALLOC) fc None m (seg_rom psegs)) mo.

Definition free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPB : Z) (LB : list cblock) (A lo : Z) (errv : word) (m : word -> option byte)
    : machine_state -> Model -> Prop :=
  fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' PERRNO [C4 errv]                       (* [comment removed for export] *)
    /\ cj_pres (cb_remove A LB) (bv_unsigned sp) m m'
    /\ LHEAP SPB (cb_remove A LB) m' mo'.

Definition free_scps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
         (SPB : Z) (LB : list cblock) (A n lo : Z) (errv : word),
  LHEAP SPB LB m mo -> In (A, n) LB ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] ->
  mem_inv psegs m ->
  tp = wz PTP ->
  a0 = wz A ->
  SCPS psegs (free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LB A lo errv m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz PFREE) fc None m (seg_rom psegs)) mo.

(* [comment removed for export] *)
Definition free_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = wz 0 ->
  evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom psegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PFREE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition realloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPB : Z) (LB : list cblock) (A k n lo : Z) (old : list byte) (m : word -> option byte)
    : machine_state -> Model -> Prop :=
  fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' PERRNO [C4 errv']
    /\ ( (a0 = wz 0 /\ LHEAP SPB LB m' mo' /\ cj_pres LB (bv_unsigned sp) m m')
         \/ (exists (B : Z) (junk : list byte),
               a0 = wz B /\ cblock_range B n /\ (B = A \/ ~ In B (map fst LB))
               /\ LHEAP SPB ((B, n) :: cb_remove A LB) m' mo'
               /\ cj_pres (cb_remove A LB) (bv_unsigned sp) m m'
               /\ rw_cells psegs m' B [CB (Z.to_nat (Z.min k n)) (firstn (Z.to_nat (Z.min k n)) old);
                                      CB (Z.to_nat (n - Z.min k n)) junk]) ).

Definition realloc_scps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
         (SPB : Z) (LB : list cblock) (A k n lo : Z) (old : list byte) (errv : word),
  LHEAP SPB LB m mo -> In (A, k) LB -> bytes_at psegs m A old -> Z.of_nat (length old) = k ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] ->
  mem_inv psegs m ->
  tp = wz PTP ->
  a0 = wz A -> a1 = wz n -> 0 <= n < 2^32 ->
  SCPS psegs (realloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LB A k n lo old m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz PREALLOC) fc None m (seg_rom psegs)) mo.

Definition realloc_null_stmt : Prop :=   (* [comment removed for export] *)
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
         (SPB : Z) (LB : list cblock) (n lo : Z) (errv : word),
  LHEAP SPB LB m mo ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] ->
  mem_inv psegs m ->
  tp = wz PTP ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n < 2^32 ->
  SCPS psegs (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LB n lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz PREALLOC) fc None m (seg_rom psegs)) mo.

End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record cj_heap_iface : Type := mkCJHI {
  LHEAP : Z -> list cblock -> (word -> option byte) -> Model -> Prop;
  (* [comment removed for export] *)
  lh_mok : forall SPB LB m mo, LHEAP SPB LB m mo -> MOK mo;
  lh_frame : forall SPB LB m m' mo W,
      LHEAP SPB LB m mo -> munch W m m' -> wmono psegs m m' -> Forall (cj_write_ok SPB LB) W -> LHEAP SPB LB m' mo;
  lh_perm : forall SPB LB LB' m mo, LHEAP SPB LB m mo -> Permutation LB LB' -> LHEAP SPB LB' m mo;
  lh_lower : forall SPB SPB' LB m mo, LHEAP SPB LB m mo -> SPB' <= SPB -> LHEAP SPB' LB m mo;
  lh_block_range : forall SPB LB m mo A n, LHEAP SPB LB m mo -> In (A, n) LB -> cblock_range A n;
  lh_blocks_disjoint : forall SPB LB m mo A1 n1 A2 n2,
      LHEAP SPB LB m mo -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 -> A1 + n1 <= A2 \/ A2 + n2 <= A1;
  lh_nodup : forall SPB LB m mo, LHEAP SPB LB m mo -> NoDup (map fst LB);
  lh_block_wr : forall SPB LB m mo A n, LHEAP SPB LB m mo -> In (A, n) LB -> wr_at psegs m A n;
  (* [comment removed for export] *)
  lh_block_slack : forall SPB LB m mo A n i, LHEAP SPB LB m mo -> In (A, n) LB ->
      0 <= i -> (A + n + i) < (A + n + 7) / 8 * 8 -> m (wa (A + n + i)) <> None;
  (* [comment removed for export] *)
  lh_ssp : forall SPB LB m mo, LHEAP SPB LB m mo ->
      rw_cells psegs m PGOT_SSP [C8 (wz PSSP)] /\ exists canary : word, rw_cells psegs m PSSP [C8 canary];
  (* [comment removed for export] *)
  lh_malloc : malloc_scps_stmt LHEAP;
  lh_free : free_scps_stmt LHEAP;
  lh_free_null : free_null_stmt;
  lh_realloc : realloc_scps_stmt LHEAP;
  lh_realloc_null : realloc_null_stmt LHEAP
}.


End CeilWrap.
