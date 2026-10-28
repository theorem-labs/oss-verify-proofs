(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_BCMP : Z := 0xd05e8.
Definition SJ_BOM : Z := 0x12f3e.

Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  apply unsigned_lit. lia.
Qed.
Lemma byte_unsigned : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma wz_diff_nz : forall d, -256 < d < 256 -> d <> 0 -> bv_eqb (Z_to_bv 64 d) (Z_to_bv 64 0) = false.
Proof.
  intros d R NZ. destruct (bv_eqb (Z_to_bv 64 d) (Z_to_bv 64 0)) eqn:E; [| reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with 18446744073709551616 in E. rewrite (Z.mod_small 0) in E by lia.
  destruct (Z.lt_ge_cases d 0).
  - replace d with (d + 18446744073709551616 + (-1) * 18446744073709551616) in E by lia.
    rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.
Lemma zxb_cmp_eq : forall c (b : byte), 0 <= c < 256 -> negb (bv_eqb (zxb (Z_to_bv 8 c)) (zxb b)) = false -> c = bv_unsigned b.
Proof.
  intros c b R K. apply negb_false_iff in K. unfold bv_eqb in K. apply Z.eqb_eq in K.
  rewrite !zxb_unsigned, byte_unsigned in K by exact R. exact K.
Qed.
Lemma zxb_cmp_ne : forall c (b : byte), 0 <= c < 256 -> negb (bv_eqb (zxb (Z_to_bv 8 c)) (zxb b)) = true -> c <> bv_unsigned b.
Proof.
  intros c b R K E. apply negb_true_iff in K. assert (EB : Z_to_bv 8 c = b).
  { apply bv_eq. rewrite byte_unsigned by exact R. exact E. }
  rewrite EB in K. unfold bv_eqb in K. rewrite Z.eqb_refl in K. discriminate.
Qed.

Definition bom_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c0 c1 c2 : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ (a0 = Z_to_bv 64 0 /\ c0 = 239 /\ c1 = 187 /\ c2 = 191
        \/ bv_eqb a0 (Z_to_bv 64 0) = false /\ ~ (c0 = 239 /\ c1 = 187 /\ c2 = 191)).

Lemma bom_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c0 c1 c2 : Z),
  mem_inv usegs m -> bytes_at usegs m A [Z_to_bv 8 c0; Z_to_bv 8 c1; Z_to_bv 8 c2] ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= A -> A + 3 < 2^64 ->
  evt usegs (bom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c0 c1 c2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 SJ_BOM) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_BCMP) fc None m (seg_rom usegs)).
Proof.
  intros until c2. intros MI BA R0 R1 R2 A0 A3.
  unfold SJ_BCMP, SJ_BOM.
  pose proof (u8ro_read usegs m A _ 0 _ (wa (A + 0)) BA eq_refl ltac:(lia) eq_refl) as RD0.
  pose proof (u8ro_read usegs m A _ 1 _ (wa (A + 1)) BA eq_refl ltac:(lia) eq_refl) as RD1.
  pose proof (u8ro_read usegs m A _ 2 _ (wa (A + 2)) BA eq_refl ltac:(lia) eq_refl) as RD2.

  step. step. if_false.
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
  step. step. step.
  assert (MISS : forall (c k : Z) (kb : byte) xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6, 0 <= c < 256 -> bv_unsigned kb = k -> 0 <= k < 256 -> c <> k ->
            ~ (c0 = 239 /\ c1 = 187 /\ c2 = 191) ->
            evt usegs (bom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c0 c1 c2 m)
              (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 (zxb (Z_to_bv 8 c)) (zxb kb) xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 853728) fc None m (seg_rom usegs))).
  { intros c k kb xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Rc Ek Rk NE NM.
    step. step. apply evt_done. unfold bom_post. do 15 eexists. split; [cbv delta [mkR]; reflexivity|]. right. split; [| exact NM].
    rewrite !zxb_unsigned, byte_unsigned, Ek by exact Rc. apply wz_diff_nz; lia. }
  if_cases K0.
  { pose proof (zxb_cmp_ne c0 _ R0 K0) as NE. eapply evt_eq; [| eapply (MISS c0 239 _)]; [cbv delta [mkR]; reflexivity| exact R0| reflexivity| lia| exact NE| intros (E & _); exact (NE E)]. }
  pose proof (zxb_cmp_eq c0 _ R0 K0) as E0. change (bv_unsigned (239 : byte)) with 239 in E0. clear K0.

  step. step. step. step. if_true.
  replace (Z_to_bv 64 (A + 0 + 1)) with (Z_to_bv 64 (A + 1)) by (f_equal; lia).
  step. step. step.
  if_cases K1.
  { pose proof (zxb_cmp_ne c1 _ R1 K1) as NE. eapply evt_eq; [| eapply (MISS c1 187 _)]; [cbv delta [mkR]; reflexivity| exact R1| reflexivity| lia| exact NE| intros (_ & E & _); exact (NE E)]. }
  pose proof (zxb_cmp_eq c1 _ R1 K1) as E1. change (bv_unsigned (187 : byte)) with 187 in E1. clear K1.
  step. step. step. step. if_true.
  replace (Z_to_bv 64 (A + 1 + 1)) with (Z_to_bv 64 (A + 2)) by (f_equal; lia).
  step. step. step.
  if_cases K2.
  { pose proof (zxb_cmp_ne c2 _ R2 K2) as NE. eapply evt_eq; [| eapply (MISS c2 191 _)]; [cbv delta [mkR]; reflexivity| exact R2| reflexivity| lia| exact NE| intros (_ & _ & E); exact (NE E)]. }
  pose proof (zxb_cmp_eq c2 _ R2 K2) as E2. change (bv_unsigned (191 : byte)) with 191 in E2. clear K2.

  step. step. step. step. if_false. step. step.
  apply evt_done. unfold bom_post. do 15 eexists. split; [cbv delta [mkR]; reflexivity|]. left. auto.
Qed.
