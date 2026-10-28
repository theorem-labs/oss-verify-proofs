(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require TMemcpy_u.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition rsegs := Ubsan.Ubsan_loaded_segments.

Definition memcpy_entry := 0xab480%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at rsegs m' (bv_unsigned a1) src.

Lemma mem_inv_munch_wr : forall (m m' : word -> option byte) (A n : Z),
  mem_inv rsegs m -> munch [(A, A + n)]%Z m m' -> wr_at rsegs m A n -> mem_inv rsegs m'.
Proof.
  intros m m' A n MI MU (HA & HB & WR) x b Hx.
  destruct (Z_lt_dec (bv_unsigned x) A) as [L|L].
  { rewrite (MU x) in Hx by (cbn; lia). exact (MI _ _ Hx). }
  destruct (Z_le_dec (A + n) (bv_unsigned x)) as [G|G].
  { rewrite (MU x) in Hx by (cbn; lia). exact (MI _ _ Hx). }
  specialize (WR (bv_unsigned x - A)%Z ltac:(lia)).
  replace (wa (A + (bv_unsigned x - A))) with x in WR.
  2:{ unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. replace (A + (bv_unsigned x - A))%Z with (bv_unsigned x) by lia.
      rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range]. }
  destruct (m x) eqn:E; [exact (MI _ _ E) | exact (wview_not_ro _ _ _ WR E)].
Qed.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xab480) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI.
  eapply evt_mono.
  { exact (TMemcpy_u.memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk SRC LEN DST SEP). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & RW & BA).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj E (conj MU (conj WM (conj _ (conj RW BA))))).
  eapply mem_inv_munch_wr; [exact MI | exact MU |].
  destruct DST as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W.
  assert (EN : Z.of_nat (Z.to_nat (bv_unsigned a2)) = bv_unsigned a2) by (apply Z2Nat.id; apply bv_unsigned_in_range).
  rewrite EN in W. exact W.
Qed.
End CEIL_WRAP_1.
