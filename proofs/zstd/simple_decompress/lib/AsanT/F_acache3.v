(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AModelFacts APrimFacts F_acache F_acache2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition cb_sm (s : Z) : Z :=
  let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
  Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT}.
Definition cb_clz (y : Z) : Z :=
  let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
             * 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT}.
Definition cb_fin (s : Z) : Z :=
  let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT}.
Definition cb_sm_ok (s : Z) : bool :=
  negb (s mod 8 =? 0) || (let y := cb_sm s in let k := cb_clz y in (0 <=? y) && (y <? 2^64) && (47 <=? k) && (k <=? 54)).
(* [comment removed for export] *)
Lemma cb_sm_ok_all : forallb_range cb_sm_ok 513 (Z.to_nat (65536 - 513 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Local Opaque cb_sm cb_clz.
Local Strategy expand [cb_sm_ok].
Lemma cb_sm_ok_sound : forall s, cb_sm_ok s = true -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros z Hz M8. unfold cb_sm_ok in Hz. cbv zeta in Hz. replace (z mod 8 =? 0) with true in Hz by (symmetry; apply Z.eqb_eq; exact M8). cbn [negb orb] in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  repeat split; assumption.
Qed.
Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  exact (range_by_compute (fun s => s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54) cb_sm_ok 513 65536 cb_sm_ok_sound cb_sm_ok_all).
Qed.
Local Transparent cb_sm cb_clz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x38130) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38054) fc None m (seg_rom bsegs)).
Proof.
  intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size;
          lazymatch goal with |- forall z, _ -> _ -> Z_to_bv 64 _ = Z_to_bv 64 _ => idtac | |- ?G => idtac "CB-GOAL" G end;
          apply (range_bv_eq8 cb_fin class_id 513 65536); vm_cast_no_check (eq_refl true)).   (* [comment removed for export] *)
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.
