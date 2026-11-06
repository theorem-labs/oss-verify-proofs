(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AKit AModelFacts APrimFacts F_acache F_acache2.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
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
(* [comment removed for export] *)
Definition m64 (x : Z) : Z := Z.land x 18446744073709551615.
Lemma m64_eq : forall x, m64 x = x mod 18446744073709551616.
Proof. intros x. unfold m64. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition sw32 (z : Z) : Z := Z.land (z + 2147483648) 4294967295 - 2147483648.
Lemma sw32_eq : forall z, sw32 z = bv_swrap 32 z.
Proof.
  intros z. unfold sw32, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.
Definition cb_clzF (y : Z) : Z :=
  let a := m64 (y - Z.land (Z.shiftr y 1) 6148914691236517205) in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr (m64 (Z.land (m64 (b + Z.shiftr (m64 b) 4)) 1085102592571150095 * 72340172838076673)) 56.
Lemma cb_clzF_eq : forall y, cb_clzF y = cb_clz y.
Proof. intros y. unfold cb_clzF, cb_clz. cbv zeta. rewrite !m64_eq. reflexivity. Qed.
Definition cb_finF (s : Z) : Z :=
  let k := cb_clzF (cb_sm s) in let sh := m64 (sw32 (62 - k)) in
  Z.lor (Z.lxor (m64 (Z.shiftl k 1)) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor (m64 (sw32 (Z.shiftl 18446744073709551615 (sh mod 32)))) 18446744073709551615))
  + -2.
Lemma cb_finF_eq : forall s, cb_finF s = cb_fin s.
Proof. intros s. unfold cb_finF, cb_fin. cbv zeta. rewrite !cb_clzF_eq, !m64_eq, !sw32_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition smtbl (l : Z) : Z := 18446744073709551616 - Z.shiftl 1 (l + 1).
Definition smT (t : Z) : bool := Z.eqb (cb_sm (8 * t)) (smtbl (Z.log2 (8 * t))).
Lemma smT_all : forallb_range smT 65 (Z.to_nat (8192 - 65 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition clzT (l : Z) : bool :=
  let y := smtbl l in let k := cb_clzF y in ((0 <=? y) && (y <? 18446744073709551616) && (47 <=? k) && (k <=? 54))%bool.
Lemma clzT_all : forallb_range clzT 9 (Z.to_nat (16 - 9 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition finT (t : Z) : bool := Z.eqb (cb_finF (8 * t)) (class_id (8 * t)).
Lemma finT_all : forallb_range finT 65 (Z.to_nat (8192 - 65 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma size8_t : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> s = 8 * (s / 8) /\ 65 <= s / 8 <= 8192.
Proof. intros s R M. Z.div_mod_to_equations. lia. Qed.
Lemma log2_size : forall s, 513 <= s <= 65536 -> 9 <= Z.log2 s <= 16.
Proof.
  intros s R. split.
  - change 9 with (Z.log2 512). apply Z.log2_le_mono. lia.
  - change 16 with (Z.log2 65536). apply Z.log2_le_mono. lia.
Qed.
Local Opaque cb_sm cb_clz cb_clzF cb_finF cb_fin.
Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros s R M. destruct (size8_t s R M) as [E T].
  pose proof (forallb_range_spec smT _ 65 smT_all (s / 8) ltac:(lia)) as H1. unfold smT in H1. rewrite <- E in H1. apply Z.eqb_eq in H1.
  pose proof (log2_size s R) as L.
  pose proof (forallb_range_spec clzT _ 9 clzT_all (Z.log2 s) ltac:(lia)) as H2. unfold clzT in H2. cbv zeta in H2.
  rewrite !Bool.andb_true_iff in H2. destruct H2 as [[[A B] C] D].
  apply Z.leb_le in A. apply Z.ltb_lt in B. apply Z.leb_le in C. apply Z.leb_le in D.
  rewrite cb_clzF_eq in C, D. rewrite H1. change (2 ^ 64) with 18446744073709551616. repeat split; assumption.
Qed.
Lemma cb_fin_class_id : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> Z_to_bv 64 (cb_fin s) = Z_to_bv 64 (class_id s).
Proof.
  intros s R M. destruct (size8_t s R M) as [E T].
  pose proof (forallb_range_spec finT _ 65 finT_all (s / 8) ltac:(lia)) as H. unfold finT in H. rewrite <- E in H. apply Z.eqb_eq in H.
  rewrite <- cb_finF_eq, H. reflexivity.
Qed.
Local Transparent cb_sm cb_clz cb_clzF cb_finF cb_fin.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x5ec28) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5eb4c) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (class_id size)) ltac:(symmetry; exact (cb_fin_class_id size SZ M8)).   (* [comment removed for export] *)
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.
