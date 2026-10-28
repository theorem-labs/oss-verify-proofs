(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import R_cache_defs R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Lemma ro_c8_image : forall (m : mem) A v, mem_inv bsegs m -> ro_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true -> (0 <= A)%Z ->
  (A + 8 <= 2^64)%Z -> ro_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v MI Hb HA Hl. pose proof (ro_cells_image bsegs m A _ MI Hb HA ltac:(rewrite length_le8; cbn; lia)) as R.
  rewrite length_le8 in R. destruct R as [_ R]. split; [exact (conj I I)| exact R].
Qed.

Lemma Z_to_bv_w64 : forall x, Z_to_bv 64 (w64 x) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, w64. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod. lia.
Qed.

Lemma mm_add_bv : forall h k,
  Z_to_bv 64 (Z.lxor (Z.land (Z.lxor (Z.shiftr (Z.land (k * 14313749767032793493) 18446744073709551615) 47)
                                    (Z.land (k * 14313749767032793493) 18446744073709551615) * 14313749767032793493)
                            18446744073709551615) h * 14313749767032793493)
  = Z_to_bv 64 (mm_add h k).
Proof.
  intros h k. unfold mm_add, mm_mix, mm_m. rewrite Z_to_bv_w64. change 18446744073709551615%Z with (Z.ones 64).
  rewrite !Z.land_ones by lia. reflexivity.
Qed.

Lemma mm_get_bv : forall H, (0 <= H < 2^64)%Z ->
  Z_to_bv 64
    (Z.lxor
       (Z.shiftr (Z.land (Z.lxor (Z.shiftr (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                                   18446744073709551615) 47)
                                 (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                    18446744073709551615) * 14313749767032793493) 18446744073709551615) 47)
       (Z.land (Z.lxor (Z.shiftr (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                                    18446744073709551615) 47)
                       (Z.land (Z.lxor 0 (Z.land H 18446744073709551615) * 14313749767032793493)
                          18446744073709551615) * 14313749767032793493) 18446744073709551615))
  = Z_to_bv 64 (mm_get (mm_add H 0)).
Proof.
  intros H RH. unfold mm_get, mm_add, mm_mix, w64, mm_m. change 18446744073709551615%Z with (Z.ones 64).
  rewrite !Z.land_ones by lia. rewrite (Z.mod_small H (2^64)) by lia. reflexivity.
Qed.

Lemma hseg_step : forall (ws : list word) j w, nth_error ws (Z.to_nat j) = Some w -> (0 <= j)%Z ->
  firstn (Z.to_nat (j + 1)) (map bv_unsigned ws) = firstn (Z.to_nat j) (map bv_unsigned ws) ++ [bv_unsigned w].
Proof.
  intros ws j w Hw Hj. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  assert (Hw' : nth_error (map bv_unsigned ws) (Z.to_nat j) = Some (bv_unsigned w)) by (rewrite nth_error_map, Hw; reflexivity).
  clear Hw. revert ws Hw'. induction (Z.to_nat j) as [|n IH]; intros ws Hw'; destruct ws as [|x ws]; cbn in *; try discriminate.
  - injection Hw' as <-. reflexivity.
  - f_equal. apply IH. exact Hw'.
Qed.

Lemma fold_mm_range : forall l h, (0 <= h < 2^64)%Z -> (0 <= fold_left mm_add l h < 2^64)%Z.
Proof. induction l as [|x l IH]; intros h Hh; cbn [fold_left]; [exact Hh| apply IH, mm_add_range]. Qed.

Section HASH.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (TR sz : Z) (ws rest : list word) (Q : machine_state -> Prop).
Hypothesis Hsz : (1 <= sz <= 254)%Z.
Hypothesis Hl : Z.of_nat (length ws) = sz.
Hypothesis HTR : (0 <= TR /\ TR + 2040 <= 2^63)%Z.
Hypothesis TB : u64arr bsegs m TR (ws ++ rest).

Section LOOP.
Variables (s3 s6 s7 : word).
Hypothesis K : forall a5 a6, evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (TR + 8 * sz))
             (Z_to_bv 64 (fold_left mm_add (map bv_unsigned ws) (mm_init sz))) (Z_to_bv 64 0) (Z_to_bv 64 (TR + 8 * sz))
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa6b2c) fc None m (seg_rom bsegs)).

Lemma hash_loop : forall k j hacc a5 a6, Z.to_nat (sz - j) = k -> (0 <= j < sz)%Z ->
  hacc = fold_left mm_add (firstn (Z.to_nat j) (map bv_unsigned ws)) (mm_init sz) ->
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (TR + 8 * j)) (Z_to_bv 64 hacc)
             (Z_to_bv 64 0) (Z_to_bv 64 (TR + 8 * sz)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa6b08) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros j hacc a5 a6 Hk Hj Eh; [lia|].
  destruct (nth_error ws (Z.to_nat j)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
  pose proof (u64arr_read bsegs m TR (ws ++ rest) j w (Z_to_bv 64 (TR + 8 * j)) TB
                ltac:(rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hw; discriminate); exact Hw)
                ltac:(lia) ltac:(reflexivity)) as RD.
  assert (Rh : (0 <= hacc < 2^64)%Z) by (rewrite Eh; apply fold_mm_range, mm_init_range).
  do 8 zstep. clear RD.
  rewrite mm_add_bv.
  assert (Eh' : mm_add hacc (bv_unsigned w) = fold_left mm_add (firstn (Z.to_nat (j + 1)) (map bv_unsigned ws)) (mm_init sz)).
  { rewrite (hseg_step ws j w Hw) by lia. rewrite fold_left_app. cbn [fold_left]. rewrite Eh. reflexivity. }
  rewrite Eh'. clear Eh'.
  zstep.
  destruct (Z.eq_dec (j + 1) sz) as [Ej|Nj].
  - ifF. replace (TR + 8 * j + 8)%Z with (TR + 8 * sz)%Z by lia. rewrite Ej. rewrite firstn_all2 by (rewrite map_length; lia). apply K.
  - ifT. replace (TR + 8 * j + 8)%Z with (TR + 8 * (j + 1))%Z by lia. apply (IH (j + 1)%Z); [lia| lia| reflexivity].
Qed.
End LOOP.

Lemma hash_frag : forall a0 a3 a4 a5 a6 s3 s6 s7,
  mem_inv bsegs m ->
  (forall a0' a1' a2' a4' a5' a6', evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' (Z_to_bv 64 0x400000) a4' a5' a6' a7 s2
             (Z_to_bv 64 (depot_hash (map bv_unsigned ws))) s4 s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xa6b6c) fc None m (seg_rom bsegs))) ->
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TR) (Z_to_bv 64 sz) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xa6ad0) fc None m (seg_rom bsegs)).
Proof.
  intros a0 a3 a4 a5 a6 s3 s6 s7 MI K2.
  pose proof (ro_c8_image m 0x102e8 mm_m MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RM.
  pose proof (ro_c8_image m 0x10338 mm_m8 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RM8.
  pose proof (ro_c8_image m 0x10458 mm_seed MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RS.
  unfold mm_m, mm_m8, mm_seed in RM, RM8, RS.
  do 14 zstep.
  assert (E1 : Z.land sz 4294967295 = sz).
  { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  assert (E2 : Z.shiftr sz 32 = 0%Z).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  rewrite E1, E2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. replace (sz * 8)%Z with (8 * sz)%Z by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (Z.lxor (sz * 3829533694005038248 mod 2 ^ 64) 10900877739976798860) with (mm_init sz).
  replace (Z_to_bv 64 TR) with (Z_to_bv 64 (TR + 8 * 0)) by (f_equal; lia).
  eapply (hash_loop s3 s6 s7) with (k := Z.to_nat sz) (j := 0%Z); [| lia| lia| reflexivity].
  intros a5' a6'.
  do 16 zstep.
  rewrite mm_get_bv by (apply fold_mm_range, mm_init_range).
  replace (mm_get (mm_add (fold_left mm_add (map bv_unsigned ws) (mm_init sz)) 0)) with (depot_hash (map bv_unsigned ws))
    by (unfold depot_hash; rewrite map_length, Hl; reflexivity).
  apply K2.
Qed.
End HASH.
