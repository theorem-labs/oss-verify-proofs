(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).

Definition Z_ADLER32 : Z := 0x1a6d8.
Definition Z_ADLER32_Z : Z := 0x1a314.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma csub_mask : forall x, 0 <= x < 2^62 ->
  wz (x + Z.land ((0 - Z.b2z (65520 <? x)) mod 18446744073709551616) 18446744073709486095) = wz (adler_csub x).
Proof.
  intros x Hx. apply Z_to_bv_eqm. unfold adler_csub.
  destruct (65520 <? x) eqn:E; cbn [Z.b2z].
  - change ((0 - 1) mod 18446744073709551616) with 18446744073709551615.
    change (Z.land 18446744073709551615 18446744073709486095) with 18446744073709486095.
    replace (x + 18446744073709486095) with ((x - 65521) + 1 * 2^64) by lia. apply Z.mod_add. lia.
  - change ((0 - 0) mod 18446744073709551616) with 0. cbn [Z.land]. rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma csub_mask16 : forall x, 0 <= x < 2^40 ->
  (x ≪ 16 + Z.land ((0 - Z.b2z (65520 <? x)) mod 18446744073709551616) 18446744069415567360) mod 18446744073709551616
  = adler_csub x * 2 ^ 16.
Proof.
  intros x Hx. unfold adler_csub. rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.ltb_spec 65520 x); cbn [Z.b2z].
  - change ((0 - 1) mod 18446744073709551616) with 18446744073709551615.
    change (Z.land 18446744073709551615 18446744069415567360) with 18446744069415567360.
    replace (x * 2 ^ 16 + 18446744069415567360) with ((x - 65521) * 2^16 + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - change ((0 - 0) mod 18446744073709551616) with 0. cbn [Z.land]. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma srliw16 : forall adler, 0 <= adler < 2^64 -> bv_swrap 32 (bv_wrap 32 adler ≫ 16) = adler mod 2 ^ 32 / 2 ^ 16.
Proof.
  intros adler HA. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= adler mod 2^32 / 2^16 < 2^16).
  { split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound adler (2^32)); lia. }
  unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition adler32_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

(* [comment removed for export] *)
Lemma adler32_z_len1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B c : Z),
  0 <= adler < 2^64 -> 0 < B < 2^63 -> 0 <= c < 256 ->
  bytes_at psegs m B [Z_to_bv 8 c] -> mem_inv psegs m ->
  evt psegs (adler32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_len1 adler c) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32_Z) fc None m (seg_rom psegs)).
Proof.
  intros until c. intros HA HB HC BY MI. unfold Z_ADLER32_Z.
  pose proof (u8ro_read psegs m B [Z_to_bv 8 c] 0 (Z_to_bv 8 c) (wa (B + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
  replace (B + 0) with B in RD by lia.
  assert (EC : bv_unsigned (Z_to_bv 8 c) = c) by (apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
  assert (RA : 0 <= adler mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  pose proof (srliw16 adler HA) as ES.
  set (sum2 := adler mod 2 ^ 32 / 2 ^ 16) in *.
  assert (RS2 : 0 <= sum2 < 65536).
  { subst sum2. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound adler (2^32)); lia. }
  (* [comment removed for export] *)
  zstep. rewrite ES.
  (* [comment removed for export] *)
  do 4 zstep. if_false.
  (* [comment removed for export] *)
  do 6 zstep. rewrite EC.
  (* [comment removed for export] *)
  do 5 zstep. rewrite (csub_mask (adler mod 65536 + c)) by lia.
  set (a := adler_csub (adler mod 65536 + c)).
  assert (RAa : 0 <= a < 65792) by (subst a; unfold adler_csub; destruct (Z.ltb_spec 65520 (adler mod 65536 + c)); lia).
  (* [comment removed for export] *)
  do 9 zstep. rewrite (csub_mask16 (a + sum2)) by lia.
  apply evt_done. unfold adler32_post. do 14 eexists. exists m.
  split; [unfold adler32_len1; fold sum2; reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adler32_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler len : Z),
  0 <= adler < 2^64 -> 0 <= len < 2^32 -> len <> 1 -> mem_inv psegs m ->
  evt psegs (adler32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz 0) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom psegs)).
Proof.
  intros until len. intros HA HL HN MI. unfold Z_ADLER32.
  do 3 zstep. do 5 zstep.
  if_cases K; zify_cond K.
  2:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
  zstep. if_true. zstep.
  apply evt_done. unfold adler32_post. do 14 eexists. exists m.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.
