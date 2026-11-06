(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition debruijn : list Z :=
  [0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8; 31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].

(* [comment removed for export] *)
Definition db_pos (j : Z) : Z := Z.shiftr ((125613361 * 2^j) mod 2^32) 27.

Lemma db_table_ok : forall j, 0 <= j < 32 -> 0 <= db_pos j <= 31 /\ znth (db_pos j) debruijn = j.
Proof.
  intros j Hj.
  assert (C : forallb (fun k => (0 <=? db_pos k) && (db_pos k <=? 31) && (znth (db_pos k) debruijn =? k)) (zseq 0 32) = true)
    by (vm_compute; reflexivity).
  apply forallb_zseq_iff with (x := j) in C; [|lia].
  apply andb_prop in C as (C & C3). apply andb_prop in C as (C1 & C2). apply Z.leb_le in C1, C2. apply Z.eqb_eq in C3. lia.
Qed.

(* [comment removed for export] *)
Definition db_mach (x : word) : Z :=
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 (mul_div M_MUL (Z_to_bv 64 125613361)
    (alu64 ALU_AND (ext_val true 0 4 x) (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (ext_val true 0 4 x)))))))
    (low32 (Z_to_bv 64 27)))).

Lemma ext4_mod32 : forall avail, 0 <= avail < 2^32 -> bv_unsigned (ext_val true 0 4 (wa avail)) mod 2^32 = avail.
Proof.
  intros avail Ha. destruct (Z_lt_le_dec avail (2^31)) as [L|L].
  - rewrite u_ext_sx0_small by (rewrite u_wa_small by lia; cbn; lia). rewrite u_wa_small by lia. apply Z.mod_small; lia.
  - rewrite u_ext_sx0_high by (first [rewrite u_wa_small by lia; cbn; lia | lia]). rewrite u_wa_small by lia.
    change (2 ^ (8 * Z.of_nat 4)) with (2^32). symmetry. apply (Z.mod_unique_pos _ _ (2^32 - 1)); lia.
Qed.

Lemma land_mod32 : forall a b, 0 <= a -> 0 <= b -> Z.land a b mod 2^32 = Z.land (a mod 2^32) (b mod 2^32).
Proof.
  intros a b Ha Hb. change (2^32) with (2^Z.of_nat 32). rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit (Z.ones (Z.of_nat 32)) i); reflexivity.
Qed.

Lemma lowbit_pow : forall avail, 0 < avail < 2^32 -> lowbit avail = 2^(ctz32 avail) /\ 0 <= ctz32 avail < 32.
Proof.
  intros avail Ha. destruct (lowbit_spec avail ltac:(lia)) as (k & Hk & Hl & Hb & _).
  unfold ctz32. rewrite Hl. unfold bit. rewrite Z.log2_pow2 by lia. split; [reflexivity|]. split; [exact Hk|].
  destruct (Z_lt_le_dec k 32) as [|Hge]; [assumption|]. exfalso.
  rewrite (Z.bits_above_log2 avail k) in Hb; [discriminate | lia |].
  apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^32)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Definition lowb_mach (x : word) : Z :=
  Z.land (bv_unsigned (ext_val true 0 4 x)) (bv_unsigned (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (ext_val true 0 4 x))))).

Lemma lowb_mach_mod32 : forall avail, 0 <= avail < 2^32 -> lowb_mach (wa avail) mod 2^32 = lowbit avail.
Proof.
  intros avail Ha. unfold lowb_mach. rewrite w_subw. unfold v_subw. rewrite u_lit64.
  set (x := ext_val true 0 4 (wa avail)).
  pose proof (ext4_mod32 avail ltac:(lia)) as HX. fold x in HX.
  pose proof (u64_range x) as Rx.
  change two64 with (2^64). change (bv_unsigned (Z_to_bv 64 0)) with 0.
  set (Xv := bv_unsigned x) in *.
  set (Yv := bv_swrap 32 (0 - Xv) mod 2^64).
  assert (RY : 0 <= Yv < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (EY : Yv mod 2^32 = (- avail) mod 2^32).
  { unfold Yv. rewrite mod64_32, swrap32_mod. rewrite Zminus_mod, HX. change (0 mod 2^32) with 0.
    rewrite !Z.sub_0_l. reflexivity. }
  rewrite land_mod32 by lia. rewrite HX, EY. unfold lowbit.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  change (2^32) with (2^Z.of_nat 32). rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
  destruct (Z_lt_le_dec i 32) as [Li|Li].
  - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
  - destruct (Z.eq_dec avail 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 avail i); [reflexivity | lia |].
    apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^32)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_le_l' : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha Hb. rewrite <- (Z2N.id a Ha), <- (Z2N.id b Hb). rewrite <- N2Z.inj_land. split; [apply N2Z.is_nonneg|].
  apply N2Z.inj_le. apply N.land_le_l.
Qed.

Lemma lowb_mach_range : forall x, 0 <= lowb_mach x < 2^64.
Proof.
  intros x. unfold lowb_mach. pose proof (u64_range (ext_val true 0 4 x)) as R1.
  pose proof (u64_range (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (ext_val true 0 4 x))))) as R2.
  pose proof (land_le_l' _ _ (proj1 R1) (proj1 R2)). lia.
Qed.

Lemma edenot_subw' : forall E a b, edenot E (EAluw ALU_SUB a b) = wa (bv_swrap 32 (zeval E a mod 2^64 - zeval E b mod 2^64)).
Proof. intros E a b. cbn [edenot]. rewrite w_subw. unfold v_subw. rewrite !zeval_sound, !u_wa. reflexivity. Qed.

Lemma swrap_small32 : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma db_mach_ok : forall avail, 0 < avail < 2^32 -> db_mach (wa avail) = db_pos (ctz32 avail).
Proof.
  intros avail Ha. unfold db_mach.
  rewrite w_srlw, w_subw. unfold v_srlw, v_subw.
  set (x := ext_val true 0 4 (wa avail)).
  pose proof (ext4_mod32 avail ltac:(lia)) as HX. fold x in HX.
  pose proof (u64_range x) as Rx.
  rewrite u_mul64, u_and64. rewrite !u_lit64.
  change two64 with (2^64). change (bv_unsigned (Z_to_bv 64 0)) with 0. change (bv_unsigned (Z_to_bv 64 125613361)) with 125613361.
  change (bv_unsigned (Z_to_bv 64 27) mod 32) with 27.
  set (Xv := bv_unsigned x) in *.
  change (125613361 mod 2^64) with 125613361. change (0 mod 2^64) with 0. change ((27 mod 2^64) mod 32) with 27.
  set (Yv := bv_swrap 32 (0 - Xv) mod 2^64).
  assert (RY : 0 <= Yv < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (EY : Yv mod 2^32 = (- avail) mod 2^32).
  { unfold Yv. rewrite mod64_32, swrap32_mod. rewrite Zminus_mod, HX. change (0 mod 2^32) with 0.
    rewrite !Z.sub_0_l. reflexivity. }
  assert (EL : Z.land Xv Yv mod 2^32 = lowbit avail).
  { rewrite land_mod32 by lia. rewrite HX, EY. unfold lowbit.
    apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
    change (2^32) with (2^Z.of_nat 32). rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
    destruct (Z_lt_le_dec i 32) as [Li|Li].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
    - rewrite (Z.bits_above_log2 avail i); [reflexivity | lia |].
      apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^32)); [lia|]. apply Z.pow_le_mono_r; lia. }
  destruct (lowbit_pow avail Ha) as (LP & Rj). rewrite LP in EL.
  set (j := ctz32 avail) in *.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  rewrite mod64_32. rewrite <- Zmult_mod_idemp_r, EL.
  unfold db_pos. fold j.
  assert (R : 0 <= Z.shiftr ((125613361 * 2 ^ j) mod 2 ^ 32) 27 < 32).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (125613361 * 2 ^ j) (2^32) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite swrap_small32 by lia. apply Z.mod_small. lia.
Qed.

