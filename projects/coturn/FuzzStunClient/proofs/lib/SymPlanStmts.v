(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lw_bytes : forall old, (0 <= old < 2 ^ 32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 old)) = bv_unsigned (Z_to_bv 64 old).
Proof.
  intros old Hold. rewrite bytes_le_N. rewrite (u_Z2bv old) by lia.
  apply Z.mod_small. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite (u_Z2bv z) by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma sextw_lw : forall v : word, v_addiw (v_lw v) 0 = v_lw v.
Proof.
  intros v. unfold v_addiw, v_lw. f_equal. rewrite Z.add_0_r, Z_to_bv_unsigned.
  rewrite <- (bv_swrap_wrap 32 (bv_wrap 64 _)).
  rewrite (bv_wrap_bv_wrap 32 64) by (compute; discriminate || lia).
  rewrite bv_swrap_wrap. apply bv_swrap_small. apply bv_swrap_in_range. discriminate.
Qed.

(* [comment removed for export] *)
Lemma w2b4_low32 : forall x y : word,
  (bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32)%Z -> word_to_le_bytes 4 x = word_to_le_bytes 4 y.
Proof.
  intros x y H. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned x)) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned y)) by (cbn; lia).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite H. reflexivity.
Qed.

Lemma u_v_lw_mod32 : forall v : word, (bv_unsigned (v_lw v) mod 2 ^ 32 = bv_unsigned v mod 2 ^ 32)%Z.
Proof.
  intros v. unfold v_lw. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_swrap 32 (bv_unsigned v)) mod 2 ^ 32)%Z with (bv_wrap 32 (bv_wrap 64 (bv_swrap 32 (bv_unsigned v)))).
  rewrite (bv_wrap_bv_wrap 32 64) by (compute; discriminate || lia).
  unfold bv_swrap. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned v + bv_half_modulus 32 - bv_half_modulus 32)%Z with (bv_unsigned v) by lia.
  reflexivity.
Qed.

Lemma lor_mod32 : forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.lor a b mod 2 ^ 32 = Z.lor (a mod 2 ^ 32) (b mod 2 ^ 32) mod 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.lor_spec. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma land_mod32 : forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.land a b mod 2 ^ 32 = Z.land (a mod 2 ^ 32) (b mod 2 ^ 32) mod 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.land_spec. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_lt32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (0 <= Z.lor a b < 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec. rewrite (Z_testbit_high 32 a k) by lia. rewrite (Z_testbit_high 32 b k) by lia. reflexivity.
Qed.

Lemma land_lt32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b)%Z -> (0 <= Z.land a b < 2 ^ 32)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec. rewrite (Z_testbit_high 32 a k) by lia. reflexivity.
Qed.

Lemma u_v_or : forall x y : word, bv_unsigned (v_or x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. pose proof (Z_lor_range _ _ (u64_range x) (u64_range y)). unfold v_or. apply u_Z2bv; lia.
Qed.

Lemma u_v_and : forall x y : word, bv_unsigned (v_and x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. pose proof (u64_range y). pose proof (Z_land_range _ (bv_unsigned y) (u64_range x) ltac:(lia)). unfold v_and. apply u_Z2bv; lia.
Qed.

Lemma w2b4_or_sext : forall (v bits : word),
  word_to_le_bytes 4 (v_or (v_lw v) bits) = word_to_le_bytes 4 (v_or v bits).
Proof.
  intros v bits. apply w2b4_low32. rewrite !u_v_or.
  pose proof (u64_range (v_lw v)). pose proof (u64_range v). pose proof (u64_range bits).
  rewrite (lor_mod32 (bv_unsigned (v_lw v))) by lia. rewrite (lor_mod32 (bv_unsigned v)) by lia.
  rewrite u_v_lw_mod32. reflexivity.
Qed.

Lemma w2b4_and_sext : forall (v mask : word),
  word_to_le_bytes 4 (v_and (v_lw v) mask) = word_to_le_bytes 4 (v_and v mask).
Proof.
  intros v mask. apply w2b4_low32. rewrite !u_v_and.
  pose proof (u64_range (v_lw v)). pose proof (u64_range v). pose proof (u64_range mask).
  rewrite (land_mod32 (bv_unsigned (v_lw v))) by lia. rewrite (land_mod32 (bv_unsigned v)) by lia.
  rewrite u_v_lw_mod32. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell32_or : forall old (bits : word), (0 <= old < 2 ^ 32)%Z ->
  word_to_le_bytes 4 (v_or (Z_to_bv 64 old) bits)
  = word_to_le_bytes 4 (Z_to_bv 64 (Z.lor old (bv_unsigned bits mod 2 ^ 32))).
Proof.
  intros old bits Hold. pose proof (u64_range bits).
  pose proof (Z.mod_pos_bound (bv_unsigned bits) (2 ^ 32) ltac:(lia)).
  pose proof (lor_lt32 old (bv_unsigned bits mod 2 ^ 32) Hold ltac:(lia)) as R.
  apply w2b4_low32. rewrite u_v_or. rewrite !u_Z2bv by lia.
  rewrite (lor_mod32 old) by lia. rewrite (Z.mod_small old) by lia.
  rewrite (Z.mod_small (Z.lor old _)) by lia. reflexivity.
Qed.

Lemma cell32_and : forall old (mask : word), (0 <= old < 2 ^ 32)%Z ->
  word_to_le_bytes 4 (v_and (Z_to_bv 64 old) mask)
  = word_to_le_bytes 4 (Z_to_bv 64 (Z.land old (bv_unsigned mask))).
Proof.
  intros old mask Hold. pose proof (u64_range mask).
  pose proof (land_lt32 old (bv_unsigned mask) Hold ltac:(lia)) as R.
  apply w2b4_low32. rewrite u_v_and. rewrite !u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmts.
Variable RSEGS : list Segment.

(* [comment removed for export] *)
Definition cas_or_stmt (pc pck : Z) : Prop :=
  forall regs mem rom (a bits : word) (old : Z),
  getr regs 14 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 11 = bits ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (Z_to_bv 64 pc) mem rom)
                 (mkst regs' (Z_to_bv 64 pck) (wbytes mem a (word_to_le_bytes 4 (v_or (Z_to_bv 64 old) bits))) rom)
    /\ getr regs' 10 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 12 = v_or (v_lw (Z_to_bv 64 old)) bits
    /\ getr regs' 13 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 13 -> r <> 15 -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Definition cas_and_stmt (pc pck : Z) : Prop :=
  forall regs mem rom (a mask : word) (old : Z),
  getr regs 12 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 13 = mask ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (Z_to_bv 64 pc) mem rom)
                 (mkst regs' (Z_to_bv 64 pck) (wbytes mem a (word_to_le_bytes 4 (v_and (Z_to_bv 64 old) mask))) rom)
    /\ getr regs' 14 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = v_and (v_lw (Z_to_bv 64 old)) mask
    /\ getr regs' 16 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Definition cas_lock_stmt (pc pck : Z) : Prop :=
  forall regs mem rom (a newv : word) (old : Z),
  getr regs 13 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 11 = v_lw (Z_to_bv 64 old) ->
  getr regs 12 = newv ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (Z_to_bv 64 pc) mem rom)
                 (mkst regs' (Z_to_bv 64 pck) (wbytes mem a (word_to_le_bytes 4 newv)) rom)
    /\ getr regs' 14 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 14 -> r <> 15 -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn RSEGS mem0 src (length bs) = Some bs;
  Hdst : store_ok RSEGS mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition memcpy_stmt (pc : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) rom,
  mcH mem0 dst src n bs ->
  forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (Z_to_bv 64 pc) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.

End Stmts.
