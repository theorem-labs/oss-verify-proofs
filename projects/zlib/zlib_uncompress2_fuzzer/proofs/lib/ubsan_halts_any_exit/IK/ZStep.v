(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require Export TSet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.


Definition w64 (z : Z) : word := Z_to_bv 64 z.
Abbreviation two64 := 18446744073709551616%Z.

Lemma two64_eq : two64 = 2 ^ 64. Proof. reflexivity. Qed.

Lemma w64_unsigned : forall z, bv_unsigned (w64 z) = z mod two64.
Proof. intros z. unfold w64. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma w64_signed : forall z, bv_signed (w64 z) = bv_swrap 64 z.
Proof. intros z. unfold w64. rewrite Z_to_bv_signed. reflexivity. Qed.

Lemma w64_eq : forall a b, a mod two64 = b mod two64 -> w64 a = w64 b.
Proof. intros a b H. apply bv_eq. rewrite !w64_unsigned. exact H. Qed.


Lemma w64_mod : forall a, w64 (a mod two64) = w64 a.
Proof. intros. apply w64_eq. rewrite two64_eq. apply Z.mod_mod. lia. Qed.

Lemma w64_of_word : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma mod_small_u64 : forall z, 0 <= z < two64 -> z mod two64 = z.
Proof. intros. apply Z.mod_small. lia. Qed.


Fixpoint zden (t : tree Z) : tree word :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => TNode (zden l) (match v with Some e => Some (w64 e) | None => None end) (zden r)
  end.

Definition zget (R : tree Z) (k : positive) : Z :=
  match tget k R with Some e => e | None => 0 end.

Definition zset (R : tree Z) (k : positive) (e : Z) : tree Z := tset k e R.

Definition zrd (R : tree Z) (r : reg) : Z :=
  if is_x0 r then 0 else zget R (bv_key r).

Lemma tget_zden : forall k R,
  tget k (zden R) = match tget k R with Some e => Some (w64 e) | None => None end.
Proof.
  induction k as [k IH|k IH|]; intros [|l v r]; cbn; auto.
Qed.

Lemma tset_zden : forall k e R, tset k (w64 e) (zden R) = zden (tset k e R).
Proof.
  induction k as [k IH|k IH|]; intros e [|l v r]; cbn; rewrite ?IH; auto;
  try reflexivity.
  - f_equal. specialize (IH e TEmpty). cbn in IH. exact IH.
  - f_equal. specialize (IH e TEmpty). cbn in IH. exact IH.
Qed.

Lemma reg_get_zden : forall R (r : reg), reg_get (zden R) r = w64 (zget R (bv_key r)).
Proof.
  intros R r. unfold reg_get, bvmap_get, zget. rewrite tget_zden.
  destruct (tget (bv_key r) R); reflexivity.
Qed.

Lemma getr_zden : forall R (r : reg), getr (zden R) r = w64 (zrd R r).
Proof.
  intros R r. unfold getr, zrd. rewrite bv_eqb0_is_x0.
  destruct (is_x0 r); [reflexivity|]. apply reg_get_zden.
Qed.

Lemma regupd_zden : forall R (r : reg) e,
  regupd (zden R) r (w64 e) = zden (zset R (bv_key r) e).
Proof. intros. unfold regupd, bvmap_set, zset. apply tset_zden. Qed.

Lemma wb_zden : forall R (rd : reg) e,
  (if bv_eqb rd 0 then zden R else regupd (zden R) rd (w64 e))
  = zden (if is_x0 rd then R else zset R (bv_key rd) e).
Proof.
  intros R rd e. rewrite bv_eqb0_is_x0. destruct (is_x0 rd); [reflexivity|].
  apply regupd_zden.
Qed.


Definition zst (segs : list Segment) (pc : Z) (R : tree Z) (M : word -> option byte)
  : machine_state := mkst (zden R) (w64 pc) M (seg_rom segs).

Definition zcfg segs pc R M (MD : Model) : config := mkCfg (zst segs pc R M) MD.


Definition zalu (op : aluop) (a b : Z) : Z :=
  match op with
  | ALU_ADD => a + b
  | ALU_SUB => a - b
  | ALU_SLL => Z.shiftl a (b mod 64)
  | ALU_SLT => Z.b2z (bv_swrap 64 a <? bv_swrap 64 b)
  | ALU_SLTU => Z.b2z (a mod two64 <? b mod two64)
  | ALU_XOR => Z.lxor a b
  | ALU_SRL => Z.shiftr (a mod two64) (b mod 64)
  | ALU_SRA => Z.shiftr (bv_swrap 64 a) (b mod 64)
  | ALU_OR => Z.lor a b
  | ALU_AND => Z.land a b
  end.

Abbreviation two32 := 4294967296%Z.

Definition zalu32u (op : aluop) (a b : Z) : Z :=
  match op with
  | ALU_ADD => a + b
  | ALU_SUB => a - b
  | ALU_SLL => Z.shiftl a (b mod 32)
  | ALU_SLT => Z.b2z (bv_swrap 32 a <? bv_swrap 32 b)
  | ALU_SLTU => Z.b2z (a mod two32 <? b mod two32)
  | ALU_XOR => Z.lxor a b
  | ALU_SRL => Z.shiftr (a mod two32) (b mod 32)
  | ALU_SRA => Z.shiftr (bv_swrap 32 a) (b mod 32)
  | ALU_OR => Z.lor a b
  | ALU_AND => Z.land a b
  end.
Definition zalu32 (op : aluop) (a b : Z) : Z := bv_swrap 32 (zalu32u op a b).

Definition zcond (c : branch_cond) (a b : Z) : bool :=
  match c with
  | BC_EQ => a mod two64 =? b mod two64
  | BC_NE => negb (a mod two64 =? b mod two64)
  | BC_LT => bv_swrap 64 a <? bv_swrap 64 b
  | BC_GE => negb (bv_swrap 64 a <? bv_swrap 64 b)
  | BC_LTU => a mod two64 <? b mod two64
  | BC_GEU => negb (a mod two64 <? b mod two64)
  end.

Definition zmul (op : mulop) (a b : Z) : Z :=
  match op with
  | M_MUL => a * b
  | M_MULHU => (a mod two64) * (b mod two64) / two64
  | _ => bv_unsigned (mul_div op (w64 a) (w64 b))
  end.

Definition zmul32 (op : mulop) (a b : Z) : Z :=
  match op with
  | M_MUL => bv_swrap 32 (a * b)
  | _ => bv_signed (mul_div op (low32 (w64 a)) (low32 (w64 b)))
  end.


Lemma land_ones_low : forall k n, 0 <= n -> 0 <= k < 2 ^ n -> Z.land k (Z.ones n) = k.
Proof. intros. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Ltac bits64 :=
  apply Z.bits_inj'; intros n Hn;
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec;
  repeat match goal with |- context [Z.testbit ?x n] => destruct (Z.testbit x n) end;
  reflexivity.

Lemma land_mod_two64 : forall a b,
  Z.land (a mod two64) (b mod two64) = (Z.land a b) mod two64.
Proof. intros a b. rewrite two64_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma lor_mod_two64 : forall a b,
  Z.lor (a mod two64) (b mod two64) = (Z.lor a b) mod two64.
Proof. intros a b. rewrite two64_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma lxor_mod_two64 : forall a b,
  Z.lxor (a mod two64) (b mod two64) = (Z.lxor a b) mod two64.
Proof. intros a b. rewrite two64_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma land_small_r : forall b k, 0 <= k < two64 -> Z.land (b mod two64) k = Z.land b k.
Proof.
  intros b k Hk. rewrite two64_eq, <- Z.land_ones by lia.
  rewrite <- (land_ones_low k 64) at 1 by lia.
  rewrite <- (land_ones_low k 64) at 2 by lia.
  bits64.
Qed.

Lemma shiftl_mod_two64 : forall a k, 0 <= k ->
  (Z.shiftl (a mod two64) k) mod two64 = (Z.shiftl a k) mod two64.
Proof.
  intros a k Hk. rewrite !Z.shiftl_mul_pow2 by lia. rewrite two64_eq.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.


Lemma b2z_if : forall b : bool, (if b then Z_to_bv 64 1 else Z_to_bv 64 0) = w64 (Z.b2z b).
Proof. intros [|]; reflexivity. Qed.

Lemma mask63 : forall b, Z.land (b mod two64) (bv_unsigned (Z_to_bv 64 63)) = b mod 64.
Proof.
  intros b. rewrite Z_to_bv_unsigned. change (bv_wrap 64 63) with (Z.ones 6).
  rewrite land_small_r by (cbv; split; [discriminate|reflexivity]).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma shiftr_u64_bound : forall a k, 0 <= k -> 0 <= (a mod two64) ≫ k < two64.
Proof.
  intros a k Hk.
  pose proof (Z.mod_pos_bound a two64 ltac:(rewrite two64_eq; lia)) as Ha.
  split; [apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  pose proof (Z.pow_pos_nonneg 2 k). nia.
Qed.

Lemma zalu_add : forall a b, alu64 ALU_ADD (w64 a) (w64 b) = w64 (a + b).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !w64_unsigned.
  change (bv_wrap 64 ?x) with (x mod two64). rewrite two64_eq, <- Zplus_mod. reflexivity.
Qed.

Lemma zalu_sub : forall a b, alu64 ALU_SUB (w64 a) (w64 b) = w64 (a - b).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_sub_unsigned, !w64_unsigned.
  change (bv_wrap 64 ?x) with (x mod two64). rewrite two64_eq, <- Zminus_mod. reflexivity.
Qed.

Lemma zalu_sll : forall a b, alu64 ALU_SLL (w64 a) (w64 b) = w64 (Z.shiftl a (b mod 64)).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftl_unsigned, bv_and_unsigned, !w64_unsigned.
  change (bv_wrap 64 ?x) with (x mod two64). rewrite mask63.
  apply shiftl_mod_two64. apply Z.mod_pos_bound. lia.
Qed.

Lemma zalu_srl : forall a b, alu64 ALU_SRL (w64 a) (w64 b) = w64 (Z.shiftr (a mod two64) (b mod 64)).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, bv_and_unsigned, !w64_unsigned.
  rewrite mask63. symmetry. apply Z.mod_small. apply shiftr_u64_bound.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma zalu_sra : forall a b, alu64 ALU_SRA (w64 a) (w64 b) = w64 (Z.shiftr (bv_swrap 64 a) (b mod 64)).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_ashiftr_unsigned, bv_and_unsigned, !w64_unsigned, w64_signed.
  change (bv_wrap 64 ?x) with (x mod two64). rewrite mask63. reflexivity.
Qed.

Lemma zalu_and : forall a b, alu64 ALU_AND (w64 a) (w64 b) = w64 (Z.land a b).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !w64_unsigned. apply land_mod_two64.
Qed.

Lemma zalu_or : forall a b, alu64 ALU_OR (w64 a) (w64 b) = w64 (Z.lor a b).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_or_unsigned, !w64_unsigned. apply lor_mod_two64.
Qed.

Lemma zalu_xor : forall a b, alu64 ALU_XOR (w64 a) (w64 b) = w64 (Z.lxor a b).
Proof.
  intros. apply bv_eq. cbn [alu64 alu]. rewrite bv_xor_unsigned, !w64_unsigned. apply lxor_mod_two64.
Qed.

Lemma zalu_slt : forall a b, alu64 ALU_SLT (w64 a) (w64 b) = w64 (Z.b2z (bv_swrap 64 a <? bv_swrap 64 b)).
Proof.
  intros. cbn [alu64 alu]. unfold bv_lts. rewrite !w64_signed. apply b2z_if.
Qed.

Lemma zalu_sltu : forall a b, alu64 ALU_SLTU (w64 a) (w64 b) = w64 (Z.b2z (a mod two64 <? b mod two64)).
Proof.
  intros. cbn [alu64 alu]. unfold bv_ltu. rewrite !w64_unsigned. apply b2z_if.
Qed.

Lemma zalu_ok : forall op a b, alu64 op (w64 a) (w64 b) = w64 (zalu op a b).
Proof.
  intros op a b. destruct op; cbn [zalu].
  - apply zalu_add. - apply zalu_sub. - apply zalu_sll. - apply zalu_slt. - apply zalu_sltu.
  - apply zalu_xor. - apply zalu_srl. - apply zalu_sra. - apply zalu_or. - apply zalu_and.
Qed.

Lemma zcond_ok : forall c a b, branch_taken c (w64 a) (w64 b) = zcond c a b.
Proof.
  intros c a b. unfold branch_taken, bv_eqb, bv_lts, bv_ltu.
  destruct c; cbn [zcond]; rewrite ?w64_unsigned, ?w64_signed; reflexivity.
Qed.

Lemma two32_eq : two32 = 2 ^ 32. Proof. reflexivity. Qed.

Lemma low32_w64 : forall a, bv_unsigned (low32 (w64 a)) = a mod two32.
Proof.
  intros a. unfold low32. rewrite bv_extract_0_unsigned, w64_unsigned.
  change (bv_wrap 32 ?x) with (x mod two32). rewrite two64_eq, two32_eq.
  symmetry. apply Znumtheory.Zmod_div_mod; try lia.
  exists (2^32). reflexivity.
Qed.

Lemma low32_w64_signed : forall a, bv_signed (low32 (w64 a)) = bv_swrap 32 a.
Proof.
  intros a. unfold bv_signed. rewrite low32_w64.
  change (a mod two32) with (bv_wrap 32 a). apply bv_swrap_wrap.
Qed.

Lemma sext64_32 : forall v : bv 32, sext 64 v = w64 (bv_swrap 32 (bv_unsigned v)).
Proof. intros. reflexivity. Qed.

Lemma swrap32_mod32 : forall x, bv_swrap 32 (x mod two32) = bv_swrap 32 x.
Proof. intros. change (x mod two32) with (bv_wrap 32 x). apply bv_swrap_wrap. Qed.

Lemma mask31 : forall b, Z.land (b mod two32) (bv_unsigned (Z_to_bv 32 31)) = b mod 32.
Proof.
  intros b. rewrite Z_to_bv_unsigned. change (bv_wrap 32 31) with (Z.ones 5).
  rewrite two32_eq, <- Z.land_ones by lia.
  rewrite <- Z.land_assoc.
  assert (H5 : Z.land (Z.ones 32) (Z.ones 5) = Z.ones 5) by reflexivity.
  rewrite H5. apply Z.land_ones. lia.
Qed.

Local Ltac a32 lem :=
  intros; cbn [alu32 alu]; rewrite lem, ?bv_and_unsigned, !low32_w64, ?mask31;
  change (bv_wrap 32 ?x) with (x mod two32).

Lemma alu32u_add : forall a b, bv_unsigned (alu32 ALU_ADD (low32 (w64 a)) (low32 (w64 b))) = (a + b) mod two32.
Proof. a32 (@bv_add_unsigned 32). rewrite two32_eq, <- Zplus_mod. reflexivity. Qed.

Lemma alu32u_sub : forall a b, bv_unsigned (alu32 ALU_SUB (low32 (w64 a)) (low32 (w64 b))) = (a - b) mod two32.
Proof. a32 (@bv_sub_unsigned 32). rewrite two32_eq, <- Zminus_mod. reflexivity. Qed.

Lemma alu32u_sll : forall a b, bv_unsigned (alu32 ALU_SLL (low32 (w64 a)) (low32 (w64 b))) = (Z.shiftl a (b mod 32)) mod two32.
Proof.
  a32 (@bv_shiftl_unsigned 32).
  rewrite !Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  rewrite two32_eq. apply Z.mul_mod_idemp_l. lia.
Qed.

Lemma alu32u_srl : forall a b, bv_unsigned (alu32 ALU_SRL (low32 (w64 a)) (low32 (w64 b))) = Z.shiftr (a mod two32) (b mod 32).
Proof. a32 (@bv_shiftr_unsigned 32). reflexivity. Qed.

Lemma alu32u_sra : forall a b, bv_unsigned (alu32 ALU_SRA (low32 (w64 a)) (low32 (w64 b))) = (Z.shiftr (bv_swrap 32 a) (b mod 32)) mod two32.
Proof. a32 (@bv_ashiftr_unsigned 32). rewrite low32_w64_signed. reflexivity. Qed.

Lemma alu32u_and : forall a b, bv_unsigned (alu32 ALU_AND (low32 (w64 a)) (low32 (w64 b))) = (Z.land a b) mod two32.
Proof. a32 (@bv_and_unsigned 32). rewrite two32_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma alu32u_or : forall a b, bv_unsigned (alu32 ALU_OR (low32 (w64 a)) (low32 (w64 b))) = (Z.lor a b) mod two32.
Proof. a32 (@bv_or_unsigned 32). rewrite two32_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma alu32u_xor : forall a b, bv_unsigned (alu32 ALU_XOR (low32 (w64 a)) (low32 (w64 b))) = (Z.lxor a b) mod two32.
Proof. a32 (@bv_xor_unsigned 32). rewrite two32_eq, <- !Z.land_ones by lia. bits64. Qed.

Lemma b2z_if32 : forall b : bool, bv_unsigned (if b then Z_to_bv 32 1 else Z_to_bv 32 0) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.

Lemma alu32u_slt : forall a b, bv_unsigned (alu32 ALU_SLT (low32 (w64 a)) (low32 (w64 b))) = Z.b2z (bv_swrap 32 a <? bv_swrap 32 b).
Proof. intros. cbn [alu32 alu]. unfold bv_lts. rewrite !low32_w64_signed. apply b2z_if32. Qed.

Lemma alu32u_sltu : forall a b, bv_unsigned (alu32 ALU_SLTU (low32 (w64 a)) (low32 (w64 b))) = Z.b2z (a mod two32 <? b mod two32).
Proof. intros. cbn [alu32 alu]. unfold bv_ltu. rewrite !low32_w64. apply b2z_if32. Qed.

Lemma zalu32_ok : forall op a b,
  sext 64 (alu32 op (low32 (w64 a)) (low32 (w64 b))) = w64 (zalu32 op a b).
Proof.
  intros op a b. rewrite sext64_32. unfold zalu32. f_equal.
  destruct op; cbn [zalu32u].
  - rewrite alu32u_add. apply swrap32_mod32.
  - rewrite alu32u_sub. apply swrap32_mod32.
  - rewrite alu32u_sll. apply swrap32_mod32.
  - rewrite alu32u_slt. reflexivity.
  - rewrite alu32u_sltu. reflexivity.
  - rewrite alu32u_xor. apply swrap32_mod32.
  - rewrite alu32u_srl. reflexivity.
  - rewrite alu32u_sra. apply swrap32_mod32.
  - rewrite alu32u_or. apply swrap32_mod32.
  - rewrite alu32u_and. apply swrap32_mod32.
Qed.

Lemma zmul_ok : forall op a b, mul_div op (w64 a) (w64 b) = w64 (zmul op a b).
Proof.
  intros op a b. destruct op; cbn [zmul]; try (symmetry; apply w64_of_word).
  - apply bv_eq. unfold mul_div. rewrite bv_mul_unsigned, !w64_unsigned.
    change (bv_wrap 64 ?x) with (x mod two64). rewrite two64_eq, <- Zmult_mod. reflexivity.
  - apply bv_eq. unfold mul_div, bv_mulhuu. rewrite Z_to_bv_unsigned, !w64_unsigned.
    change (bv_wrap 64 ?x) with (x mod two64). rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zmul32_ok : forall op a b,
  sext 64 (mul_div op (low32 (w64 a)) (low32 (w64 b))) = w64 (zmul32 op a b).
Proof.
  intros op a b. rewrite sext64_32. destruct op; cbn [zmul32]; try reflexivity.
  f_equal. unfold mul_div. rewrite bv_mul_unsigned, !low32_w64.
  change (bv_wrap 32 ?x) with (x mod two32). rewrite two32_eq, <- Zmult_mod.
  apply swrap32_mod32.
Qed.


Section Rules.
Variable segs : list Segment.

Lemma w64_pc4 : forall pc, v_addi (w64 pc) 4 = w64 (pc + 4).
Proof. intros. unfold v_addi. apply w64_eq. rewrite w64_unsigned, two64_eq. apply Zplus_mod_idemp_l. Qed.


Lemma zx_raw : forall pc R M MD T R' pc' M',
  m_halted MD = None ->
  RiscvSemantics.step segs (zst segs pc R M) = MachineOk (mkst (zden R') (w64 pc') M' (seg_rom segs)) ->
  realizes segs (zcfg segs pc' R' M' MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros pc R M MD T R' pc' M' Hh Hs Hk.
  eapply rz_step; [exact Hh | reflexivity | exact Hs | exact Hk].
Qed.


Lemma zx_opimm : forall pc R M MD T w op rd rs (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu op (zrd R rs) (bv_signed imm))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_opimm_gen by eassumption.
  rewrite getr_zden. change (sext 64 imm) with (w64 (bv_signed imm)).
  rewrite zalu_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zext64_6 : forall (sh : bv 6), zext 64 sh = w64 (bv_unsigned sh).
Proof. reflexivity. Qed.
Lemma zext32_5 : forall (sh : bv 5), zext 32 sh = low32 (w64 (bv_unsigned sh)).
Proof.
  intros sh. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned', low32_w64. reflexivity.
Qed.
Lemma sext32_12 : forall (imm : bv 12), sext 32 imm = low32 (w64 (bv_signed imm)).
Proof.
  intros imm. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, low32_w64. reflexivity.
Qed.

Lemma zx_shiftimm : forall pc R M MD T w op rd rs (sh : bv 6),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu op (zrd R rs) (bv_unsigned sh))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs sh F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_shiftimm_gen by eassumption.
  rewrite getr_zden, zext64_6, zalu_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_op : forall pc R M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu op (zrd R rs1) (zrd R rs2))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs1 rs2 F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_op_gen by eassumption.
  rewrite !getr_zden, zalu_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_opimm32 : forall pc R M MD T w rd rs (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu32 ALU_ADD (zrd R rs) (bv_signed imm))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_opimm32_gen by eassumption.
  rewrite getr_zden, sext32_12, zalu32_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_shiftimm32 : forall pc R M MD T w op rd rs (sh : bv 5),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu32 op (zrd R rs) (bv_unsigned sh))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs sh F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_shiftimm32_gen by eassumption.
  rewrite getr_zden, zext32_5, zalu32_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_op32 : forall pc R M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zalu32 op (zrd R rs1) (zrd R rs2))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs1 rs2 F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_op32_gen by eassumption.
  rewrite !getr_zden, zalu32_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_mul : forall pc R M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zmul op (zrd R rs1) (zrd R rs2))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs1 rs2 F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_mul_gen by eassumption.
  rewrite !getr_zden, zmul_ok, wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_mul32 : forall pc R M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (zmul32 op (zrd R rs1) (zrd R rs2))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w op rd rs1 rs2 F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_mul32_gen by eassumption.
  rewrite !getr_zden, zmul32_ok, wb_zden, w64_pc4. reflexivity.
Qed.


Lemma zx_lui : forall pc R M MD T w rd (imm : bv 20),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (Z.shiftl (bv_signed imm) 12)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_lui by eassumption.
  change (v_lui ?z) with (w64 z).
  rewrite wb_zden, w64_pc4. reflexivity.
Qed.

Lemma zx_auipc : forall pc R M MD T w rd (imm : bv 20),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (pc + Z.shiftl (bv_signed imm) 12)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_auipc by eassumption.
  replace (v_auipc (w64 pc) (Z.shiftl (bv_signed imm) 12)) with (w64 (pc + Z.shiftl (bv_signed imm) 12)).
  2:{ unfold v_auipc. apply w64_eq. rewrite w64_unsigned, two64_eq, Zplus_mod_idemp_r. f_equal. lia. }
  rewrite wb_zden, w64_pc4. reflexivity.
Qed.


Lemma w64_addi : forall pc i, v_addi (w64 pc) i = w64 (pc + i).
Proof. intros. unfold v_addi. apply w64_eq. rewrite w64_unsigned, two64_eq. apply Zplus_mod_idemp_l. Qed.

Lemma zx_jal : forall pc R M MD T w rd (imm : bv 21),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (pc + bv_signed imm)
    (if is_x0 rd then R else zset R (bv_key rd) (pc + 4)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_jal_link by eassumption.
  unfold btgt. rewrite !w64_addi, wb_zden. reflexivity.
Qed.

Definition zjalr_tgt (a imm : Z) : Z := Z.land (a + imm) (-2).

Lemma zx_jalr : forall pc R M MD T w rd rs1 (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  m_halted MD = None ->
  realizes segs (zcfg segs (zjalr_tgt (zrd R rs1) (bv_signed imm))
    (if is_x0 rd then R else zset R (bv_key rd) (pc + 4)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs1 imm F E D Hh Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite step_jalr_gen by eassumption.
  rewrite getr_zden, w64_addi, wb_zden.
  unfold jalr_tgt, jalr_tgtZ, zjalr_tgt. rewrite w64_unsigned.
  replace (Z_to_bv 64 (Z.land (zrd R rs1 mod two64 + bv_signed imm) (-2)))
    with (w64 (Z.land (zrd R rs1 + bv_signed imm) (-2))); [reflexivity|].
  apply w64_eq. rewrite two64_eq.
  rewrite <- !Z.land_ones by lia.
  rewrite <- !Z.land_assoc, !(Z.land_comm (-2) (Z.ones 64)), !Z.land_assoc.
  rewrite !Z.land_ones by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma zx_jalr_to : forall pc R M MD T w rd rs1 (imm : bv 12) tgt,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  m_halted MD = None ->
  zrd R rs1 + bv_signed imm = tgt -> Z.land tgt (-2) = tgt ->
  realizes segs (zcfg segs tgt
    (if is_x0 rd then R else zset R (bv_key rd) (pc + 4)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs1 imm tgt F E D Hh Ht He Hk.
  eapply zx_jalr; try eassumption.
  unfold zjalr_tgt. rewrite Ht, He. exact Hk.
Qed.

Lemma zx_branch : forall pc R M MD T w c rs1 rs2 (imm : bv 13) (b : bool),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  m_halted MD = None ->
  zcond c (zrd R rs1) (zrd R rs2) = b ->
  realizes segs (zcfg segs (if b then pc + bv_signed imm else pc + 4) R M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w c rs1 rs2 imm b F E D Hh Hc Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. destruct b.
  - erewrite step_branch_tk_gen; try eassumption.
    + unfold btgt. rewrite w64_addi. reflexivity.
    + rewrite !getr_zden, zcond_ok. exact Hc.
  - erewrite step_branch_ft_gen; try eassumption.
    + rewrite w64_addi. reflexivity.
    + rewrite !getr_zden, zcond_ok. exact Hc.
Qed.

Lemma zx_ecall : forall pc R M MD T w,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = true ->
  m_halted MD = None ->
  realizes segs (mkCfg
     {| ms_regs := zden R; ms_fregs := bvmap_empty; ms_pc_val := w64 pc;
        ms_svc_pending := Some (w64 (zrd R 17)); ms_resv := None;
        ms_fcsr := Z_to_bv 32 0; ms_mem := M; ms_rom := seg_rom segs |} MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros pc R M MD T w F E Hh Hk.
  eapply rz_step; [exact Hh| reflexivity | | exact Hk].
  unfold zst. erewrite step_ecall by eassumption. rewrite getr_zden. reflexivity.
Qed.

End Rules.



Fixpoint zupd (Rb : tree Z) (l : list (positive * Z)) : tree Z :=
  match l with
  | [] => Rb
  | (k, e) :: l' => zset (zupd Rb l') k e
  end.

Fixpoint alookup (l : list (positive * Z)) (k : positive) : option Z :=
  match l with
  | [] => None
  | (k', e) :: l' => if Pos.eqb k' k then Some e else alookup l' k
  end.

Definition zget_l (Rb : tree Z) (l : list (positive * Z)) (k : positive) : Z :=
  match alookup l k with Some e => e | None => zget Rb k end.

Definition zrd_l (Rb : tree Z) (l : list (positive * Z)) (r : reg) : Z :=
  if is_x0 r then 0 else zget_l Rb l (bv_key r).

Lemma tset_same : forall {A} k (v1 v2 : A) t, tset k v2 (tset k v1 t) = tset k v2 t.
Proof.
  induction k as [k IH|k IH|]; intros v1 v2 [|l v r]; cbn; rewrite ?IH; try reflexivity.
Qed.

Lemma tset_comm : forall {A} k1 k2 (v1 v2 : A) t, k1 <> k2 ->
  tset k1 v1 (tset k2 v2 t) = tset k2 v2 (tset k1 v1 t).
Proof.
  induction k1 as [k1 IH|k1 IH|]; intros [k2|k2|] v1 v2 [|l v r] Hne; cbn; try reflexivity;
    try (rewrite IH by congruence; reflexivity); try congruence.
  all: try (f_equal; apply IH; congruence).
Qed.

Lemma zget_zset_same : forall R k e, zget (zset R k e) k = e.
Proof. intros. unfold zget, zset. rewrite tget_tset_same. reflexivity. Qed.

Lemma zget_zset_other : forall R k k' e, k <> k' -> zget (zset R k e) k' = zget R k'.
Proof. intros. unfold zget, zset. rewrite tget_tset_other by assumption. reflexivity. Qed.

Lemma zget_zupd : forall Rb l k, zget (zupd Rb l) k = zget_l Rb l k.
Proof.
  intros Rb l k. unfold zget_l. induction l as [|[k' e] l IH]; cbn [zupd alookup]; [reflexivity|].
  destruct (Pos.eqb k' k) eqn:E.
  - apply Pos.eqb_eq in E. subst. apply zget_zset_same.
  - apply Pos.eqb_neq in E. rewrite zget_zset_other by assumption. exact IH.
Qed.

Lemma zrd_zupd : forall Rb l r, zrd (zupd Rb l) r = zrd_l Rb l r.
Proof. intros. unfold zrd, zrd_l. rewrite zget_zupd. reflexivity. Qed.


Fixpoint remove_key (k : positive) (l : list (positive * Z)) : list (positive * Z) :=
  match l with
  | [] => []
  | (k', e) :: l' => if Pos.eqb k' k then remove_key k l' else (k', e) :: remove_key k l'
  end.

Lemma zupd_cons_remove : forall Rb k e l,
  zupd Rb ((k, e) :: l) = zupd Rb ((k, e) :: remove_key k l).
Proof.
  intros Rb k e l. revert e. induction l as [|[k' e'] l IH]; intros e; [reflexivity|].
  cbn [remove_key]. destruct (Pos.eqb k' k) eqn:E.
  - apply Pos.eqb_eq in E. subst. cbn [zupd]. unfold zset at 1 2. rewrite tset_same.
    specialize (IH e). cbn [zupd] in IH. exact IH.
  - apply Pos.eqb_neq in E. cbn [zupd]. unfold zset. rewrite tset_comm by congruence.
    specialize (IH e). cbn [zupd] in IH. unfold zset in IH. rewrite IH.
    rewrite tset_comm by congruence. reflexivity.
Qed.

Fixpoint dedup (l : list (positive * Z)) : list (positive * Z) :=
  match l with
  | [] => []
  | (k, e) :: l' => (k, e) :: remove_key k (dedup l')
  end.

Lemma zupd_cons_congr : forall Rb k e l1 l2, zupd Rb l1 = zupd Rb l2 ->
  zupd Rb ((k, e) :: l1) = zupd Rb ((k, e) :: l2).
Proof. intros. cbn [zupd]. rewrite H. reflexivity. Qed.

Lemma zupd_dedup : forall Rb l, zupd Rb l = zupd Rb (dedup l).
Proof.
  intros Rb l. induction l as [|[k e] l IH]; [reflexivity|].
  cbn [dedup]. rewrite <- zupd_cons_remove. apply zupd_cons_congr. exact IH.
Qed.

Lemma zcfg_dedup : forall segs pc Rb l M MD,
  zcfg segs pc (zupd Rb l) M MD = zcfg segs pc (zupd Rb (dedup l)) M MD.
Proof. intros. rewrite <- zupd_dedup. reflexivity. Qed.


Section URules.
Variable segs : list Segment.

Definition wb (rd : reg) (e : Z) (l : list (positive * Z)) : list (positive * Z) :=
  if is_x0 rd then l else (bv_key rd, e) :: l.

Lemma wb_zupd : forall Rb l rd e,
  (if is_x0 rd then zupd Rb l else zset (zupd Rb l) (bv_key rd) e) = zupd Rb (wb rd e l).
Proof. intros. unfold wb. destruct (is_x0 rd); reflexivity. Qed.

Local Ltac lift L :=
  intros; rewrite <- wb_zupd, <- ?zrd_zupd in *; eapply L; eassumption.

Lemma zu_opimm : forall pc Rb l M MD T w op rd rs (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu op (zrd_l Rb l rs) (bv_signed imm)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_opimm. Qed.

Lemma zu_shiftimm : forall pc Rb l M MD T w op rd rs (sh : bv 6),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu op (zrd_l Rb l rs) (bv_unsigned sh)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_shiftimm. Qed.

Lemma zu_op : forall pc Rb l M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu op (zrd_l Rb l rs1) (zrd_l Rb l rs2)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_op. Qed.

Lemma zu_opimm32 : forall pc Rb l M MD T w rd rs (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu32 ALU_ADD (zrd_l Rb l rs) (bv_signed imm)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_opimm32. Qed.

Lemma zu_shiftimm32 : forall pc Rb l M MD T w op rd rs (sh : bv 5),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu32 op (zrd_l Rb l rs) (bv_unsigned sh)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_shiftimm32. Qed.

Lemma zu_op32 : forall pc Rb l M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zalu32 op (zrd_l Rb l rs1) (zrd_l Rb l rs2)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_op32. Qed.

Lemma zu_mul : forall pc Rb l M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zmul op (zrd_l Rb l rs1) (zrd_l Rb l rs2)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_mul. Qed.

Lemma zu_mul32 : forall pc Rb l M MD T w op rd rs1 rs2,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (zmul32 op (zrd_l Rb l rs1) (zrd_l Rb l rs2)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_mul32. Qed.

Lemma zu_lui : forall pc Rb l M MD T w rd (imm : bv 20),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (Z.shiftl (bv_signed imm) 12) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_lui. Qed.

Lemma zu_auipc : forall pc Rb l M MD T w rd (imm : bv 20),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (pc + Z.shiftl (bv_signed imm) 12) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_auipc. Qed.

Lemma zu_jal : forall pc Rb l M MD T w rd (imm : bv 21),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (pc + bv_signed imm) (zupd Rb (wb rd (pc + 4) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_jal. Qed.

Lemma zu_jalr : forall pc Rb l M MD T w rd rs1 (imm : bv 12),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) -> m_halted MD = None ->
  realizes segs (zcfg segs (zjalr_tgt (zrd_l Rb l rs1) (bv_signed imm)) (zupd Rb (wb rd (pc + 4) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_jalr. Qed.

Lemma zu_jalr_to : forall pc Rb l M MD T w rd rs1 (imm : bv 12) tgt,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) -> m_halted MD = None ->
  zrd_l Rb l rs1 + bv_signed imm = tgt -> Z.land tgt (-2) = tgt ->
  realizes segs (zcfg segs tgt (zupd Rb (wb rd (pc + 4) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift zx_jalr_to. Qed.

Lemma zu_branch : forall pc Rb l M MD T w c rs1 rs2 (imm : bv 13) (b : bool),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zcond c (zrd_l Rb l rs1) (zrd_l Rb l rs2) = b ->
  realizes segs (zcfg segs (if b then pc + bv_signed imm else pc + 4) (zupd Rb l) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. intros; rewrite <- ?zrd_zupd in *; eapply zx_branch; eassumption. Qed.

Lemma zu_ecall : forall pc Rb l M MD T w,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = true -> m_halted MD = None ->
  realizes segs (mkCfg
     {| ms_regs := zden (zupd Rb l); ms_fregs := bvmap_empty; ms_pc_val := w64 pc;
        ms_svc_pending := Some (w64 (zrd_l Rb l 17)); ms_resv := None;
        ms_fcsr := Z_to_bv 32 0; ms_mem := M; ms_rom := seg_rom segs |} MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. intros; rewrite <- ?zrd_zupd in *; eapply zx_ecall; eassumption. Qed.

End URules.
