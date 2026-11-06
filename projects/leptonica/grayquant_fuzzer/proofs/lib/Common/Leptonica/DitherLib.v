(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec SeqExec CatSim StepTac Hoare StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun RefPrintfLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytea (p : Z) : Z := p - p mod 4 + (3 - p mod 4).

Lemma bytea_bounds : forall L n p, L mod 4 = 0 -> L <= p < L + 4 * n -> L <= bytea p < L + 4 * n.
Proof. intros L n p HL Hp. unfold bytea. apply flip3_bounds; assumption. Qed.

Lemma bytea_near : forall p, p - 3 <= bytea p <= p + 3.
Proof. intros p. unfold bytea. pose proof (Z.mod_pos_bound p 4 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma bytea_spec : forall p, exists q r, p = 4 * q + r /\ 0 <= r < 4 /\ bytea p = 4 * q + 3 - r.
Proof.
  intros p. exists (p / 4), (p mod 4). pose proof (Z.div_mod p 4 ltac:(lia)). pose proof (Z.mod_pos_bound p 4 ltac:(lia)).
  unfold bytea. lia.
Qed.
Lemma al4_ex : forall a, a mod 4 = 0 -> exists c, a = 4 * c.
Proof. intros a H. exists (a / 4). pose proof (Z.div_mod a 4 ltac:(lia)). lia. Qed.

Lemma bytea_inj_ne : forall p q, p <> q -> bytea p <> bytea q.
Proof.
  intros p q Hne. unfold bytea.
  pose proof (Z.div_mod p 4 ltac:(lia)). pose proof (Z.mod_pos_bound p 4 ltac:(lia)).
  pose proof (Z.div_mod q 4 ltac:(lia)). pose proof (Z.mod_pos_bound q 4 ltac:(lia)). lia.
Qed.

Lemma dl_xor3 : forall p, 0 <= p < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 p) (Z_to_bv 64 3) = Z_to_bv 64 (bytea p).
Proof.
  intros p Hp. rewrite alu_xor. unfold v_xor, bytea. rewrite !u_Z2bv by lia. f_equal. apply lxor3_eq. lia.
Qed.

Lemma dl_addi0 : forall a : word, v_addi a 0 = a.
Proof. intros a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma dl_srl5_and : forall j, 0 <= j < 2 ^ 32 ->
  alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 j) (Z_to_bv 64 5)) (Z_to_bv 64 134217727) = Z_to_bv 64 (j / 32).
Proof.
  intros j Hj. rewrite alu_srl, alu_and. unfold v_srl, v_and.
  assert (D : 0 <= j / 32 < 2 ^ 27) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv j) by lia. rewrite (u_Z2bv 5) by lia. change (5 mod 64) with 5. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite (u_Z2bv (j / 32)) by lia. rewrite (u_Z2bv 134217727) by lia. f_equal.
  change 134217727 with (Z.ones 27). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma dl_srl4_and : forall j, 0 <= j < 2 ^ 32 ->
  alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 j) (Z_to_bv 64 4)) (Z_to_bv 64 268435455) = Z_to_bv 64 (j / 16).
Proof.
  intros j Hj. rewrite alu_srl, alu_and. unfold v_srl, v_and.
  assert (D : 0 <= j / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv j) by lia. rewrite (u_Z2bv 4) by lia. change (4 mod 64) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (u_Z2bv (j / 16)) by lia. rewrite (u_Z2bv 268435455) by lia. f_equal.
  change 268435455 with (Z.ones 28). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma dl_mul4 : forall x, 0 <= x < 2 ^ 60 -> mul_div M_MUL (Z_to_bv 64 4) (Z_to_bv 64 x) = Z_to_bv 64 (4 * x).
Proof.
  intros x Hx. rewrite m_mul. unfold v_mul. rewrite !u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dl_bitword : forall line j, 0 <= j < 2 ^ 32 ->
  alu64 ALU_ADD (Z_to_bv 64 line) (mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 j) (Z_to_bv 64 5)) (Z_to_bv 64 134217727)))
  = Z_to_bv 64 (line + 4 * (j / 32)).
Proof.
  intros line j Hj. rewrite dl_srl5_and by exact Hj.
  assert (D : 0 <= j / 32 < 2 ^ 27) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite dl_mul4 by lia. apply alu_add_Z.
Qed.
Lemma dl_dibitword : forall line j, 0 <= j < 2 ^ 32 ->
  alu64 ALU_ADD (Z_to_bv 64 line) (mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 j) (Z_to_bv 64 4)) (Z_to_bv 64 268435455)))
  = Z_to_bv 64 (line + 4 * (j / 16)).
Proof.
  intros line j Hj. rewrite dl_srl4_and by exact Hj.
  assert (D : 0 <= j / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite dl_mul4 by lia. apply alu_add_Z.
Qed.
(* [comment removed for export] *)
Lemma dl_srlw_small : forall j k, 0 <= j < 2 ^ 31 -> 0 <= k < 32 ->
  sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (j / 2 ^ k).
Proof.
  intros j k Hj Hk. rewrite w_srlw. unfold v_srlw. rewrite (u_Z2bv j) by lia. rewrite (u_Z2bv k) by lia.
  rewrite (Z.mod_small k 32) by lia. rewrite (wrap32_small j) by lia. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
  assert (0 <= j / 2 ^ k <= j) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]).
  rewrite swrap32_small by lia. reflexivity.
Qed.
Lemma dl_bitword_w : forall line j, 0 <= j < 2 ^ 31 ->
  alu64 ALU_ADD (Z_to_bv 64 line) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 5)))))
  = Z_to_bv 64 (line + 4 * (j / 32)).
Proof.
  intros line j Hj. rewrite dl_srlw_small by lia. change (2 ^ 5) with 32.
  assert (D : 0 <= j / 32 < 2 ^ 27) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite dl_mul4 by lia. apply alu_add_Z.
Qed.
Lemma dl_dibitword_w : forall line j, 0 <= j < 2 ^ 31 ->
  alu64 ALU_ADD (Z_to_bv 64 line) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 4)))))
  = Z_to_bv 64 (line + 4 * (j / 16)).
Proof.
  intros line j Hj. rewrite dl_srlw_small by lia. change (2 ^ 4) with 16.
  assert (D : 0 <= j / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite dl_mul4 by lia. apply alu_add_Z.
Qed.

(* [comment removed for export] *)
Lemma dl_addw : forall a b, 0 <= a < 2 ^ 63 -> - 2 ^ 31 <= b < 2 ^ 31 -> 0 <= a + b < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. rewrite w_addw. unfold v_addw. f_equal. rewrite (u_Z2bv a) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z_lt_ge_dec b 0) as [Hn|Hp].
  - replace (b mod 2 ^ 64) with (b + 2 ^ 64) by (symmetry; rewrite <- (Z_mod_plus_full b 1 (2 ^ 64)); apply Z.mod_small; lia).
    replace (a + (b + 2 ^ 64) + 2 ^ 31) with (a + b + 2 ^ 31 + 4294967296 * 2 ^ 32) by (change (2 ^ 64) with (4294967296 * 2 ^ 32); lia).
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small b) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma dl_zext32 : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (Z_to_bv 64 x)) (Z_to_bv 64 32) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite m_mul, alu_srl. unfold v_mul, v_srl. rewrite (u_Z2bv 4294967296) by lia. rewrite (u_Z2bv x) by lia.
  rewrite (u_Z2bv (4294967296 * x)) by lia. rewrite (u_Z2bv 32) by lia. change (32 mod 64) with 32.
  rewrite Z.shiftr_div_pow2 by lia. f_equal. change (2 ^ 32) with 4294967296. rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma dl_div_bounds : forall j k, 0 <= j -> 0 < k -> 0 <= j / k /\ k * (j / k) <= j < k * (j / k) + k.
Proof.
  intros j k Hj Hk. pose proof (Z.div_mod j k ltac:(lia)). pose proof (Z.mod_pos_bound j k Hk). split; [apply Z.div_pos; lia | lia].
Qed.

Lemma dl_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. exact alu_add_Z. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rdv (sx : bool) (n : nat) (bs : list byte) : Z := bv_unsigned (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))).

Lemma rdv_range : forall sx n bs, 0 <= rdv sx n bs < 2 ^ 64.
Proof. intros. unfold rdv. pose proof (bv_unsigned_in_range _ (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)))) as H. unfold bv_modulus in H. exact H. Qed.

Lemma rdv_eq : forall sx n bs, Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = Z_to_bv 64 (rdv sx n bs).
Proof. intros. unfold rdv. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma dl_read : forall (m : word -> option byte) (a : word) (z : Z) (n : nat) (sx : bool) (bs : list byte) (e : word),
  a = Z_to_bv 64 z -> rdn segs m (Z_to_bv 64 z) n = Some bs -> e = Z_to_bv 64 (rdv sx n bs) ->
  exists bs', rdn segs m a n = Some bs' /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs')) = e.
Proof. intros m a z n sx bs e -> R ->. exists bs. split; [exact R | apply rdv_eq]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition incell (c : Z * Z) (a : word) : Prop := fst c <= u a < fst c + snd c.
Definition mframe (cells : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  mem_grows m m' /\ forall a : word, (forall c, In c cells -> ~ incell c a) -> m' a = m a.

Lemma mframe_refl : forall cells m, mframe cells m m.
Proof. intros. split; [apply mem_grows_refl | reflexivity]. Qed.

Lemma mframe_wbytes : forall cells m m' (z : Z) (a : word) (bs : list byte) (n : Z),
  mframe cells m m' -> a = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> z + n <= 2 ^ 64 -> Z.of_nat (length bs) = n -> In (z, n) cells ->
  mframe cells m (wbytes m' a bs).
Proof.
  intros cells m m' z a bs n [G F] -> Hz Hn L I. split.
  - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  - intros x Hx. rewrite wbytes_outside.
    + apply F, Hx.
    + rewrite u_Z2bv by lia. lia.
    + rewrite u_Z2bv by lia. specialize (Hx (z, n) I). unfold incell in Hx. cbn [fst snd] in Hx. lia.
Qed.

Lemma mframe_wword : forall cells m m' (z : Z) (a : word) (w : nat) (v : word),
  mframe cells m m' -> a = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> z + Z.of_nat w <= 2 ^ 64 -> In (z, Z.of_nat w) cells ->
  mframe cells m (wbytes m' a (word_to_le_bytes w v)).
Proof.
  intros cells m m' z a w v F Ha Hz Hn I. apply (mframe_wbytes cells m m' z a _ (Z.of_nat w) F Ha Hz Hn); [| exact I].
  rewrite length_N_to_le_bytes. reflexivity.
Qed.

Lemma mframe_incl : forall c1 c2 m m', mframe c1 m m' -> (forall c, In c c1 -> In c c2) -> mframe c2 m m'.
Proof. intros c1 c2 m m' [G F] I. split; [exact G|]. intros a Ha. apply F. intros c Hc. apply Ha, I, Hc. Qed.

Lemma mframe_trans : forall c1 c2 m1 m2 m3, mframe c1 m1 m2 -> mframe c2 m2 m3 -> mframe (c1 ++ c2) m1 m3.
Proof.
  intros c1 c2 m1 m2 m3 [G1 F1] [G2 F2]. split; [eapply mem_grows_trans; eassumption|].
  intros a Ha. rewrite F2, F1; [reflexivity | |]; intros c Hc; apply Ha, in_or_app; [left | right]; exact Hc.
Qed.

Lemma mframe_step : forall C c1 m m1 m2, mframe C m m1 -> mframe c1 m1 m2 -> (forall x, In x c1 -> In x C) -> mframe C m m2.
Proof.
  intros C c1 m m1 m2 [G1 F1] [G2 F2] I. split; [eapply mem_grows_trans; eassumption|].
  intros a Ha. rewrite F2, F1; [reflexivity | exact Ha |]. intros c Hc. apply Ha, I, Hc.
Qed.

(* [comment removed for export] *)
Definition cells_ok (m : word -> option byte) (cells : list (Z * Z)) : Prop :=
  forall c, In c cells -> 0 <= fst c /\ fst c + snd c <= 2 ^ 64 /\ store_ok segs m (Z_to_bv 64 (fst c)) (Z.to_nat (snd c)) = true.

Lemma cells_ok_sok : forall m m' cells z n, cells_ok m cells -> mem_grows m m' -> In (z, n) cells ->
  store_ok segs m' (Z_to_bv 64 z) (Z.to_nat n) = true.
Proof. intros m m' cells z n CK G I. destruct (CK _ I) as (_ & _ & S). eapply store_ok_mono; [exact G | exact S]. Qed.

Lemma cells_ok_read : forall m m' cells z n, wr_readable segs -> cells_ok m cells -> mem_grows m m' -> In (z, n) cells ->
  exists bs, rdn segs m' (Z_to_bv 64 z) (Z.to_nat n) = Some bs.
Proof.
  intros m m' cells z n WR CK G I.
  destruct (store_ok_rdn segs m' (Z.to_nat n) (Z_to_bv 64 z) WR (cells_ok_sok m m' cells z n CK G I)) as (bs & Hbs & _).
  exists bs. exact Hbs.
Qed.

(* [comment removed for export] *)
Lemma dl_rdn_hit : forall m (a : word) (z : Z) (w : nat) (v : word),
  a = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> z + Z.of_nat w <= 2 ^ 64 ->
  rdn segs (wbytes m a (word_to_le_bytes w v)) (Z_to_bv 64 z) w = Some (word_to_le_bytes w v).
Proof.
  intros m a z w v -> Hz Hw. pose proof (rdn_wbytes_hit segs (word_to_le_bytes w v) m (Z_to_bv 64 z)) as H.
  rewrite length_N_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. exact Hw.
Qed.
Lemma dl_rdn_skip : forall m (a : word) (za z : Z) (w n : nat) (v : word) r,
  a = Z_to_bv 64 za -> 0 <= za < 2 ^ 64 -> za + Z.of_nat w <= 2 ^ 64 -> 0 <= z < 2 ^ 64 -> z + Z.of_nat n <= 2 ^ 64 ->
  (z + Z.of_nat n <= za \/ za + Z.of_nat w <= z) ->
  rdn segs m (Z_to_bv 64 z) n = r -> rdn segs (wbytes m a (word_to_le_bytes w v)) (Z_to_bv 64 z) n = r.
Proof.
  intros m a za z w n v r -> Hza Hw Hz Hn D <-. apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Definition inreg (lo n : Z) (a : word) : Prop := lo <= u a < lo + n.

(* [comment removed for export] *)
Definition rinv (regs : list (Z * Z)) (M0 Mi : word -> option byte) : Prop :=
  mem_grows M0 Mi /\ forall a : word, (forall r, In r regs -> ~ inreg (fst r) (snd r) a) -> Mi a = M0 a.

Lemma rinv_refl : forall regs M0, rinv regs M0 M0.
Proof. intros. split; [apply mem_grows_refl | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma rinv_mframe : forall regs cells M0 Mi Mi',
  rinv regs M0 Mi -> mframe cells Mi Mi' ->
  (forall c, In c cells -> exists r, In r regs /\ fst r <= fst c /\ fst c + snd c <= fst r + snd r) ->
  rinv regs M0 Mi'.
Proof.
  intros regs cells M0 Mi Mi' [G F] [G' F'] INC. split; [eapply mem_grows_trans; eassumption|].
  intros a Ha. rewrite F'; [apply F, Ha|].
  intros c Hc IC. destruct (INC c Hc) as (r & Hr & H1 & H2). apply (Ha r Hr). unfold inreg, incell in *. lia.
Qed.

(* [comment removed for export] *)
Lemma reg_sok : forall M0 Mi (lo : Z) (N : nat) (z : Z) (n : nat),
  mem_grows M0 Mi -> store_ok segs M0 (Z_to_bv 64 lo) N = true -> 0 <= lo -> lo + Z.of_nat N <= 2 ^ 64 ->
  lo <= z -> z + Z.of_nat n <= lo + Z.of_nat N -> store_ok segs Mi (Z_to_bv 64 z) n = true.
Proof.
  intros M0 Mi lo N z n G S Hlo HN Hz Hn. eapply store_ok_mono; [exact G|].
  destruct n as [|n']; [reflexivity|].
  eapply (store_ok_sub segs M0 (Z_to_bv 64 lo) _ N); [ | exact S | | ]; rewrite ?u_Z2bv by lia; lia.
Qed.

Lemma reg_read : forall M0 Mi (lo : Z) (N : nat) (z : Z) (n : nat), wr_readable segs ->
  mem_grows M0 Mi -> store_ok segs M0 (Z_to_bv 64 lo) N = true -> 0 <= lo -> lo + Z.of_nat N <= 2 ^ 64 ->
  lo <= z -> z + Z.of_nat n <= lo + Z.of_nat N -> exists bs, rdn segs Mi (Z_to_bv 64 z) n = Some bs.
Proof.
  intros M0 Mi lo N z n WR G S Hlo HN Hz Hn.
  destruct (store_ok_rdn segs Mi n (Z_to_bv 64 z) WR (reg_sok M0 Mi lo N z n G S Hlo HN Hz Hn)) as (bs & Hbs & _).
  exists bs. exact Hbs.
Qed.

(* [comment removed for export] *)
Lemma mframe_rdn : forall cells m m' (z : Z) (n : nat), mframe cells m m' -> 0 <= z -> z + Z.of_nat n <= 2 ^ 64 ->
  (forall c, In c cells -> z + Z.of_nat n <= fst c \/ fst c + snd c <= z) ->
  rdn segs m' (Z_to_bv 64 z) n = rdn segs m (Z_to_bv 64 z) n.
Proof.
  intros cells m m' z n [_ F] Hz Hn D. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply F. intros c Hc IC. unfold incell in IC. specialize (D c Hc). lia.
Qed.
Lemma rinv_rdn : forall regs M0 Mi (z : Z) (n : nat), rinv regs M0 Mi -> 0 <= z -> z + Z.of_nat n <= 2 ^ 64 ->
  (forall r, In r regs -> z + Z.of_nat n <= fst r \/ fst r + snd r <= z) ->
  rdn segs Mi (Z_to_bv 64 z) n = rdn segs M0 (Z_to_bv 64 z) n.
Proof.
  intros regs M0 Mi z n [_ F] Hz Hn D. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply F. intros r Hr IR. unfold inreg in IR. specialize (D r Hr). lia.
Qed.
Lemma rinv_trans : forall regs M0 M1 M2, rinv regs M0 M1 -> rinv regs M1 M2 -> rinv regs M0 M2.
Proof.
  intros regs M0 M1 M2 [G1 F1] [G2 F2]. split; [eapply mem_grows_trans; eassumption|]. intros a Ha. rewrite F2, F1 by exact Ha. reflexivity.
Qed.
Lemma rinv_incl : forall r1 r2 M0 Mi, rinv r1 M0 Mi -> (forall r, In r r1 -> In r r2) -> rinv r2 M0 Mi.
Proof. intros r1 r2 M0 Mi [G F] I. split; [exact G|]. intros a Ha. apply F. intros r Hr. apply Ha, I, Hr. Qed.

(* [comment removed for export] *)
Lemma rdv_word8 : forall x : word, Z_to_bv 64 (rdv false 8 (word_to_le_bytes 8 x)) = x.
Proof.
  intros x. unfold rdv. rewrite Z_to_bv_bv_unsigned. unfold extz.
  rewrite (bytes_le_to_Z_8 x). apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Definition regions_ok (M0 : word -> option byte) (regs : list (Z * Z)) : Prop :=
  forall r, In r regs -> 0 <= fst r /\ fst r + snd r <= 2 ^ 64 /\ 0 <= snd r /\ store_ok segs M0 (Z_to_bv 64 (fst r)) (Z.to_nat (snd r)) = true.
Definition cells_in (regs cells : list (Z * Z)) : Prop :=
  forall c, In c cells -> 0 <= snd c /\ exists r, In r regs /\ fst r <= fst c /\ fst c + snd c <= fst r + snd r.

Lemma cells_in_incl : forall r1 r2 cells, cells_in r1 cells -> (forall r, In r r1 -> In r r2) -> cells_in r2 cells.
Proof. intros r1 r2 cells CI I c Hc. destruct (CI c Hc) as (Hn & r & Hr & H). split; [exact Hn|]. exists r. split; [apply I, Hr | exact H]. Qed.

Lemma cells_ok_of : forall M0 Mi regs cells, regions_ok M0 regs -> mem_grows M0 Mi -> cells_in regs cells -> cells_ok Mi cells.
Proof.
  intros M0 Mi regs cells RO G CI c Hc. destruct (CI c Hc) as (Hn & r & Hr & H1 & H2). destruct (RO r Hr) as (R0 & R1 & R2 & S).
  split; [lia|]. split; [lia|].
  apply (reg_sok M0 Mi (fst r) (Z.to_nat (snd r)) (fst c) (Z.to_nat (snd c)) G S R0); rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma rinv_cells : forall regs cells M0 Mi Mi', rinv regs M0 Mi -> mframe cells Mi Mi' -> cells_in regs cells -> rinv regs M0 Mi'.
Proof.
  intros regs cells M0 Mi Mi' RI F CI. apply (rinv_mframe regs cells M0 Mi Mi' RI F).
  intros c Hc. destruct (CI c Hc) as (_ & r & Hr & H1 & H2). exists r. split; [exact Hr | split; assumption].
Qed.

End WithSegs.
