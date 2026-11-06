(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Export AsanHeapSortDef.

From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import LiaFastAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid.

Import ListNotations.
Local Instance hs_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Lemma HS_CODE_length : length HS_CODE = HS_N. Proof. reflexivity. Qed.
Lemma HS_WORDS_length : length HS_WORDS = HS_N. Proof. reflexivity. Qed.

Lemma hs_decode_all : map decode_any HS_WORDS = map (fun i => Some (i, 4)) HS_CODE.
Proof. apply (@bool_decide_eq_true_1 _ _). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma hs_ecall_all : map is_ecall HS_WORDS = repeat false HS_N.
Proof. vm_compute. reflexivity. Qed.

Lemma hs_decode : forall k, (k < HS_N)%nat ->
  decode_any (nth k HS_WORDS (Z_to_bv 32 0)) = Some (nth k HS_CODE Ecall, 4).
Proof.
  intros k Hk.
  rewrite <- (map_nth decode_any HS_WORDS (Z_to_bv 32 0) k).
  rewrite (nth_indep (map decode_any HS_WORDS) (decode_any (Z_to_bv 32 0)) None) by (rewrite length_map; exact Hk).
  rewrite hs_decode_all.
  rewrite (nth_indep _ None (Some (Ecall, 4))) by (rewrite length_map; exact Hk).
  rewrite (map_nth (fun i => Some (i, 4)) HS_CODE Ecall k). reflexivity.
Qed.

Lemma hs_no_ecall : forall k, (k < HS_N)%nat -> is_ecall (nth k HS_WORDS (Z_to_bv 32 0)) = false.
Proof.
  intros k Hk.
  rewrite <- (map_nth is_ecall HS_WORDS (Z_to_bv 32 0) k).
  rewrite (nth_indep (map is_ecall HS_WORDS) (is_ecall (Z_to_bv 32 0)) true) by (rewrite length_map; exact Hk).
  rewrite hs_ecall_all. apply nth_repeat_lt. exact Hk.
Qed.

Lemma hs_two64_eq : hs_two64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma hs_m32_eq : hs_m32 = 2 ^ 32. Proof. reflexivity. Qed.

Lemma hs_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite AX2S.u_lit64a. apply Z.mod_small. lia. Qed.

Lemma bv64_mod_eq : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !AX2S.u_lit64a. exact H. Qed.

Lemma w64_mod : forall z, - 2 ^ 64 <= z < 2 ^ 65 -> w64 z = z mod 2 ^ 64.
Proof.
  intros z Hz. unfold w64. rewrite hs_two64_eq.
  destruct (Z.ltb_spec z 0) as [H0|H0].
  - apply (Z.mod_unique z (2 ^ 64) (-1)); lia.
  - destruct (Z.leb_spec (2 ^ 64) z) as [H1|H1].
    + apply (Z.mod_unique z (2 ^ 64) 1); lia.
    + symmetry. apply Z.mod_small. lia.
Qed.

Lemma w64_range : forall z, - 2 ^ 64 <= z < 2 ^ 65 -> 0 <= w64 z < 2 ^ 64.
Proof. intros z Hz. rewrite w64_mod by exact Hz. apply Z.mod_pos_bound. lia. Qed.

Lemma w64_bv : forall z, - 2 ^ 64 <= z < 2 ^ 65 -> Z_to_bv 64 (w64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply bv64_mod_eq. rewrite w64_mod by exact Hz. apply Z.mod_mod. lia. Qed.

Lemma imm12_range : forall imm : bv 12, - 2048 <= bv_signed imm < 2048.
Proof. intros imm. pose proof (bv_signed_in_range 12 imm ltac:(lia)) as H. unfold bv_half_modulus, bv_modulus in H. cbn in H. lia. Qed.
Lemma imm13_range : forall imm : bv 13, - 4096 <= bv_signed imm < 4096.
Proof. intros imm. pose proof (bv_signed_in_range 13 imm ltac:(lia)) as H. unfold bv_half_modulus, bv_modulus in H. cbn in H. lia. Qed.
Lemma imm21_range : forall imm : bv 21, - 2 ^ 20 <= bv_signed imm < 2 ^ 20.
Proof. intros imm. pose proof (bv_signed_in_range 21 imm ltac:(lia)) as H. unfold bv_half_modulus, bv_modulus in H. cbn in H. lia. Qed.
Lemma sh6_range : forall sh : bv 6, 0 <= bv_unsigned sh < 64.
Proof. intros sh. pose proof (bv_unsigned_in_range 6 sh) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma v_addi_w : forall x imm, 0 <= x < 2 ^ 64 -> - 2 ^ 20 <= imm < 2 ^ 20 ->
  v_addi (Z_to_bv 64 x) imm = Z_to_bv 64 (w64 (x + imm)).
Proof. intros x imm Hx Hi. unfold v_addi. rewrite hs_u64 by lia. rewrite w64_bv by lia. reflexivity. Qed.

Lemma v_add_w : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (w64 (x + y)).
Proof. intros x y Hx Hy. unfold v_add. rewrite !hs_u64 by lia. rewrite w64_bv by lia. reflexivity. Qed.

Lemma land_ones64 : forall z, Z.land z (hs_two64 - 1) = z mod 2 ^ 64.
Proof. intros z. change (hs_two64 - 1) with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma v_slli_w : forall x sh, 0 <= x < 2 ^ 64 -> 0 <= sh ->
  v_slli (Z_to_bv 64 x) sh = Z_to_bv 64 (Z.land (Z.shiftl x sh) (hs_two64 - 1)).
Proof. intros x sh Hx Hs. unfold v_slli. rewrite hs_u64 by lia. apply bv64_mod_eq. rewrite land_ones64. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma slli_range : forall x sh, 0 <= Z.land (Z.shiftl x sh) (hs_two64 - 1) < 2 ^ 64.
Proof. intros x sh. rewrite land_ones64. apply Z.mod_pos_bound. lia. Qed.

Lemma v_srli_w : forall x sh, 0 <= x < 2 ^ 64 -> v_srli (Z_to_bv 64 x) sh = Z_to_bv 64 (Z.shiftr x sh).
Proof. intros x sh Hx. unfold v_srli. rewrite hs_u64 by lia. reflexivity. Qed.

Lemma srli_range : forall x sh, 0 <= x < 2 ^ 64 -> 0 <= sh -> 0 <= Z.shiftr x sh < 2 ^ 64.
Proof.
  intros x sh Hx Hs. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ x); [|lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (1 <= 2 ^ sh) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := sh) in Hs; [exact Hs | lia]). nia.
Qed.

Lemma v_lw_w : forall v, 0 <= v < 2 ^ 32 -> v_lw (Z_to_bv 64 v) = Z_to_bv 64 (sx32 v).
Proof.
  intros v Hv. unfold v_lw. rewrite hs_u64 by lia. apply bv64_mod_eq.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  unfold sx32. rewrite hs_two64_eq, hs_m32_eq.
  destruct (Z.leb_spec 2147483648 v) as [H|H].
  - rewrite <- (Z.mod_unique (v + 2 ^ 31) (2 ^ 32) 1 (v + 2 ^ 31 - 2 ^ 32)) by lia.
    replace (v + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (v - 2 ^ 32) by lia.
    replace (v + (2 ^ 64 - 2 ^ 32)) with ((v - 2 ^ 32) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
  - rewrite (Z.mod_small (v + 2 ^ 31)) by lia. f_equal. lia.
Qed.

Lemma sx32_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= sx32 v < 2 ^ 64.
Proof. intros v Hv. unfold sx32. rewrite hs_two64_eq, hs_m32_eq. destruct (Z.leb_spec 2147483648 v); lia. Qed.

Lemma c_ltu_w : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold c_ltu, bv_ltu. rewrite !hs_u64 by lia. reflexivity. Qed.

Lemma c_eq_w : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold c_eq, bv_eqb. rewrite !hs_u64 by lia. reflexivity. Qed.

Lemma land_m2_bounds : forall z, z - 1 <= Z.land z (-2) <= z.
Proof.
  intros z. change (-2) with (Z.lnot (Z.ones 1)).
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. pose proof (Z.div_mod z 2 ltac:(lia)) as H. pose proof (Z.mod_pos_bound z 2 ltac:(lia)). lia.
Qed.

Lemma v_jalr_w : forall x imm, 0 <= x < 2 ^ 64 -> - 2048 <= imm < 2048 ->
  v_jalr (Z_to_bv 64 x) imm = Z_to_bv 64 (w64 (Z.land (x + imm) (-2))).
Proof.
  intros x imm Hx Hi. unfold v_jalr, jalr_tgtZ. rewrite hs_u64 by lia.
  pose proof (land_m2_bounds (x + imm)). rewrite w64_bv by lia. reflexivity.
Qed.

Lemma jalr_range : forall x imm, 0 <= x < 2 ^ 64 -> - 2048 <= imm < 2048 -> 0 <= w64 (Z.land (x + imm) (-2)) < 2 ^ 64.
Proof. intros x imm Hx Hi. pose proof (land_m2_bounds (x + imm)). apply w64_range. lia. Qed.

Definition bytes_ok (zs : list Z) : Prop := Forall (fun b => 0 <= b < 256) zs.

Lemma le_bytes : forall zs, bytes_ok zs -> bytes_le_to_Z (map (Z_to_bv 8) zs) = le zs.
Proof.
  induction zs as [|b zs IH]; intros H; [reflexivity|]. inversion H as [|b' zs' Hb Hzs]; subst.
  cbn [map bytes_le_to_Z le]. rewrite IH by exact Hzs. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma le_range : forall zs, bytes_ok zs -> 0 <= le zs < 2 ^ (8 * Z.of_nat (length zs)).
Proof.
  intros zs H. rewrite <- le_bytes by exact H. pose proof (AX2S.bytes_le_to_Z_bound (map (Z_to_bv 8) zs)) as B.
  rewrite length_map in B. exact B.
Qed.

Lemma tole_bytes : forall n z, map (Z_to_bv 8) (tole n z) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros z; [reflexivity|]. cbn [tole map Z_to_le_bytes]. rewrite IH. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_mod. lia.
Qed.

Lemma tole_ok : forall n z, bytes_ok (tole n z).
Proof.
  induction n as [|n IH]; intros z; [constructor|]. cbn [tole]. constructor; [|apply IH].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound z (2 ^ 8) ltac:(lia)). cbn in *. lia.
Qed.

Lemma length_tole : forall n z, length (tole n z) = n.
Proof. induction n as [|n IH]; intros z; [reflexivity|]. cbn [tole length]. rewrite IH. reflexivity. Qed.

Lemma word_to_le_bytes_w : forall n y, 0 <= y < 2 ^ 64 -> word_to_le_bytes n (Z_to_bv 64 y) = map (Z_to_bv 8) (tole n y).
Proof. intros n y Hy. unfold word_to_le_bytes. rewrite hs_u64 by exact Hy. symmetry. apply tole_bytes. Qed.

Lemma rk_inj : forall r1 r2 : reg, rk r1 = rk r2 -> r1 = r2.
Proof.
  intros r1 r2 H. unfold rk in H. apply bv_eq.
  pose proof (bv_unsigned_in_range 5 r1). pose proof (bv_unsigned_in_range 5 r2).
  apply Z2Pos.inj in H; lia.
Qed.

Lemma rk_x0 : forall r : reg, rk r = xH -> r = 0%bv.
Proof.
  intros r H. unfold rk in H. apply bv_eq. pose proof (bv_unsigned_in_range 5 r).
  change (bv_unsigned (0 : bv 5)%bv) with 0. destruct (Z.eq_dec (bv_unsigned r) 0) as [E|E]; [exact E|].
  exfalso. assert (Z.to_pos (bv_unsigned r + 1) <> 1%positive) by (intros C; apply (f_equal Zpos) in C; rewrite Z2Pos.id in C by lia; lia).
  congruence.
Qed.

Lemma rk_0 : rk 0%bv = xH. Proof. reflexivity. Qed.

Definition RREG (m : tree Z) (regs : bvmap 5 word) : Prop :=
  forall (r : reg) v, zg m (rk r) = Some v -> getr regs r = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64.

Definition setrd (regs : bvmap 5 word) (rd : reg) (v : word) : bvmap 5 word :=
  if bv_eqb rd 0 then regs else regupd regs rd v.

Lemma bv_eqb_true : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma zg_zset_same : forall m k v, k <> xH -> zg (zset m k v) k = Some v.
Proof. intros m k v Hk. destruct k; [apply tget_tset_same | apply tget_tset_same | exfalso; exact (Hk eq_refl)]. Qed.

Lemma zg_zset_other : forall m k k' v, k' <> k -> zg (zset m k v) k' = zg m k'.
Proof.
  intros m k k' v Hne. unfold zg, zset.
  destruct k' as [p'|p'|]; [ | | reflexivity];
    (destruct k as [q|q|]; [apply tget_tset_other; congruence | apply tget_tset_other; congruence | reflexivity]).
Qed.

Lemma rreg_set : forall m regs (rd : reg) v, RREG m regs -> 0 <= v < 2 ^ 64 ->
  RREG (zset m (rk rd) v) (setrd regs rd (Z_to_bv 64 v)).
Proof.
  intros m regs rd v HR Hv r w Hw. unfold setrd.
  destruct (bv_eqb rd 0) eqn:E0.
  - apply bv_eqb_true in E0. subst rd. rewrite rk_0 in Hw. exact (HR r w Hw).
  - assert (Hrd : rd <> 0%bv) by (intros C; subst rd; discriminate E0).
    assert (Hk : rk rd <> xH) by (intros C; apply Hrd, rk_x0, C).
    destruct (bv_eq_dec 5 r rd) as [->|Hne].
    + rewrite zg_zset_same in Hw by exact Hk. injection Hw as <-. split; [apply getr_same; exact Hrd | exact Hv].
    + assert (Hkr : rk r <> rk rd) by (intros C; apply Hne, rk_inj, C).
      rewrite getr_other by exact Hne. rewrite zg_zset_other in Hw by exact Hkr. exact (HR r w Hw).
Qed.

Lemma rreg_get : forall m regs (r : reg) v, RREG m regs -> zg m (rk r) = Some v -> getr regs r = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64.
Proof. intros m regs r v HR H. exact (HR r v H). Qed.

Lemma rreg_entry : forall regs ret T n,
  getr regs 1%bv = Z_to_bv 64 ret -> getr regs 10%bv = Z_to_bv 64 T -> getr regs 11%bv = Z_to_bv 64 n ->
  0 <= ret < 2 ^ 64 -> 0 <= T < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  RREG (hs_regs0 ret T n) regs.
Proof.
  intros regs ret T n H1 H10 H11 R1 R10 R11 r v Hv. unfold hs_regs0, zg in Hv.
  destruct (rk r) as [k|k|] eqn:Ek.
  -
    destruct (Pos.eq_dec (xI k) 11) as [E|E].
    + assert (r = 10%bv) by (apply rk_inj; rewrite Ek, E; reflexivity). subst r. rewrite E in Hv. cbn in Hv. injection Hv as <-. split; assumption.
    + rewrite tget_tset_other in Hv by congruence. rewrite tget_tset_other in Hv by congruence. rewrite tget_tset_other in Hv by (intros C; discriminate C).
      cbn in Hv. discriminate.
  - destruct (Pos.eq_dec (xO k) 12) as [E|E].
    + assert (r = 11%bv) by (apply rk_inj; rewrite Ek, E; reflexivity). subst r. rewrite E in Hv. cbn in Hv. injection Hv as <-. split; assumption.
    + rewrite tget_tset_other in Hv by congruence.
      destruct (Pos.eq_dec (xO k) 2) as [E2|E2].
      * assert (r = 1%bv) by (apply rk_inj; rewrite Ek, E2; reflexivity). subst r. rewrite E2 in Hv. cbn in Hv. injection Hv as <-. split; assumption.
      * rewrite tget_tset_other in Hv by (intros C; discriminate C). rewrite tget_tset_other in Hv by congruence. cbn in Hv. discriminate.
  - injection Hv as <-. apply rk_x0 in Ek. subst r. split; [reflexivity | lia].
Qed.

Definition tbyte (tbl : list (list Z)) (j : Z) : Z := nth (Z.to_nat (j mod 16)) (nth (Z.to_nat (j / 16)) tbl []) 0.

Definition RECS (n : nat) (tbl : list (list Z)) : Prop :=
  length tbl = n /\ Forall (fun rec => length rec = 16%nat /\ bytes_ok rec) tbl.

Lemma lupd_length : forall {A} (l : list A) r f, length (lupd l r f) = length l.
Proof. intros A l. induction l as [|h t IH]; intros r f; [destruct r; reflexivity|]. destruct r; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma lupd_nth_same : forall {A} (l : list A) r f d, (r < length l)%nat -> nth r (lupd l r f) d = f (nth r l d).
Proof. intros A l. induction l as [|h t IH]; intros r f d Hr; [cbn in Hr; lia|]. destruct r; cbn; [reflexivity | apply IH; cbn in Hr; lia]. Qed.

Lemma lupd_nth_other : forall {A} (l : list A) r r' f d, r' <> r -> nth r' (lupd l r f) d = nth r' l d.
Proof.
  intros A l. induction l as [|h t IH]; intros r r' f d Hne; [destruct r; reflexivity|].
  destruct r, r'; cbn; try reflexivity; [lia | apply IH; lia].
Qed.

Lemma Forall_lupd : forall {A} (P : A -> Prop) l r f, Forall P l -> (forall x, P x -> P (f x)) -> Forall P (lupd l r f).
Proof.
  intros A P l. induction l as [|h t IH]; intros r f HP Hf; [destruct r; constructor|].
  inversion HP as [|h' t' Hh Ht]; subst. destruct r; cbn; constructor; auto.
Qed.

Lemma nth_firstn_lt : forall {A} (l : list A) m k d, (k < m)%nat -> nth k (firstn m l) d = nth k l d.
Proof. intros A l. induction l as [|h t IH]; intros m k d Hk; destruct m; cbn; try reflexivity; try lia. destruct k; [reflexivity|]. apply IH. lia. Qed.

Lemma nth_skipn' : forall {A} (l : list A) o k d, nth k (skipn o l) d = nth (o + k) l d.
Proof. intros A l. induction l as [|h t IH]; intros o k d; destruct o; cbn; try reflexivity; [destruct k; reflexivity | apply IH]. Qed.

Lemma splice_length : forall o bs rec, (o + length bs <= length rec)%nat -> length (splice o bs rec) = length rec.
Proof. intros o bs rec H. unfold splice. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma splice_nth : forall o bs rec i d, (o + length bs <= length rec)%nat -> (i < length rec)%nat ->
  nth i (splice o bs rec) d = if (Nat.leb o i && Nat.ltb i (o + length bs))%bool then nth (i - o) bs d else nth i rec d.
Proof.
  intros o bs rec i d H Hi. unfold splice.
  assert (Lf : length (firstn o rec) = o) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec i o) as [Hlt|Hge].
  - rewrite app_nth1 by lia. rewrite nth_firstn_lt by exact Hlt.
    destruct (Nat.leb_spec o i); [lia | reflexivity].
  - rewrite app_nth2 by lia. rewrite Lf.
    destruct (Nat.ltb_spec (i - o) (length bs)) as [Hb|Hb].
    + rewrite app_nth1 by exact Hb. destruct (Nat.leb_spec o i); [|lia]. destruct (Nat.ltb_spec i (o + length bs)); [reflexivity | lia].
    + rewrite app_nth2 by exact Hb. rewrite nth_skipn'.
      destruct (Nat.leb_spec o i); [|lia]. destruct (Nat.ltb_spec i (o + length bs)); [lia|]. cbn. f_equal. lia.
Qed.

Lemma bytes_ok_nth : forall zs k, bytes_ok zs -> 0 <= nth k zs 0 < 256.
Proof.
  intros zs k H. destruct (Nat.lt_ge_cases k (length zs)) as [Hk|Hk].
  - exact (proj1 (Forall_forall _ _) H _ (nth_In _ _ Hk)).
  - rewrite nth_overflow by exact Hk. lia.
Qed.

Lemma in_firstn' : forall {A} (l : list A) m x, In x (firstn m l) -> In x l.
Proof. intros A l m x H. rewrite <- (firstn_skipn m l). apply in_or_app. left. exact H. Qed.
Lemma in_skipn' : forall {A} (l : list A) m x, In x (skipn m l) -> In x l.
Proof. intros A l m x H. rewrite <- (firstn_skipn m l). apply in_or_app. right. exact H. Qed.

Lemma bytes_ok_firstn : forall zs m, bytes_ok zs -> bytes_ok (firstn m zs).
Proof. intros zs m H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H). exact (in_firstn' _ _ _ Hx). Qed.

Lemma bytes_ok_skipn : forall zs m, bytes_ok zs -> bytes_ok (skipn m zs).
Proof. intros zs m H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H). exact (in_skipn' _ _ _ Hx). Qed.

Lemma bytes_ok_splice : forall o bs rec, bytes_ok bs -> bytes_ok rec -> bytes_ok (splice o bs rec).
Proof. intros o bs rec Hb Hr. unfold splice. apply Forall_app; split; [apply bytes_ok_firstn; exact Hr|]. apply Forall_app; split; [exact Hb | apply bytes_ok_skipn; exact Hr]. Qed.

Lemma recs_nth : forall n tbl r, RECS n tbl -> (r < n)%nat -> length (nth r tbl []) = 16%nat /\ bytes_ok (nth r tbl []).
Proof. intros n tbl r [Hl HF] Hr. apply (proj1 (Forall_forall _ _) HF). apply nth_In. lia. Qed.

Lemma tbyte_ok : forall n tbl j, RECS n tbl -> 0 <= tbyte tbl j < 256.
Proof.
  intros n tbl j HR. unfold tbyte. destruct (Nat.lt_ge_cases (Z.to_nat (j / 16)) (length tbl)) as [H|H].
  - destruct HR as [Hl HF]. pose proof (proj1 (Forall_forall _ _) HF _ (nth_In _ [] H)) as [_ Hb]. apply bytes_ok_nth. exact Hb.
  - rewrite (nth_overflow tbl [] H). destruct (Z.to_nat (j mod 16)); cbn; lia.
Qed.

Lemma divmod16 : forall d k, 0 <= d -> 0 <= k -> d mod 16 + k < 16 -> (d + k) / 16 = d / 16 /\ (d + k) mod 16 = d mod 16 + k.
Proof.
  intros d k Hd Hk H. pose proof (Z.div_mod d 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound d 16 ltac:(lia)).
  split.
  - symmetry. apply (Z.div_unique (d + k) 16 (d / 16) (d mod 16 + k)); lia.
  - symmetry. apply (Z.mod_unique (d + k) 16 (d / 16) (d mod 16 + k)); lia.
Qed.

Lemma zld_sound : forall n T tbl a m bs, RECS n tbl -> zld T tbl a m = Some bs ->
  0 <= a - T /\ a - T + Z.of_nat m <= 16 * Z.of_nat n /\ length bs = m /\ bytes_ok bs
  /\ forall k, (k < m)%nat -> nth k bs 0 = tbyte tbl (a - T + Z.of_nat k).
Proof.
  intros n T tbl a m bs HR H. unfold zld in H.
  set (d := a - T) in *.
  destruct (Z.leb 0 d && Z.ltb (d / 16) (Z.of_nat (length tbl)) && Z.leb (d mod 16 + Z.of_nat m) 16)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  destruct HR as [Hl HF]. rewrite Hl in H2.
  pose proof (Z.div_mod d 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound d 16 ltac:(lia)) as Hmb.
  assert (Hr : (Z.to_nat (d / 16) < n)%nat) by lia.
  destruct (recs_nth n tbl (Z.to_nat (d / 16)) (conj Hl HF) Hr) as [Lr Br].
  split; [exact H1|]. split; [nia|].
  split; [rewrite length_firstn, length_skipn, Lr; lia|].
  split; [apply bytes_ok_firstn, bytes_ok_skipn, Br|].
  intros k Hk. rewrite nth_firstn_lt by exact Hk. rewrite nth_skipn'.
  unfold tbyte. destruct (divmod16 d (Z.of_nat k) H1 ltac:(lia) ltac:(lia)) as [E1 E2]. rewrite E1, E2.
  f_equal. lia.
Qed.

Lemma zstt_sound : forall n T tbl a bs tbl', RECS n tbl -> bytes_ok bs -> zstt T tbl a bs = Some tbl' ->
  0 <= a - T /\ a - T + Z.of_nat (length bs) <= 16 * Z.of_nat n /\ RECS n tbl'
  /\ forall j, 0 <= j -> tbyte tbl' j =
       if (Z.leb (a - T) j && Z.ltb j (a - T + Z.of_nat (length bs)))%bool then nth (Z.to_nat (j - (a - T))) bs 0 else tbyte tbl j.
Proof.
  intros n T tbl a bs tbl' HR Hbs H. unfold zstt in H.
  set (d := a - T) in *.
  destruct (Z.leb 0 d && Z.ltb (d / 16) (Z.of_nat (length tbl)) && Z.leb (d mod 16 + Z.of_nat (length bs)) 16)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  destruct HR as [Hl HF]. rewrite Hl in H2.
  pose proof (Z.div_mod d 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound d 16 ltac:(lia)) as Hmb.
  set (r := Z.to_nat (d / 16)) in *. set (o := Z.to_nat (d mod 16)) in *.
  assert (Hr : (r < n)%nat) by lia.
  destruct (recs_nth n tbl r (conj Hl HF) Hr) as [Lr Br].
  split; [exact H1|]. split; [nia|].
  split.
  - split; [rewrite lupd_length; exact Hl|]. apply Forall_lupd; [exact HF|].
    intros rec [Lrec Brec]. split; [rewrite splice_length; lia|]. apply bytes_ok_splice; assumption.
  - intros j Hj. unfold tbyte.
    pose proof (Z.div_mod j 16 ltac:(lia)) as Hjm. pose proof (Z.mod_pos_bound j 16 ltac:(lia)) as Hjb.
    destruct (Nat.eq_dec (Z.to_nat (j / 16)) r) as [Er|Er].
    + rewrite Er. rewrite lupd_nth_same by lia. rewrite splice_nth by (rewrite ?Lr; lia).
      assert (Ejr : j / 16 = d / 16) by lia.
      destruct (Nat.leb_spec o (Z.to_nat (j mod 16))) as [Ho|Ho];
      destruct (Nat.ltb_spec (Z.to_nat (j mod 16)) (o + length bs)) as [Hb|Hb]; cbn [andb].
      * destruct (Z.leb_spec d j); [|lia]. destruct (Z.ltb_spec j (d + Z.of_nat (length bs))); [|lia]. cbn [andb].
        f_equal. lia.
      * destruct (Z.leb_spec d j); destruct (Z.ltb_spec j (d + Z.of_nat (length bs))); cbn [andb]; try reflexivity; lia.
      * destruct (Z.leb_spec d j); destruct (Z.ltb_spec j (d + Z.of_nat (length bs))); cbn [andb]; try reflexivity; lia.
      * destruct (Z.leb_spec d j); destruct (Z.ltb_spec j (d + Z.of_nat (length bs))); cbn [andb]; try reflexivity; lia.
    + rewrite lupd_nth_other by exact Er.
      destruct (Z.leb_spec d j); destruct (Z.ltb_spec j (d + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
      exfalso. apply Er. unfold r. f_equal.
      destruct (divmod16 d (j - d) H1 ltac:(lia) ltac:(lia)) as [E1 _]. replace (d + (j - d)) with j in E1 by lia. exact E1.
Qed.

Definition dst_ok (i : instr) : Prop :=
  match i with
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | Load _ _ rd _ _ => rd = 0%bv \/ In (AX2.ridx rd) HS_DSTS
  | _ => True
  end.
Definition dst_okb (i : instr) : bool :=
  match i with
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | Load _ _ rd _ _ => bv_eqb rd 0 || existsb (Nat.eqb (AX2.ridx rd)) HS_DSTS
  | _ => true
  end.
Lemma dst_okb_ok : forall i, dst_okb i = true -> dst_ok i.
Proof.
  intros i H. destruct i; cbn [dst_okb dst_ok] in H |- *; try exact I;
    (apply orb_prop in H as [H|H]; [left; apply bv_eqb_true; exact H | right; apply existsb_exists in H as (x & Hx & Hq); apply Nat.eqb_eq in Hq; rewrite Hq; exact Hx]).
Qed.
Lemma hs_dsts_all : forallb dst_okb HS_CODE = true. Proof. vm_compute. reflexivity. Qed.
Lemma hs_dst : forall k, (k < HS_N)%nat -> dst_ok (nth k HS_CODE Ecall).
Proof.
  intros k Hk. apply dst_okb_ok. pose proof hs_dsts_all as H. rewrite forallb_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Definition KEPT (regs regs' : bvmap 5 word) : Prop := forall r, ~ In (AX2.ridx r) HS_DSTS -> getr regs' r = getr regs r.

Lemma kept_refl : forall regs, KEPT regs regs. Proof. intros regs r _. reflexivity. Qed.
Lemma kept_setrd : forall regs rd v, rd = 0%bv \/ In (AX2.ridx rd) HS_DSTS -> KEPT regs (setrd regs rd v).
Proof.
  intros regs rd v Hd r Hr. unfold setrd. destruct (bv_eqb rd 0) eqn:E; [reflexivity|].
  destruct Hd as [Hd|Hd]; [subst rd; discriminate E|].
  apply getr_other. intros C. subst r. exact (Hr Hd).
Qed.
Lemma kept_trans : forall r1 r2 r3, KEPT r1 r2 -> KEPT r2 r3 -> KEPT r1 r3.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma rdn1_ext : forall segs (m m' : word -> option byte) a, m a = m' a -> rdn segs m a 1 = rdn segs m' a 1.
Proof. intros segs m m' a H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma hs_rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

Lemma map_nth_seq : forall {A B} (g : A -> B) (l : list A) d, map (fun k => g (nth k l d)) (seq 0 (length l)) = map g l.
Proof.
  intros A B g l d. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma mkzt_get : forall l k t q,
  tget q (mkzt l k t) = if (Nat.leb (Pos.to_nat k) (Pos.to_nat q) && Nat.ltb (Pos.to_nat q) (Pos.to_nat k + length l))%bool
                        then nth_error l (Pos.to_nat q - Pos.to_nat k) else tget q t.
Proof.
  induction l as [|i r IH]; intros k t q.
  - cbn [mkzt length]. destruct (Nat.leb_spec (Pos.to_nat k) (Pos.to_nat q)); destruct (Nat.ltb_spec (Pos.to_nat q) (Pos.to_nat k + 0)); cbn; try reflexivity; lia.
  - cbn [mkzt length]. rewrite IH. rewrite Pos2Nat.inj_succ.
    destruct (Pos.eq_dec q k) as [->|Hne].
    + destruct (Nat.leb_spec (S (Pos.to_nat k)) (Pos.to_nat k)); [lia|]. cbn [andb].
      rewrite tget_tset_same. destruct (Nat.leb_spec (Pos.to_nat k) (Pos.to_nat k)); [|lia].
      destruct (Nat.ltb_spec (Pos.to_nat k) (Pos.to_nat k + S (length r))); [|lia]. cbn. rewrite Nat.sub_diag. reflexivity.
    + rewrite tget_tset_other by congruence.
      assert (Pos.to_nat q <> Pos.to_nat k) by (intros C; apply Hne, Pos2Nat.inj, C).
      destruct (Nat.leb_spec (S (Pos.to_nat k)) (Pos.to_nat q)) as [H1|H1];
      destruct (Nat.ltb_spec (Pos.to_nat q) (S (Pos.to_nat k) + length r)) as [H2|H2];
      destruct (Nat.leb_spec (Pos.to_nat k) (Pos.to_nat q)) as [H3|H3];
      destruct (Nat.ltb_spec (Pos.to_nat q) (Pos.to_nat k + S (length r))) as [H4|H4]; cbn [andb]; try lia; try reflexivity.
      replace (Pos.to_nat q - Pos.to_nat k)%nat with (S (Pos.to_nat q - S (Pos.to_nat k))) by lia. reflexivity.
Qed.

Lemma tget_empty : forall {A} q, @tget A q TEmpty = None.
Proof. intros A q. destruct q; reflexivity. Qed.

Lemma zfetch_sound : forall p pc i, zfetch p pc = Some i ->
  exists k, (k < HS_N)%nat /\ pc = p + 4 * Z.of_nat k /\ i = tozi (nth k HS_CODE Ecall).
Proof.
  intros p pc i H. unfold zfetch in H.
  destruct (Z.leb 0 (pc - p) && Z.eqb ((pc - p) mod 4) 0)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [H0 H4]. apply Z.leb_le in H0. apply Z.eqb_eq in H4.
  rewrite ZT_eq, mkzt_get in H. cbn [tget] in H.
  assert (Hx : 0 <= (pc - p) / 4) by (apply Z.div_pos; lia).
  assert (Hq : Pos.to_nat (Z.to_pos ((pc - p) / 4 + 1)) = S (Z.to_nat ((pc - p) / 4))).
  { rewrite <- Z2Nat.inj_pos. rewrite Z2Pos.id by lia. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia. }
  rewrite Hq in H. change (Pos.to_nat 1) with 1%nat in H. rewrite length_map, HS_CODE_length in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc2; [|rewrite tget_empty in H; discriminate H] end.
  apply andb_prop in Hc2 as [_ Hlt]. apply Nat.ltb_lt in Hlt.
  replace (S (Z.to_nat ((pc - p) / 4)) - 1)%nat with (Z.to_nat ((pc - p) / 4)) in H by lia.
  exists (Z.to_nat ((pc - p) / 4)). split; [lia|]. split.
  - rewrite Z2Nat.id by lia. pose proof (Z.div_mod (pc - p) 4 ltac:(lia)) as Hdm. lia.
  - rewrite nth_error_map in H. rewrite (nth_error_nth' HS_CODE Ecall) in H by (rewrite HS_CODE_length; lia).
    cbn in H. injection H as <-. reflexivity.
Qed.

Section Sim.
Variable segs : list Segment.
Variable T : Z.
Variable n : nat.
Variable M0 : word -> option byte.
Hypothesis HT : 0 <= T /\ T + 16 * Z.of_nat n <= 2 ^ 64.
Hypothesis HST : forall d m, 0 <= d -> d + Z.of_nat m <= 16 * Z.of_nat n ->
  RiscvSemantics.store_ok segs M0 (Z_to_bv 64 (T + d)) m = true.

Definition TREL (M : word -> option byte) (tbl : list (list Z)) : Prop :=
  RECS n tbl
  /\ (forall j, 0 <= j < 16 * Z.of_nat n -> rdn segs M (Z_to_bv 64 (T + j)) 1 = Some [Z_to_bv 8 (tbyte tbl j)])
  /\ (forall x, (bv_unsigned x < T \/ T + 16 * Z.of_nat n <= bv_unsigned x) -> M x = M0 x)
  /\ mem_grows M0 M.

Lemma trel_load : forall M tbl a m bs, TREL M tbl -> zld T tbl a m = Some bs -> 0 <= a < 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) m = Some (map (Z_to_bv 8) bs) /\ bytes_ok bs /\ length bs = m.
Proof.
  intros M tbl a m bs [HR [Hrd _]] H Ha.
  destruct (zld_sound n T tbl a m bs HR H) as (H0 & H1 & Hlen & Hok & Hnth).
  split; [|split; assumption].
  subst m. rewrite <- (map_nth_seq (Z_to_bv 8) bs 0).
  apply (hs_rdn_of_nth segs M (length bs) (Z_to_bv 64 a) (fun k => Z_to_bv 8 (nth k bs 0))); [rewrite hs_u64 by lia; lia|].
  intros j Hj. rewrite hs_u64 by lia. replace (a + Z.of_nat j) with (T + (a - T + Z.of_nat j)) by lia.
  rewrite Hrd by lia. rewrite Hnth by exact Hj. reflexivity.
Qed.

Lemma trel_store : forall M tbl a bs tbl', TREL M tbl -> bytes_ok bs -> zstt T tbl a bs = Some tbl' -> 0 <= a < 2 ^ 64 ->
  RiscvSemantics.store_ok segs M (Z_to_bv 64 a) (length bs) = true
  /\ TREL (wbytes M (Z_to_bv 64 a) (map (Z_to_bv 8) bs)) tbl'.
Proof.
  intros M tbl a bs tbl' [HR [Hrd [Hfr Hgr]]] Hbs H Ha.
  destruct (zstt_sound n T tbl a bs tbl' HR Hbs H) as (H0 & H1 & HR' & Hby).
  remember (a - T) as d eqn:Ed.
  assert (Hlm : length (map (Z_to_bv 8) bs) = length bs) by apply length_map.
  assert (Hnw : bv_unsigned (Z_to_bv 64 a) + Z.of_nat (length (map (Z_to_bv 8) bs)) <= 2 ^ 64) by (rewrite hs_u64, Hlm by lia; lia).
  split.
  - eapply store_ok_mono; [exact Hgr|]. replace a with (T + d) by lia. apply HST; lia.
  - split; [exact HR'|]. split; [|split].
    + intros j Hj. rewrite (Hby j ltac:(lia)).
      destruct (Z.leb_spec d j) as [Hl|Hl]; destruct (Z.ltb_spec j (d + Z.of_nat (length bs))) as [Hu|Hu]; cbn [andb].
      * apply rdn1_overlay.
        replace (Z_to_bv 64 (T + j)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + Z.of_nat (Z.to_nat (j - d)))) by (rewrite hs_u64 by lia; f_equal; lia).
        rewrite AX2S.wbytes_nth by (rewrite ?Hlm; lia).
        rewrite map_nth. reflexivity.
      * rewrite <- (Hrd j Hj). apply rdn1_ext. apply AX2S.wbytes_out; [exact Hnw|]. rewrite !hs_u64 by lia. rewrite Hlm. lia.
      * rewrite <- (Hrd j Hj). apply rdn1_ext. apply AX2S.wbytes_out; [exact Hnw|]. rewrite !hs_u64 by lia. rewrite Hlm. lia.
      * rewrite <- (Hrd j Hj). apply rdn1_ext. apply AX2S.wbytes_out; [exact Hnw|]. rewrite !hs_u64 by lia. rewrite Hlm. lia.
    + intros x Hx. rewrite AX2S.wbytes_out; [exact (Hfr x Hx) | exact Hnw |]. rewrite !hs_u64 by lia. rewrite Hlm. lia.
    + eapply mem_grows_trans; [exact Hgr | apply wbytes_grows].
Qed.

Ltac gsolve := repeat match goal with |- _ /\ _ => split end.

Definition SIMC (regs : bvmap 5 word) (pc : Z) (M rom : word -> option byte) (st' : zst) : Prop :=
  exists regs' M', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 pc) M rom) = MachineOk (mkst regs' (Z_to_bv 64 (z_pc st')) M' rom)
    /\ RREG (z_regs st') regs' /\ TREL M' (z_tbl st') /\ 0 <= z_pc st' < 2 ^ 64 /\ KEPT regs regs'.

Lemma npc_w : forall pc, 0 <= pc < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (w64 (pc + 4)) /\ 0 <= w64 (pc + 4) < 2 ^ 64.
Proof. intros pc Hpc. split; [apply v_addi_w; lia | apply w64_range; lia]. Qed.

Lemma sim_branch : forall c rs1 rs2 imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4) ->
  dst_ok (Branch c rs1 rs2 imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Branch c rs1 rs2 imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros c rs1 rs2 imm w pc m tbl st' regs M rom Hf He Hd _ Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc].
  pose proof (imm13_range imm) as Ri.
  assert (Htg : btgt (Z_to_bv 64 pc) (bv_signed imm) = Z_to_bv 64 (w64 (pc + bv_signed imm))) by (unfold btgt; apply v_addi_w; lia).
  assert (Rtg : 0 <= w64 (pc + bv_signed imm) < 2 ^ 64) by (apply w64_range; lia).
  destruct c; cbn [tozi zexec z_pc z_regs z_tbl] in Hx.
  all: try discriminate.
  all: destruct (zg m (rk rs1)) as [x|] eqn:Ex; [|discriminate]; destruct (zg m (rk rs2)) as [y|] eqn:Ey; [|discriminate].
  all: injection Hx as <-; destruct (HR rs1 x Ex) as [Gx Rx]; destruct (HR rs2 y Ey) as [Gy Ry].
  all: exists regs, M; cbn [z_pc z_regs z_tbl].
  - destruct (Z.eqb_spec x y) as [Exy|Exy]; refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))).
    + rewrite (step_beq_tk segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_eq_w by lia; apply Z.eqb_eq; exact Exy). rewrite Htg. reflexivity.
    + exact Rtg.
    + rewrite (step_beq_ft segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_eq_w by lia; apply Z.eqb_neq; exact Exy). rewrite Hnpc. reflexivity.
    + exact Rnpc.
  - destruct (Z.eqb_spec x y) as [Exy|Exy]; refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))).
    + rewrite (step_bne_ft segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_eq_w by lia; apply Z.eqb_eq; exact Exy). rewrite Hnpc. reflexivity.
    + exact Rnpc.
    + rewrite (step_bne_tk segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_eq_w by lia; apply Z.eqb_neq; exact Exy). rewrite Htg. reflexivity.
    + exact Rtg.
  - destruct (Z.ltb_spec x y) as [Exy|Exy]; refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))).
    + rewrite (step_bltu_tk segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_ltu_w by lia; apply Z.ltb_lt; exact Exy). rewrite Htg. reflexivity.
    + exact Rtg.
    + rewrite (step_bltu_ft segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_ltu_w by lia; apply Z.ltb_ge; exact Exy). rewrite Hnpc. reflexivity.
    + exact Rnpc.
  - destruct (Z.ltb_spec x y) as [Exy|Exy]; refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))).
    + rewrite (step_bgeu_ft segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_ltu_w by lia; apply Z.ltb_lt; exact Exy). rewrite Hnpc. reflexivity.
    + exact Rnpc.
    + rewrite (step_bgeu_tk segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, Gy, c_ltu_w by lia; apply Z.ltb_ge; exact Exy). rewrite Htg. reflexivity.
    + exact Rtg.
Qed.

Lemma sim_jal : forall rd imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
  dst_ok (Jal rd imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Jal rd imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros rd imm w pc m tbl st' regs M rom Hf He Hd _ Hpc Hx HR HT'.
  cbn [tozi] in Hx. destruct (bv_eqb rd 0) eqn:E0; [|discriminate]. apply bv_eqb_true in E0. subst rd.
  cbn [zexec z_pc z_regs z_tbl] in Hx. injection Hx as <-.
  pose proof (imm21_range imm) as Ri.
  exists regs, M. cbn [z_pc z_regs z_tbl].
  refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))); [|apply w64_range; lia].
  rewrite (step_jal_x0 segs regs _ M rom w imm Hf He Hd). unfold btgt. rewrite v_addi_w by lia. reflexivity.
Qed.

Lemma sim_jalr : forall rd rs imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Jalr rd rs imm, 4) ->
  dst_ok (Jalr rd rs imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Jalr rd rs imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros rd rs imm w pc m tbl st' regs M rom Hf He Hd _ Hpc Hx HR HT'.
  cbn [tozi] in Hx. destruct (bv_eqb rd 0) eqn:E0; [|discriminate]. apply bv_eqb_true in E0. subst rd.
  cbn [zexec z_pc z_regs z_tbl] in Hx.
  destruct (zg m (rk rs)) as [x|] eqn:Ex; [|discriminate]. injection Hx as <-.
  destruct (HR rs x Ex) as [Gx Rx]. pose proof (imm12_range imm) as Ri.
  exists regs, M. cbn [z_pc z_regs z_tbl].
  refine (conj _ (conj HR (conj HT' (conj _ (kept_refl regs))))); [|apply jalr_range; lia].
  rewrite (step_jalr_x0 segs regs _ M rom w rs imm _ Hf He Hd eq_refl). rewrite Gx. rewrite v_jalr_w by lia. reflexivity.
Qed.

Lemma sim_load : forall sz sg rd rs imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Load sz sg rd rs imm, 4) ->
  dst_ok (Load sz sg rd rs imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Load sz sg rd rs imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros sz sg rd rs imm w pc m tbl st' regs M rom Hf He Hd Hdst Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc]. pose proof (imm12_range imm) as Ri.
  destruct sz, sg; cbn [tozi zexec z_pc z_regs z_tbl] in Hx; try discriminate.
  -
    destruct (zg m (rk rs)) as [x|] eqn:Ex; [|discriminate]. destruct (HR rs x Ex) as [Gx Rx].
    assert (Ra : 0 <= w64 (x + bv_signed imm) < 2 ^ 64) by (apply w64_range; lia).
    destruct (zld T tbl (w64 (x + bv_signed imm)) 4) as [bs|] eqn:Hl; [|discriminate]. injection Hx as <-.
    destruct (trel_load M tbl _ 4 bs HT' Hl Ra) as (Hrd & Hok & Hlen).
    pose proof (le_range bs Hok) as Rle. rewrite Hlen in Rle. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rle.
    exists (setrd regs rd (Z_to_bv 64 (sx32 (le bs)))), M. cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj (rreg_set m regs rd _ HR (sx32_range _ Rle)) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
    rewrite (step_lw segs regs _ M rom w rd rs imm (map (Z_to_bv 8) bs) (Z_to_bv 64 (le bs)) Hf He Hd).
    + rewrite Hnpc, <- (v_lw_w (le bs) Rle). reflexivity.
    + rewrite Gx, v_addi_w by lia. exact Hrd.
    + rewrite le_bytes by exact Hok. rewrite hs_u64 by lia. reflexivity.
  -
    destruct (zg m (rk rs)) as [x|] eqn:Ex; [|discriminate]. destruct (HR rs x Ex) as [Gx Rx].
    assert (Ra : 0 <= w64 (x + bv_signed imm) < 2 ^ 64) by (apply w64_range; lia).
    destruct (zld T tbl (w64 (x + bv_signed imm)) 8) as [bs|] eqn:Hl; [|discriminate]. injection Hx as <-.
    destruct (trel_load M tbl _ 8 bs HT' Hl Ra) as (Hrd & Hok & Hlen).
    pose proof (le_range bs Hok) as Rle. rewrite Hlen in Rle. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rle.
    exists (setrd regs rd (Z_to_bv 64 (le bs))), M. cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj (rreg_set m regs rd _ HR Rle) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
    rewrite (step_ld segs regs _ M rom w rd rs imm (map (Z_to_bv 8) bs) (Z_to_bv 64 (le bs)) Hf He Hd).
    + rewrite Hnpc. reflexivity.
    + rewrite Gx, v_addi_w by lia. exact Hrd.
    + rewrite le_bytes by exact Hok. rewrite hs_u64 by lia. reflexivity.
Qed.

Lemma sim_store : forall sz rs1 rs2 imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
  dst_ok (Store sz rs1 rs2 imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Store sz rs1 rs2 imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros sz rs1 rs2 imm w pc m tbl st' regs M rom Hf He Hd _ Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc]. pose proof (imm12_range imm) as Ri.
  destruct sz; cbn [tozi zexec z_pc z_regs z_tbl] in Hx; try discriminate;
    (destruct (zg m (rk rs1)) as [x|] eqn:Ex; [|discriminate]; destruct (zg m (rk rs2)) as [y|] eqn:Ey; [|discriminate];
     destruct (HR rs1 x Ex) as [Gx Rx]; destruct (HR rs2 y Ey) as [Gy Ry];
     assert (Ra : 0 <= w64 (x + bv_signed imm) < 2 ^ 64) by (apply w64_range; lia)).
  - destruct (zstt T tbl (w64 (x + bv_signed imm)) (tole 4 y)) as [tbl'|] eqn:Hs; [|discriminate]. injection Hx as <-.
    destruct (trel_store M tbl _ (tole 4 y) tbl' HT' (tole_ok 4 y) Hs Ra) as [Hok HT''].
    rewrite length_tole in Hok.
    exists regs, (wbytes M (Z_to_bv 64 (w64 (x + bv_signed imm))) (map (Z_to_bv 8) (tole 4 y))). cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj HR (conj HT'' (conj Rnpc (kept_refl regs))))).
    rewrite (step_sw_val segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, v_addi_w by lia; exact Hok).
    rewrite Hnpc, Gx, Gy, v_addi_w by lia. rewrite word_to_le_bytes_w by exact Ry. reflexivity.
  - destruct (zstt T tbl (w64 (x + bv_signed imm)) (tole 8 y)) as [tbl'|] eqn:Hs; [|discriminate]. injection Hx as <-.
    destruct (trel_store M tbl _ (tole 8 y) tbl' HT' (tole_ok 8 y) Hs Ra) as [Hok HT''].
    rewrite length_tole in Hok.
    exists regs, (wbytes M (Z_to_bv 64 (w64 (x + bv_signed imm))) (map (Z_to_bv 8) (tole 8 y))). cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj HR (conj HT'' (conj Rnpc (kept_refl regs))))).
    rewrite (step_sd_val segs regs _ M rom w rs1 rs2 imm Hf He Hd) by (rewrite Gx, v_addi_w by lia; exact Hok).
    rewrite Hnpc, Gx, Gy, v_addi_w by lia. rewrite word_to_le_bytes_w by exact Ry. reflexivity.
Qed.

Lemma sim_opimm : forall op rd rs imm w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (OpImm op rd rs imm, 4) ->
  dst_ok (OpImm op rd rs imm) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (OpImm op rd rs imm)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros op rd rs imm w pc m tbl st' regs M rom Hf He Hd Hdst Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc]. pose proof (imm12_range imm) as Ri.
  destruct op; cbn [tozi zexec z_pc z_regs z_tbl] in Hx; try discriminate.
  destruct (zg m (rk rs)) as [x|] eqn:Ex; [|discriminate]. destruct (HR rs x Ex) as [Gx Rx]. injection Hx as <-.
  assert (Rv : 0 <= w64 (x + bv_signed imm) < 2 ^ 64) by (apply w64_range; lia).
  exists (setrd regs rd (Z_to_bv 64 (w64 (x + bv_signed imm)))), M. cbn [z_pc z_regs z_tbl].
  refine (conj _ (conj (rreg_set m regs rd _ HR Rv) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
  rewrite (step_addi segs regs _ M rom w rd rs imm Hf He Hd). rewrite Hnpc, Gx, v_addi_w by lia. reflexivity.
Qed.

Lemma sim_shiftimm : forall op rd rs sh w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm op rd rs sh, 4) ->
  dst_ok (ShiftImm op rd rs sh) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (ShiftImm op rd rs sh)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros op rd rs sh w pc m tbl st' regs M rom Hf He Hd Hdst Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc]. pose proof (sh6_range sh) as Rs.
  destruct op; cbn [tozi zexec z_pc z_regs z_tbl] in Hx; try discriminate;
    (destruct (zg m (rk rs)) as [x|] eqn:Ex; [|discriminate]; destruct (HR rs x Ex) as [Gx Rx]; injection Hx as <-).
  - exists (setrd regs rd (Z_to_bv 64 (Z.land (Z.shiftl x (bv_unsigned sh)) (hs_two64 - 1)))), M. cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj (rreg_set m regs rd _ HR (slli_range _ _)) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
    rewrite (step_slli segs regs _ M rom w rd rs sh Hf He Hd). rewrite Hnpc, Gx, v_slli_w by lia. reflexivity.
  - exists (setrd regs rd (Z_to_bv 64 (Z.shiftr x (bv_unsigned sh)))), M. cbn [z_pc z_regs z_tbl].
    refine (conj _ (conj (rreg_set m regs rd _ HR (srli_range x (bv_unsigned sh) Rx ltac:(lia))) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
    rewrite (step_srli segs regs _ M rom w rd rs sh Hf He Hd). rewrite Hnpc, Gx, v_srli_w by lia. reflexivity.
Qed.

Lemma sim_op : forall op rd r1 r2 w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Op op rd r1 r2, 4) ->
  dst_ok (Op op rd r1 r2) -> 0 <= pc < 2 ^ 64 -> zexec T (tozi (Op op rd r1 r2)) (ZS pc m tbl) = Some st' ->
  RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros op rd r1 r2 w pc m tbl st' regs M rom Hf He Hd Hdst Hpc Hx HR HT'.
  destruct (npc_w pc Hpc) as [Hnpc Rnpc].
  destruct op; cbn [tozi zexec z_pc z_regs z_tbl] in Hx; try discriminate.
  destruct (zg m (rk r1)) as [x|] eqn:Ex; [|discriminate]. destruct (zg m (rk r2)) as [y|] eqn:Ey; [|discriminate].
  destruct (HR r1 x Ex) as [Gx Rx]. destruct (HR r2 y Ey) as [Gy Ry]. injection Hx as <-.
  assert (Rv : 0 <= w64 (x + y) < 2 ^ 64) by (apply w64_range; lia).
  exists (setrd regs rd (Z_to_bv 64 (w64 (x + y)))), M. cbn [z_pc z_regs z_tbl].
  refine (conj _ (conj (rreg_set m regs rd _ HR Rv) (conj HT' (conj Rnpc (kept_setrd regs rd _ Hdst))))).
  rewrite (step_add segs regs _ M rom w rd r1 r2 Hf He Hd). rewrite Hnpc, Gx, Gy, v_add_w by lia. reflexivity.
Qed.

Lemma zexec_sim : forall i w pc m tbl st' regs M rom,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) -> dst_ok i ->
  0 <= pc < 2 ^ 64 -> zexec T (tozi i) (ZS pc m tbl) = Some st' -> RREG m regs -> TREL M tbl -> SIMC regs pc M rom st'.
Proof.
  intros i w pc m tbl st' regs M rom Hf He Hd Hdst Hpc Hx HR HT'.
  destruct i; try (exfalso; cbn [tozi zexec] in Hx; discriminate).
  - eapply sim_jal; eassumption.
  - eapply sim_jalr; eassumption.
  - eapply sim_branch; eassumption.
  - eapply sim_load; eassumption.
  - eapply sim_store; eassumption.
  - eapply sim_opimm; eassumption.
  - eapply sim_shiftimm; eassumption.
  - eapply sim_op; eassumption.
Qed.

Variable p : Z.
Hypothesis Hp : 0 <= p /\ p + 4 * Z.of_nat HS_N <= 2 ^ 64.
Hypothesis HF : forall k, (k < HS_N)%nat -> fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) = Some (nth k HS_WORDS (Z_to_bv 32 0)).

Definition hres_st (r : hres) : option zst := match r with HDone st => Some st | HMore st => Some st | HFail => None end.

Lemma hs_steps_sim : forall fuel st st' regs M rom,
  hres_st (hs_steps p T fuel st) = Some st' -> 0 <= z_pc st < 2 ^ 64 -> RREG (z_regs st) regs -> TREL M (z_tbl st) ->
  exists regs' M', msteps segs (mkst regs (Z_to_bv 64 (z_pc st)) M rom) (mkst regs' (Z_to_bv 64 (z_pc st')) M' rom)
    /\ RREG (z_regs st') regs' /\ TREL M' (z_tbl st') /\ 0 <= z_pc st' < 2 ^ 64 /\ KEPT regs regs'.
Proof.
  induction fuel as [|f IH]; intros st st' regs M rom Hr Hpc HR HT'.
  - cbn [hs_steps hres_st] in Hr. injection Hr as <-. exists regs, M. split; [apply mst_refl|].
    split; [exact HR|]. split; [exact HT'|]. split; [exact Hpc | apply kept_refl].
  - cbn [hs_steps] in Hr.
    destruct (zfetch p (z_pc st)) as [i|] eqn:Hfe.
    + destruct (zexec T i st) as [st1|] eqn:Hx; [|discriminate].
      destruct (zfetch_sound p (z_pc st) i Hfe) as (k & Hk & Epc & Ei). subst i.
      destruct st as [pc m tbl]. cbn [z_pc z_regs z_tbl] in *.
      pose proof (HF k Hk) as Hf. rewrite <- Epc in Hf.
      destruct (zexec_sim (nth k HS_CODE Ecall) _ pc m tbl st1 regs M rom Hf (hs_no_ecall k Hk) (hs_decode k Hk) (hs_dst k Hk) Hpc Hx HR HT')
        as (regs1 & M1 & Hst & HR1 & HT1 & Hpc1 & Hk1).
      destruct (IH st1 st' regs1 M1 rom Hr Hpc1 HR1 HT1) as (regs2 & M2 & Hms & HR2 & HT2 & Hpc2 & Hk2).
      exists regs2, M2. split; [|split; [exact HR2 | split; [exact HT2 | split; [exact Hpc2 | eapply kept_trans; eassumption]]]].
      eapply mst_step; [reflexivity | exact Hst | exact Hms].
    + cbn [hres_st] in Hr. injection Hr as <-. exists regs, M. split; [apply mst_refl|].
      split; [exact HR|]. split; [exact HT'|]. split; [exact Hpc | apply kept_refl].
Qed.

Lemma hs_run_sim : forall fuel st st' regs M rom,
  hs_run p T fuel st = Some st' -> 0 <= z_pc st < 2 ^ 64 -> RREG (z_regs st) regs -> TREL M (z_tbl st) ->
  exists regs' M', msteps segs (mkst regs (Z_to_bv 64 (z_pc st)) M rom) (mkst regs' (Z_to_bv 64 (z_pc st')) M' rom)
    /\ RREG (z_regs st') regs' /\ TREL M' (z_tbl st') /\ 0 <= z_pc st' < 2 ^ 64 /\ KEPT regs regs'.
Proof.
  induction fuel as [|f IH]; intros st st' regs M rom Hr Hpc HR HT'; [discriminate|].
  cbn [hs_run] in Hr.
  destruct (hs_steps p T HS_CHUNK st) as [st1|st1|] eqn:Hs; [injection Hr as <- | | discriminate].
  - apply (hs_steps_sim HS_CHUNK st st1 regs M rom); [rewrite Hs; reflexivity | exact Hpc | exact HR | exact HT'].
  - destruct (hs_steps_sim HS_CHUNK st st1 regs M rom ltac:(rewrite Hs; reflexivity) Hpc HR HT') as (regs1 & M1 & Hms1 & HR1 & HT1 & Hpc1 & Hk1).
    destruct (IH st1 st' regs1 M1 rom Hr Hpc1 HR1 HT1) as (regs2 & M2 & Hms2 & HR2 & HT2 & Hpc2 & Hk2).
    exists regs2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HR2|]. split; [exact HT2|]. split; [exact Hpc2 | eapply kept_trans; eassumption].
Qed.

End Sim.

Lemma chunk16_length : forall n l, length (chunk16 n l) = n.
Proof. induction n as [|n IH]; intros l; [reflexivity|]. cbn [chunk16 length]. rewrite IH. reflexivity. Qed.

Lemma chunk16_recs : forall n l, length l = (16 * n)%nat -> bytes_ok l -> RECS n (chunk16 n l).
Proof.
  induction n as [|n IH]; intros l Hl Hok; [split; [reflexivity | constructor]|].
  cbn [chunk16]. destruct (IH (skipn 16 l) ltac:(rewrite length_skipn; lia) (bytes_ok_skipn l 16 Hok)) as [L F].
  split; [cbn [length]; rewrite L; reflexivity|]. constructor; [|exact F].
  split; [rewrite length_firstn; lia | apply bytes_ok_firstn; exact Hok].
Qed.

Lemma chunk16_tbyte : forall n l j, length l = (16 * n)%nat -> 0 <= j < 16 * Z.of_nat n ->
  tbyte (chunk16 n l) j = nth (Z.to_nat j) l 0.
Proof.
  induction n as [|n IH]; intros l j Hl Hj; [lia|]. cbn [chunk16]. unfold tbyte.
  destruct (Z_lt_le_dec j 16) as [Hs|Hs].
  - rewrite (Z.div_small j 16) by lia. rewrite (Z.mod_small j 16) by lia. cbn [Z.to_nat nth].
    apply nth_firstn_lt. lia.
  - assert (E1 : j / 16 = (j - 16) / 16 + 1).
    { replace j with ((j - 16) + 1 * 16) at 1 by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (E2 : j mod 16 = (j - 16) mod 16).
    { replace j with ((j - 16) + 1 * 16) at 1 by lia. apply Z.mod_add. lia. }
    assert (Hd : 0 <= (j - 16) / 16) by (apply Z.div_pos; lia).
    rewrite E1, E2. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. cbn [Nat.add]. change (Z.to_nat 1) with 1%nat. cbn [Nat.add nth].
    fold (tbyte (chunk16 n (skipn 16 l)) (j - 16)).
    rewrite IH by (rewrite ?length_skipn; lia). rewrite nth_skipn'. f_equal. lia.
Qed.

Definition hsort_spec (segs : list Segment) (p : Z) : Prop :=
  forall (T : Z) (n : nat) (M : word -> option byte) (regs : bvmap 5 word) (rom : word -> option byte) (ret : Z) (tz : list Z) fuel st',
    0 <= T < 2 ^ 64 -> T + 16 * Z.of_nat n <= 2 ^ 64 -> 0 <= ret < 2 ^ 64 ->
    getr regs 1%bv = Z_to_bv 64 ret -> getr regs 10%bv = Z_to_bv 64 T -> getr regs 11%bv = Z_to_bv 64 (Z.of_nat n) ->
    length tz = (16 * n)%nat -> bytes_ok tz ->
    (forall j, 0 <= j < 16 * Z.of_nat n -> rdn segs M (Z_to_bv 64 (T + j)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat j) tz 0)]) ->
    (forall d m, 0 <= d -> d + Z.of_nat m <= 16 * Z.of_nat n -> RiscvSemantics.store_ok segs M (Z_to_bv 64 (T + d)) m = true) ->
    hs_run p T fuel (ZS p (hs_regs0 ret T (Z.of_nat n)) (chunk16 n tz)) = Some st' ->
    exists regs' M', msteps segs (mkst regs (Z_to_bv 64 p) M rom) (mkst regs' (Z_to_bv 64 (z_pc st')) M' rom)
      /\ KEPT regs regs' /\ RECS n (z_tbl st')
      /\ (forall j, 0 <= j < 16 * Z.of_nat n -> rdn segs M' (Z_to_bv 64 (T + j)) 1 = Some [Z_to_bv 8 (tbyte (z_tbl st') j)])
      /\ (forall x, (bv_unsigned x < T \/ T + 16 * Z.of_nat n <= bv_unsigned x) -> M' x = M x)
      /\ mem_grows M M'.

Theorem hsort_spec_of_code : forall segs p, 0 <= p -> p + 4 * Z.of_nat HS_N <= 2 ^ 64 ->
  (forall k, (k < HS_N)%nat -> fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) = Some (nth k HS_WORDS (Z_to_bv 32 0))) ->
  hsort_spec segs p.
Proof.
  intros segs p Hp0 Hp1 HF T n M regs rom ret tz fuel st' [HT0 HT0'] HT1 Hret G1 G10 G11 Hlen Hok Hrd Hst Hrun.
  assert (RN : 0 <= Z.of_nat n < 2 ^ 64) by lia.
  assert (Hp2 : 0 <= p < 2 ^ 64) by (unfold HS_N in Hp1; lia).
  assert (HTR : TREL segs T n M M (chunk16 n tz)).
  { split; [apply chunk16_recs; assumption|]. split; [|split; [reflexivity | apply mem_grows_refl]].
    intros j Hj. rewrite chunk16_tbyte by assumption. exact (Hrd j Hj). }
  assert (HRR : RREG (hs_regs0 ret T (Z.of_nat n)) regs) by (apply rreg_entry; try assumption; lia).
  destruct (hs_run_sim segs T n M (conj HT0 HT1) Hst p HF fuel _ st' regs M rom Hrun ltac:(cbn [z_pc]; exact Hp2) HRR HTR)
    as (regs' & M' & Hms & HR' & (HRC & Hrd' & Hfr & Hgr) & Hpc' & Hk).
  exists regs', M'. cbn [z_pc] in Hms.
  split; [exact Hms|]. split; [exact Hk|]. split; [exact HRC|]. split; [exact Hrd'|]. split; [exact Hfr | exact Hgr].
Qed.

Lemma hs_words_length : forall n tbl, RECS n tbl -> length (hs_words tbl) = (2 * n)%nat.
Proof.
  intros n tbl [Hl _]. subst n. unfold hs_words. induction tbl as [|rec t IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app. rewrite IH. cbn. lia.
Qed.

Lemma hs_words_nth : forall tbl i, (i < 2 * length tbl)%nat ->
  nth i (hs_words tbl) 0 = le (firstn 8 (skipn (8 * (i mod 2)) (nth (i / 2) tbl []))).
Proof.
  intros tbl. unfold hs_words. induction tbl as [|rec t IH]; intros i Hi; [cbn in Hi; lia|].
  cbn [map concat]. destruct i as [|[|i']].
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn [app nth]. rewrite IH by (cbn [length] in Hi; lia).
    replace (S (S i') mod 2)%nat with (i' mod 2)%nat by (replace (S (S i')) with (i' + 1 * 2)%nat by lia; rewrite Nat.Div0.mod_add; reflexivity).
    replace (S (S i') / 2)%nat with (S (i' / 2)) by (replace (S (S i')) with (i' + 1 * 2)%nat by lia; rewrite Nat.div_add by lia; lia).
    reflexivity.
Qed.

Lemma tole_le : forall bs, bytes_ok bs -> tole (length bs) (le bs) = bs.
Proof.
  induction bs as [|b t IH]; intros Hok; [reflexivity|]. inversion Hok as [|b' t' Hb Ht]; subst.
  pose proof (le_range t Ht) as Rt.
  cbn [length tole le]. f_equal.
  - rewrite Z.land_lor_distr_l. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_mul by lia. rewrite Z.mod_small by lia. apply Z.lor_0_r.
  - rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 8) by lia. rewrite Z.div_small by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite Z.lor_0_l. apply IH. exact Ht.
Qed.

Lemma hs_word_read : forall segs M T n tbl i,
  RECS n tbl -> 0 <= T -> T + 16 * Z.of_nat n <= 2 ^ 64 ->
  (forall j, 0 <= j < 16 * Z.of_nat n -> rdn segs M (Z_to_bv 64 (T + j)) 1 = Some [Z_to_bv 8 (tbyte tbl j)]) ->
  (i < 2 * n)%nat ->
  rdn segs M (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth i (hs_words tbl) 0)))
  /\ 0 <= nth i (hs_words tbl) 0 < 2 ^ 64.
Proof.
  intros segs M T n tbl i HR HT0 HT1 Hrd Hi.
  destruct HR as [Hl HF].
  set (r := (i / 2)%nat). set (h := (i mod 2)%nat).
  assert (Hih : i = (2 * r + h)%nat) by (unfold r, h; pose proof (Nat.div_mod i 2 ltac:(lia)); lia).
  assert (Hh : (h < 2)%nat) by (unfold h; apply Nat.mod_upper_bound; lia).
  assert (Hr : (r < n)%nat) by lia.
  destruct (recs_nth n tbl r (conj Hl HF) Hr) as [Lr Br].
  set (rec := nth r tbl []) in *.
  set (bs := firstn 8 (skipn (8 * h) rec)).
  assert (Lbs : length bs = 8%nat) by (unfold bs; rewrite length_firstn, length_skipn, Lr; destruct h as [|[|]]; cbn; lia).
  assert (Bbs : bytes_ok bs) by (unfold bs; apply bytes_ok_firstn, bytes_ok_skipn, Br).
  assert (Ew : nth i (hs_words tbl) 0 = le bs) by (unfold bs, rec, r, h; apply hs_words_nth; lia).
  pose proof (le_range bs Bbs) as Rle. rewrite Lbs in Rle. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rle.
  rewrite Ew. split; [|exact Rle].
  assert (Etl : tole 8 (le bs) = bs) by (rewrite <- Lbs; apply tole_le; exact Bbs).
  rewrite word_to_le_bytes_w by exact Rle. rewrite Etl.
  assert (Hnw : bv_unsigned (Z_to_bv 64 (T + 8 * Z.of_nat i)) + Z.of_nat 8 <= 2 ^ 64) by (rewrite hs_u64 by lia; lia).
  rewrite <- (map_nth_seq (Z_to_bv 8) bs 0). rewrite Lbs.
  apply (hs_rdn_of_nth segs M 8 _ (fun k => Z_to_bv 8 (nth k bs 0)) Hnw).
  intros k Hk. rewrite hs_u64 by lia.
  replace (T + 8 * Z.of_nat i + Z.of_nat k) with (T + (16 * Z.of_nat r + (8 * Z.of_nat h + Z.of_nat k))) by lia.
  rewrite Hrd by lia. f_equal. f_equal. f_equal.
  unfold tbyte.
  assert (E1 : (16 * Z.of_nat r + (8 * Z.of_nat h + Z.of_nat k)) / 16 = Z.of_nat r).
  { symmetry. apply (Z.div_unique _ 16 (Z.of_nat r) (8 * Z.of_nat h + Z.of_nat k)); lia. }
  assert (E2 : (16 * Z.of_nat r + (8 * Z.of_nat h + Z.of_nat k)) mod 16 = 8 * Z.of_nat h + Z.of_nat k).
  { symmetry. apply (Z.mod_unique _ 16 (Z.of_nat r) (8 * Z.of_nat h + Z.of_nat k)); lia. }
  rewrite E1, E2. rewrite Nat2Z.id. fold rec.
  unfold bs. rewrite nth_firstn_lt by lia. rewrite nth_skipn'. f_equal. lia.
Qed.
