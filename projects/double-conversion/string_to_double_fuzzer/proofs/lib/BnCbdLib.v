(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim StoreOk Hoare
  BnModel BnMath BnZX BnMem BnDefs LibIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_rom : forall segs k m (a : word),
  bv_unsigned a + Z.of_nat k <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k ->
     forall b, m x = Some b -> memory_read segs x 1 = Some [b]) ->
  rdn segs m a k = rdn segs (fun _ => None) a k.
Proof.
  intros segs k. induction k as [|k IH]; intros m a Hnw Hro; [reflexivity|].
  cbn [rdn].
  assert (E1 : match m a with Some b => Some b | None => seg_rom segs a end = seg_rom segs a).
  { destruct (m a) as [b|] eqn:E; [|reflexivity].
    unfold seg_rom. rewrite (Hro a ltac:(pose proof (u64_range a); lia) b E). reflexivity. }
  rewrite E1. destruct (seg_rom segs a) as [b|]; [|reflexivity].
  destruct k as [|k']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  rewrite (IH m (a + 1)%bv ltac:(lia) ltac:(intros x Hx; apply Hro; lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arr32_rom : forall segs m a l,
  0 <= a -> a + 4 * Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x b, a <= x < a + 4 * Z.of_nat (length l) -> m (Z_to_bv 64 x) = Some b -> memory_read segs (Z_to_bv 64 x) 1 = Some [b]) ->
  arr32 segs (fun _ => None) a l -> arr32 segs m a l.
Proof.
  intros segs m a l Ha Hb Hro H i Hi. destruct (H i Hi) as (bs & Hr & Hv). exists bs. split; [|exact Hv].
  rewrite <- Hr. apply rdn_rom.
  - rewrite u_Z2bv64, Z.mod_small by lia. zwidth. lia.
  - intros x Hx b Hm. rewrite u_Z2bv64, Z.mod_small in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hm |- *. apply Hro; [|exact Hm]. zwidth. cbn [Z.of_nat] in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition five_tbl_chk (segs : list Segment) : bool :=
  forallb (fun k => match rdn segs (fun _ => None) (Z_to_bv 64 (80520 + 4 * Z.of_nat k)) 4 with
                    | Some bs => bytes_le_to_Z bs =? nth k [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625] 0
                    | None => false end) (seq 0 12).

Lemma five_tbl_of_chk : forall segs, five_tbl_chk segs = true ->
  arr32 segs (fun _ => None) 80520 [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].
Proof.
  intros segs H i Hi. cbn [length] in Hi.
  pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hk. cbn beta in Hk. unfold cellN.
  destruct (rdn segs _ _ 4) as [bs|]; [|discriminate]. exists bs. split; [reflexivity|]. apply Z.eqb_eq. exact Hk.
Qed.

Lemma five_tbl_P0 : arr32 SEGS_P (fun _ => None) 80520 [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].
Proof. apply five_tbl_of_chk. vm_compute. reflexivity. Qed.
Lemma five_tbl_U0 : arr32 SEGS_U (fun _ => None) 80520 [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].
Proof. apply five_tbl_of_chk. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dsof (segs : list Segment) (m : word -> option byte) (buf : Z) (n : nat) : list Z :=
  map (fun i => match rdn segs m (Z_to_bv 64 (buf + Z.of_nat i)) 1 with
                | Some [d] => bv_unsigned d
                | _ => 0
                end) (seq 0 n).

Lemma dsof_length : forall segs m buf n, length (dsof segs m buf n) = n.
Proof. intros. unfold dsof. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_le_to_Z_1 : forall d : byte, bytes_le_to_Z [d] = bv_unsigned d.
Proof. intros d. cbn. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma dsof_spec : forall segs m buf len,
  0 <= len ->
  (forall i, 0 <= i < len -> exists d, rdn segs m (Z_to_bv 64 (buf + i)) 1 = Some [d] /\ 48 <= bv_unsigned d <= 57) ->
  let ds := dsof segs m buf (Z.to_nat len) in
  zlen ds = len /\ digits_ok ds
  /\ (forall k, (k < length ds)%nat -> cellN segs m (buf + Z.of_nat k) 1 (nth k ds 0)).
Proof.
  intros segs m buf len Hlen Hd. cbn zeta.
  split; [unfold zlen; rewrite dsof_length; lia|].
  split.
  - unfold digits_ok, dsof. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (i & <- & Hi). apply in_seq in Hi.
    destruct (Hd (Z.of_nat i) ltac:(lia)) as (d & Hr & Hdr). rewrite Hr. exact Hdr.
  - intros k Hk. rewrite dsof_length in Hk. unfold dsof.
    set (f := fun i : nat => match rdn segs m (Z_to_bv 64 (buf + Z.of_nat i)) 1 with Some [d] => bv_unsigned d | _ => 0 end).
    rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
    rewrite map_nth, seq_nth by exact Hk. unfold f. cbn [Nat.add].
    destruct (Hd (Z.of_nat k) ltac:(lia)) as (d & Hr & Hdr). rewrite Hr.
    exists [d]. split; [exact Hr | apply bytes_le_to_Z_1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. intros z. reflexivity. Qed.

Lemma swrap32_low : forall a4 e, a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2147483648 <= e < 2147483648 ->
  bv_swrap 32 (a4 mod 2 ^ 64) = e.
Proof.
  intros a4 e Ha He. rewrite swrap32_eq.
  change (2 ^ 32) with 4294967296 in Ha. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma swrap32_neg_low : forall a4 e, a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2147483647 <= e < 2147483648 ->
  bv_swrap 32 (0 - a4 mod 2 ^ 64) = - e.
Proof.
  intros a4 e Ha He. rewrite swrap32_eq.
  change (2 ^ 32) with 4294967296 in Ha. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cmp_loop_range : forall fuel a b i, -1 <= cmp_loop fuel a b i <= 1.
Proof.
  induction fuel as [|f IH]; intros a b i; cbn [cmp_loop]; [lia|].
  destruct (i <? _); [lia|]. destruct (_ <? _); [lia|]. destruct (_ <? _); [lia|]. apply IH.
Qed.

Lemma compare_range : forall a b, -1 <= compare a b <= 1.
Proof.
  intros a b. unfold compare. destruct (_ <? _); [lia|]. destruct (_ <? _); [lia|]. apply cmp_loop_range.
Qed.

Lemma assign_decimal_ex : forall ds, digits_ok ds -> ex (assign_decimal ds) = 0.
Proof.
  intros ds Hds. pose proof (assign_decimal_spec ds Hds) as SP. cbn zeta in SP. destruct SP as (_ & _ & _ & Hex).
  destruct (cells (assign_decimal ds)) eqn:E; [|apply Hex; congruence].
  unfold assign_decimal in *. destruct (ads_loop _ ds bn_zero) as [b1 rest]. unfold clamp in *. cbn [cells BnModel.ex] in *.
  rewrite E. reflexivity.
Qed.

Lemma assign_u64_facts : forall v, 0 <= v < 2 ^ 64 ->
  ok (cells (assign_u64 v)) /\ norm (cells (assign_u64 v)) /\ val (cells (assign_u64 v)) = v /\ ex (assign_u64 v) = 0.
Proof.
  intros v Hv. unfold assign_u64. cbn [cells BnModel.ex].
  destruct (chunks_spec 3 v ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (H1 & H2 & H3 & _). auto.
Qed.

Lemma shl_ex_le : forall n b, 0 <= n -> 0 <= ex b -> 0 <= ex (shl n b) <= ex b + n / 28.
Proof.
  intros n b Hn He. unfold shl. destruct (cells b); cbn [BnModel.ex]; [pose proof (Z.div_pos n 28); lia|].
  destruct (shl_l _ _ _) as [r c]. cbn [BnModel.ex]. pose proof (Z.div_pos n 28). lia.
Qed.

Lemma mulpow10_ex_le : forall e b, ok (cells b) -> norm (cells b) -> 0 <= e -> 0 <= ex b ->
  0 <= ex (mulpow10 e b) <= ex b + e / 28.
Proof.
  intros e b Hok Hn He Hex. pose proof (mulpow10_spec e b Hok Hn He) as SP. cbn zeta in SP. destruct SP as (_ & _ & _ & Hexe & Hnil).
  pose proof (Z.div_pos e 28 He ltac:(lia)).
  destruct (cells b) eqn:E.
  - (* [comment removed for export] *)
    unfold mulpow10. destruct (e =? 0); [lia|]. rewrite E. lia.
  - rewrite Hexe; [lia|]. congruence.
Qed.

(* [comment removed for export] *)
Lemma zlen_le_124 : forall l, ok l -> norm l -> val l < B ^ 124 -> zlen l <= 124.
Proof. intros l Hok Hn Hv. apply len_bound; auto; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma env1 : 10 ^ 309 * 2 ^ 27 < B ^ 124. Proof. vm_compute. reflexivity. Qed.
Lemma env2 : 10 ^ 780 * 2 ^ 27 < B ^ 124. Proof. vm_compute. reflexivity. Qed.
Lemma env3 : 2 ^ 64 * 5 ^ 1103 * 2 ^ 27 < B ^ 124. Proof. vm_compute. reflexivity. Qed.

Lemma pow10_le : forall a b, 0 <= a <= b -> 10 ^ a <= 10 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow5_le_pow10 : forall a, 0 <= a -> 5 ^ a <= 10 ^ a.
Proof. intros. apply Z.pow_le_mono_l; lia. Qed.
Lemma pow5_le : forall a b, 0 <= a <= b -> 5 ^ a <= 5 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_mod28_le : forall e, 2 ^ (e mod 28) <= 2 ^ 27.
Proof. intros. apply Z.pow_le_mono_r; [lia|]. pose proof (Z.mod_pos_bound e 28). lia. Qed.

(* [comment removed for export] *)
Lemma envA : forall v F X L M P W T, 0 <= v < L -> 0 < F <= X -> 0 < M <= W -> L * X <= P -> 1 <= W -> P * W < T ->
  v * F < T /\ F * M * v < T.
Proof.
  intros v F X L M P W T Hv HF HM HLX HW HPT.
  assert (A1 : v * F < L * X).
  { apply Z.lt_le_trans with (m := L * F); [apply Z.mul_lt_mono_pos_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
  assert (HP : 0 <= P) by nia.
  assert (A0 : P * 1 <= P * W) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (VF : 0 <= v * F) by (apply Z.mul_nonneg_nonneg; lia).
  assert (A2 : v * F * M <= v * F * W) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A3 : v * F * W < L * X * W) by (apply Z.mul_lt_mono_pos_r; lia).
  assert (A4 : L * X * W <= P * W) by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [lia|]. replace (F * M * v) with (v * F * M) by lia. lia.
Qed.

Lemma envB : forall v F M P W Q T, 0 <= v < Q -> 0 < F <= P -> 0 < M <= W -> 1 <= W -> Q * P * W < T ->
  v * F < T /\ F * M * v < T.
Proof.
  intros v F M P W Q T Hv HF HM HW HT.
  assert (A1 : v * F < Q * P).
  { apply Z.lt_le_trans with (m := Q * F); [apply Z.mul_lt_mono_pos_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
  assert (QP : 0 <= Q * P) by (apply Z.mul_nonneg_nonneg; lia).
  assert (A0 : Q * P * 1 <= Q * P * W) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (VF : 0 <= v * F) by (apply Z.mul_nonneg_nonneg; lia).
  assert (A2 : v * F * M <= v * F * W) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A3 : v * F * W < Q * P * W) by (apply Z.mul_lt_mono_pos_r; lia).
  split; [lia|]. replace (F * M * v) with (v * F * M) by lia. lia.
Qed.

Lemma envC : forall v L P W T, 0 <= v < L -> L <= P -> 1 <= W -> P * W < T -> v < T.
Proof.
  intros v L P W T Hv HL HW HT. assert (A0 : P * 1 <= P * W) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma two27_ge1 : 1 <= 2 ^ 27. Proof. vm_compute. discriminate. Qed.
Lemma two64_ge0 : 0 <= 2 ^ 64. Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Lemma env_buf_pos : forall v len expo, 0 <= v < 10 ^ len -> 0 <= expo -> 1 <= len -> len + expo <= 309 ->
  v * 5 ^ expo < B ^ 124 /\ 5 ^ expo * 2 ^ (expo mod 28) * v < B ^ 124.
Proof.
  intros v len expo Hv He Hl Hle.
  pose proof (pow10_le (len + expo) 309 ltac:(lia)) as H1. rewrite Z.pow_add_r in H1 by lia.
  apply (envA v (5 ^ expo) (10 ^ expo) (10 ^ len) (2 ^ (expo mod 28)) (10 ^ 309) (2 ^ 27) (B ^ 124) Hv).
  - split; [apply Z.pow_pos_nonneg; lia | apply pow5_le_pow10; exact He].
  - split; [apply Z.pow_pos_nonneg; [lia | pose proof (Z.mod_pos_bound expo 28); lia] | apply pow2_mod28_le].
  - exact H1.
  - apply two27_ge1.
  - apply env1.
Qed.

(* [comment removed for export] *)
Lemma env_buf0 : forall v len, 0 <= v < 10 ^ len -> 1 <= len <= 780 -> v < B ^ 124.
Proof.
  intros v len Hv Hl. apply (envC v (10 ^ len) (10 ^ 780) (2 ^ 27) (B ^ 124) Hv).
  - apply pow10_le. lia.
  - apply two27_ge1.
  - apply env2.
Qed.

(* [comment removed for export] *)
Lemma env_diy_neg : forall v k, 0 <= v < 2 ^ 64 -> 0 <= k <= 1103 ->
  v * 5 ^ k < B ^ 124 /\ 5 ^ k * 2 ^ (k mod 28) * v < B ^ 124.
Proof.
  intros v k Hv Hk.
  apply (envB v (5 ^ k) (2 ^ (k mod 28)) (5 ^ 1103) (2 ^ 27) (2 ^ 64) (B ^ 124) Hv).
  - split; [apply Z.pow_pos_nonneg; lia | apply pow5_le; lia].
  - split; [apply Z.pow_pos_nonneg; [lia | pose proof (Z.mod_pos_bound k 28); lia] | apply pow2_mod28_le].
  - apply two27_ge1.
  - apply env3.
Qed.

Lemma env_diy0 : forall v, 0 <= v < 2 ^ 64 -> v < B ^ 124.
Proof.
  intros v Hv.
  assert (H : 2 ^ 64 <= 2 ^ 64 * 5 ^ 1103).
  { rewrite <- (Z.mul_1_r (2 ^ 64)) at 1. apply Z.mul_le_mono_nonneg_l; [apply two64_ge0|].
    pose proof (Z.pow_pos_nonneg 5 1103 ltac:(lia) ltac:(lia)). lia. }
  apply (envC v (2 ^ 64) (2 ^ 64 * 5 ^ 1103) (2 ^ 27) (B ^ 124) Hv H two27_ge1 env3).
Qed.

(* [comment removed for export] *)
Lemma shl_ok_any : forall n b, ok (cells b) -> ok (cells (shl n b)).
Proof.
  intros n b Hok. unfold shl. destruct (cells b) as [|x t] eqn:E; [rewrite E; exact Hok|].
  pose proof (Z.mod_pos_bound n 28 ltac:(lia)) as Hm.
  pose proof (shl_l_spec (n mod 28) (x :: t) 0 Hok ltac:(lia) ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SS.
  destruct (shl_l _ _ _) as [r c]. destruct SS as (_ & Hokr & _ & Hc). cbn [cells].
  destruct (c =? 0); [exact Hokr|]. apply ok_app. split; [exact Hokr|]. apply ok_cons. split; [|apply ok_nil].
  pose proof (pow2_mod28_le n). unfold B. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cbd_facts : forall ds len expo f e,
  digits_ok ds -> zlen ds = len -> 1 <= len <= 780 -> -323 <= len + expo <= 309 -> 0 <= f < 2 ^ 64 -> -2047 <= e <= 2047 ->
  let a0 := assign_decimal ds in
  let b0 := assign_u64 f in
  let a1 := if 0 <=? expo then mulpow10 expo a0 else a0 in
  let b1 := if 0 <=? expo then b0 else mulpow10 (- expo) b0 in
  (ok (cells a0) /\ norm (cells a0) /\ ex a0 = 0 /\ (0 <= expo -> val (cells a0) * 5 ^ expo < B ^ 124))
  /\ (ok (cells b0) /\ norm (cells b0) /\ ex b0 = 0 /\ (expo < 0 -> val (cells b0) * 5 ^ (- expo) < B ^ 124))
  /\ (ok (cells a1) /\ norm (cells a1) /\ zlen (cells a1) <= 124 /\ 0 <= ex a1 <= 12)
  /\ (ok (cells b1) /\ norm (cells b1) /\ zlen (cells b1) <= 124 /\ 0 <= ex b1 <= 40)
  /\ ok (cells (shl (- e) a1)) /\ ok (cells (shl e b1)).
Proof.
  intros ds len expo f e Hds Hlen Hl Hle Hf He. cbn zeta.
  pose proof (assign_decimal_spec ds Hds) as SA. cbn zeta in SA. destruct SA as (Aok & An & Av & _).
  pose proof (assign_decimal_ex ds Hds) as Aex.
  pose proof (decval_bound ds Hds) as Dv. rewrite Hlen in Dv.
  destruct (assign_u64_facts f Hf) as (Bok & Bn & Bv & Bex).
  set (a0 := assign_decimal ds) in *. set (b0 := assign_u64 f) in *.
  assert (FA : ok (cells a0) /\ norm (cells a0) /\ ex a0 = 0 /\ (0 <= expo -> val (cells a0) * 5 ^ expo < B ^ 124)).
  { repeat split; auto. intros Hp. rewrite Av. apply (proj1 (env_buf_pos _ len expo Dv Hp ltac:(lia) ltac:(lia))). }
  assert (FB : ok (cells b0) /\ norm (cells b0) /\ ex b0 = 0 /\ (expo < 0 -> val (cells b0) * 5 ^ (- expo) < B ^ 124)).
  { repeat split; auto. intros Hn. rewrite Bv. apply (proj1 (env_diy_neg f (- expo) Hf ltac:(lia))). }
  assert (F1 : let a1 := if 0 <=? expo then mulpow10 expo a0 else a0 in
               ok (cells a1) /\ norm (cells a1) /\ zlen (cells a1) <= 124 /\ 0 <= ex a1 <= 12).
  { cbn zeta. destruct (Z.leb_spec 0 expo) as [Hp|Hn].
    - pose proof (mulpow10_spec expo a0 Aok An Hp) as SP. cbn zeta in SP. destruct SP as (Ok1 & N1 & V1 & _ & _).
      pose proof (mulpow10_ex_le expo a0 Aok An Hp ltac:(lia)) as X1.
      repeat split; auto.
      + apply zlen_le_124; auto. rewrite V1, Av. apply (proj2 (env_buf_pos _ len expo Dv Hp ltac:(lia) ltac:(lia))).
      + lia.
      + assert (expo / 28 <= 11) by (apply Z.div_le_upper_bound || idtac; lia). lia.
    - repeat split; auto; try lia. apply zlen_le_124; auto. rewrite Av. apply (env_buf0 _ len Dv ltac:(lia)). }
  assert (F2 : let b1 := if 0 <=? expo then b0 else mulpow10 (- expo) b0 in
               ok (cells b1) /\ norm (cells b1) /\ zlen (cells b1) <= 124 /\ 0 <= ex b1 <= 40).
  { cbn zeta. destruct (Z.leb_spec 0 expo) as [Hp|Hn].
    - repeat split; auto; try lia. apply zlen_le_124; auto. rewrite Bv. apply (env_diy0 f Hf).
    - pose proof (mulpow10_spec (- expo) b0 Bok Bn ltac:(lia)) as SP. cbn zeta in SP. destruct SP as (Ok1 & N1 & V1 & _ & _).
      pose proof (mulpow10_ex_le (- expo) b0 Bok Bn ltac:(lia) ltac:(lia)) as X1.
      repeat split; auto.
      + apply zlen_le_124; auto. rewrite V1, Bv. apply (proj2 (env_diy_neg f (- expo) Hf ltac:(lia))).
      + lia.
      + assert (- expo / 28 <= 39) by lia. lia. }
  cbn zeta in F1, F2. destruct F1 as (Ok1 & N1 & L1 & X1). destruct F2 as (Ok2 & N2 & L2 & X2).
  split; [exact FA|]. split; [exact FB|]. split; [repeat split; auto; lia|]. split; [repeat split; auto; lia|].
  split; apply shl_ok_any; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap64_eq : forall z, bv_swrap 64 z = (z + 9223372036854775808) mod 18446744073709551616 - 9223372036854775808.
Proof. intros z. reflexivity. Qed.

Lemma swrap64_small : forall x, -9223372036854775808 <= x < 9223372036854775808 -> bv_swrap 64 x = x.
Proof. intros x Hx. rewrite swrap64_eq. rewrite Z.mod_small; lia. Qed.

Lemma swrap32_small : forall x, -2147483648 <= x < 2147483648 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite swrap32_eq. rewrite Z.mod_small; lia. Qed.

Lemma swrap32_low' : forall a4 e, a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2147483648 <= e < 2147483648 ->
  bv_swrap 32 a4 = e.
Proof.
  intros a4 e Ha He. rewrite swrap32_eq. change (2 ^ 32) with 4294967296 in Ha. lia.
Qed.

Lemma swrap32_neg_low' : forall a4 e, a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2147483647 <= e < 2147483648 ->
  bv_swrap 32 (0 - a4) = - e.
Proof.
  intros a4 e Ha He. rewrite swrap32_eq. change (2 ^ 32) with 4294967296 in Ha. lia.
Qed.
