(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CkUB Require Import CkBImg CkBTables.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma no_image_asan : forall s1 s2, 0x67f000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

Notation rt_got m :=
  (rw_cells asegs m 0xd1320 [C8 (Z_to_bv 64 0x16b668); C8 (Z_to_bv 64 0xd7338); C8 (Z_to_bv 64 0xd9b38);
                             C8 (Z_to_bv 64 0xda828); C8 (Z_to_bv 64 0xda830); C8 (Z_to_bv 64 0xda820)]).
Notation rt_shbase m := (rw_cells asegs m 0xd9b38 [C8 (Z_to_bv 64 0x7fff8000)]).

Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xc9de4).


Definition shrng (RNG : footprint) (lo hi : Z) : Prop :=
  lo < hi -> rng RNG (shad lo) (shad (hi - 1) + 1 - shad lo).

Lemma shrng_sub : forall RNG lo hi lo' hi',
  shrng RNG lo hi -> lo <= lo' -> hi' <= hi -> shrng RNG lo' hi'.
Proof.
  intros RNG lo hi lo' hi' H H1 H2 Hlt. eapply rng_sub'; [apply H; lia|].
  rewrite !shad_div. Z.div_mod_to_equations. lia.
Qed.

Lemma shrng_rng : forall RNG lo hi, shrng RNG lo hi -> lo < hi -> rng RNG (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof. intros RNG lo hi H L. exact (H L). Qed.

Lemma shrng_of_block : forall RNG A n, rng RNG (shad A) (nshad n) -> A mod 8 = 0 -> 0 <= A -> shrng RNG A (A + n).
Proof.
  intros RNG A n R HA A0 Hlt. eapply rng_sub'; [exact R|].
  rewrite !shad_div, nshad_div. Z.div_mod_to_equations. lia.
Qed.

Lemma shrng_of_region : forall RNG SLO SLEN lo hi,
  rng RNG SLO SLEN -> SLO <= shad lo -> shad (hi - 1) + 1 <= SLO + SLEN -> shrng RNG lo hi.
Proof. intros RNG SLO SLEN lo hi R H1 H2 Hlt. eapply rng_sub'; [exact R|]. lia. Qed.

Lemma shrng_acc : forall RNG lo hi a,
  shrng RNG lo hi -> lo <= a < hi -> 0 <= lo ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
  intros RNG lo hi a H Ha L0. specialize (H ltac:(lia)).
  apply (rng_acc_litZ RNG (shad lo) (shad (hi - 1) + 1 - shad lo) _ 1%nat 1 H eq_refl ltac:(lia)).
  rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
  Z.div_mod_to_equations. lia.
Qed.


Fixpoint wabove (W : list ivl) (L : Z) : Prop :=
  match W with [] => True | (lo, _) :: W' => L <= lo /\ wabove W' L end.

Lemma wabove_disjoint : forall W L a n, wabove W L -> a + n <= L -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros L a n HW Ha; cbn in *; [exact I|].
  destruct HW as [H1 H2]. split; [lia| eapply IH; eauto].
Qed.

Lemma wabove_outside : forall W L x, wabove W L -> x < L -> outside W x.
Proof.
  intros W L x HW Hx. eapply disjoint_outside; [apply (wabove_disjoint W L x 1 HW); lia| lia].
Qed.

Lemma shad_lt_floor : forall a L, a < L -> KHIGH <= L -> shad a + 1 <= L.
Proof. intros a L Ha HL. rewrite shad_div. unfold ASHOFF, KHIGH in *. Z.div_mod_to_equations. lia. Qed.

Lemma unpoisoned_mu : forall W L m m1 lo hi,
  unpoisoned m lo hi -> munch W m m1 -> wabove W L -> hi <= L -> KHIGH <= L -> unpoisoned m1 lo hi.
Proof.
  intros W L m m1 lo hi U MU HW Hhi HL.
  destruct (Z.lt_ge_cases lo hi) as [Hlt|Hge].
  - eapply unpoisoned_munch; [exact U| exact MU|]. eapply wabove_disjoint; [exact HW|].
    pose proof (shad_lt_floor (hi - 1) L ltac:(lia) HL). lia.
  - destruct U as (A & B & _). split; [lia|]. split; [lia|]. intros G H0; lia.
Qed.

Lemma unpoisoned_check_mu : forall W L m m1 lo hi a N,
  unpoisoned m lo hi -> munch W m m1 -> wabove W L -> hi <= L -> KHIGH <= L ->
  lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros W L m m1 lo hi a N U MU HW Hhi HL H1 H2 H3 H4.
  pose proof (unpoisoned_mu W L m m1 lo hi U MU HW Hhi HL) as U1.
  destruct (unpoisoned_check_rd asegs m1 lo hi a N U1 H1 H2 H3 H4) as (b & RD & CK).
  exists b. split; [|split; [exact CK| apply sval_range]].
  unfold shad, ASHOFF in RD. unfold wa in RD.
  replace (Z.shiftr a 3 + 2147450880) with (2147450880 + Z.shiftr a 3) by lia. exact RD.
Qed.


Definition ck_sh (m : word -> option byte) : Prop :=
  shadow_bytes m (shad ACRCTAB) (shad ACRCTAB + 128) (fun _ => 0)
  /\ shadow_bytes m (shad ABRAID) (shad ABRAID + 512) (fun _ => 0)
  /\ shadow_bytes m (shad AX2N) (shad AX2N + 16) (fun _ => 0).

Lemma shad_ACRCTAB : shad ACRCTAB = 0x7fffc5b4. Proof. vm_compute. reflexivity. Qed.
Lemma shad_ABRAID : shad ABRAID = 0x7fffc654. Proof. vm_compute. reflexivity. Qed.
Lemma shad_AX2N : shad AX2N = 0x7fffc518. Proof. vm_compute. reflexivity. Qed.

Local Ltac lit_le := apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.

Lemma ck_sh_mu : forall W L m m1, ck_sh m -> munch W m m1 -> wabove W L -> KHIGH <= L -> ck_sh m1.
Proof.
  intros W L m m1 (A & B & C) MU HW HL. unfold KHIGH in HL.
  split; [|split].
  - apply (shadow_bytes_munch W m m1 _ _ _ A MU). apply (wabove_disjoint W L _ _ HW). rewrite shad_ACRCTAB. lia.
  - apply (shadow_bytes_munch W m m1 _ _ _ B MU). apply (wabove_disjoint W L _ _ HW). rewrite shad_ABRAID. lia.
  - apply (shadow_bytes_munch W m m1 _ _ _ C MU). apply (wabove_disjoint W L _ _ HW). rewrite shad_AX2N. lia.
Qed.

Lemma ctab_unpoisoned : forall m, ck_sh m -> unpoisoned m ACRCTAB (ACRCTAB + 1024).
Proof.
  intros m (A & _ & _). apply (unpoisoned_of_zero m _ _ _ ACRCTAB (ACRCTAB + 1024) A); try (intros; reflexivity); lit_le.
Qed.
Lemma btab_unpoisoned : forall m, ck_sh m -> unpoisoned m ABRAID (ABRAID + 4096).
Proof.
  intros m (_ & B & _). apply (unpoisoned_of_zero m _ _ _ ABRAID (ABRAID + 4096) B); try (intros; reflexivity); lit_le.
Qed.
Lemma x2n_unpoisoned : forall m, ck_sh m -> unpoisoned m AX2N (AX2N + 128).
Proof.
  intros m (_ & _ & C). apply (unpoisoned_of_zero m _ _ _ AX2N (AX2N + 128) C); try (intros; reflexivity); lit_le.
Qed.

Lemma ctab_shrng : forall RNG, rng_aimg_sh RNG -> shrng RNG ACRCTAB (ACRCTAB + 1024).
Proof. intros RNG R. eapply shrng_of_region; [exact R| |]; lit_le. Qed.
Lemma btab_shrng : forall RNG, rng_aimg_sh RNG -> shrng RNG ABRAID (ABRAID + 4096).
Proof. intros RNG R. eapply shrng_of_region; [exact R| |]; lit_le. Qed.
Lemma x2n_shrng : forall RNG, rng_aimg_sh RNG -> shrng RNG AX2N (AX2N + 128).
Proof. intros RNG R. eapply shrng_of_region; [exact R| |]; lit_le. Qed.

Lemma tab_check_mu : forall W L m m1 T n i,
  unpoisoned m T (T + 4 * n) -> munch W m m1 -> wabove W L -> T + 4 * n <= L -> KHIGH <= L ->
  T mod 8 = 0 -> 0 <= i < n ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr (T + 4 * i) 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ (T + 4 * i) mod 8 + 3 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros W L m m1 T n i U MU HW HT HL T8 Hi.
  destruct (unpoisoned_check_mu W L m m1 T (T + 4 * n) (T + 4 * i) 4 U MU HW HT HL
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
  exists b. split; [exact RD|]. split; [|exact SR]. destruct CK as [Z0|CK]; [left; exact Z0| right; lia].
Qed.


Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall k l, zb (firstn k l) = firstn k (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.
Lemma zb_skipn : forall k l, zb (skipn k l) = skipn k (zb l).
Proof. intros. unfold zb. symmetry. apply skipn_map. Qed.

Definition ck_buf (RNG : footprint) (m : word -> option byte) (A : Z) (bs : list Z) : Prop :=
  bytes_at asegs m A (zb bs)
  /\ Forall (fun b => 0 <= b < 256) bs
  /\ unpoisoned m A (A + Z.of_nat (length bs))
  /\ rng RNG A (Z.of_nat (length bs))
  /\ shrng RNG A (A + Z.of_nat (length bs)).

Lemma Forall_firstn_ : forall {X} (P : X -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros X P k. induction k as [|k IH]; intros [|x l] H; cbn; try constructor; inversion H; subst; auto. Qed.
Lemma Forall_skipn_ : forall {X} (P : X -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros X P k. induction k as [|k IH]; intros [|x l] H; cbn; try assumption; inversion H; subst; auto. Qed.

Lemma bytes_at_sub : forall m A (bs : list byte) (off k : nat),
  bytes_at asegs m A bs -> (off + k <= length bs)%nat ->
  bytes_at asegs m (A + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m A bs off k (H0 & H1 & H) Hk.
  assert (L : length (firstn k (skipn off bs)) = k) by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  replace (A + Z.of_nat off + Z.of_nat i) with (A + Z.of_nat (off + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec i k) as [_|C]; [|lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma ck_buf_sub : forall RNG m A bs (off k : nat),
  ck_buf RNG m A bs -> (off + k <= length bs)%nat ->
  ck_buf RNG m (A + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros RNG m A bs off k (B & F & U & R & S) Hk.
  assert (L : length (firstn k (skipn off bs)) = k) by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  pose proof B as (B0 & B1 & _). rewrite zb_length in B1.
  unfold ck_buf. rewrite L. split; [|split; [|split; [|split]]].
  - rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [exact B| rewrite zb_length; exact Hk].
  - apply Forall_firstn_, Forall_skipn_. exact F.
  - eapply unpoisoned_sub; [exact U| lia | lia].
  - eapply rng_sub'; [exact R| lia].
  - eapply shrng_sub; [exact S| lia | lia].
Qed.

Definition bz (bs : list Z) (i : Z) : Z := nth (Z.to_nat i) bs 0.

Lemma ck_buf_read : forall m A bs (i : Z) a,
  bytes_at asegs m A (zb bs) -> 0 <= i < Z.of_nat (length bs) -> a = wa (A + i) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 (bz bs i)].
Proof.
  intros m A bs i a HB Hi ->. unfold bz.
  apply (u8ro_read asegs m A (zb bs) i); [exact HB| | lia | reflexivity].
  unfold zb. rewrite nth_error_map. rewrite (nth_error_nth' bs 0) by lia. reflexivity.
Qed.

Lemma bz_range : forall bs i, Forall (fun b => 0 <= b < 256) bs -> 0 <= bz bs i < 256.
Proof.
  intros bs i F. unfold bz.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [L|L].
  - apply (proj1 (Forall_forall _ _) F). apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma bz_val : forall bs i, Forall (fun b => 0 <= b < 256) bs -> bv_unsigned (Z_to_bv 8 (bz bs i)) = bz bs i.
Proof.
  intros bs i F. pose proof (bz_range bs i F) as R.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia.
Qed.

Lemma firstn_S_nth : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
Lemma skipn_nth_S : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bz_firstn_S : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  firstn (Z.to_nat (i + 1)) bs = firstn (Z.to_nat i) bs ++ [bz bs i].
Proof.
  intros bs i Hi. unfold bz. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply firstn_S_nth. lia.
Qed.

Lemma bz_skipn : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  skipn (Z.to_nat i) bs = bz bs i :: skipn (Z.to_nat (i + 1)) bs.
Proof.
  intros bs i Hi. unfold bz. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply skipn_nth_S. lia.
Qed.
