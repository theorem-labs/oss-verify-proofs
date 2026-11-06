(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Notation ASAN_B := 2147450880%Z.
Notation KHI := 17594333495296%Z.
Notation KTOP := 140737488355328%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Lemma zeros_length : forall n, length (zeros n) = n.
Proof. intros. apply repeat_length. Qed.
Lemma zeros_app : forall a b, zeros (a + b) = zeros a ++ zeros b.
Proof. intros. unfold zeros. apply repeat_app. Qed.
Lemma nth_error_zeros : forall n i, (i < n)%nat -> nth_error (zeros n) i = Some (Z_to_bv 8 0).
Proof.
  intros n i Hi. unfold zeros. rewrite nth_error_nth' with (d := Z_to_bv 8 0).
  - f_equal. apply nth_repeat.
  - rewrite repeat_length. exact Hi.
Qed.
Lemma firstn_zeros : forall k n, (k <= n)%nat -> firstn k (zeros n) = zeros k.
Proof.
  intros k n Hk. replace n with (k + (n - k))%nat by lia. rewrite zeros_app.
  rewrite firstn_app, firstn_all2 by (rewrite zeros_length; lia).
  rewrite zeros_length, Nat.sub_diag. cbn. apply app_nil_r.
Qed.
Lemma skipn_zeros : forall k n, skipn k (zeros n) = zeros (n - k).
Proof.
  intros k n. destruct (Nat.le_gt_cases k n).
  - replace n with (k + (n - k))%nat at 1 by lia. rewrite zeros_app, skipn_app, skipn_all2 by (rewrite zeros_length; lia).
    rewrite zeros_length, Nat.sub_diag. reflexivity.
  - rewrite skipn_all2 by (rewrite zeros_length; lia). replace (n - k)%nat with 0%nat by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition shz (m : word -> option byte) (a n : Z) : Prop :=
  (0 <= n)%Z /\ bytes_at segs m a (zeros (Z.to_nat n)).

#[using="Type"] Lemma shz_bound : forall m a n, shz m a n -> (0 <= a /\ 0 <= n /\ a + n <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n [Hn Hb]. pose proof (bytes_at_bound segs m a _ Hb) as B. rewrite zeros_length, Z2Nat.id in B by lia. lia.
Qed.

#[using="Type"] Lemma shz_nil : forall m a, (0 <= a <= 2^64)%Z -> shz m a 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros m a Ha. split; [lia|]. cbn. apply bytes_at_nil. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_app : forall m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  shz m a (n1 + n2) <-> shz m a n1 /\ shz m (a + n1) n2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n1 n2 H1 H2. unfold shz.
  rewrite Z2Nat.inj_add, zeros_app by lia. rewrite bytes_at_app, zeros_length, Z2Nat.id by lia.
  split; [intros (A & B & C) | intros ((A & B) & (C & D))].
  - split; split; try assumption.
  - split; [lia|]. split; assumption.
Qed.

#[using="Type"] Lemma shz_sub : forall m a n a' n', shz m a n -> (a <= a')%Z -> (0 <= n')%Z -> (a' + n' <= a + n)%Z -> shz m a' n'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n a' n' H Ha Hn' Hle. pose proof (shz_bound _ _ _ H) as B.
  replace n with ((a' - a) + (n - (a' - a)))%Z in H by lia.
  apply (proj1 (shz_app m a (a' - a) (n - (a' - a)) ltac:(lia) ltac:(lia))) in H. destruct H as [_ H].
  replace (a + (a' - a))%Z with a' in H by lia.
  replace (n - (a' - a))%Z with (n' + (n - (a' - a) - n'))%Z in H by lia.
  apply (proj1 (shz_app m a' n' (n - (a' - a) - n') ltac:(lia) ltac:(lia))) in H. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_read : forall m a n (E : Z) (k : nat),
  shz m a n -> (a <= E)%Z -> (E + Z.of_nat k <= a + n)%Z ->
  ov_read_bytes segs m (Z_to_bv 64 E) k = Some (zeros k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n E k [Hn Hb] HaE Hk. pose proof (bytes_at_bound segs m a _ Hb) as B. rewrite zeros_length in B.
  replace (Z_to_bv 64 E) with (wa (a + (E - a)))%Z by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read segs m a (zeros (Z.to_nat n)) (E - a) k Hb) by (rewrite ?zeros_length; lia).
  rewrite skipn_zeros, firstn_zeros by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_read_w : forall m a n (w : word) (E : Z) (k : nat),
  shz m a n -> bv_unsigned w = E -> (a <= E)%Z -> (E + Z.of_nat k <= a + n)%Z ->
  ov_read_bytes segs m w k = Some (zeros k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n w E k H Hw HaE Hk. replace w with (Z_to_bv 64 E).
  - eapply shz_read; eauto.
  - rewrite <- Hw. apply Z_to_bv_lit_self.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_write_other : forall m a n (c : Z) (bs : list byte),
  shz m a n -> (0 <= c)%Z -> (c + Z.of_nat (length bs) <= 2^64)%Z ->
  (a + n <= c \/ c + Z.of_nat (length bs) <= a)%Z ->
  shz (write_to_mem m (wa c) bs) a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n c bs [Hn Hb] Hc Hcl Hd. split; [exact Hn|].
  apply bytes_at_write_other; [exact Hb | lia | lia |]. rewrite zeros_length, Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_transport : forall W m m' a n,
  shz m a n -> munch W m m' -> disjoint_from W a n -> shz m' a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' a n [Hn Hb] MU Hd. split; [exact Hn|].
  eapply bytes_at_transport; [exact Hb | exact MU |]. rewrite zeros_length, Z2Nat.id by lia. exact Hd.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shz_of_bytes_at : forall m a bs,
  bytes_at segs m a bs -> Forall (fun b => b = Z_to_bv 8 0) bs -> shz m a (Z.of_nat (length bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a bs Hb Hall. split; [lia|]. rewrite Nat2Z.id.
  assert (E : zeros (length bs) = bs).
  { clear Hb. unfold zeros. induction Hall as [|b bs Hb0 Hall IH]; [reflexivity|]. cbn [length repeat]. rewrite IH, Hb0. reflexivity. }
  rewrite E. exact Hb.
Qed.

#[using="Type"] Lemma shz_of_ro_cells : forall m a cs,
  ro_cells segs m a cs -> Forall (fun b => b = Z_to_bv 8 0) (cells_bytes cs) ->
  shz m a (Z.of_nat (cells_size cs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a cs [Hwf Hb] Hall. rewrite <- (cells_bytes_length cs Hwf). apply shz_of_bytes_at; assumption.
Qed.

#[using="Type"] Lemma shz_of_rw_cells : forall m a cs,
  rw_cells segs m a cs -> Forall (fun b => b = Z_to_bv 8 0) (cells_bytes cs) ->
  shz m a (Z.of_nat (cells_size cs)).
Proof. LiaFast.lf_pins LiaFast.u0. intros m a cs [Hc _] Hall. apply shz_of_ro_cells; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8ro_of_shz : forall m a n, shz m a n -> u8ro segs m a (zeros (Z.to_nat n)).
Proof. LiaFast.lf_pins LiaFast.u0. intros m a n [_ Hb]. exact Hb. Qed.

#[using="Type"] Lemma ro_cells_of_shz : forall m a n, shz m a n -> ro_cells segs m a [CB (Z.to_nat n) (zeros (Z.to_nat n))].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n [_ Hb]. split; [cbn; split; [apply zeros_length| exact I]|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rdbl (m : word -> option byte) (a n : Z) : Prop :=
  (0 <= a)%Z /\ (a + n <= 2^64)%Z /\
  forall i, (0 <= i < n)%Z -> exists b, mrd segs m (wa (a + i)) = Some b.

#[using="Type"] Lemma rdbl_bound : forall m a n, rdbl m a n -> (0 <= a /\ a + n <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m a n (H1 & H2 & _). lia. Qed.

#[using="Type"] Lemma rdbl_mono : forall m m' a n, rdbl m a n -> wmono segs m m' -> rdbl m' a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' a n (H1 & H2 & H) WM. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as [b Hb]. unfold mrd in *.
  destruct (m (wa (a + i)%Z)) as [b0|] eqn:E0.
  - specialize (WM (wa (a + i)%Z)). rewrite E0 in WM.
    destruct (m' (wa (a + i)%Z)) as [b1|]; [exists b1; reflexivity|]. exfalso. apply WM; [discriminate|reflexivity].
  - destruct (m' (wa (a + i)%Z)) as [b1|]; [exists b1; reflexivity|]. exists b. exact Hb.
Qed.

#[using="Type"] Lemma rdbl_write : forall m a n w bs, rdbl m a n -> rdbl (write_to_mem m w bs) a n.
Proof. LiaFast.lf_pins LiaFast.u0. intros m a n w bs H. eapply rdbl_mono; [exact H | apply wmono_write_to_mem]. Qed.

#[using="Type"] Lemma rdbl_sub : forall m a n a' n', rdbl m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> rdbl m a' n'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

#[using="Type"] Lemma rdbl_bytes : forall m a n (E : Z) (k : nat),
  rdbl m a n -> (a <= E)%Z -> (E + Z.of_nat k <= a + n)%Z ->
  exists bs, length bs = k /\ bytes_at segs m E bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n E k (H1 & H2 & H) HaE Hk.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\
             forall i, (i < j)%nat -> mrd segs m (wa (E + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (E - a + Z.of_nat j)%Z ltac:(lia)) as [b Hb].
      replace (a + (E - a + Z.of_nat j))%Z with (E + Z.of_nat j)%Z in Hb by lia.
      exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i j).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G k ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. apply Hbs. rewrite <- Hlen. exact Hi.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdbl_read : forall m a n (E : Z) (k : nat),
  rdbl m a n -> (a <= E)%Z -> (E + Z.of_nat k <= a + n)%Z ->
  exists bs, length bs = k /\ ov_read_bytes segs m (Z_to_bv 64 E) k = Some bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n E k H HaE Hk. pose proof (rdbl_bound _ _ _ H) as B.
  destruct (rdbl_bytes m a n E k H HaE Hk) as (bs & Hlen & Hb).
  exists bs. split; [exact Hlen|].
  replace (Z_to_bv 64 E) with (wa (E + 0))%Z by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read segs m E bs 0 k Hb); [ | lia | rewrite Hlen; cbn; lia ].
  change (skipn (Z.to_nat 0) bs) with bs. rewrite firstn_all2 by lia. reflexivity.
Qed.

#[using="Type"] Lemma rdbl_of_bytes_at : forall m a bs, bytes_at segs m a bs -> rdbl m a (Z.of_nat (length bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a bs (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros i Hi. specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma rdbl_of_shz : forall m a n, shz m a n -> rdbl m a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n [Hn Hb]. pose proof (rdbl_of_bytes_at _ _ _ Hb) as R. rewrite zeros_length, Z2Nat.id in R by lia. exact R.
Qed.

#[using="Type"] Lemma rdbl_of_rw_cells : forall m a cs, rw_cells segs m a cs -> rdbl m a (Z.of_nat (cells_size cs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a cs [[Hwf Hb] _]. rewrite <- (cells_bytes_length cs Hwf). apply rdbl_of_bytes_at. exact Hb.
Qed.

#[using="Type"] Lemma rdbl_of_stk : forall m lo hi, stk segs m lo hi -> rdbl m lo (hi - lo).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (lo + i)%Z ltac:(lia)) as [_ Hb]. exact Hb.
Qed.

#[using="Type"] Lemma rdbl_app : forall m a n1 n2, rdbl m a n1 -> rdbl m (a + n1) n2 -> (0 <= n1)%Z -> rdbl m a (n1 + n2).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n1 n2 (A1 & A2 & A) (B1 & B2 & B) Hn. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.ltb_spec0 i n1).
  - apply A. lia.
  - replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply B. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_mono : forall m m' lo hi, stk segs m lo hi -> wmono segs m m' -> stk segs m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' lo hi (H1 & H2 & H) WM. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply (wmono_wview segs m m' WM); exact Hw|].
  unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:E0.
  - specialize (WM (wa a)). rewrite E0 in WM.
    destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity|]. exfalso. apply WM; [discriminate|reflexivity].
  - destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity|]. exists b. exact Hb.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shz_write_other_lit : forall segs m a (bs : list byte) X b A2 n2,
  store_ctx a (Z.of_nat (length bs)) X b -> shz segs m A2 n2 ->
  chk_lit b A2 n2 = true -> shz segs (write_to_mem m (wa a) bs) A2 n2.
Proof.
  intros segs m a bs X b A2 n2 (Ha & Hl & Hb) H Hc. apply shz_write_other; auto.
  pose proof (chk_lit_sound X a (a + Z.of_nat (length bs)) b A2 n2 Hb Hc). lia.
Qed.
Lemma shz_write_other_sb : forall segs m a (bs : list byte) X b c n2,
  store_ctx a (Z.of_nat (length bs)) X b -> shz segs m (X + c) n2 ->
  chk_sb b c n2 = true -> shz segs (write_to_mem m (wa a) bs) (X + c) n2.
Proof.
  intros segs m a bs X b c n2 (Ha & Hl & Hb) H Hc. apply shz_write_other; auto.
  pose proof (chk_sb_sound X a (a + Z.of_nat (length bs)) b c n2 Hb Hc). lia.
Qed.
Lemma shz_write_other_sb0 : forall segs m a (bs : list byte) X b n2,
  store_ctx a (Z.of_nat (length bs)) X b -> shz segs m X n2 ->
  chk_sb b 0 n2 = true -> shz segs (write_to_mem m (wa a) bs) X n2.
Proof.
  intros segs m a bs X b n2 (Ha & Hl & Hb) H Hc. apply shz_write_other; auto.
  pose proof (chk_sb0_sound X a (a + Z.of_nat (length bs)) b n2 Hb Hc). lia.
Qed.
Lemma shz_write_other_h : forall segs m a (bs : list byte) X b A2 n2,
  store_ctx a (Z.of_nat (length bs)) X b -> shz segs m A2 n2 ->
  (A2 + n2 <= a \/ a + Z.of_nat (length bs) <= A2)%Z -> shz segs (write_to_mem m (wa a) bs) A2 n2.
Proof. intros segs m a bs X b A2 n2 (Ha & Hl & Hb) H Hd. apply shz_write_other; auto. Qed.

Lemma shz_transport_lit : forall segs m m' X B A2 n2,
  call_ctx segs m m' X B -> shz segs m A2 n2 -> chks_lit B A2 n2 = true -> shz segs m' A2 n2.
Proof. intros segs m m' X B A2 n2 (W & MU & WM & HB) H Hc. eapply shz_transport; eauto. eapply chks_lit_sound; eauto. Qed.
Lemma shz_transport_sb : forall segs m m' X B c n2,
  call_ctx segs m m' X B -> shz segs m (X + c) n2 -> chks_sb B c n2 = true -> shz segs m' (X + c) n2.
Proof. intros segs m m' X B c n2 (W & MU & WM & HB) H Hc. eapply shz_transport; eauto. eapply chks_sb_sound; eauto. Qed.
Lemma shz_transport_sb0 : forall segs m m' X B n2,
  call_ctx segs m m' X B -> shz segs m X n2 -> chks_sb B 0 n2 = true -> shz segs m' X n2.
Proof. intros segs m m' X B n2 (W & MU & WM & HB) H Hc. eapply shz_transport; eauto. eapply chks_sb0_sound; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shr3_div : forall x, Z.shiftr x 3 = (x / 8)%Z.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac shr3 := rewrite ?shr3_div; repeat (rewrite unsigned_lit by lia).
Ltac shside := rewrite ?shr3_div; repeat (rewrite unsigned_lit by lia); lia.

Lemma div8_of_aligned_add : forall a i, (a mod 8 = 0)%Z -> ((a + i) / 8 = a / 8 + i / 8)%Z.
Proof. intros a i Ha. Z.div_mod_to_equations. nia. Qed.

Lemma mod8_of_aligned_add : forall a i, (a mod 8 = 0)%Z -> ((a + i) mod 8 = i mod 8)%Z.
Proof. intros a i Ha. Z.div_mod_to_equations. nia. Qed.

Lemma div8_lt_of_lt : forall x y, (0 <= x)%Z -> (x < y)%Z -> (y mod 8 = 0)%Z -> (x / 8 < y / 8)%Z.
Proof. intros x y Hx Hxy Hy. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zxb_lit : forall z, (0 <= z < 256)%Z -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma sxb_lit_pos : forall z, (0 <= z < 128)%Z -> sxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sxb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[Z.add Z.sub Z.modulo]. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sxb_lit_neg : forall z, (128 <= z < 256)%Z -> sxb (Z_to_bv 8 z) = Z_to_bv 64 (z - 256).
Proof.
  intros z Hz. unfold sxb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[Z.add Z.sub Z.modulo]. Z.div_mod_to_equations. lia.
Qed.
Lemma zxb_0 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0. Proof. apply zxb_lit. lia. Qed.
Lemma sxb_0 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0. Proof. apply sxb_lit_pos. lia. Qed.

(* [comment removed for export] *)
Lemma bv_lts_small : forall x y : word,
  (bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
  bv_lts x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed.
  pose proof (bv_unsigned_in_range 64 x). pose proof (bv_unsigned_in_range 64 y).
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)); try reflexivity; lia.
Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = (x mod 8)%Z.
Proof. intros. change 7%Z with (2^3 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, (0 <= x)%Z -> Z.land x (-8) = (x - x mod 8)%Z.
Proof.
  intros x Hx.
  change (-8)%Z with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac unwrap_lits := repeat (rewrite unsigned_lit by first [ lia | Z.div_mod_to_equations; lia ]).

(* [comment removed for export] *)
Ltac slow_blt_taken :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true;
      [ cbv iota
      | symmetry; rewrite ?land7_mod8; rewrite bv_lts_small by (unwrap_lits; Z.div_mod_to_equations; lia);
        unwrap_lits; apply Z.ltb_lt; Z.div_mod_to_equations; lia ]
  end.
Ltac slow_bge_not_taken :=   (* [comment removed for export] *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; rewrite ?land7_mod8; rewrite bv_lts_small by (unwrap_lits; Z.div_mod_to_equations; lia);
        unwrap_lits; apply Bool.negb_false_iff; apply Z.ltb_lt; Z.div_mod_to_equations; lia ]
  end.

(* [comment removed for export] *)
Ltac fold_byte_lits :=
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 ?z)] => is_Zlit z; rewrite (zxb_lit z) by lia
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z;
      first [ rewrite (sxb_lit_pos z) by lia | rewrite (sxb_lit_neg z) by lia; fold_closed_in_goal ]
  end.

(* [comment removed for export] *)
Ltac zlit_small k :=
  let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 65536))%Z in
  lazymatch ok with true => k end.

(* [comment removed for export] *)
Ltac sum_split e :=
  lazymatch e with
  | Z.add ?a ?b =>
      let ra := sum_split a in let rb := sum_split b in
      lazymatch ra with (?la, ?ca) =>
      lazymatch rb with (?lb, ?cb) =>
        let c := eval vm_compute in (ca + cb)%Z in
        let l := sum_cat la lb in constr:((l, c))
      end end
  | Z.sub ?a ?b =>
      lazymatch b with
      | Z0 => sum_split a
      | Zpos _ => let ra := sum_split a in
                  lazymatch ra with (?la, ?ca) => let c := eval vm_compute in (ca - b)%Z in constr:((la, c)) end
      | Zneg _ => let ra := sum_split a in
                  lazymatch ra with (?la, ?ca) => let c := eval vm_compute in (ca - b)%Z in constr:((la, c)) end
      | _ => constr:(((e, tt), 0%Z))
      end
  | Z0 => constr:((tt, e))
  | Zpos _ => constr:((tt, e))
  | Zneg _ => constr:((tt, e))
  | _ => constr:(((e, tt), 0%Z))
  end
with sum_cat la lb :=
  lazymatch la with
  | tt => lb
  | (?x, ?rest) => let r := sum_cat rest lb in constr:((x, r))
  end.

(* [comment removed for export] *)
Ltac sum_remove x l :=
  lazymatch l with
  | (x, ?rest) => rest
  | (?y, ?rest) => let r := sum_remove x rest in constr:((y, r))
  end.

(* [comment removed for export] *)
Ltac sum_same la lb :=
  lazymatch la with
  | tt => lazymatch lb with tt => constr:(tt) end
  | (?x, ?rest) => let lb' := sum_remove x lb in sum_same rest lb'
  end.

Ltac addr_diff E A ::=
  let re := sum_split E in let ra := sum_split A in
  lazymatch re with (?le, ?ce) =>
  lazymatch ra with (?la, ?ca) =>
    let ok := sum_same le la in
    let k := eval vm_compute in (ce - ca)%Z in
    zlit_small k
  end end.

(* [comment removed for export] *)
Ltac fold_closed_in_goal ::=
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
  | |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
  | |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
  | |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
        replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
        replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
        replace (bv_swrap n z) with v by (vm_compute; reflexivity)
  | |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.div ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.div a b) in change (Z.div a b) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
        replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
  | |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
  end.

(* [comment removed for export] *)
Ltac fold_ext_lit :=
  repeat match goal with
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_Zlit z; let t := constr:(zx32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let t := constr:(sx32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [zxb (Z_to_bv 8 ?z)] => is_Zlit z; rewrite (zxb_lit z) by lia
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z;
      first [ rewrite (sxb_lit_pos z) by lia | rewrite (sxb_lit_neg z) by lia; fold_closed_in_goal ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kp_sha_rng a :=
  lazymatch a with
  | Z_to_bv 64 ?E =>
      lazymatch E with context [Z.shiftr _ 3] => fail | _ => idtac end;
      let T := type of (unsigned_lit E) in
      lazymatch T with ?P -> _ => assert_succeeds (assert P by lia) end
  end.
Ltac kp_sha_syn b n k :=
  lazymatch constr:((b, n, k)) with
  | context [Z.shiftr _ 3] => fail
  | context [bv_unsigned (Z_to_bv 64 _)] => fail
  | _ => idtac
  end.
Ltac solve_load_shadow :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?k] =>
      tryif kp_sha_rng a then
        match goal with
        | H : shz segs m ?b ?n |- _ =>
            first
              [ lazymatch a with
                | Z_to_bv 64 ?E => rewrite (shz_read segs m b n E k H) by shside
                | wa ?E => rewrite (shz_read segs m b n E k H) by shside
                end
              | tryif kp_sha_syn b n k then fail
                else erewrite (shz_read_w segs m b n a _ k H) by (first [reflexivity | shside]) ]
        end
      else
        match goal with
        | H : shz segs m ?b ?n |- _ =>
            first
              [ lazymatch a with
                | Z_to_bv 64 ?E => rewrite (shz_read segs m b n E k H) by shside
                | wa ?E => rewrite (shz_read segs m b n E k H) by shside
                end
              | erewrite (shz_read_w segs m b n a _ k H) by (first [reflexivity | shside]) ]
        end
  end;
  cbv beta iota delta [zeros repeat];
  load_post; fold_byte_lits.

Ltac solve_load ::= first [ solve_load_base; fold_byte_lits; fold_ext_lit | solve_load_image; fold_ext_lit | solve_load_shadow ].

(* [comment removed for export] *)
Ltac lit_cond c :=
  lazymatch c with
  | negb ?c' => lit_cond c'
  | bv_eqb (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_lts (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_leu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  end.
Ltac decide_lit_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lit_cond c;
      let v := eval vm_compute in c in
      replace c with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
Ltac step ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac transport_chunks_sc_extra segs m a bs SC X b ::=
  match goal with
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ tr_lit H (shz_write_other_lit segs m a bs X b A2 n2 SC) b A2 n2
            | tr_sb H (shz_write_other_sb segs m a bs X b) (shz_write_other_sb0 segs m a bs X b) chk_sb b X A2 n2 SC
            | apply (shz_write_other_h segs m a bs X b A2 n2 SC) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_write segs m A2 n2 (wa a) bs) in H
  end.
Ltac transport_chunks_orig_extra segs m a bs ::=
  match goal with
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ apply (shz_write_other segs m A2 n2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_write segs m A2 n2 (wa a) bs) in H
  end.

Ltac transport_after_call_orig_A segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call_cc_A segs m m' MU WM CC X B :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lits H (bytes_at_transport_lit segs m m' X B A2 bs2 CC) B A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2)) CC
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z) CC
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z) CC
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : shz segs m ?A2 ?n2 |- _ =>
      first [ tr_lits H (shz_transport_lit segs m m' X B A2 n2 CC) B A2 n2
            | tr_sb H (shz_transport_sb segs m m' X B) (shz_transport_sb0 segs m m' X B) chks_sb B X A2 n2 CC
            | apply (shz_transport segs W m m' A2 n2) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ => apply (stk_mono segs m m' loq hiq) in H; [ | exact WM ]
  | H : rdbl segs m ?A2 ?n2 |- _ => apply (rdbl_mono segs m m' A2 n2) in H; [ | exact WM ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ tr_lits_pr H (pristine_transport_lit segs m m' X B lo hi CC) B lo hi
            | apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM ::=
  call_ctx_pose segs m m' MU WM ltac:(lia)
    ltac:(fun CC X B => transport_after_call_cc_A segs m m' MU WM CC X B)
    ltac:(transport_after_call_orig_A segs m m' MU WM).

(* [comment removed for export] *)
Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  lazymatch type of PO with
  | _ /\ _ => destruct PO as [MIc PO]
  | _ => rename PO into MIc
  end;
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in
      change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kp_sas_pre5 := match goal with
  | |- context [length (u32s _)] => idtac | |- context [length (u64s _)] => idtac | |- context [length (upd _ _ _)] => idtac
  | |- context [length (zeros _)] => idtac | |- context [length (List.repeat _ _)] => idtac
  | _ : context [length (u32s _)] |- _ => idtac | _ : context [length (u64s _)] |- _ => idtac | _ : context [length (upd _ _ _)] |- _ => idtac
  | _ : context [length (zeros _)] |- _ => idtac | _ : context [length (List.repeat _ _)] |- _ => idtac
  end.
Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length in *) else idtac.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stashed (P : Prop) : Prop := P.

Ltac stash H := lazymatch type of H with ?T => change (stashed T) in H end.

Ltac unstash_all MU WM :=
  lazymatch type of MU with
  | munch ?W ?m ?m' =>
      lazymatch goal with
      | |- evt ?segs _ _ =>
          repeat match goal with
          | H : stashed ?T |- _ => unfold stashed in H
          end;
          transport_after_call segs m m' MU WM
      end
  end.
