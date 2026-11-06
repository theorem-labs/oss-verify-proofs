(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the instruction walk of check_value (fuzz_uci.c), the
   plain image's 0x12dc4, against lib/Prog/check_value_c.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YL0i YL00 YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_uci_int_c check_no_overread_c
  check_value_c memcpy_c FuzzDup CheckGlue KindB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  Tac ZBridge.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- list helpers ---------------- *)

Lemma skipn_nth_cons : forall (l : list Z) (i : nat), (i < length l)%nat ->
  skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [|c t IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [skipn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma first_line_nth : forall (l : list Z) i, (i < length (first_line l))%nat ->
  nth i (first_line l) 0 = nth i l 0.
Proof.
  induction l as [|c t IH]; intros i Hi; [cbn in Hi; lia|].
  cbn [first_line] in Hi |- *. destruct (c =? 10); [cbn in Hi; lia|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. cbn [length] in Hi. lia.
Qed.

Lemma first_line_le : forall (l : list Z), (length (first_line l) <= length l)%nat.
Proof.
  induction l as [|c t IH]; cbn [first_line length]; [lia|].
  destruct (c =? 10); cbn [length]; lia.
Qed.

(* ---------------- bit-level helpers ---------------- *)

Lemma u8lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite u8lit by exact Hc. reflexivity. Qed.

(* the {9, 13, 32} bit mask of the trailing-blank loop *)
Lemma mask_bit : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr 4294976000 c) 1 = (if is_trail_blank c then 1 else 0).
Proof.
  intros c Hc.
  assert (E : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/
              c = 31 \/ c = 32) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity|]). subst c. vm_compute. reflexivity.
Qed.

Lemma shr_rng : forall c, 0 <= c -> 0 <= Z.shiftr 4294976000 c < 2 ^ 64.
Proof.
  intros c Hc. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc) as Hp.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with 4294976000; [|lia].
  apply Z.div_le_upper_bound; [lia | nia].
Qed.

Lemma mask_u : forall c, 0 <= c <= 32 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294976000 c))) 1 = (if is_trail_blank c then 1 else 0).
Proof.
  intros c Hc. rewrite (unsigned_lit _ (shr_rng c ltac:(lia))). apply mask_bit. exact Hc.
Qed.


(* the 32-bit sign extension the `sext.w` of the int-range test leaves behind *)
Lemma swrap32 : forall x, bv_swrap 32 x = (x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). reflexivity.
Qed.
(* the sign-extension test of the int-range check *)
Lemma sx32_lit : forall x, bv_unsigned (sx32 (Z_to_bv 64 x)) = ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64.
Proof.
  intros x. unfold sx32. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite unsigned_lit_wrap.
  f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_self : forall x, INT_MIN <= x <= INT_MAX -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold INT_MIN, INT_MAX in Hx. apply bv_eq. rewrite sx32_lit, unsigned_lit_wrap.
  f_equal. Z.div_mod_to_equations. lia.
Qed.

(* ---------------- the digit value stays in a machine word ---------------- *)

Lemma digits_ev_rng : forall l v, 0 <= v < 10 ^ 11 -> 0 <= fst (digits_ev v l) < 10 ^ 11.
Proof.
  induction l as [|c t IH]; intros v Hv; cbn [digits_ev fst]; [exact Hv|].
  destruct (is_digit c) eqn:D; [|cbn; exact Hv].
  unfold is_digit in D. apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
  apply IH. destruct (Z.ltb_spec v (10 ^ 10)); lia.
Qed.

Lemma fl_nl : forall c t, c = 10 -> first_line (c :: t) = [].
Proof. intros c t ->. reflexivity. Qed.

Lemma fl_other : forall c t, c <> 10 -> first_line (c :: t) = c :: first_line t.
Proof. intros c t H. cbn [first_line]. rewrite (proj2 (Z.eqb_neq c 10) H). reflexivity. Qed.

Lemma skip_t : forall f c t, f c = true -> skip f (c :: t) = skip f t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma skip_f : forall f c t, f c = false -> skip f (c :: t) = c :: t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma lb_32 : forall c, c = 32 -> is_lead_blank c = true.
Proof. intros c ->. reflexivity. Qed.

Lemma lb_9 : forall c, c = 9 -> is_lead_blank c = true.
Proof. intros c ->. reflexivity. Qed.

Lemma tb_of : forall c, c = 32 \/ c = 9 \/ c = 13 -> is_trail_blank c = true.
Proof. intros c [->|[->| ->]]; reflexivity. Qed.

Lemma digit_land : forall c, is_digit c = true -> Z.land c 15 = c - 48.
Proof.
  intros c D. unfold is_digit in D. apply andb_true_iff in D as [D1 D2].
  apply Z.leb_le in D1. apply Z.leb_le in D2.
  change 15 with (2 ^ 4 - 1). rewrite zb_land_mask by lia. change (2 ^ 4) with 16. mlia.
Qed.

Lemma digits_ev_stop : forall v c t, is_digit c = false -> digits_ev v (c :: t) = (v, c :: t).
Proof. intros v c t D. cbn [digits_ev]. rewrite D. reflexivity. Qed.


Lemma ss_fst : forall c t, fst (sign_split (c :: t)) = (c =? 45).
Proof.
  intros c t. cbn [sign_split]. destruct ((c =? 43) || (c =? 45))%bool eqn:E; cbn [fst]; [reflexivity|].
  apply orb_false_iff in E as [_ E2]. symmetry. exact E2.
Qed.

Lemma finish_nil : forall neg v rest cur0, skip is_trail_blank rest = [] ->
  finish neg v rest cur0 = (if ((if neg then - v else v) <? INT_MIN) || (INT_MAX <? (if neg then - v else v))
                            then cur0 else (if neg then - v else v)).
Proof. intros neg v rest cur0 H. unfold finish. rewrite H. reflexivity. Qed.

Lemma finish_rest : forall neg v rest cur0, skip is_trail_blank rest <> [] -> finish neg v rest cur0 = cur0.
Proof.
  intros neg v rest cur0 H. unfold finish.
  destruct (skip is_trail_blank rest); [contradiction | reflexivity].
Qed.

Lemma skipn_inj : forall (l : list Z) i j, (i <= length l)%nat -> (j <= length l)%nat ->
  skipn i l = skipn j l -> i = j.
Proof.
  intros l i j Hi Hj H.
  assert (E : length (skipn i l) = length (skipn j l)) by (rewrite H; reflexivity).
  rewrite !length_skipn in E. lia.
Qed.

Lemma digits_ev_step : forall v c t, is_digit c = true ->
  digits_ev v (c :: t) = digits_ev (if v <? 10 ^ 10 then v * 10 + (c - 48) else v) t.
Proof. intros v c t D. cbn [digits_ev]. rewrite D. reflexivity. Qed.

Lemma ss_plus : forall c t, c = 43 -> sign_split (c :: t) = (false, t).
Proof. intros c t ->. reflexivity. Qed.

Lemma ss_minus : forall c t, c = 45 -> sign_split (c :: t) = (true, t).
Proof. intros c t ->. reflexivity. Qed.

Lemma ss_none : forall c t, c <> 43 -> c <> 45 -> sign_split (c :: t) = (false, c :: t).
Proof.
  intros c t H1 H2. cbn [sign_split].
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

Definition nthz (l : list Z) (i : Z) : Z := nth (Z.to_nat i) l 0.

Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  rewrite ?swrap32; decide_tests; reflexivity.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv beta iota | symmetry; solve_c]
  end.
Ltac fact := cbv delta [zxb]; wsub; rewrite ?unsigned_lit_wrap; mlia.
(* the same, for a register whose value the walk built from literal shifts (the two mask constants) *)
Ltac factw := zsimp; wsub; zsimp; mlia.

(* ---------------- the inlined expected_value, 0x12e24 - 0x12f50 ---------------- *)

Section Ev.
Variables (ra sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (r n cur e : Z) (zs : list Z) (Q : machine_state -> Prop).
Hypothesis HR0 : 4096 <= r.
Hypothesis HRN : r + n < 2 ^ 64.
Hypothesis HN : 0 < n <= 255.
Hypothesis HL : Z.of_nat (length zs) = n.
Hypothesis BR : forall i, 0 <= nthz zs i < 256.
Hypothesis RD : forall i, 0 <= i < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (r + i)) 1 = Some [Z_to_bv 8 (nthz zs i)].
Hypothesis CUR : INT_MIN <= cur <= INT_MAX.
Hypothesis HE : Z.of_nat (length (first_line zs)) = e.
Hypothesis S0 : bv_unsigned s0 = cur mod 2 ^ 64.

Local Notation ST pc a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 r) (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma sfx_cons : forall i, 0 <= i < n -> skipn (Z.to_nat i) zs = nthz zs i :: skipn (Z.to_nat (i + 1)) zs.
Proof.
  intros i Hi. unfold nthz. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply skipn_nth_cons. lia.
Qed.

Lemma eloc : 0 <= e <= n.
Proof. pose proof (first_line_le zs) as H. lia. Qed.

(* the scan for the first '\n': 0x12e2c, a0 the index *)
Lemma loop_nl :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), bv_unsigned a0 = e -> e < n ->
     evt rsegs Q (ST 0x12e5c a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), bv_unsigned a0 = n -> e = n ->
     evt rsegs Q (ST 0x12e60 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  forall k i (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word),
  0 <= i -> i + Z.of_nat (S k) = n ->
  e = i + Z.of_nat (length (first_line (skipn (Z.to_nat i) zs))) ->
  bv_unsigned a0 = i -> bv_unsigned a1 = 10 ->
  evt rsegs Q (ST 0x12e2c a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros K5 K6 k. induction k as [|k IH]; intros i a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 Hi0 Hk Hinv Ha0 Ha1.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (sfx_cons i Hin) in Hinv.
  all: step.
  all: pose proof (RD i Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR i)).
  all: destruct (Z.eq_dec (nthz zs i) 10) as [Ec|Ec].
  - rewrite (fl_nl _ _ Ec) in Hinv. cbn [length] in Hinv.
    assert (Ei : e = i) by lia.
    step. take true. apply K5; [rewrite Ei; exact Ha0 | lia].
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [first_line length] in Hinv.
    step. take false. step. step. take false.
    do 2 step. apply K6; [fact | lia].
  - rewrite (fl_nl _ _ Ec) in Hinv. cbn [length] in Hinv.
    assert (Ei : e = i) by lia.
    step. take true. apply K5; [rewrite Ei; exact Ha0 | lia].
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    step. take false. step. step. take true.
    apply (IH (i + 1)); [lia | lia | lia | fact | exact Ha1].
Qed.

Lemma fl_nth_zs : forall j, 0 <= j < e -> nthz (first_line zs) j = nthz zs j.
Proof. intros j Hj. unfold nthz. apply first_line_nth. lia. Qed.

Lemma flsfx_cons : forall j, 0 <= j < e ->
  skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs).
Proof.
  intros j Hj. rewrite <- (fl_nth_zs j Hj). unfold nthz.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply skipn_nth_cons. lia.
Qed.

(* the leading-blank skip: 0x12e6c, a3 the index *)
Lemma loop_lb :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), skip is_lead_blank (first_line zs) = [] ->
     evt rsegs Q (ST 0x12f50 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word) j,
     bv_unsigned a0 = e -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j -> 0 <= j < e ->
     skip is_lead_blank (first_line zs) = skipn (Z.to_nat j) (first_line zs) ->
     is_lead_blank (nthz zs j) = false ->
     evt rsegs Q (ST 0x12e88 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  forall k j (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word),
  0 <= j -> j + Z.of_nat (S k) = e ->
  skip is_lead_blank (first_line zs) = skip is_lead_blank (skipn (Z.to_nat j) (first_line zs)) ->
  bv_unsigned a0 = e -> bv_unsigned a2 = 32 -> bv_unsigned a4 = 9 -> bv_unsigned a3 = j ->
  evt rsegs Q (ST 0x12e6c a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros KB KN k. induction k as [|k IH]; intros j a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 Hj0 Hk Hinv Ha0 Ha2 Ha4 Ha3.
  all: pose proof eloc as Hel.
  all: assert (Hje : 0 <= j < e) by lia.
  all: assert (Hin : 0 <= j < n) by lia.
  all: pose proof (BR j) as Hb.
  all: rewrite (flsfx_cons j Hje) in Hinv.
  all: step.
  all: pose proof (RD j Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR j)).
  all: destruct (Z.eq_dec (nthz zs j) 32) as [E32|E32];
       [ | destruct (Z.eq_dec (nthz zs j) 9) as [E9|E9] ].
  (* k = 0 *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    step. take true. step. step. take false. step. apply KB. exact Hinv.
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    step. take false. step. take false. step. step. take false. step. apply KB. exact Hinv.
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    step. take false. step. take true.
    apply (KN _ _ _ _ _ _ _ _ _ _ j); [exact Ha0 | fact | exact Ha3 | lia | | exact Hnb].
    rewrite Hinv. symmetry. apply flsfx_cons. lia.
  (* k = S k *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    step. take true. step. step. take true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha0 | exact Ha2 | exact Ha4 | fact].
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    step. take false. step. take false. step. step. take true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha0 | exact Ha2 | exact Ha4 | fact].
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    step. take false. step. take true.
    apply (KN _ _ _ _ _ _ _ _ _ _ j); [exact Ha0 | fact | exact Ha3 | lia | | exact Hnb].
    rewrite Hinv. symmetry. apply flsfx_cons. lia.
Qed.

(* the optional sign: 0x12e88 - 0x12e9c.  d0 = j + (sign ? 1 : 0), and the model's list after the sign is
   skipn d0 (first_line zs) in both cases *)
Lemma seg_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word) j,
  bv_unsigned a0 = e -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j -> 0 <= j < e ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' : word) d0,
     bv_unsigned a0' = e -> bv_unsigned a1' = nthz zs j -> bv_unsigned a3' = d0 -> j <= d0 < e ->
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat d0) (first_line zs) ->
     evt rsegs Q (ST 0x12ea0 a0' a1' a2' a3' a4' a5' a6' a7' t0' t1')) ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' : word),
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = [] ->
     evt rsegs Q (ST 0x12f50 a0' a1' a2' a3' a4' a5' a6' a7' t0' t1')) ->
  evt rsegs Q (ST 0x12e88 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 j Ha0 Ha1 Ha3 Hje KD KZ.
  pose proof (BR j) as Hb. pose proof eloc as Hel.
  assert (SP : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx_cons; lia).
  destruct (Z.eq_dec (nthz zs j) 43) as [E43|E43].
  { (* '+' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_plus _ _ E43); reflexivity).
    step. step. take true. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - take true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - take false. apply (KD _ _ _ _ _ _ _ _ _ _ (j + 1)); [exact Ha0 | exact Ha1 | fact | lia | exact SG]. }
  destruct (Z.eq_dec (nthz zs j) 45) as [E45|E45].
  { (* '-' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_minus _ _ E45); reflexivity).
    step. step. take false. step. step. take false. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - take true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - take false. apply (KD _ _ _ _ _ _ _ _ _ _ (j + 1)); [exact Ha0 | exact Ha1 | fact | lia | exact SG]. }
  (* no sign *)
  assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat j) (first_line zs))
    by (rewrite SP at 1; rewrite (ss_none _ _ E43 E45); rewrite <- SP; reflexivity).
  step. step. take false. step. step. take true. step. take false.
  apply (KD _ _ _ _ _ _ _ _ _ _ j); [exact Ha0 | exact Ha1 | exact Ha3 | lia | exact SG].
Qed.

(* the digit loop: 0x12ebc, a4 the index, a2 the value *)
Lemma loop_dg : forall d0 (a0 a1 a3 : word),
  bv_unsigned a3 = d0 -> bv_unsigned a0 = e ->
  (forall (a2 a4 a5 a6 a7 t0 t1 : word) i vf,
     bv_unsigned a4 = i -> bv_unsigned a2 = vf -> 0 <= vf < 10 ^ 11 -> d0 <= i <= e ->
     digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
     (i = d0 /\ is_digit (nthz zs d0) = false) \/ d0 < i ->
     evt rsegs Q (ST 0x12ee8 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  forall k i v (a2 a4 a5 a6 a7 t0 t1 : word),
  0 <= d0 <= i -> i + Z.of_nat (S k) = e -> 0 <= v < 10 ^ 11 ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = digits_ev v (skipn (Z.to_nat i) (first_line zs)) ->
  bv_unsigned a4 = i -> bv_unsigned a2 = v -> bv_unsigned a5 = 9 -> bv_unsigned a6 = 10 ->
  bv_unsigned a7 = 10 ^ 10 ->
  evt rsegs Q (ST 0x12ebc a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros d0 a0 a1 a3 Ha3 Ha0 K k. induction k as [|k IH];
    intros i v a2 a4 a5 a6 a7 t0 t1 Hd0 Hk Hv Hinv Ha4 Ha2 Ha5 Ha6 Ha7.
  all: pose proof eloc as Hel.
  all: assert (Hie : 0 <= i < e) by lia.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (flsfx_cons i Hie) in Hinv.
  all: step.
  all: pose proof (RD i Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR i)).
  all: step.
  all: destruct (is_digit (nthz zs i)) eqn:Dg;
       [ assert (Dgr : 48 <= nthz zs i <= 57) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_true_iff in D as [D1 D2]; apply Z.leb_le in D1; apply Z.leb_le in D2; lia)
       | assert (Dgr : nthz zs i < 48 \/ 57 < nthz zs i) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_false_iff in D as [D1|D1]; apply Z.leb_gt in D1; [left | right]; lia) ].
  (* k = 0, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    step. take false. step.
    destruct (Z.ltb_spec v (10 ^ 10)) as [Hlt|Hlt].
    + take false. step. step.
      rewrite (unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. take false. step.
      apply (K _ _ _ _ _ _ _ e (v * 10 + (nthz zs i - 48))); [fact | fact | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
    + take true. step. step. take false. step.
      apply (K _ _ _ _ _ _ _ e v); [fact | fact | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
  (* k = 0, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    step. take true.
    apply (K _ _ _ _ _ _ _ i v); [exact Ha4 | exact Ha2 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
  (* k = S k, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    step. take false. step.
    destruct (Z.ltb_spec v (10 ^ 10)) as [Hlt|Hlt].
    + take false. step. step.
      rewrite (unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. take true.
      apply (IH (i + 1) (v * 10 + (nthz zs i - 48)));
        [lia | lia | lia | exact Hinv | fact | fact | exact Ha5 | exact Ha6 | exact Ha7].
    + take true. step. step. take true.
      apply (IH (i + 1) v);
        [lia | lia | lia | exact Hinv | fact | exact Ha2 | exact Ha5 | exact Ha6 | exact Ha7].
  (* k = S k, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    step. take true.
    apply (K _ _ _ _ _ _ _ i v); [exact Ha4 | exact Ha2 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
Qed.

(* the trailing-blank loop: 0x12f0c, a3 = -p, a4 = r + p, a5 = -e *)
Lemma loop_tb : forall i_f (a0 a1 a2 a6 a7 t1 : word),
  bv_unsigned a0 = e -> bv_unsigned a6 = 32 -> bv_unsigned a7 = 4294976000 ->
  (forall (a3 a4 a5 t0 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     evt rsegs Q (ST 0x12f38 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  (forall (a3 a4 a5 t0 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     evt rsegs Q (ST 0x12f50 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  forall k p (a3 a5 t0 : word),
  0 <= p -> p + Z.of_nat (S k) = e ->
  skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) =
    skip is_trail_blank (skipn (Z.to_nat p) (first_line zs)) ->
  bv_unsigned a3 = (0 - p) mod 2 ^ 64 -> bv_unsigned a5 = (0 - e) mod 2 ^ 64 ->
  evt rsegs Q (ST 0x12f0c a0 a1 a2 a3 (Z_to_bv 64 (r + p)) a5 a6 a7 t0 t1).
Proof.
  intros i_f a0 a1 a2 a6 a7 t1 Ha0 Ha6 Ha7 KE KN k. induction k as [|k IH];
    intros p a3 a5 t0 Hp0 Hk Hinv Ha3 Ha5.
  all: pose proof eloc as Hel.
  all: assert (Hpe : 0 <= p < e) by lia.
  all: assert (Hpn : 0 <= p < n) by lia.
  all: pose proof (BR p) as Hb.
  all: rewrite (flsfx_cons p Hpe) in Hinv.
  all: pose proof (RD p Hpn) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR p)).
  all: step.
  all: destruct (Z_le_gt_dec (nthz zs p) 32) as [H32|H32];
       [ take false; step; rewrite Ha7;
         rewrite (unsigned_lit (nthz zs p)) by lia; rewrite (Z.mod_small (nthz zs p) 64) by lia;
         step; rewrite (mask_u (nthz zs p) ltac:(lia));
         destruct (is_trail_blank (nthz zs p)) eqn:Tb; cbv beta iota; step
       | take true ].
  (* k = 0: blank, end reached *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    take false. step. step. step. take false. step.
    apply KE. rewrite Hinv, skipn_all2 by lia. reflexivity.
  (* k = 0: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    take true. step. step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = 0: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false).
    { unfold is_trail_blank.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 32)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 9)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 13)) by lia. reflexivity. }
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: blank, loop *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    take false. step. step.
    rewrite ?(unsigned_lit (r + p)) by lia. replace (r + p + 1) with (r + (p + 1)) by lia.
    step. take true.
    apply (IH (p + 1)); [lia | lia | exact Hinv | fact | exact Ha5].
  (* k = S k: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    take true. step. step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false).
    { unfold is_trail_blank.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 32)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 9)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 13)) by lia. reflexivity. }
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. step. take true.
    apply KN. rewrite Hinv. discriminate.
Qed.

(* the entry of the trailing scan: 0x12eec *)
Lemma seg_trail : forall i_f (a0 a1 a2 t1 : word),
  bv_unsigned a0 = e -> 0 <= i_f <= e ->
  (forall (a3 a4 a5 a6 a7 t0 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     evt rsegs Q (ST 0x12f38 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  (forall (a3 a4 a5 a6 a7 t0 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     evt rsegs Q (ST 0x12f50 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1)) ->
  forall (a3 a4 a5 a6 a7 t0 : word), bv_unsigned a4 = i_f ->
  evt rsegs Q (ST 0x12eec a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros i_f a0 a1 a2 t1 Ha0 Hif KE KN a3 a4 a5 a6 a7 t0 Ha4.
  pose proof eloc as Hel.
  step. destruct (Z.eq_dec i_f e) as [Ee|Ee].
  - take true. step. take false. apply KE. rewrite Ee, skipn_all2 by lia. reflexivity.
  - take false. step. step. step.
    rewrite ?(unsigned_lit r) by lia. rewrite Ha4.
    do 4 step.
    eapply (loop_tb i_f a0 a1 a2 _ _ t1 Ha0) with (k := Z.to_nat (e - i_f - 1)) (p := i_f).
    all: first [ lia | reflexivity | factw
               | intros A3 A4 A5 T0 HH;
                 first [ apply (KE A3 A4 A5 _ _ T0 HH) | apply (KN A3 A4 A5 _ _ T0 HH) ] ].
Qed.

(* ---- the model, read through the projections the walk produces ---- *)

Notation SKL := (skip is_lead_blank (first_line zs)).

Lemma ev_val : expected_value_m zs cur =
  match snd (sign_split SKL) with
  | c :: _ => if is_digit c
              then finish (fst (sign_split SKL)) (fst (digits_ev 0 (snd (sign_split SKL))))
                     (snd (digits_ev 0 (snd (sign_split SKL)))) cur
              else cur
  | [] => cur
  end.
Proof.
  unfold expected_value_m. destruct (sign_split SKL) as [neg l]. cbn [fst snd].
  destruct l as [|c t]; [reflexivity|]. destruct (is_digit c); [|reflexivity].
  destruct (digits_ev 0 (c :: t)) as [v rest]. cbn [fst snd]. reflexivity.
Qed.

Lemma ev_cur_nil : snd (sign_split SKL) = [] -> expected_value_m zs cur = cur.
Proof. intros H. rewrite ev_val, H. reflexivity. Qed.

Lemma ev_cur_nodigit : forall c l, snd (sign_split SKL) = c :: l -> is_digit c = false ->
  expected_value_m zs cur = cur.
Proof. intros c l H D. rewrite ev_val, H, D. reflexivity. Qed.

Lemma ev_fin : forall c l vf rest, snd (sign_split SKL) = c :: l -> is_digit c = true ->
  digits_ev 0 (c :: l) = (vf, rest) ->
  expected_value_m zs cur = finish (fst (sign_split SKL)) vf rest cur.
Proof.
  intros c l vf rest H D E. rewrite ev_val, H, D, E. cbn [fst snd]. reflexivity.
Qed.

(* ---- the walk from 0x12e24 to 0x12f50 ---- *)

Local Notation STS pc s0' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 r) (Z_to_bv 64 n) s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Hypothesis KFIN : forall (s0' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word),
  bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
  evt rsegs Q (STS 0x12f50 s0' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).

Lemma ev_cur : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), expected_value_m zs cur = cur ->
  evt rsegs Q (ST 0x12f50 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof. intros. apply KFIN. rewrite H. exact S0. Qed.

(* the sign and the int-range test: 0x12f38 - 0x12f4c *)
Lemma ev_tail : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word) c0 v rest,
  0 <= c0 < 256 -> 0 <= v < 10 ^ 11 -> skip is_trail_blank rest = [] ->
  bv_unsigned a1 = c0 -> bv_unsigned a2 = v ->
  finish (c0 =? 45) v rest cur = expected_value_m zs cur ->
  evt rsegs Q (ST 0x12f38 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 c0 v rest Hc0 Hv Ht Ha1 Ha2 HM.
  rewrite (finish_nil _ _ _ _ Ht) in HM.
  step. step. destruct (Z.eq_dec c0 45) as [E45|E45].
  - rewrite E45, Z.eqb_refl in HM.
    take false. step. step.
    destruct (Z.ltb_spec (- v) INT_MIN) as [Hlo|Hlo];
      [ idtac | destruct (Z.ltb_spec INT_MAX (- v)) as [Hhi|Hhi] ];
      cbv beta iota delta [orb] in HM; unfold INT_MIN, INT_MAX in *.
    + step. take true. apply KFIN. rewrite <- HM. exact S0.
    + exfalso. lia.
    + step. take false. step. apply KFIN. rewrite <- HM. fact.
  - rewrite (proj2 (Z.eqb_neq c0 45) E45) in HM.
    take true. step.
    destruct (Z.ltb_spec v INT_MIN) as [Hlo|Hlo];
      [ idtac | destruct (Z.ltb_spec INT_MAX v) as [Hhi|Hhi] ];
      cbv beta iota delta [orb] in HM; unfold INT_MIN, INT_MAX in *.
    + exfalso. lia.
    + step. take true. apply KFIN. rewrite <- HM. exact S0.
    + step. take false. step. apply KFIN. rewrite <- HM. fact.
Qed.

(* 0x12ee8: `i == d0` is the harness's `no digit read` test *)
Lemma ev_ee8 : forall (a0 a1 a3 : word) d0 c0,
  bv_unsigned a0 = e -> bv_unsigned a1 = c0 -> bv_unsigned a3 = d0 ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  forall (a2 a4 a5 a6 a7 t0 t1 : word) i vf,
  bv_unsigned a4 = i -> bv_unsigned a2 = vf -> 0 <= vf < 10 ^ 11 -> d0 <= i <= e ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
  (i = d0 /\ is_digit (nthz zs d0) = false) \/ d0 < i ->
  evt rsegs Q (ST 0x12ee8 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a3 d0 c0 Ha0 Ha1 Ha3 Hc0 Hd0 HL2 HF a2 a4 a5 a6 a7 t0 t1 i vf Ha4 Ha2 Hvf Hie Hdg Hdisj.
  pose proof eloc as Hel.
  assert (HD : skipn (Z.to_nat d0) (first_line zs) = nthz zs d0 :: skipn (Z.to_nat (d0 + 1)) (first_line zs))
    by (apply flsfx_cons; lia).
  step. destruct (Z.eq_dec i d0) as [Ei|Ei].
  - take true. apply ev_cur.
    assert (Dg : is_digit (nthz zs d0) = false) by (destruct Hdisj as [[_ H]|H]; [exact H | lia]).
    apply (ev_cur_nodigit (nthz zs d0) (skipn (Z.to_nat (d0 + 1)) (first_line zs)));
      [rewrite HL2, HD; reflexivity | exact Dg].
  - take false.
    assert (Dg : is_digit (nthz zs d0) = true).
    { destruct (is_digit (nthz zs d0)) eqn:D; [reflexivity|]. exfalso.
      rewrite HD, (digits_ev_stop _ _ _ D) in Hdg. injection Hdg as _ Hl. rewrite <- HD in Hl.
      pose proof (skipn_inj (first_line zs) (Z.to_nat d0) (Z.to_nat i) ltac:(lia) ltac:(lia) Hl). lia. }
    assert (HE2 : expected_value_m zs cur = finish (c0 =? 45) vf (skipn (Z.to_nat i) (first_line zs)) cur).
    { rewrite <- HF.
      apply (ev_fin (nthz zs d0) (skipn (Z.to_nat (d0 + 1)) (first_line zs)) vf);
        [rewrite HL2, HD; reflexivity | exact Dg | rewrite <- HD; exact Hdg]. }
    apply (seg_trail i a0 a1 a2 t1 Ha0 ltac:(lia)); [| | exact Ha4].
    + intros a3' a4' a5' a6' a7' t0' Hnil.
      apply (ev_tail a0 a1 a2 a3' a4' a5' a6' a7' t0' t1 c0 vf (skipn (Z.to_nat i) (first_line zs)));
        [exact Hc0 | exact Hvf | exact Hnil | exact Ha1 | exact Ha2 | symmetry; exact HE2].
    + intros a3' a4' a5' a6' a7' t0' Hne.
      apply ev_cur. rewrite HE2. apply finish_rest. exact Hne.
Qed.

(* 0x12ea0: the digit loop's set-up, then the loop *)
Lemma ev_dgt : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word) d0 c0,
  bv_unsigned a0 = e -> bv_unsigned a1 = c0 -> bv_unsigned a3 = d0 ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  evt rsegs Q (ST 0x12ea0 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 d0 c0 Ha0 Ha1 Ha3 Hc0 Hd0 HL2 HF.
  pose proof eloc as Hel.
  do 7 step.
  eapply (loop_dg d0 a0 a1 a3 Ha3 Ha0 (ev_ee8 a0 a1 a3 d0 c0 Ha0 Ha1 Ha3 Hc0 Hd0 HL2 HF))
    with (k := Z.to_nat (e - d0 - 1)) (i := d0) (v := 0).
  all: first [ lia | reflexivity | factw ].
Qed.

(* 0x12e88: the sign *)
Lemma ev_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word) j,
  bv_unsigned a0 = e -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j -> 0 <= j < e ->
  SKL = skipn (Z.to_nat j) (first_line zs) -> is_lead_blank (nthz zs j) = false ->
  evt rsegs Q (ST 0x12e88 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 j Ha0 Ha1 Ha3 Hje HS _.
  pose proof eloc as Hel.
  assert (HJ : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx_cons; lia).
  assert (HF : fst (sign_split SKL) = (nthz zs j =? 45)) by (rewrite HS, HJ; apply ss_fst).
  apply (seg_sign a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 j Ha0 Ha1 Ha3 Hje).
  - intros a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' d0 Ha0' Ha1' Ha3' Hd0 Hsnd.
    apply (ev_dgt a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' d0 (nthz zs j));
      [exact Ha0' | exact Ha1' | exact Ha3' | apply BR | lia | rewrite HS; exact Hsnd | exact HF].
  - intros a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' Hnil.
    apply ev_cur. apply ev_cur_nil. rewrite HS. exact Hnil.
Qed.

(* 0x12e60: the leading-blank loop's set-up, then the loop *)
Lemma ev_lb_nil : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), SKL = [] ->
  evt rsegs Q (ST 0x12f50 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof. intros. apply ev_cur. apply ev_cur_nil. rewrite H. reflexivity. Qed.

Lemma ev_60 : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), bv_unsigned a0 = e -> 0 < e ->
  evt rsegs Q (ST 0x12e60 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 Ha0 He0.
  pose proof eloc as Hel.
  do 3 step.
  apply (loop_lb ev_lb_nil ev_sign (Z.to_nat (e - 1)) 0);
    [lia | lia | reflexivity | exact Ha0 | fact | fact | fact].
Qed.

(* 0x12e5c: the empty-first-line test *)
Lemma ev_5c : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), bv_unsigned a0 = e -> e < n ->
  evt rsegs Q (ST 0x12e5c a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 Ha0 Hen.
  pose proof eloc as Hel.
  step. destruct (Z.eq_dec e 0) as [E0|E0].
  - take true. apply ev_lb_nil.
    assert (Hnil : first_line zs = []) by (apply length_zero_iff_nil; lia).
    rewrite Hnil. reflexivity.
  - take false. apply ev_60; [exact Ha0 | lia].
Qed.

Lemma ev_60n : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word), bv_unsigned a0 = n -> e = n ->
  evt rsegs Q (ST 0x12e60 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof. intros. apply ev_60; [rewrite H, H0; reflexivity | lia]. Qed.

(* 0x12e24: the whole of the inlined expected_value *)
Lemma ev_block : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 : word),
  evt rsegs Q (ST 0x12e24 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1.
  step. step.
  apply (loop_nl ev_5c ev_60n (Z.to_nat (n - 1)) 0);
    [lia | lia | change (skipn (Z.to_nat 0) zs) with zs; lia | fact | fact].
Qed.

End Ev.

(* ---------------- the three straight-line segments of the call ---------------- *)

Definition CV_MALLOC : Z := 0x13e50.
Definition CV_FREE : Z := 0x13d10.

Definition cv_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r n cur : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x12df8) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 cur) s1
                  (Z_to_bv 64 (fuzz_dup_size n)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 r) (Z_to_bv 64 n)
                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cv_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
    0 <= n <= 255 ->
    evt rsegs (cv_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r n cur m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 n) (Z_to_bv 64 cur) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r n cur lo
    ST LO HI HN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold CHECK_VALUE.
  carve_frame 48%nat ST.
  do 13 step.
  apply evt_done. unfold cv_s1_post.
  do 15 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|].
       replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. eassumption. }
  f_equal.
  - unfold mkR. repeat match goal with
    | |- TNode _ _ _ = TNode _ _ _ => f_equal
    | |- Some _ = Some _ => f_equal
    end.
    f_equal. unfold fuzz_dup_size. zsimp.
    destruct (Z.ltb_spec n 1) as [Hn1|Hn1]; cbn [Z.b2z].
    + replace n with 0 by lia. reflexivity.
    + rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)). lia.
Qed.

(* 0x12f60: `mv a0, s2`, the epilogue and `ret` *)
Lemma cv_seg3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v4 v3 v2 v1 v0 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 s2 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f60) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v4 v3 v2 v1 v0 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 9 step.
  apply evt_done. f_equal.
Qed.

Definition cv_s2_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c n got : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x12f60) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 c) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 got) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_FREE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (c, c + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

(* 0x12f50 - 0x12f5c: `sext.w s0, s0`, the property test (s2 == s0) and the call of free *)
Lemma cv_end :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (c n got : Z),
    bv_unsigned s0 = got mod 2 ^ 64 -> INT_MIN <= got <= INT_MAX ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (c, c + n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs (cv_s2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c n got m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 got) s3 s4 s5 s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f50) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m0 c n got
    Hs0 Hgot MU WM MI.
  unfold INT_MIN, INT_MAX in Hgot.
  step. step. take false. step. step.
  apply evt_done. unfold cv_s2_post. do 16 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact MI].
Qed.

Lemma zbytes_rng : forall bs i, 0 <= nthz (zbytes bs) i < 256.
Proof.
  intros bs i. unfold nthz, zbytes. destruct (Nat.lt_ge_cases (Z.to_nat i) (length (map (@bv_unsigned 8) bs)))
    as [Hl|Hl].
  - pose proof (nth_In (map (@bv_unsigned 8) bs) 0 Hl) as Hin.
    apply in_map_iff in Hin as (x & Ex & _). rewrite <- Ex.
    pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. cbn in R. lia.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma rd_of_bytes : forall m r bs i, bytes_at rsegs m r bs -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (r + i)) 1 = Some [Z_to_bv 8 (nthz (zbytes bs) i)].
Proof.
  intros m r bs i (H0 & H1 & H) Hi.
  assert (Hlt : (Z.to_nat i < length bs)%nat) by lia.
  pose proof (H (Z.to_nat i) Hlt) as E. rewrite Z2Nat.id in E by lia.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hlt) in E.
  assert (Eb : Z_to_bv 8 (nthz (zbytes bs) i) = nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  { unfold nthz, zbytes.
    rewrite (nth_indep (map (@bv_unsigned 8) bs) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hlt).
    rewrite map_nth. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite Eb. change (Z_to_bv 64 (r + i)) with (wa (r + i)).
  rewrite ov_rdn, rdn_unfold, E. reflexivity.
Qed.

Lemma rw_cb_bytes : forall m a k bs, rw_cells rsegs m a [CB k bs] -> bytes_at rsegs m a bs.
Proof. intros m a k bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(* 0x12df8 - 0x12f5c: the NULL test of fuzz_dup, the copy, rp_uci_int, the inlined expected_value, the property
   test, up to the call of free *)
Lemma cv_seg2 : memcpy_contract -> rp_uci_int_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 s2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur c lo : Z) (bs : list byte),
  0 <= n <= 255 -> Z.of_nat (length bs) = n -> INT_MIN <= cur <= INT_MAX ->
  4096 <= c -> c + fuzz_dup_size n <= lo ->
  (0 < n -> 4096 <= r /\ r + n <= lo /\ (r + n <= c \/ c + n <= r) /\ bytes_at rsegs m r bs) ->
  (forall i, 0 <= i < fuzz_dup_size n -> present m (c + i)) ->
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 63 ->
  evt rsegs (cv_s2_post sp gp tp (Z_to_bv 64 r) (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11 F fc c n
              (rp_uci_int_m (zbytes bs) cur) m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 cur) s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2
             (Z_to_bv 64 r) (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12df8) fc None m (seg_rom rsegs)).
Proof.
  intros MCc RUIc ra sp gp tp t0 t1 t2 s1 s2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r n cur c lo bs HN HL HC Hc0 Hc1 HR Hpres MI ST HLO HSP.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rp_uci_int_range (zbytes bs) cur HC) as Hgot.
  assert (Hfd : 1 <= fuzz_dup_size n <= n + 1) by (unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia).
  step. take false. step. step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - (* n = 0: no copy; rp_uci_int (c, 0, cur) *)
    destruct bs as [|b0 bs']; [|cbn in HL; lia]. clear HL. subst n.
    take true. step. step. step.
    eapply evt_cut.
    { eapply RUIc with (bs := []) (cur := cur) (lo := lo).
      - split; [rewrite unsigned_lit by lia; lia|]. split; [cbn; rewrite unsigned_lit by lia; lia|].
        intros i Hi. cbn in Hi. lia.
      - cbn. rewrite unsigned_lit by lia. lia.
      - cbn. rewrite unsigned_lit by lia. reflexivity.
      - reflexivity.
      - exact HC.
      - exact MI.
      - exact ST.
      - unfold RP_UCI_INT_FRAME. lia.
      - lia.
      - left. cbn. rewrite unsigned_lit by lia. unfold RP_UCI_INT_FRAME. lia. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1
      & WM1 & MI1 & _ & _).
    unfold RP_UCI_INT_FRAME in MU1.
    rewrite ret_pc_even by first [lia | reflexivity].
    step. step.
    apply cv_end; [rewrite unsigned_lit_wrap; reflexivity | exact Hgot | | exact WM1 | exact MI1].
    refine (munch_weaken _ _ m m1 _ MU1). intros x Hx. cbn [outside] in *. tauto.
  - (* n > 0: copy, rp_uci_int (c, n, cur), expected_value (r, n, cur) *)
    take false.
    destruct (HR ltac:(lia)) as (Hr0 & Hr1 & Hrc & BA).
    assert (Efd : fuzz_dup_size n = n) by (unfold fuzz_dup_size; rewrite (proj2 (Z.eqb_neq n 0) N0); reflexivity).
    rewrite Efd in Hc1, Hpres. clear Hfd Efd HR.
    destruct (present_rw_cells rsegs m c (Z.to_nat n) ltac:(lia) ltac:(lia)) as [junk RW].
    { intros i Hi. apply Hpres. lia. }
    step. step. step.
    eapply evt_cut.
    { eapply MCc with (src := bs) (junk := junk).
      - rewrite unsigned_lit by lia. exact BA.
      - rewrite unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by lia. exact RW.
      - rewrite !unsigned_lit by lia. lia.
      - exact MI. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1
      & WM1 & MI1 & RW1 & BA1).
    assert (HNn : 0 <= n < 2 ^ 64) by (clear - HN; lia).
    assert (HNc : 0 <= c < 2 ^ 64) by (clear - Hc0 Hc1 HN HLO Rsp; lia).
    rewrite (unsigned_lit c HNc), (unsigned_lit n HNn) in MU1, RW1.
    rewrite (unsigned_lit r) in BA1 by (clear - Hr0 Hr1 HN HLO Rsp; lia).
    rewrite ret_pc_even by first [lia | reflexivity].
    assert (ST1 : stk rsegs m1 lo (bv_unsigned sp)).
    { apply (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1). cbn [disjoint_from].
      split; [right; lia | exact I]. }
    pose proof (rw_cb_bytes _ _ _ _ RW1) as BC1.
    step. step. step. step.
    eapply evt_cut.
    { eapply RUIc with (bs := bs) (cur := cur) (lo := lo).
      - rewrite unsigned_lit by lia. exact BC1.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - reflexivity.
      - exact HC.
      - exact MI1.
      - exact ST1.
      - unfold RP_UCI_INT_FRAME. lia.
      - lia.
      - left. rewrite unsigned_lit by lia. unfold RP_UCI_INT_FRAME. lia. }
    intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2
      & WM2 & MI2 & _ & _).
    unfold RP_UCI_INT_FRAME in MU2.
    rewrite ret_pc_even by first [lia | reflexivity].
    assert (BA2 : bytes_at rsegs m2 r bs)
      by (apply (bytes_at_transport rsegs _ m1 m2 r bs BA1 MU2); cbn [disjoint_from]; split; [left; lia | exact I]).
    step.
    eapply (ev_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r n cur (Z.of_nat (length (first_line (zbytes bs))))
      (zbytes bs)).
    all: try (first
      [ lia
      | reflexivity
      | apply zbytes_rng
      | (unfold zbytes; rewrite length_map; lia)
      | (intros i Hi; apply rd_of_bytes; [exact BA2 | lia])
      | (rewrite unsigned_lit_wrap; reflexivity) ]).
    intros s0' A0 A1 A2 A3 A4 A5 A6 A7 T0 T1 Hs0.
    apply cv_end.
    + rewrite Hs0, <- uci_value_ok. reflexivity.
    + exact Hgot.
    + apply (munch_trans _ m m1 m2).
      * refine (munch_weaken _ _ m m1 _ MU1). intros x Hx. cbn [outside] in *. tauto.
      * refine (munch_weaken _ _ m1 m2 _ MU2). intros x Hx. cbn [outside] in *. tauto.
    + exact (wmono_trans rsegs m m1 m2 WM1 WM2).
    + exact MI2.
Qed.

(* ---------------- the SR walk: the allocator calls around the segments ---------------- *)

(* From here on the names are the contract's: the allocator's ceiling (lib/Reusable/YM05.v), not the kit's
   Lib/Ceiling.v class, and YK11's getr / mkst, not Lib/PropExec.v's, which the Lib imports above shadow them
   with (the same fix as lib/Prog/check_no_overread.v). *)
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).
Local Abbreviation getr := YK11.getr (only parsing).
Local Abbreviation mkst := YK11.mkst (only parsing).

Section CV.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x13e50.
Hypothesis FREEPC : ms_free B = 0x13d10.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis RUI : rp_uci_int_contract.

Lemma cv_blk_bytes : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity.
Qed.

(* a heap byte, seen in the normalized memory of a crt_runN segment, is still there *)
Lemma cv_blk_present : forall m a, 0 <= a < 2 ^ 64 -> present m a -> ~ in_img B a ->
  present (normalize rsegs m) a.
Proof.
  intros m a Ha [bt Hb] Hni.
  assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa a) = false)
    by (apply crt_ro_false; [lia | exact (crt_fs_none B SEGS a Hni)]).
  rewrite SEGS in Hra. exists bt. unfold normalize, Mem.wa in *. rewrite Hra. exact Hb.
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (r n cur : Z) (bs : list byte) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CV_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 r.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 cur.
Hypothesis HC : INT_MIN <= cur <= INT_MAX.
Hypothesis HN : 0 <= n <= REPLY_MAX.
Hypothesis HL : Z.of_nat (length bs) = n.
Hypothesis BD : blk_data B mem r bs.
Hypothesis IB : 0 < n -> in_block L A r n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : cv_room b n.

Let cv_inv := cg_inv B API CV_STACK L A regs mem md.

Definition cv_keep (r' : bvmap 5 word) : Prop :=
  getr r' 3 = getr regs 3 /\ getr r' 4 = getr regs 4 /\ getr r' 21 = getr regs 21 /\ getr r' 22 = getr regs 22 /\
  getr r' 23 = getr regs 23 /\ getr r' 24 = getr regs 24 /\ getr r' 25 = getr regs 25 /\
  getr r' 26 = getr regs 26 /\ getr r' 27 = getr regs 27.

Definition cv_frame (m' : word -> option byte) : Prop :=
  rw_cells rsegs m' (spZ regs - 48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
    C8 (getr regs 8); C8 (getr regs 1)].

Definition cv_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CV_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cv_keep_pres : forall r1 r2, cv_keep r1 -> regs_preserved r1 r2 -> cv_keep r2.
Proof.
  intros r1 r2 (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - transitivity (getr r1 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r1 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r1 21); [apply (Hp 21); unfold callee_saved; lia | exact K21].
  - transitivity (getr r1 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r1 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r1 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r1 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r1 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r1 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

Lemma cv_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cv_inv Lk Ak mk mdk -> cv_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cv_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 I FR Hpost Hsp HE.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cv_frame in *. rewrite <- SEGS in FR |- *.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  apply (cg_cells_call B API CV_STACK L A regs mem md PRE Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 _ _ I FR Hpost);
    [lia | cbn [Cells.cells_size Cells.csize Nat.add]; lia | exact Hsp | exact HE | exact ERR].
Qed.

(* 0x12f60: the epilogue, and the return *)
Lemma cv_ph3 : forall (fx7 : FPState) L3 A3 regs6 m3 md3 got,
  frm_zero (@fp_csr fx7) ->
  cv_inv L3 A3 m3 md3 -> st_init_done A3 = true -> blocks L3 A3 = blocks L A ->
  res_ok_slots A3 b -> got = rp_uci_int_m (zbytes bs) cur ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs6 18 = Z_to_bv 64 got ->
  cv_keep regs6 -> cv_frame m3 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs6 (Z_to_bv 64 0x12f60) m3 (seg_rom (ms_segs B))) md3) cv_final.
Proof.
  intros fx7 L3 A3 regs6 m3 md3 got Hfrm I Hinit Hb3 Hres Egot G2 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L3 A3 m3 md3 M3) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs6 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (crt_runA (fx := fx7) B SEGS regs6 _ m3 md3); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply cv_seg3. unfold cv_frame in FR. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs7 -> Hg7. cbn [MState.MS ms_pc_val ms_mem].
  assert (G7a : getr regs7 1 = getr regs 1) by (rewrite Hg7; reflexivity).
  assert (G7b : getr regs7 2 = Z_to_bv 64 (bv_unsigned (getr regs6 2) + 48)) by (rewrite Hg7; reflexivity).
  rewrite USP in G7b. replace (spZ regs - 48 + 48) with (spZ regs) in G7b by lia.
  assert (G7d : getr regs7 10 = Z_to_bv 64 got) by (rewrite Hg7; exact G18).
  assert (P7 : regs_preserved regs regs7).
  { destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs7 2 = getr regs 2) by (rewrite G7b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r' Hr. unfold callee_saved in Hr.
    assert (C : r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 8 \/ r' = 9 \/ r' = 18 \/ r' = 19 \/ r' = 20 \/ r' = 21 \/
                r' = 22 \/ r' = 23 \/ r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg7; first [reflexivity | exact K3 | exact K4 | exact K21 | exact K22 | exact K23
        | exact K24 | exact K25 | exact K26 | exact K27]]. }
  rewrite (ret_pc_of_ok _ Hra).
  apply SR_ret. exists fx7, L3, A3, regs7, m3, md3.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split; [apply (kb_post B API); [exact (proj1 I) | exact P7]|].
  split; [rewrite G7d, Egot; reflexivity|].
  split; [exact Hb3|].
  split; [exact (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I)|].
  split; [exact I5|]. split; [exact I4|]. split; [exact Hres | exact Hinit].
Qed.

(* free(c), entered with ra = 0x12f60 *)
Lemma cv_ph_free : forall (fx7 : FPState) L2 A2 regs5 m2 md2 c got d1 d2,
  frm_zero (@fp_csr fx7) ->
  cv_inv L2 A2 m2 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = d1 ++ (c, fuzz_dup_size n) :: d2 -> blocks L A = d1 ++ d2 ->
  res_ok_slots A2 (sb_malloc b (fuzz_dup_size n)) -> got = rp_uci_int_m (zbytes bs) cur ->
  getr regs5 1 = Z_to_bv 64 0x12f60 -> getr regs5 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs5 10 = Z_to_bv 64 c -> getr regs5 18 = Z_to_bv 64 got ->
  cv_keep regs5 -> cv_frame m2 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs5 (Z_to_bv 64 CV_FREE) m2 (seg_rom (ms_segs B))) md2) cv_final.
Proof.
  intros fx7 L2 A2 regs5 m2 md2 c got d1 d2 Hfrm I Hinit Hb2 Hb0 Hres Egot G1 G2 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof (fuzz_dup_size_range n ltac:(unfold REPLY_MAX in HN; lia)) as Hfd.
  pose proof I as ((M2 & W2 & B2 & _) & I2 & I3 & I4 & I5).
  assert (S5 : spZ regs5 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW2 : pairwise ranges_disjoint (d1 ++ (c, fuzz_dup_size n) :: d2))
    by (rewrite <- Hb2; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2)).
  destruct (crt_bu L2 A2 c _ ltac:(rewrite Hb2; apply crt_in_mid)) as (p & Hp & Ep).
  assert (Hpre5 : call_pre B (aa_MR API) L2 A2 regs5 m2 md2).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L2 A2 regs5 m2 md2)).
    apply (cg_pre B API CV_STACK L A regs mem md PRE L2 A2 m2 md2 regs5 48 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S5; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CV_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L2 A2 regs5 m2 md2 p (fuzz_dup_size n) (sb_malloc b (fuzz_dup_size n)) Hpre5 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L3 & A3 & regs6 & m3 & md3 & -> & Hpost & (e1 & e2 & He1 & He2) & Hkept & Hro3 & Hgk3 & Hub3 &
    Hinit3 & Hlen3 & Hres3).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp6 & _).
  rewrite Ep in He1.
  assert (ND2 : ~ In (c, fuzz_dup_size n) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW2); cbn; lia).
  assert (Hb3 : blocks L3 A3 = blocks L A).
  { rewrite He2, Hb0. symmetry. apply (crt_rm (c, fuzz_dup_size n) d1 d2 e1 e2 ND2). rewrite <- Hb2. exact He1. }
  assert (HD2 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L2 p, fuzz_dup_size n) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid d1 d2 _ y PW2). rewrite <- Hb0. exact Hy. }
  assert (HU3 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A3)).
  { intros q' k Hq'. apply Hub3;
      [exact (I3 q' k Hq') | exact (cg_free_keep B API CV_STACK L A regs mem md L2 A2 m2 md2 p _ I Hp
        ltac:(lia) HD2 q' k Hq')]. }
  assert (I3' : cv_inv L3 A3 m3 md3).
  { apply (cg_inv_call B API CV_STACK L A regs mem md PRE AX CT L2 A2 m2 md2 regs5 ALLOC_STACK _ L3 A3 regs6 m3
      md3 I Hpost);
      [rewrite S5, HK0; unfold ALLOC_STACK; lia | lia | exact (crt_heap_E B API L2 A2 m2 md2 p _ AX M2 Hp)
      | exact Hlen3 | exact HU3 | exact Hro3 | exact Hgk3]. }
  assert (FR3 : cv_frame m3).
  { apply (cv_frame_call L2 A2 m2 md2 regs5 ALLOC_STACK _ L3 A3 regs6 m3 md3 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (crt_heap_E B API L2 A2 m2 md2 p _ AX M2 Hp a Ha)). }
  rewrite G1.
  apply (cv_ph3 fx7 L3 A3 regs6 m3 md3 got Hfrm I3' (Hinit3 Hinit) Hb3).
  - rewrite sb_free_malloc in Hres3. exact Hres3.
  - exact Egot.
  - transitivity (getr regs5 2); [apply (Hp6 2); unfold callee_saved; lia | exact G2].
  - transitivity (getr regs5 18); [apply (Hp6 18); unfold callee_saved; lia | exact G18].
  - exact (cv_keep_pres regs5 regs6 GK Hp6).
  - exact FR3.
Qed.

(* 0x12df8 - 0x12f5c as one crt_runN segment over the normalized memory *)
Lemma cv_ph2 : forall L1 A1 regs2 m2 md1 c d1 d2,
  cv_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (c, fuzz_dup_size n) :: d2 -> blocks L A = d1 ++ d2 ->
  res_ok_slots A1 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 cur ->
  getr regs2 10 = Z_to_bv 64 c -> getr regs2 19 = Z_to_bv 64 r -> getr regs2 20 = Z_to_bv 64 n ->
  cv_keep regs2 -> cv_frame m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x12df8) m2 (seg_rom (ms_segs B))) md1) cv_final.
Proof.
  intros L1 A1 regs2 m2 md1 c d1 d2 I Hinit Hb1 Hb0 Hres G2 G8 G10 G19 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as Hfd.
  assert (Hfdn : n <= fuzz_dup_size n) by (unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia).
  pose proof I as ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (USP : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (c, fuzz_dup_size n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InC : In (c, fuzz_dup_size n) (blocks L1 A1)) by (rewrite Hb1; apply crt_in_mid).
  destruct (crt_blk B API AX L1 A1 m2 md1 c _ M1 InC) as (HC1 & HC2 & _ & HCi).
  assert (HRr : 0 < n -> 4096 <= r /\ r + n <= spZ regs - 48 - 32 /\ (r + n <= c \/ c + n <= r) /\
                 bytes_at rsegs (normalize rsegs m2) r bs).
  { intros Hn. destruct (IB Hn) as (qa & ka & Hqa & Ha1 & Ha2).
    destruct (crt_blk B API AX L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
    assert (Hqin : In (qa, ka) (d1 ++ d2)) by (rewrite <- Hb0; exact Hqa).
    pose proof (crt_pw _ _ _ _ _ _ PW1 Hqin) as DCA.
    assert (Efd : fuzz_dup_size n = n) by (unfold fuzz_dup_size; rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia));
      reflexivity).
    split; [lia|]. split; [lia|]. split; [lia|].
    apply (bytes_at_normalize rsegs); [exact Hro'|].
    apply cv_blk_bytes; [lia | lia |].
    pose proof (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I) as KP.
    intros i Hi. rewrite <- (BD i Hi).
    pose proof (KP qa ka (r - qa + i) Hqa (fun H => H) ltac:(lia)) as E.
    replace (qa + (r - qa + i)) with (r + i) in E by ring. exact E. }
  assert (ST : stk rsegs (normalize rsegs m2) (spZ regs - 48 - 32) (spZ regs - 48)).
  { rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S1. left. lia. }
  eapply (crt_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G19, G20.
    apply (cv_seg2 MC RUI) with (r := r) (n := n) (cur := cur) (c := c) (bs := bs)
      (lo := spZ regs - 48 - 32);
      rewrite ?USP;
      first [ exact HL | exact HC | exact HRr | exact (mem_inv_normalize rsegs m2) | exact ST | lia
            | (intros i Hi; destruct (HCi i ltac:(lia)) as (X1 & X2 & _);
               apply cv_blk_present; [lia | exact X1 | exact X2]) ]. }
  { intros ms (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs5 (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM &
    MI') Hrel Hsame Hg5.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR'). cbn [ms_mem MState.MS] in HR'.
  rewrite USP in MU.
  set (W := [(spZ regs - 48 - 32, spZ regs - 48); (c, c + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR' Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR' Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (Hout2 : forall x, ~ Frame.outside W x -> (spZ regs - 48 - 32 <= x < spZ regs - 48) \/ (c <= x < c + n))
    by (intros x Hx; unfold W in Hx; cbn [Frame.outside] in Hx; lia).
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (Hout2 _ Hout) as [Hs|Hs].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HCi (bv_unsigned x - c) ltac:(lia)) as (_ & Hni & _).
      replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in Hni by ring. exact Hni. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CV_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (Hout2 _ Hout) as [Hs|Hs].
    - left. lia.
    - right. destruct (HCi (x - c) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (c + (x - c)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. assert (Hin : In (ptr_addr L p, k) (d1 ++ d2))
        by (rewrite <- Hb0; exact (crt_ub L A p k Hp)).
      pose proof (crt_pw _ _ _ _ _ _ PW1 Hin). lia. }
  pose proof (cg_inv_A B API CV_STACK L A regs mem md PRE SEGS L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7)
    as I7.
  assert (FR7 : cv_frame (ms_mem ms)).
  { unfold cv_frame in *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep B m2 (ms_mem ms) _ _ FR). intros i Hi.
    change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr].
  apply (cv_ph_free (mkFP fp_regs fp_csr) L1 A1 regs5 (ms_mem ms) md1 c (rp_uci_int_m (zbytes bs) cur) d1 d2
    FRM I7 Hinit Hb1 Hb0 Hres eq_refl);
    [rewrite Hg5; reflexivity | rewrite Hg5; exact G2 | rewrite Hg5; reflexivity | rewrite Hg5; reflexivity
    | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg5;
    first [exact K3 | exact K4 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x12dc4 - 0x12df4 and malloc(n ? n : 1) *)
Lemma cv_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_VALUE) mem (seg_rom (ms_segs B))) md) cv_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cv_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : stk rsegs mem (spZ regs - CV_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CV_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12. eapply cv_seg1; [exact ST | unfold spZ in *; lia | unfold spZ in *; lia
    | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12df8) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (fuzz_dup_size n)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 cur) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 r) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (K1 : cv_keep regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cv_inv L A m1 md).
  { apply (cg_inv_A B API CV_STACK L A regs mem md PRE SEGS L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CV_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_slots b (fuzz_dup_size n)).
  { destruct ROOM as (R1 & R2 & R3). apply fuzz_dup_room; lia. }
  replace (Z_to_bv 64 CV_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC L A regs1 m1 md (fuzz_dup_size n) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cv_inv L1 A1 m2 md1).
  { apply (cg_inv_call B API CV_STACK L A regs mem md PRE AX CT L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1
      Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cv_frame m2).
  { apply (cv_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1 Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (cv_ph2 L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - exact (cv_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_value_holds : check_value_contract B API.
Proof.
  intros L A regs mem md r n cur bs b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  eapply cv_entry; eassumption.
Qed.
End CV.
