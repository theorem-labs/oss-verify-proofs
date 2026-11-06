(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the instruction walk of check_value (fuzz_uci.c) on the
   UBSan image, 0x12e48 (133 instructions, 48-byte frame), against lib/U/Prog/check_value_c.v: check_value_holds.
   The UBSan twin of lib/Prog/check_value.v at this image's values (r in s4, n in s3, c in s1, got in s2, cur in s0),
   laid out as lib/Prog/check_no_overread.v / libreac/fuzz_decode's released check_round_trip.v: the inlined
   expected_value as continuation-style loop lemmas (Section Ev: loop_nl, loop_lb, seg_sign, loop_dg, seg_after,
   loop_tb, seg_fin, composed by ev_all), the straight-line segments (cv_seg1 / cv_seg2 / cv_tail / cv_seg3), and the
   SR phases that carry CheckGlue's cg_inv across malloc and free (cv_entry / cv_ph2 / cv_ph3).
   Walked: 131 of 133 instructions (0x12e48 - 0x13050); the other two are the `jal abort` at 0x13054 and the UBSan
   trap `unimp` at 0x13058, and no path reaches them:
   - 0x12e7c `beqz a0` (fuzz_dup's malloc returned NULL) to abort: c = P is the allocator's block, 4096 <= P (its
     malloc_ret, as FuzzDup.fuzz_dup_no_null states); the same fact discharges rp_uci_int_c's UBSan premise
     `bv_unsigned a0 <> 0` at both rp_uci_int calls (0x12ea0 for n > 0, 0x12ef8 for n = 0).
   - 0x13024 `bne s2, s0` (the property test) to abort: s2 = rp_uci_int_m (zbytes bs) cur and s0 = (int)
     expected_value_m (zbytes bs) cur, equal by UciModel.uci_value_ok, and an int by rp_uci_int_range (sext_self).
   - the UBSan pointer checks on r + i, all to 0x13058, run only for n > 0, where in_block puts [r, r + n) in a live
     block (crt_blk: 4096 <= r, r + n <= alloc_ceiling): 0x12ec0 `bltu a5, s4` (r + i wraps), 0x12ecc `beqz a6`
     (r + i is NULL exactly when r is not), 0x12ed0 `beqz s4` (r == NULL), 0x12f1c `bltu a4, s4`, 0x12f38 `beqz a4`,
     0x12f40 `bltu a3, a2` (~r < j), 0x12f7c `bltu a3, a4`, 0x12fd0 `bltu a3, a4`.
   - 0x12fa0 `bne t1, t2` (signed overflow of v * 10) to 0x13058: the multiply runs only when 0x12f90 found
     v <= 9999999999, so v * 10 < 2^63 (mul_nov).
   - 0x13010 `bne a0, a2` (overflow of -v) to 0x13058: 0 <= v < 10^11 (digits_ev_rng / loop_dg), so v > 0 and -v < 0
     agree (neg_nov). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac
  Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import CheckGlue FuzzDup memcpy_c rp_uci_int_c
  check_no_overread_c check_value_c.
Import ListNotations.
Local Open Scope Z_scope.

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

Lemma tb_big : forall c, 32 < c -> is_trail_blank c = false.
Proof.
  intros c H. unfold is_trail_blank.
  destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 13); try lia; reflexivity.
Qed.

Lemma digit_land : forall c, is_digit c = true -> Z.land c 15 = c - 48.
Proof.
  intros c D. unfold is_digit in D. apply andb_true_iff in D as [D1 D2].
  apply Z.leb_le in D1. apply Z.leb_le in D2.
  change 15 with (2 ^ 4 - 1). rewrite zb_land_mask by lia. change (2 ^ 4) with 16. mlia.
Qed.

Lemma digits_ev_stop : forall v c t, is_digit c = false -> digits_ev v (c :: t) = (v, c :: t).
Proof. intros v c t D. cbn [digits_ev]. rewrite D. reflexivity. Qed.

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

(* ---------------- the inlined expected_value, 0x12ea8 - 0x13020 ---------------- *)

Section Ev.
Variables (ra sp gp tp s1 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
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

(* s4 holds r throughout; s3 holds n, then (from 0x12f08) e *)
Local Abbreviation ST pc s0 s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  do 3 (decide_tests; cbv beta iota; cbn [Z.b2z]); reflexivity.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv beta iota | symmetry; solve_c]
  end.
Ltac fact := cbv delta [zxb]; wsub; rewrite ?unsigned_lit_wrap; mlia.
Ltac factw := zsimp; wsub; zsimp; mlia.

Lemma sfx_cons : forall i, 0 <= i < n -> skipn (Z.to_nat i) zs = nthz zs i :: skipn (Z.to_nat (i + 1)) zs.
Proof.
  intros i Hi. unfold nthz. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply skipn_nth_cons. lia.
Qed.

Lemma eloc : 0 <= e <= n.
Proof. pose proof (first_line_le zs) as H. lia. Qed.

(* a byte of r read through a register that holds r + i *)
Lemma rd_at : forall (w : word) i, bv_unsigned w = r + i -> 0 <= i < n ->
  ov_read_bytes rsegs m w 1 = Some [Z_to_bv 8 (nthz zs i)].
Proof. intros w i Hw Hi. rewrite <- (Z_to_bv_lit_self w), Hw. apply RD. exact Hi. Qed.

(* the scan for the first '\n': 0x12ec0, a0 = -i, a4 = a5 = r + i; the UBSan checks on r + i at 0x12ec0 (wrap),
   0x12ecc (NULL-ness of r + i against r) and 0x12ed0 (r == NULL) are not taken: 4096 <= r, r + n < 2^64 *)
Lemma loop_nl :
  (forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), e = 0 ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), bv_unsigned s3 = e -> 0 < e ->
     evt rsegs Q (ST 0x12f0c (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k i (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word),
  0 <= i -> i + Z.of_nat (S k) = n ->
  e = i + Z.of_nat (length (first_line (skipn (Z.to_nat i) zs))) ->
  bv_unsigned a0 = (- i) mod 2 ^ 64 -> bv_unsigned a1 = (- n) mod 2 ^ 64 -> bv_unsigned a2 = 1 ->
  bv_unsigned a3 = 10 -> bv_unsigned a4 = r + i -> bv_unsigned a5 = r + i ->
  evt rsegs Q (ST 0x12ec0 (Z_to_bv 64 cur) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros K0 K1 k. induction k as [|k IH];
    intros i a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hi0 Hk Hinv Ha0 Ha1 Ha2 Ha3 Ha4 Ha5.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (sfx_cons i Hin) in Hinv.
  all: step. all: take false.
  all: step. all: step. all: step. all: take false.
  all: step. all: take false.
  all: pose proof (rd_at a4 i Ha4 Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR i)).
  all: step.
  all: destruct (Z.eq_dec (nthz zs i) 10) as [Ec|Ec].
  - rewrite (fl_nl _ _ Ec) in Hinv. cbn [length] in Hinv.
    take true. step.
    destruct (Z.eq_dec i 0) as [Ei|Ei].
    + take true. apply K0. lia.
    + take false. step. apply K1; [fact | lia].
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [first_line length] in Hinv.
    take false. do 4 step. take false. step. apply K1; [fact | lia].
  - rewrite (fl_nl _ _ Ec) in Hinv. cbn [length] in Hinv.
    take true. step.
    destruct (Z.eq_dec i 0) as [Ei|Ei].
    + take true. apply K0. lia.
    + take false. step. apply K1; [fact | lia].
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    take false. do 4 step. take true.
    apply (IH (i + 1)); [lia | lia | lia | fact | exact Ha1 | exact Ha2 | exact Ha3 | fact | fact].
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

(* a closed register value: evaluated, never on a goal with a machine state in it *)
Ltac cfact := lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) = _ => vm_compute; reflexivity end.
Ltac anyfact := lazymatch goal with |- bv_unsigned _ = _ => first [ fact | factw | cfact ] end.

(* the leading-blank skip: 0x12f18, a2 = j; the 0x12f1c wrap check on r + j is not taken *)
Lemma loop_lb : forall (s3 : word), bv_unsigned s3 = e ->
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), skip is_lead_blank (first_line zs) = [] ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) j,
     bv_unsigned a0 = nthz zs j -> bv_unsigned a2 = j -> bv_unsigned a4 = r + j -> 0 <= j < e ->
     skip is_lead_blank (first_line zs) = skipn (Z.to_nat j) (first_line zs) ->
     evt rsegs Q (ST 0x12f38 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k j (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word),
  0 <= j -> j + Z.of_nat (S k) = e ->
  skip is_lead_blank (first_line zs) = skip is_lead_blank (skipn (Z.to_nat j) (first_line zs)) ->
  bv_unsigned a1 = 32 -> bv_unsigned a3 = 9 -> bv_unsigned a2 = j ->
  evt rsegs Q (ST 0x12f18 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 Hs3 KB KN k. induction k as [|k IH];
    intros j a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hj0 Hk Hinv Ha1 Ha3 Ha2.
  all: pose proof eloc as Hel.
  all: assert (Hje : 0 <= j < e) by lia.
  all: assert (Hin : 0 <= j < n) by lia.
  all: pose proof (BR j) as Hb.
  all: rewrite (flsfx_cons j Hje) in Hinv.
  all: step. all: step. all: take false.
  all: pose proof (RD j Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR j)).
  all: step.
  all: destruct (Z.eq_dec (nthz zs j) 32) as [E32|E32];
       [ | destruct (Z.eq_dec (nthz zs j) 9) as [E9|E9] ].
  (* k = 0 *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    take true. step. step. take false. step. apply KB. exact Hinv.
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    take false. step. take false. step. step. take false. step. apply KB. exact Hinv.
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    take false. step. take true.
    apply (KN _ _ _ _ _ _ _ _ _ _ _ j); [anyfact | exact Ha2 | anyfact | lia |].
    rewrite Hinv. symmetry. apply flsfx_cons. lia.
  (* k = S k *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    take true. step. step. take true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha1 | exact Ha3 | fact].
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    take false. step. take false. step. step. take true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha1 | exact Ha3 | fact].
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    take false. step. take true.
    apply (KN _ _ _ _ _ _ _ _ _ _ _ j); [anyfact | exact Ha2 | anyfact | lia |].
    rewrite Hinv. symmetry. apply flsfx_cons. lia.
Qed.

(* the optional sign, 0x12f38 - 0x12f78, ending at the digit loop's head: d0 = j + (sign ? 1 : 0). The UBSan checks
   0x12f38 (r + j == NULL) and 0x12f40 (~r < j: r + j wraps) are not taken. *)
Lemma seg_sign : forall (s3 : word), bv_unsigned s3 = e ->
  forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) j,
  bv_unsigned a0 = nthz zs j -> bv_unsigned a2 = j -> bv_unsigned a4 = r + j -> 0 <= j < e ->
  (forall (a1' a2' a3' a4' a5' a6' a7' : word),
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = [] ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1' a2' a3' a4' a5' a6' a7' t0 t1 t2)) ->
  (forall (a1' a2' a3' a4' a5' a6' a7' : word) d0,
     bv_unsigned a1' = 0 -> bv_unsigned a2' = d0 -> bv_unsigned a3' = 2 ^ 64 - 1 - r -> bv_unsigned a4' = d0 ->
     bv_unsigned a5' = 9 -> bv_unsigned a6' = 9999999999 -> bv_unsigned a7' = 10 -> j <= d0 < e ->
     sign_split (skipn (Z.to_nat j) (first_line zs)) = (nthz zs j =? 45, skipn (Z.to_nat d0) (first_line zs)) ->
     evt rsegs Q (ST 0x12f7c (Z_to_bv 64 cur) s3 a0 a1' a2' a3' a4' a5' a6' a7' t0 t1 t2)) ->
  evt rsegs Q (ST 0x12f38 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 Hs3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 j Ha0 Ha2 Ha4 Hje KZ KD.
  pose proof (BR j) as Hb. pose proof eloc as Hel.
  assert (SP : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx_cons; lia).
  step. take false. step.
  rewrite ?(unsigned_lit r) by lia. rewrite ?(zb_lxor_ones r) by lia.
  step. take false.
  step. step.
  destruct (Z.eq_dec (nthz zs j) 43) as [E43|E43].
  { (* '+' *)
    assert (SG : sign_split (skipn (Z.to_nat j) (first_line zs)) =
                 (nthz zs j =? 45, skipn (Z.to_nat (j + 1)) (first_line zs)))
      by (rewrite SP, (ss_plus _ _ E43), E43; reflexivity).
    take true. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - take true. apply KZ. rewrite SG, Ee. cbn [snd]. apply skipn_all2. lia.
    - take false. do 8 step.
      apply (KD _ _ _ _ _ _ _ (j + 1)); [anyfact | anyfact | anyfact | anyfact | anyfact | anyfact | anyfact
        | lia | exact SG]. }
  destruct (Z.eq_dec (nthz zs j) 45) as [E45|E45].
  { (* '-' *)
    assert (SG : sign_split (skipn (Z.to_nat j) (first_line zs)) =
                 (nthz zs j =? 45, skipn (Z.to_nat (j + 1)) (first_line zs)))
      by (rewrite SP, (ss_minus _ _ E45), E45; reflexivity).
    take false. step. step. take false. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - take true. apply KZ. rewrite SG, Ee. cbn [snd]. apply skipn_all2. lia.
    - take false. do 8 step.
      apply (KD _ _ _ _ _ _ _ (j + 1)); [anyfact | anyfact | anyfact | anyfact | anyfact | anyfact | anyfact
        | lia | exact SG]. }
  (* no sign *)
  assert (SG : sign_split (skipn (Z.to_nat j) (first_line zs)) =
               (nthz zs j =? 45, skipn (Z.to_nat j) (first_line zs))).
  { rewrite SP at 1. rewrite (ss_none _ _ E43 E45), <- SP. rewrite (proj2 (Z.eqb_neq _ _) E45). reflexivity. }
  take false. step. step. take true. step. take false. do 8 step.
  apply (KD _ _ _ _ _ _ _ j); [anyfact | anyfact | anyfact | anyfact | anyfact | anyfact | anyfact | lia | exact SG].
Qed.

(* the signed-overflow test of v * 10 (0x12f94 - 0x12fa0): for v < 10^10 the high word and the sign of the low
   word are both 0 *)
Lemma mul_nov : forall (a1 a7 : word) v, bv_unsigned a1 = v -> bv_unsigned a7 = 10 -> 0 <= v < 10 ^ 10 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_signed a1 * bv_signed a7) 64))
         (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (bv_unsigned a1 * bv_unsigned a7))) 63)) = true.
Proof.
  intros a1 a7 v H1 H7 Hv.
  rewrite !zb_signed, H1, H7. rewrite (unsigned_lit (v * 10)) by lia.
  replace (v <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (10 <? 2 ^ 63) with true by reflexivity.
  replace (v * 10 <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.div_small (v * 10) (2 ^ 64)) by lia. rewrite (Z.div_small (v * 10) (2 ^ 63)) by lia.
  reflexivity.
Qed.

(* the digit loop: 0x12f7c, a4 = i, a1 = v. The UBSan checks: 0x12f7c (~r < i: r + i wraps) is not taken; the
   multiply runs only for v <= 9999999999 (0x12f90), so its signed-overflow check 0x12fa0 is not taken. *)
Lemma loop_dg : forall (s3 a0 a2 a3 a5 a6 a7 : word) d0, bv_unsigned s3 = e -> bv_unsigned a2 = d0 ->
  bv_unsigned a3 = 2 ^ 64 - 1 - r -> bv_unsigned a5 = 9 -> bv_unsigned a6 = 9999999999 -> bv_unsigned a7 = 10 ->
  0 <= d0 ->
  (forall (a1 a4 t0 t1 t2 : word) i vf,
     bv_unsigned a4 = i -> bv_unsigned a1 = vf -> 0 <= vf < 10 ^ 11 -> d0 <= i <= e ->
     digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
     (i = d0 /\ is_digit (nthz zs d0) = false) \/ d0 < i ->
     evt rsegs Q (ST 0x12fb8 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k i v (a1 a4 t0 t1 t2 : word),
  d0 <= i -> i + Z.of_nat (S k) = e -> 0 <= v < 10 ^ 11 ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = digits_ev v (skipn (Z.to_nat i) (first_line zs)) ->
  bv_unsigned a4 = i -> bv_unsigned a1 = v ->
  evt rsegs Q (ST 0x12f7c (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 a0 a2 a3 a5 a6 a7 d0 Hs3 Ha2 Ha3 Ha5 Ha6 Ha7 Hd0 K k. induction k as [|k IH];
    intros i v a1 a4 t0 t1 t2 Hdi Hk Hv Hinv Ha4 Ha1.
  all: pose proof eloc as Hel.
  all: assert (Hie : 0 <= i < e) by lia.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (flsfx_cons i Hie) in Hinv.
  all: step. all: take false.
  all: step.
  all: pose proof (RD i Hin) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR i)).
  all: step. all: step.
  all: destruct (is_digit (nthz zs i)) eqn:Dg;
       [ assert (Dgr : 48 <= nthz zs i <= 57) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_true_iff in D as [D1 D2]; apply Z.leb_le in D1; apply Z.leb_le in D2; lia)
       | assert (Dgr : nthz zs i < 48 \/ 57 < nthz zs i) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_false_iff in D as [D1|D1]; apply Z.leb_gt in D1; [left | right]; lia) ].
  (* k = 0, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    take false. step.
    destruct (Z.ltb_spec v (10 ^ 10)) as [Hlt|Hlt].
    + take false. step. step. step. step.
      rewrite (mul_nov a1 a7 v Ha1 Ha7 ltac:(lia)). cbn [negb]. cbv beta iota.
      step. rewrite (unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. take false. step.
      apply (K _ _ _ _ _ e (v * 10 + (nthz zs i - 48))); [anyfact | anyfact | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
    + take true. step. step. take false. step.
      apply (K _ _ _ _ _ e v); [anyfact | exact Ha1 | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
  (* k = 0, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    take true.
    apply (K _ _ _ _ _ i v); [exact Ha4 | exact Ha1 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
  (* k = S k, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    take false. step.
    destruct (Z.ltb_spec v (10 ^ 10)) as [Hlt|Hlt].
    + take false. step. step. step. step.
      rewrite (mul_nov a1 a7 v Ha1 Ha7 ltac:(lia)). cbn [negb]. cbv beta iota.
      step. rewrite (unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. take true.
      apply (IH (i + 1) (v * 10 + (nthz zs i - 48))); [lia | lia | lia | exact Hinv | anyfact | anyfact].
    + take true. step. step. take true.
      apply (IH (i + 1) v); [lia | lia | lia | exact Hinv | anyfact | exact Ha1].
  (* k = S k, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    take true.
    apply (K _ _ _ _ _ i v); [exact Ha4 | exact Ha1 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
Qed.

(* the trailing-blank loop: 0x12fd0, a4 = p, a5 the {9, 13, 32} mask; its 0x12fd0 wrap check on r + p is not taken *)
Lemma loop_tb : forall (s3 a0 a1 a2 a3 a5 a7 t0 t1 t2 : word) i_f, bv_unsigned s3 = e -> bv_unsigned a2 = 32 ->
  bv_unsigned a3 = 2 ^ 64 - 1 - r -> bv_unsigned a5 = 4294976000 ->
  (forall (a4 a6 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     evt rsegs Q (ST 0x12ffc (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (a4 a6 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k p (a4 a6 : word),
  0 <= p -> p + Z.of_nat (S k) = e ->
  skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) =
    skip is_trail_blank (skipn (Z.to_nat p) (first_line zs)) ->
  bv_unsigned a4 = p ->
  evt rsegs Q (ST 0x12fd0 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 a0 a1 a2 a3 a5 a7 t0 t1 t2 i_f Hs3 Ha2 Ha3 Ha5 KE KN k. induction k as [|k IH];
    intros p a4 a6 Hp0 Hk Hinv Ha4.
  all: pose proof eloc as Hel.
  all: assert (Hpe : 0 <= p < e) by lia.
  all: assert (Hpn : 0 <= p < n) by lia.
  all: pose proof (BR p) as Hb.
  all: rewrite (flsfx_cons p Hpe) in Hinv.
  all: step. all: take false.
  all: step.
  all: pose proof (RD p Hpn) as Rd; step; clear Rd.
  all: rewrite (zxb_lit _ (BR p)).
  all: step.
  all: destruct (Z_le_gt_dec (nthz zs p) 32) as [H32|H32];
       [ take false; step;
         rewrite Ha5, (unsigned_lit (nthz zs p)) by lia; rewrite (Z.mod_small (nthz zs p) 64) by lia;
         step; rewrite (mask_u (nthz zs p) ltac:(lia));
         destruct (is_trail_blank (nthz zs p)) eqn:Tb; cbv beta iota; step
       | take true ].
  (* k = 0: blank, end reached *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    take false. step. step. take false. step.
    apply KE. rewrite Hinv, skipn_all2 by lia. reflexivity.
  (* k = 0: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    take true. step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = 0: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false) by (apply tb_big; lia).
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: blank, loop *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    take false. step. step. take true.
    apply (IH (p + 1)); [lia | lia | exact Hinv | anyfact].
  (* k = S k: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    take true. step. take true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false) by (apply tb_big; lia).
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. take true.
    apply KN. rewrite Hinv. discriminate.
Qed.

(* 0x12fb8 - 0x12fcc: no digit read (i_f = d0), all read (i_f = e), or the trailing scan *)
Lemma seg_after : forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) d0 i_f,
  bv_unsigned s3 = e -> bv_unsigned a2 = d0 -> bv_unsigned a3 = 2 ^ 64 - 1 - r -> bv_unsigned a4 = i_f ->
  0 <= d0 <= i_f -> i_f <= e ->
  (i_f = d0 -> evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (a2' a4' a5' a6' : word), d0 < i_f -> skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     evt rsegs Q (ST 0x12ffc (Z_to_bv 64 cur) s3 a0 a1 a2' a3 a4' a5' a6' a7 t0 t1 t2)) ->
  (forall (a2' a4' a5' a6' : word), d0 < i_f -> skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2' a3 a4' a5' a6' a7 t0 t1 t2)) ->
  evt rsegs Q (ST 0x12fb8 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 d0 i_f Hs3 Ha2 Ha3 Ha4 Hd Hie K0 KE KN.
  pose proof eloc as Hel.
  step. destruct (Z.eq_dec i_f d0) as [Ed|Ed]; [take true; apply K0; exact Ed | take false].
  step. destruct (Z.eq_dec i_f e) as [Ee|Ee].
  - take true. step. take false. apply KE; [lia |]. rewrite Ee, skipn_all2 by lia. reflexivity.
  - take false. do 4 step.
    eapply (loop_tb s3 a0 a1 _ a3 _ a7 t0 t1 t2 i_f Hs3 _ Ha3 _ _ _ (Z.to_nat (e - i_f - 1)) i_f).
    Unshelve.
    all: first [ exact Ha4 | anyfact | lia | reflexivity
               | (intros ? ? H; first [apply KE | apply KN]; [lia | exact H]) ].
Qed.

(* the value finish computes once the trailing scan reached the end *)
Definition fin_val (neg : bool) (vf c : Z) : Z :=
  let v' := if neg then - vf else vf in if (v' <? INT_MIN) || (INT_MAX <? v') then c else v'.

(* the int-range test sext.w / bne (0x13014 - 0x13018) *)
Lemma sext_eq : forall (w : word) v, bv_unsigned w = v mod 2 ^ 64 -> - 2 ^ 40 < v < 2 ^ 40 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0))) w = negb ((v <? INT_MIN) || (INT_MAX <? v)).
Proof.
  intros w v H Hv. unfold bv_eqb. rewrite unsigned_lit_wrap, H.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  unfold INT_MIN, INT_MAX.
  destruct (Z.ltb_spec v (- 2 ^ 31)) as [L1|L1]; destruct (Z.ltb_spec (2 ^ 31 - 1) v) as [L2|L2];
    cbn [orb negb].
  - exfalso. lia.
  - apply Z.eqb_neq. Z.div_mod_to_equations. lia.
  - apply Z.eqb_neq. Z.div_mod_to_equations. lia.
  - apply Z.eqb_eq. Z.div_mod_to_equations. lia.
Qed.

(* the UBSan negation-overflow test (0x13004 - 0x13010): v > 0 and -v < 0 agree for 0 <= v < 2^62 *)
Lemma neg_nov : forall (a1 : word) v, bv_unsigned a1 = v -> 0 <= v < 2 ^ 62 ->
  bv_eqb (v_slt (Z_to_bv 64 0) a1) (v_slti (Z_to_bv 64 (0 - bv_unsigned a1)) 0) = true.
Proof.
  intros a1 v H Hv. unfold v_slt, v_slti, c_lts, zsig, bv_lts. rewrite !zb_signed, H.
  rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.eq_dec v 0) as [->|Hne].
  - vm_compute. reflexivity.
  - replace ((0 - v) mod 2 ^ 64) with (2 ^ 64 - v) by (Z.div_mod_to_equations; lia).
    replace (0 <? 2 ^ 63) with true by reflexivity.
    replace (v <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (2 ^ 64 - v <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (2 ^ 64 - v - 2 ^ 64 <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

(* 0x12ffc - 0x1301c: the sign, the UBSan negation check 0x13010 (not taken: 0 <= vf < 10^11), and the int-range
   test; s0 = the value, or cur when it is out of range *)
Lemma seg_fin : forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) c vf,
  bv_unsigned a0 = c -> bv_unsigned a1 = vf -> 0 <= vf < 10 ^ 11 ->
  (forall (s0 a0' a1' a2' : word), bv_unsigned s0 = fin_val (c =? 45) vf cur mod 2 ^ 64 ->
     evt rsegs Q (ST 0x13020 s0 s3 a0' a1' a2' a3 a4 a5 a6 a7 t0 t1 t2)) ->
  evt rsegs Q (ST 0x12ffc (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 c vf Ha0 Ha1 Hv KF.
  step. step.
  destruct (Z.eq_dec c 45) as [E45|E45].
  - assert (FV : fin_val (c =? 45) vf cur = (if (- vf <? INT_MIN) || (INT_MAX <? - vf) then cur else - vf))
      by (unfold fin_val; rewrite (proj2 (Z.eqb_eq c 45) E45); reflexivity).
    rewrite FV in KF.
    take false. step. step. step. step.
    rewrite (neg_nov a1 vf Ha1 ltac:(lia)). cbn [negb]. cbv beta iota.
    step. step.
    rewrite (sext_eq (Z_to_bv 64 (0 - bv_unsigned a1)) (- vf)) by (rewrite ?unsigned_lit_wrap, ?Ha1; first [lia | mlia]).
    destruct ((- vf <? INT_MIN) || (INT_MAX <? - vf)) eqn:Rg; cbn [negb]; cbv beta iota.
    + apply KF. rewrite unsigned_lit_wrap. reflexivity.
    + step. apply KF. fact.
  - assert (FV : fin_val (c =? 45) vf cur = (if (vf <? INT_MIN) || (INT_MAX <? vf) then cur else vf))
      by (unfold fin_val; rewrite (proj2 (Z.eqb_neq c 45) E45); reflexivity).
    rewrite FV in KF.
    take true. step. step.
    rewrite (sext_eq a1 vf) by (rewrite ?Ha1; first [lia | mlia]).
    destruct ((vf <? INT_MIN) || (INT_MAX <? vf)) eqn:Rg; cbn [negb]; cbv beta iota.
    + apply KF. rewrite unsigned_lit_wrap. reflexivity.
    + step. apply KF. fact.
Qed.

(* ---- the model at each exit ---- *)

Lemma finish_nil : forall neg vf rest c, skip is_trail_blank rest = [] -> finish neg vf rest c = fin_val neg vf c.
Proof. intros neg vf rest c H. unfold finish, fin_val. rewrite H. reflexivity. Qed.

Lemma finish_cons : forall neg vf rest c, skip is_trail_blank rest <> [] -> finish neg vf rest c = c.
Proof. intros neg vf rest c H. unfold finish. destruct (skip is_trail_blank rest); [contradiction | reflexivity]. Qed.

Lemma ev_m_e0 : e = 0 -> expected_value_m zs cur = cur.
Proof.
  intros E0. assert (FL : first_line zs = []) by (destruct (first_line zs); [reflexivity | cbn in HE; lia]).
  unfold expected_value_m. rewrite FL. reflexivity.
Qed.

Lemma ev_m_lb_nil : skip is_lead_blank (first_line zs) = [] -> expected_value_m zs cur = cur.
Proof. intros H. unfold expected_value_m. rewrite H. reflexivity. Qed.

Lemma ev_m_sign_nil : forall j, skip is_lead_blank (first_line zs) = skipn (Z.to_nat j) (first_line zs) ->
  snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = [] -> expected_value_m zs cur = cur.
Proof.
  intros j H1 H2. unfold expected_value_m. rewrite H1.
  destruct (sign_split (skipn (Z.to_nat j) (first_line zs))) as [neg l]. cbn [snd] in H2. subst l. reflexivity.
Qed.

Lemma ev_m_nodigit : forall j d0 b, skip is_lead_blank (first_line zs) = skipn (Z.to_nat j) (first_line zs) ->
  sign_split (skipn (Z.to_nat j) (first_line zs)) = (b, skipn (Z.to_nat d0) (first_line zs)) ->
  0 <= d0 < e -> is_digit (nthz zs d0) = false -> expected_value_m zs cur = cur.
Proof.
  intros j d0 b H1 H2 Hd D. unfold expected_value_m. rewrite H1, H2, (flsfx_cons d0 Hd).
  cbv beta iota zeta. rewrite D. reflexivity.
Qed.

Lemma ev_m_digits : forall j d0 i vf b, skip is_lead_blank (first_line zs) = skipn (Z.to_nat j) (first_line zs) ->
  sign_split (skipn (Z.to_nat j) (first_line zs)) = (b, skipn (Z.to_nat d0) (first_line zs)) ->
  0 <= d0 < i -> i <= e ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
  expected_value_m zs cur = finish b vf (skipn (Z.to_nat i) (first_line zs)) cur.
Proof.
  intros j d0 i vf b H1 H2 Hd Hi H3.
  pose proof eloc as Hel.
  assert (Hd' : 0 <= d0 < e) by lia.
  destruct (is_digit (nthz zs d0)) eqn:D.
  - unfold expected_value_m. rewrite H1, H2. cbv beta iota zeta. rewrite H3, (flsfx_cons d0 Hd').
    cbv beta iota zeta. rewrite D. reflexivity.
  - exfalso. rewrite (flsfx_cons d0 Hd'), (digits_ev_stop _ _ _ D) in H3.
    injection H3 as _ H4. apply (f_equal (@length Z)) in H4.
    cbn [length] in H4. rewrite !length_skipn in H4. lia.
Qed.

Lemma snez_fact : forall x, 0 < x < 2 ^ 64 -> bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x)) = 1.
Proof.
  intros x Hx. rewrite v_sltu_b2z, (unsigned_lit 0), (unsigned_lit x) by lia.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* the whole inlined expected_value: 0x12ea8 to 0x13020, with s0 = its value *)
Lemma ev_all :
  (forall (s0 s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word),
     bv_unsigned s0 = expected_value_m zs cur mod 2 ^ 64 ->
     evt rsegs Q (ST 0x13020 s0 s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word),
  evt rsegs Q (ST 0x12ea8 (Z_to_bv 64 cur) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros KEND a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2.
  pose proof eloc as Hel.
  assert (KC : forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), expected_value_m zs cur = cur ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)).
  { intros s3 b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 H. apply KEND. rewrite H, unsigned_lit_wrap. reflexivity. }
  assert (K0 : forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), e = 0 ->
     evt rsegs Q (ST 0x13020 (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)).
  { intros s3 b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 H. apply KC. exact (ev_m_e0 H). }
  assert (K1 : forall (s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), bv_unsigned s3 = e -> 0 < e ->
     evt rsegs Q (ST 0x12f0c (Z_to_bv 64 cur) s3 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)).
  { intros s3 b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 Hs3 He0.
    do 3 step.
    apply (loop_lb s3 Hs3) with (k := Z.to_nat (e - 1)) (j := 0);
      [ | | lia | lia | reflexivity | anyfact | anyfact | anyfact ].
    - intros c0 c1 c2 c3 c4 c5 c6 c7 v0 v1 v2 Hsk. apply KC. exact (ev_m_lb_nil Hsk).
    - intros c0 c1 c2 c3 c4 c5 c6 c7 v0 v1 v2 j Hc0 Hc2 Hc4 Hje Hsk.
      apply (seg_sign s3 Hs3 c0 c1 c2 c3 c4 c5 c6 c7 v0 v1 v2 j Hc0 Hc2 Hc4 Hje).
      + intros d1 d2 d3 d4 d5 d6 d7 Hsn. apply KC. exact (ev_m_sign_nil j Hsk Hsn).
      + intros d1 d2 d3 d4 d5 d6 d7 d0 Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd0 SG.
        apply (loop_dg s3 c0 d2 d3 d5 d6 d7 d0 Hs3 Hd2 Hd3 Hd5 Hd6 Hd7 ltac:(lia))
          with (k := Z.to_nat (e - d0 - 1)) (i := d0) (v := 0);
          [ | lia | lia | lia | reflexivity | exact Hd4 | exact Hd1 ].
        intros f1 f4 w0 w1 w2 i vf Hf4 Hf1 Hvf Hi Hdg Hcase.
        apply (seg_after s3 c0 f1 d2 d3 f4 d5 d6 d7 w0 w1 w2 d0 i Hs3 Hd2 Hd3 Hf4 ltac:(lia) ltac:(lia)).
        * intros Eid. apply KC. destruct Hcase as [[_ Dg] | Hlt]; [|lia].
          exact (ev_m_nodigit j d0 _ Hsk SG ltac:(lia) Dg).
        * intros g2 g4 g5 g6 Hlt Hnil.
          apply (seg_fin s3 c0 f1 g2 d3 g4 g5 g6 d7 w0 w1 w2 (nthz zs j) vf Hc0 Hf1 Hvf).
          intros s0 h0 h1 h2 Hs0. apply KEND.
          rewrite (ev_m_digits j d0 i vf _ Hsk SG ltac:(lia) ltac:(lia) Hdg), (finish_nil _ _ _ _ Hnil).
          exact Hs0.
        * intros g2 g4 g5 g6 Hlt Hcons. apply KC.
          rewrite (ev_m_digits j d0 i vf _ Hsk SG ltac:(lia) ltac:(lia) Hdg). apply finish_cons. exact Hcons. }
  do 6 step.
  apply (loop_nl K0 K1) with (k := Z.to_nat (n - 1)) (i := 0);
    [ lia | lia | replace (skipn (Z.to_nat 0) zs) with zs by reflexivity; lia | anyfact | anyfact
    | first [anyfact | apply snez_fact; lia]
    | anyfact | anyfact | anyfact ].
Qed.

End Ev.

(* ---------------- the straight-line segments of the call ---------------- *)

Local Ltac crt_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Local Ltac crt_usub :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

Local Ltac crt_w := crt_usub; rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Local Ltac crt_fin := apply evt_done; f_equal; crt_regs; crt_w.

(* the jal targets on the UBSan image: malloc (0x12e78) and free (0x1302c) *)
Definition CV_MALLOC : Z := 0x13f74.
Definition CV_FREE : Z := 0x13e34.

(* 0x12e48 - 0x12e78: the frame is pushed (ra, s0 - s4), s0 = cur, s3 = n, s4 = r, a0 = n ? n : 1, malloc *)
Definition cv_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r n cur : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x12e7c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 cur) s1
               (Z_to_bv 64 (fuzz_dup_size n)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 r)
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* `seqz a0, a1` + `add a0, a1, a0` is fuzz_dup's n ? n : 1 *)
Lemma fds_val : forall n, 0 <= n <= 255 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (fuzz_dup_size n).
Proof.
  intros n Hn. unfold v_sltiu, fuzz_dup_size. rewrite (unsigned_lit n) by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  destruct (Z.eqb_spec n 0) as [->|H].
  - apply bv_eq. vm_compute. reflexivity.
  - replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

Lemma cv_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    0 <= n <= 255 ->
    evt rsegs (cv_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r n cur m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 n) (Z_to_bv 64 cur)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r n cur lo
    ST LO HN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 13 step.
  apply evt_done. unfold cv_s1_post.
  do 15 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
       eassumption. }
  f_equal; crt_regs; try crt_w.
  apply fds_val. exact HN.
Qed.

(* 0x13030 - 0x13050: a0 = s2, the frame is popped, ret *)
Lemma cv_seg3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 v1 v2 v3 v4 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 s2 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13030) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 v4 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 9 step.
  crt_fin.
Qed.

(* what segment 2 may write: rp_uci_int's 32-byte frame below sp, and the k-byte block c = P *)
Definition cv_W (sp P k : Z) : list (Z * Z) := [(sp - 32, sp); (P, P + k)].

(* segment 2 ends at free(c) with ra = 0x13030, s1 = a0 = c, s2 = got and the frame (outside cv_W) untouched *)
Definition cv_s2_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P k got : Z) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x13030) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 got) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_FREE) fc None m' (seg_rom rsegs) /\
    munch (cv_W (bv_unsigned sp) P k) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Lemma cv_subS : forall sp P k, sub_fp [(sp - 32, sp)] (cv_W sp P k).
Proof. intros sp P k x Hx. unfold cv_W in Hx. cbn [outside] in *. tauto. Qed.

Lemma cv_subP : forall sp P k j, j <= k -> sub_fp [(P, P + j)] (cv_W sp P k).
Proof. intros sp P k j Hj x Hx. unfold cv_W in Hx. cbn [outside] in *. split; [lia | exact I]. Qed.

Lemma cv_cells_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof.
  intros m A k bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma skipn_nth_g : forall {T : Type} (d : T) (l : list T) (i : nat), (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros T d l. induction l as [|c t IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [skipn nth]; [reflexivity|]. apply IH. lia.
Qed.

(* a reply byte as the loops read it, and the bound on its model value *)
Lemma rd_of_bytes : forall m r bs i, bytes_at rsegs m r bs -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (r + i)) 1 = Some [Z_to_bv 8 (nthz (zbytes bs) i)].
Proof.
  intros m r bs i H Hi.
  change (Z_to_bv 64 (r + i)) with (wa (r + i)).
  rewrite (bytes_at_read rsegs m r bs i 1 H ltac:(lia) ltac:(lia)).
  rewrite (skipn_nth_g (Z_to_bv 8 0) bs (Z.to_nat i) ltac:(lia)). cbn [firstn].
  f_equal. f_equal. unfold nthz, zbytes.
  rewrite (nth_indep (map (@bv_unsigned 8) bs) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma br_zbytes : forall bs i, 0 <= nthz (zbytes bs) i < 256.
Proof.
  intros bs i. unfold nthz, zbytes.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [Hl|Hl].
  - rewrite (nth_indep (map (@bv_unsigned 8) bs) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
  - rewrite nth_overflow by (rewrite length_map; lia). lia.
Qed.

Lemma len_zbytes : forall bs, length (zbytes bs) = length bs.
Proof. intros bs. unfold zbytes. apply length_map. Qed.

(* `sext.w s0, s0` at 0x13020 leaves an int unchanged *)
Lemma sext_self : forall (s0 : word) X, bv_unsigned s0 = X mod 2 ^ 64 -> INT_MIN <= X <= INT_MAX ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned s0 + 0)) = Z_to_bv 64 X.
Proof.
  intros s0 X H HX. rewrite H. apply Z_to_bv_eqm.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  unfold INT_MIN, INT_MAX in HX. Z.div_mod_to_equations. lia.
Qed.

(* 0x13020 - 0x1302c: s0 = (int) s0; the property test `bne s2, s0` to the abort at 0x13054 is not taken because
   s0 and s2 hold the same int; free(c) *)
Lemma cv_tail :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (P k X : Z),
    bv_unsigned s0 = X mod 2 ^ 64 -> INT_MIN <= X <= INT_MAX -> 0 <= P < 2 ^ 64 ->
    munch (cv_W (bv_unsigned sp) P k) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs (cv_s2_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc P k X m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 X) s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13020) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m P k X
    Hs0 HX HP MU WM MI.
  step. rewrite (sext_self s0 X Hs0 HX).
  step.
  lazymatch goal with
  | |- context [negb (bv_eqb ?x ?x)] =>
      replace (negb (bv_eqb x x)) with false by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity)
  end; cbv iota.
  step. step.
  apply evt_done. unfold cv_s2_post.
  do 18 eexists. split; [f_equal; crt_regs; crt_w|].
  split; [exact MU|]. split; [exact WM | exact MI].
Qed.

Local Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Local Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  do 3 (decide_tests; cbv beta iota; cbn [Z.b2z]); reflexivity.
Local Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv beta iota | symmetry; solve_c]
  end.

(* 0x12e7c - 0x1302c: fuzz_dup's NULL test and copy, rp_uci_int(c, n, cur), the inlined expected_value, the property
   test and free(c). The `beqz a0` at 0x12e7c to the abort at 0x13054 is not taken: c = P >= 4096 (the allocator's
   block, FuzzDup.fuzz_dup_no_null). rp_uci_int's UBSan premise `bv_unsigned a0 <> 0` holds for the same reason. *)
Lemma cv_seg2 : memcpy_contract -> rp_uci_int_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 s2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur P : Z) (bs : list byte),
    Z.of_nat (length bs) = n -> 0 <= n <= 255 -> INT_MIN <= cur <= INT_MAX ->
    4096 <= P -> P + fuzz_dup_size n <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 63 ->
    (0 < n -> 4096 <= r /\ r + n <= bv_unsigned sp - 32 /\ (r + n <= P \/ P + n <= r) /\ bytes_at rsegs m r bs) ->
    mem_inv rsegs m ->
    stk rsegs m P (P + fuzz_dup_size n) -> stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
    evt rsegs (cv_s2_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc P (fuzz_dup_size n) (rp_uci_int_m (zbytes bs) cur) m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 cur) s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 n) (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e7c) fc None m (seg_rom rsegs)).
Proof.
  intros MC RUI ra sp gp tp t0 t1 t2 s1 s2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r n cur P bs
    HL HN HC HP HPS HSP HR MI SP ST.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2].
  (* 0x12e7c beqz a0: c == NULL, to the abort at 0x13054; not taken; 0x12e80 s1 = c *)
  step. take false. step.
  (* 0x12e84 beqz s3: n == 0 *)
  step. destruct (Z.eq_dec n 0) as [E0|Hn0].
  - assert (Ebs : bs = []) by (destruct bs as [|b0 bs']; [reflexivity | cbn in HL; lia]). subst bs.
    change (Z.of_nat (length (@nil byte))) with 0 in HL. subst n.
    take true.
    (* 0x12ef0 - 0x12ef8: rp_uci_int(c, 0, cur) *)
    do 3 step.
    eapply evt_cut.
    { eapply RUI with (bs := []) (cur := cur) (lo := bv_unsigned sp - 32) (m := m).
      all: try rewrite (unsigned_lit P) by lia.
      - lia.
      - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
      - cbn. lia.
      - vm_compute. reflexivity.
      - first [reflexivity | f_equal; lia].
      - exact HC.
      - exact MI.
      - exact ST.
      - unfold RP_UCI_INT_FRAME. lia.
      - exact HSP.
      - unfold RP_UCI_INT_FRAME. cbn. lia. }
    intros ms3 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 &
      ST3 & BP3).
    rewrite ret_pc_even by first [lia | reflexivity].
    unfold RP_UCI_INT_FRAME in MU3.
    (* 0x12efc s2 = got; 0x12f00 j 0x13020 *)
    step. step.
    rewrite ?Z.add_0_r.
    eapply cv_tail.
    + rewrite unsigned_lit_wrap. reflexivity.
    + apply rp_uci_int_range. exact HC.
    + lia.
    + exact (munch_weaken _ _ m m3 (cv_subS (bv_unsigned sp) P _) MU3).
    + exact WM3.
    + exact MI3.
  - take false.
    destruct (HR ltac:(lia)) as (Hr0 & Hr1 & DRP & BR).
    assert (Hnz : fuzz_dup_size n = n) by (unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia).
    rewrite Hnz in *.
    (* 0x12e88 - 0x12e90: memcpy(c, r, n) *)
    do 3 step.
    destruct (stk_carve rsegs m P (P + n) (Z.to_nat n) SP ltac:(lia)) as [_ (jP & CP)].
    replace (P + n - Z.of_nat (Z.to_nat n)) with P in CP by lia.
    eapply evt_cut.
    { eapply MC with (src := bs) (junk := jP).
      - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact BR.
      - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. lia.
      - rewrite !unsigned_lit by lia. rewrite ?Z.add_0_r. exact CP.
      - rewrite !unsigned_lit by lia. rewrite ?Z.add_0_r. lia.
      - exact MI. }
    intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 &
      CP1 & BR1).
    rewrite ret_pc_even by first [lia | reflexivity].
    rewrite !unsigned_lit in MU1 by lia. rewrite ?unsigned_lit in CP1 by lia. rewrite ?unsigned_lit in BR1 by lia.
    rewrite ?Z.add_0_r in MU1, CP1, BR1.
    pose proof (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1 ltac:(cbn [disjoint_from]; lia)) as ST1.
    pose proof (munch_weaken _ _ m m1 (cv_subP (bv_unsigned sp) P n n ltac:(lia)) MU1) as MU1'.
    pose proof (cv_cells_bytes m1 P _ bs CP1) as BP1.
    (* 0x12e94 - 0x12ea0: rp_uci_int(c, n, cur); its UBSan premise c != NULL: 4096 <= P *)
    do 4 step.
    eapply evt_cut.
    { eapply RUI with (bs := bs) (cur := cur) (lo := bv_unsigned sp - 32) (m := m1).
      all: rewrite ?unsigned_lit by lia; rewrite ?Z.add_0_r.
      - lia.
      - exact BP1.
      - lia.
      - lia.
      - first [reflexivity | f_equal; lia].
      - exact HC.
      - exact MI1.
      - exact ST1.
      - unfold RP_UCI_INT_FRAME. lia.
      - exact HSP.
      - unfold RP_UCI_INT_FRAME. lia. }
    intros ms2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 &
      ST2 & BP2).
    rewrite ret_pc_even by first [lia | reflexivity].
    unfold RP_UCI_INT_FRAME in MU2.
    pose proof (bytes_at_transport rsegs _ m1 m2 r bs BR1 MU2 ltac:(cbn [disjoint_from]; lia)) as BR2.
    pose proof (munch_trans _ m m1 m2 MU1' (munch_weaken _ _ m1 m2 (cv_subS (bv_unsigned sp) P n) MU2)) as MU2'.
    pose proof (wmono_trans rsegs m m1 m2 WM1 WM2) as WM2'.
    (* 0x12ea4 s2 = got *)
    step. rewrite ?Z.add_0_r.
    (* 0x12ea8 - 0x13020: the inlined expected_value *)
    eapply ev_all with (zs := zbytes bs) (e := Z.of_nat (length (first_line (zbytes bs)))).
    Unshelve.
    all: try lia.
    all: try reflexivity.
    + rewrite len_zbytes. exact HL.
    + exact (br_zbytes bs).
    + intros i Hi. apply rd_of_bytes; [exact BR2 | lia].
    + intros s0 s3 x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 Hs0.
      eapply cv_tail; [rewrite uci_value_ok; exact Hs0 | apply rp_uci_int_range; exact HC | lia | exact MU2'
        | exact WM2' | exact MI2].
Qed.

(* ---------------- the SR level: the allocator calls between the segments ---------------- *)

Lemma cv_not_out2 : forall a1 b1 a2 b2 x,
  ~ Frame.outside [(a1, b1); (a2, b2)] x -> (a1 <= x < b1) \/ (a2 <= x < b2).
Proof. intros a1 b1 a2 b2 x H. cbn [Frame.outside] in H. lia. Qed.

(* From here on the names are the contract's: the allocator's ceiling (lib/U/Reusable/YM05.v), and YK11's getr /
   mkst, which the Lib imports above shadow *)
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).
Local Abbreviation getr := YK11.getr (only parsing).
Local Abbreviation mkst := YK11.mkst (only parsing).

Section CV.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x13f74.
Hypothesis FREEPC : ms_free B = 0x13e34.
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

(* a heap block, seen in the normalized memory of a crt_runN segment, is stack-like: writable and readable *)
Lemma cv_blk_stk : forall m a k, ro_agree (ms_segs B) m -> 0 <= a -> a + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> present m (a + i) /\ ~ in_img B (a + i)) ->
  stk rsegs (normalize rsegs m) a (a + k).
Proof.
  intros m a k Hro H0 H1 H. rewrite <- SEGS.
  pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H (x - a) ltac:(lia)) as [[bt Hb] Hni]. replace (a + (x - a)) with x in Hb, Hni by ring.
  assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa x) = false)
    by (apply crt_ro_false; [lia | exact (crt_fs_none B SEGS x Hni)]).
  split.
  - rewrite (wview_rel_rw (ms_segs B) m _ _ HR Hra). unfold wview, Mem.wa. rewrite Hb. discriminate.
  - exists bt. rewrite <- (mrd_rel (ms_segs B) m _ _ HR). unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity.
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

(* free(c) at 0x1302c, entered at free with ra = 0x13030, then the epilogue 0x13030 - 0x13050 *)
Lemma cv_ph3 : forall (fx7 : FPState) L3 A3 regs7 m7 md3 P c1 c2,
  frm_zero (@fp_csr fx7) ->
  cv_inv L3 A3 m7 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = c1 ++ (P, fuzz_dup_size n) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs7 1 = Z_to_bv 64 0x13030 -> getr regs7 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs7 10 = Z_to_bv 64 P -> getr regs7 18 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) ->
  cv_keep regs7 -> cv_frame m7 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CV_FREE) m7 (seg_rom (ms_segs B))) md3) cv_final.
Proof.
  intros fx7 L3 A3 regs7 m7 md3 P c1 c2 Hfrm I Hinit Hb3 Hb0 Hres G1 G2 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2].
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  assert (S7 : spZ regs7 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW3 : pairwise ranges_disjoint (c1 ++ (P, fuzz_dup_size n) :: c2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  destruct (crt_bu L3 A3 P _ ltac:(rewrite Hb3; apply crt_in_mid)) as (p & Hp & Ep).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 m7 md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 m7 md3)).
    apply (cg_pre B API CV_STACK L A regs mem md PRE L3 A3 m7 md3 regs7 48 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CV_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L3 A3 regs7 m7 md3 p (fuzz_dup_size n) (sb_malloc b (fuzz_dup_size n)) Hpre7 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Ep in Hd1.
  assert (ND3 : ~ In (P, fuzz_dup_size n) (c1 ++ c2)) by (apply (crt_notin c1 c2 _ PW3); cbn; lia).
  assert (Hb4 : blocks L4 A4 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (crt_rm (P, fuzz_dup_size n) c1 c2 d1 d2 ND3). rewrite <- Hb3. exact Hd1. }
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 p, fuzz_dup_size n) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid c1 c2 _ y PW3). rewrite <- Hb0. exact Hy. }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4;
      [exact (I3 q' k Hq') | exact (cg_free_keep B API CV_STACK L A regs mem md L3 A3 m7 md3 p _ I Hp
        ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cv_inv L4 A4 m8 md4).
  { apply (cg_inv_call B API CV_STACK L A regs mem md PRE AX CT L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8
      md4 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp)
      | exact Hlen4 | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cv_frame m8).
  { apply (cv_frame_call L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp a Ha)). }
  assert (G8a : getr regs8 2 = Z_to_bv 64 (spZ regs - 48))
    by (transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G2]).
  assert (G8b : getr regs8 18 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur))
    by (transitivity (getr regs7 18); [apply (Hp8 18); unfold callee_saved; lia | exact G18]).
  pose proof (cv_keep_pres regs7 regs8 GK Hp8) as GK8.
  (* the epilogue *)
  pose proof I4' as ((M4 & _) & _ & _ & _ & _).
  destruct (kb_md B API L4 A4 m8 md4 M4) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs8 2) = spZ regs - 48) by (rewrite G8a; apply MState.unsigned_lit; lia).
  rewrite G1.
  eapply (crt_runA (fx := fx7) B SEGS regs8 _ m8 md4); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply cv_seg3. rewrite USP. exact FR4. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs9 -> Hg9. cbn [MState.MS ms_pc_val ms_mem].
  rewrite (kb_ret_pc _ Hra).
  assert (G9a : getr regs9 1 = getr regs 1) by (rewrite Hg9; reflexivity).
  assert (G9b : getr regs9 2 = Z_to_bv 64 (bv_unsigned (getr regs8 2) + 48)) by (rewrite Hg9; reflexivity).
  rewrite USP in G9b. replace (spZ regs - 48 + 48) with (spZ regs) in G9b by lia.
  assert (G9c : getr regs9 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur)) by (rewrite Hg9; exact G8b).
  assert (P9 : regs_preserved regs regs9).
  { destruct GK8 as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs9 2 = getr regs 2) by (rewrite G9b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r' Hr. unfold callee_saved in Hr.
    assert (C : r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 8 \/ r' = 9 \/ r' = 18 \/ r' = 19 \/ r' = 20 \/ r' = 21 \/
                r' = 22 \/ r' = 23 \/ r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg9; first [reflexivity | exact K3 | exact K4 | exact K21 | exact K22 | exact K23
        | exact K24 | exact K25 | exact K26 | exact K27]]. }
  apply SR_ret. exists fx7, L4, A4, regs9, m8, md4.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I4' as (I4a & _). apply (kb_post B API); [exact I4a | exact P9]. }
  split; [exact G9c|].
  split; [exact Hb4|].
  split; [exact (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I4')|].
  destruct I4' as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres4; exact Hres4 | exact (Hinit4 Hinit)].
Qed.

(* 0x12e7c - 0x1302c as one crt_runN segment over the normalized memory (cv_seg2) *)
Lemma cv_ph2 : forall L1 A1 regs2 m2 md1 P c1 c2,
  cv_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, fuzz_dup_size n) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 cur -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 19 = Z_to_bv 64 n -> getr regs2 20 = Z_to_bv 64 r ->
  cv_keep regs2 -> cv_frame m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x12e7c) m2 (seg_rom (ms_segs B))) md1) cv_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G8 G10 G19 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2].
  pose proof I as ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (USP : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (c1 ++ (P, fuzz_dup_size n) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InP : In (P, fuzz_dup_size n) (blocks L1 A1)) by (rewrite Hb1; apply crt_in_mid).
  destruct (crt_blk B API AX L1 A1 m2 md1 P _ M1 InP) as (HP1 & HP2 & _ & HPi).
  (* the reply r: inside an old block, so apart from the new one and kept since entry *)
  assert (HR : 0 < n -> 4096 <= r /\ r + n <= spZ regs - 48 - 32 /\ (r + n <= P \/ P + n <= r) /\
                bytes_at rsegs (normalize rsegs m2) r bs).
  { intros Hn. destruct (IB Hn) as (qa & ka & Hqa & Ha1 & Ha2).
    destruct (crt_blk B API AX L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
    assert (Ac : In (qa, ka) (c1 ++ c2)) by (rewrite <- Hb0; exact Hqa).
    pose proof (crt_pw _ _ _ _ _ _ PW1 Ac) as DPA.
    assert (Hnz : fuzz_dup_size n = n) by (unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia).
    split; [lia|]. split; [lia|]. split; [lia|].
    apply (bytes_at_normalize rsegs); [exact Hro'|].
    apply cv_blk_bytes; [lia | lia |].
    pose proof (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I) as KP.
    intros i Hi. rewrite <- (BD i Hi).
    pose proof (KP qa ka (r - qa + i) Hqa (fun H => H) ltac:(lia)) as E.
    replace (qa + (r - qa + i)) with (r + i) in E by ring. exact E. }
  assert (Hold : forall y, In y (blocks L A) -> In y (c1 ++ c2)) by (intros y Hy; rewrite <- Hb0; exact Hy).
  assert (ST : stk rsegs (normalize rsegs m2) (spZ regs - 48 - 32) (spZ regs - 48)).
  { rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S1. left. lia. }
  assert (SPn : stk rsegs (normalize rsegs m2) P (P + fuzz_dup_size n)).
  { apply cv_blk_stk; [exact I4 | lia | lia |].
    intros i Hi. destruct (HPi i Hi) as (X1 & X2 & _). split; assumption. }
  eapply (crt_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G19, G20.
    apply (cv_seg2 MC RUI) with (r := r) (n := n) (cur := cur) (P := P) (bs := bs);
      rewrite ?USP; first [exact HL | exact HC | exact HR | exact (mem_inv_normalize rsegs m2) | exact SPn
        | exact ST | lia]. }
  { intros ms (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & x3 & x4 & x5 & x6 & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & x3 & x4 & x5 & x6 & m' & -> &
    MU & WM & MI') Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR'). cbn [ms_mem MState.MS] in HR'.
  rewrite USP in MU. unfold cv_W in MU.
  set (W := [(spZ regs - 48 - 32, spZ regs - 48); (P, P + fuzz_dup_size n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR' Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR' Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (cv_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CV_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (cv_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - left. lia.
    - right. destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (P + (x - P)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. pose proof (Hold _ (crt_ub L A p k Hp)) as Y1.
      pose proof (crt_pw _ _ _ _ _ _ PW1 Y1). lia. }
  pose proof (cg_inv_A B API CV_STACK L A regs mem md PRE SEGS L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7)
    as I7.
  assert (FR7 : cv_frame (ms_mem ms)).
  { unfold cv_frame in *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep B m2 (ms_mem ms) _ _ FR). intros i Hi.
    change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr].
  apply (cv_ph3 (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 P c1 c2 FRM I7 Hinit Hb1 Hb0 Hres);
    [rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity
    | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x12e48 - 0x12e78 and malloc(n ? n : 1), fuzz_dup's allocation *)
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
  { unfold rmk. rewrite R10, R11, R12. eapply cv_seg1; [exact ST | unfold spZ in *; lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12e7c) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (fuzz_dup_size n)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 cur) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 r) by (rewrite Hg1; reflexivity).
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
  assert (Hroom : room_slots b (fuzz_dup_size n))
    by (destruct ROOM as (R1 & R2 & R3); apply fuzz_dup_room; lia).
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
