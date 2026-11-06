(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the walk of rp_uci_int (src/repace_conf.c:35-68), the plain
   image's 0x13150, 85 instructions, every one stepped. It proves rp_uci_int_contract (rp_uci_int_c.v): the result is
   lib/Spec/UciModel.v's rp_uci_int_m of the n reply bytes. The one callee, memchr, is used through memchr_holds.
   - 0x13174-0x13184: memchr (reply, '\n', n) sets end; model_line ties memchr_res to first_line.
   - each loop is an induction over the bytes left, stated by the model applied to that suffix: lead_loop/lead_body
     (skip is_lead_blank, then sign_split), digit_loop (digits_rp), trail_loop (skip is_trail_blank).
   - fin and epilogue: the int test of finish, then the restore of ra/s0/s1/s2 and the release of the 32-byte frame.
   rp_uci_int calls no abort. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_uci_int_c memchr_c memchr.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes, reads, and the branch tactics (take: check_braid.v's idiom; take_by: the same with a given proof) ---- *)

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply rd1. exact H. Qed.

Lemma bytes_at_hd : forall m P b l, bytes_at rsegs m P (b :: l) -> mrd rsegs m (wa P) = Some b.
Proof. intros m P b l (_ & _ & H). specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. exact H. Qed.

Lemma bytes_at_tl : forall m P b l, bytes_at rsegs m P (b :: l) -> bytes_at rsegs m (P + 1) l.
Proof.
  intros m P b l H. apply (proj1 (bytes_at_app rsegs m P [b] l)) in H. destruct H as [_ H]. exact H.
Qed.

Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac shn := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; zb_fold_lits.
Ltac norm := wsub; do 3 (shn; usub).
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu, zxb; rewrite ?zb_signed; norm;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
Ltac take_by b tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.
Ltac fact := wsub; usub; first [ reflexivity | lia ].

(* ---- the model pieces, one byte at a time ---- *)

Lemma skip_stop : forall f c t, f c = false -> skip f (c :: t) = c :: t.
Proof. intros f c t H. cbn. rewrite H. reflexivity. Qed.
Lemma skip_go : forall f c t, f c = true -> skip f (c :: t) = skip f t.
Proof. intros f c t H. cbn. rewrite H. reflexivity. Qed.
Lemma zbytes_cons : forall b l, zbytes (b :: l) = bv_unsigned b :: zbytes l.
Proof. reflexivity. Qed.
Lemma trail_big : forall c, 32 < c -> is_trail_blank c = false.
Proof. intros c H. unfold is_trail_blank. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

(* `sext.w a0, a2; bne a0, a2` (0x1327c-0x13280): the value is an int exactly when its sign extension is itself *)
Lemma sext_cond : forall x, -2 ^ 31 <= x <= 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0))) (Z_to_bv 64 x) = (x <=? 2 ^ 31 - 1).
Proof.
  intros x Hx. destruct (Z.eq_dec x (2 ^ 31)) as [->|Hne]; [vm_compute; reflexivity|].
  assert (S : bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0) = x).
  { rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
    replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
    replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
    Z.div_mod_to_equations; lia. }
  rewrite S. unfold bv_eqb. rewrite Z.eqb_refl. symmetry. apply Z.leb_le. lia.
Qed.

(* the trailing-blank test of 0x13254-0x1325c: bit c of 0x100002200 is set exactly for c in {9, 13, 32} *)
Lemma mask_cond : forall (a6 : word) (b : byte), bv_unsigned a6 = 4294976000 -> bv_unsigned b <= 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a6) (bv_unsigned (zxb b) mod 64)))) 1))
    (Z_to_bv 64 0) = negb (is_trail_blank (bv_unsigned b)).
Proof.
  intros a6 b H6 Hb. rewrite H6. unfold zxb. pose proof (byte_range b) as Rb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia.
  revert Hb Rb. generalize (bv_unsigned b) as c. intros c Hb Rb.
  assert (Hall : forallb (fun c => Bool.eqb
    (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294976000 (c mod 64)))) 1)) (Z_to_bv 64 0))
    (negb (is_trail_blank c))) (zseq 33) = true) by (vm_compute; reflexivity).
  apply Bool.eqb_prop. exact (forallb_zseq 33 _ Hall c ltac:(lia)).
Qed.

(* `addi a7, a6, -0x30; bltu a3, a7` with a3 = 9 (0x1320c-0x13210): the byte is not a decimal digit *)
Lemma digit_cond : forall (a3 : word) (b : byte), bv_unsigned a3 = 9 ->
  bv_ltu a3 (Z_to_bv 64 (bv_unsigned (zxb b) + -48)) = negb (is_digit (bv_unsigned b)).
Proof.
  intros a3 b H3. unfold bv_ltu. rewrite H3. unfold zxb. pose proof (byte_range b) as Rb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia.
  revert Rb. generalize (bv_unsigned b) as c. intros c Rb.
  assert (Hall : forallb (fun c => Bool.eqb (9 <? bv_unsigned (Z_to_bv 64 (c + -48))) (negb (is_digit c)))
    (zseq 256) = true) by (vm_compute; reflexivity).
  apply Bool.eqb_prop. exact (forallb_zseq 256 _ Hall c ltac:(lia)).
Qed.

(* `andi a6, a6, 0xf` (0x13218): for a digit, c & 15 = c - '0' *)
Lemma land_digit : forall c, 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
  intros c Hc. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  Z.div_mod_to_equations; lia.
Qed.

Lemma digits_stop : forall v c t, is_digit c = false -> digits_rp v (c :: t) = Some (v, c :: t).
Proof. intros v c t H. cbn. rewrite H. reflexivity. Qed.
Lemma digits_go : forall v c t, is_digit c = true ->
  digits_rp v (c :: t) = if 2 ^ 31 <? v * 10 + (c - 48) then None else digits_rp (v * 10 + (c - 48)) t.
Proof. intros v c t H. cbn [digits_rp]. rewrite H. reflexivity. Qed.

(* rp_uci_int_m past its first_line: parse_m is repace_conf.c:43-67 run over the line [p, end) *)
Definition after_sign (neg : bool) (l : list Z) (cur : Z) : Z :=
  match l with
  | c :: _ =>
      if is_digit c then
        match digits_rp 0 l with
        | None => cur
        | Some (v, rest) => finish neg v rest cur
        end
      else cur
  | [] => cur
  end.

Definition parse_m (l : list Z) (cur : Z) : Z :=
  let '(neg, l2) := sign_split (skip is_lead_blank l) in after_sign neg l2 cur.

Lemma after_sign_digit : forall neg c t cur, is_digit c = true ->
  after_sign neg (c :: t) cur = match digits_rp 0 (c :: t) with None => cur | Some (v, rest) => finish neg v rest cur end.
Proof. intros neg c t cur H. unfold after_sign. rewrite H. reflexivity. Qed.
Lemma after_sign_nondigit : forall neg c t cur, is_digit c = false -> after_sign neg (c :: t) cur = cur.
Proof. intros neg c t cur H. unfold after_sign. rewrite H. reflexivity. Qed.

(* `addi a2, a2, -0x3a; bltu a2, a3` with a3 = -10 (0x131e4-0x131ec): the byte is not a decimal digit *)
Lemma digit_cond2 : forall b : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + -58)) (Z_to_bv 64 (-10)) = negb (is_digit (bv_unsigned b)).
Proof.
  intros b. unfold bv_ltu, zxb. pose proof (byte_range b) as Rb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia.
  revert Rb. generalize (bv_unsigned b) as c. intros c Rb.
  assert (Hall : forallb (fun c => Bool.eqb (bv_unsigned (Z_to_bv 64 (c + -58)) <? bv_unsigned (Z_to_bv 64 (-10)))
    (negb (is_digit c))) (zseq 256) = true) by (vm_compute; reflexivity).
  apply Bool.eqb_prop. exact (forallb_zseq 256 _ Hall c ltac:(lia)).
Qed.

Lemma parse_nosign : forall c t cur, is_lead_blank c = false -> c <> 43 -> c <> 45 ->
  parse_m (c :: t) cur = after_sign false (c :: t) cur.
Proof.
  intros c t cur H1 H2 H3. unfold parse_m. rewrite skip_stop by exact H1. unfold sign_split.
  rewrite (proj2 (Z.eqb_neq c 43)), (proj2 (Z.eqb_neq c 45)) by assumption. reflexivity.
Qed.
Lemma parse_blank : forall c t cur, is_lead_blank c = true -> parse_m (c :: t) cur = parse_m t cur.
Proof. intros c t cur H. unfold parse_m. rewrite skip_go by exact H. reflexivity. Qed.
Lemma parse_plus : forall t cur, parse_m (43 :: t) cur = after_sign false t cur.
Proof. reflexivity. Qed.
Lemma parse_minus : forall t cur, parse_m (45 :: t) cur = after_sign true t cur.
Proof. reflexivity. Qed.

Section Parse.
Variables (x1 x2 gp tp x5 x6 x7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur E : Z) (aE : word).
Hypothesis HEw : bv_unsigned aE = E.
Variable Q : machine_state -> Prop.

Local Abbreviation ST pc x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 :=
  (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma trail_loop : forall (x8 a1 a2 a4 a5 a6 : word),
  bv_unsigned a4 = 32 -> bv_unsigned a5 = E -> bv_unsigned a6 = 4294976000 ->
  forall k lb P (s1 a3 a7 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E ->
  bv_unsigned s1 = P -> bv_unsigned a3 = Z.of_nat (length lb) ->
  (forall lt P' (y9 y13 y17 : word), zbytes lt = skip is_trail_blank (zbytes lb) ->
     P' + Z.of_nat (length lt) = E -> bv_unsigned y9 = P' ->
     evt rsegs Q (ST 0x13270 x8 y9 aE a1 a2 y13 a4 a5 a6 y17)) ->
  evt rsegs Q (ST 0x1324c x8 s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros x8 a1 a2 a4 a5 a6 H4 H5 H6 k. induction k as [|k IH];
    intros [|b lb] P s1 a3 a7 HL HB HPE H1 H3 K; try discriminate.
  all: pose proof (byte_range b) as Rb.
  all: pose proof (rdw0 m s1 _ _ (bytes_at_hd m P b lb HB) H1) as R.
  all: step; clear R.
  all: step; destruct (Z.ltb_spec 32 (bv_unsigned b)) as [Hbig|Hsm].
  all: try (take true; apply (K (b :: lb) P s1); [rewrite zbytes_cons, skip_stop by (apply trail_big; lia); reflexivity | exact HPE | exact H1]).
  all: take false.
  all: step; step; step.
  all: destruct (is_trail_blank (bv_unsigned b)) eqn:TB.
  2,4: take_by true ltac:(rewrite (mask_cond a6 b H6 Hsm), TB; reflexivity);
       apply (K (b :: lb) P s1); [rewrite zbytes_cons, skip_stop by exact TB; reflexivity | exact HPE | exact H1].
  all: take_by false ltac:(rewrite (mask_cond a6 b H6 Hsm), TB; reflexivity).
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: cbn [length] in HL, HPE, H3, BB.
  all: step; step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    take false. step.
    apply (K [] E); [rewrite zbytes_cons, skip_go by exact TB; reflexivity | cbn; lia | exact H5].
  - take true.
    apply (IH lb (P + 1)); [lia | exact (bytes_at_tl m P b lb HB) | lia | fact | fact |].
    intros lt P' y9 y13 y17 Hz HP' H9. apply (K lt P'); [rewrite zbytes_cons, skip_go by exact TB; exact Hz | exact HP' | exact H9].
Qed.

Definition KR (R : Z) : Prop := forall y9 y10 y11 y12 y13 y14 y15 y16 y17 : word,
  evt rsegs Q (ST 0x13288 (Z_to_bv 64 R) y9 y10 y11 y12 y13 y14 y15 y16 y17).

Definition fin_val (neg : bool) (v cur : Z) : Z :=
  let v' := if neg then - v else v in if (v' <? INT_MIN) || (INT_MAX <? v') then cur else v'.

Lemma fin : forall (neg : bool) (v : Z) (lt : list byte) (P' : Z) (y9 a1 a2 a3 a4 a5 a6 a7 : word),
  P' + Z.of_nat (length lt) = E -> bv_unsigned y9 = P' ->
  bv_unsigned a1 = (if neg then 0 else 1) -> bv_unsigned a2 = v -> 0 <= v <= 2 ^ 31 -> INT_MIN <= cur <= INT_MAX ->
  KR (match zbytes lt with [] => fin_val neg v cur | _ :: _ => cur end) ->
  evt rsegs Q (ST 0x13270 (Z_to_bv 64 cur) y9 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros neg v lt P' y9 a1 a2 a3 a4 a5 a6 a7 HPE H9 H1 H2 Hv HC K. unfold KR in K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  assert (E2 : a2 = Z_to_bv 64 v) by (rewrite <- H2; symmetry; apply Z_to_bv_bv_unsigned). subst a2.
  step. destruct lt as [|b lt].
  2: { cbn [length] in HPE. take true. apply K. }
  cbn [length Z.of_nat] in HPE. take false. cbn [zbytes map] in K.
  unfold INT_MIN, INT_MAX in HC.
  step. destruct neg.
  - (* '-': v' = -v, always an int since v <= 2^31 *)
    take false. step. step. step.
    take_by false ltac:(rewrite sext_cond by (rewrite (unsigned_lit v) by lia; lia);
      rewrite (unsigned_lit v) by lia; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
    step. rewrite (unsigned_lit v) by lia.
    assert (FV : fin_val true v cur = 0 - v)
      by (unfold fin_val, INT_MIN, INT_MAX; rewrite !(proj2 (Z.ltb_ge _ _)) by lia; cbn; lia).
    rewrite FV in K. apply K.
  - take true. step. step.
    destruct (Z.leb_spec v (2 ^ 31 - 1)) as [Hin|Hout].
    + take_by false ltac:(rewrite sext_cond by lia; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
      step.
      assert (FV : fin_val false v cur = v)
        by (unfold fin_val, INT_MIN, INT_MAX; rewrite !(proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      rewrite FV in K. apply K.
    + take_by true ltac:(rewrite sext_cond by lia; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
      assert (FV : fin_val false v cur = cur)
        by (unfold fin_val, INT_MIN, INT_MAX; rewrite (proj2 (Z.ltb_lt (2 ^ 31 - 1) v)) by lia;
            rewrite orb_true_r; reflexivity).
      rewrite FV in K. apply K.
Qed.

(* 0x13230: after the digits; the trailing-blank loop, then fin *)
Lemma tail : forall (neg : bool) (v : Z) (lb : list byte) (P : Z) (s1 a1 a2 a3 a4 a5 a6 a7 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> bv_unsigned s1 = P ->
  bv_unsigned a1 = (if neg then 0 else 1) -> bv_unsigned a2 = v -> 0 <= v <= 2 ^ 31 -> INT_MIN <= cur <= INT_MAX ->
  KR (finish neg v (zbytes lb) cur) ->
  evt rsegs Q (ST 0x13230 (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros neg v lb P s1 a1 a2 a3 a4 a5 a6 a7 HB HPE H1 Ha1 Ha2 Hv HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE, BB. take true.
    exact (fin neg v [] P s1 a1 a2 a3 a4 a5 a6 a7 ltac:(cbn; lia) H1 Ha1 Ha2 Hv HC K).
  - cbn [length] in HPE, BB. take false.
    do 6 step.
    eapply (trail_loop (Z_to_bv 64 cur) a1 a2) with (k := length lb) (lb := b :: lb) (P := P).
    1-3: fact.
    1: reflexivity.
    1: exact HB.
    1: cbn [length]; lia.
    1: exact H1.
    1: cbn [length]; fact.
    intros lt P' y9 y13 y17 Hz HP' H9.
    eapply (fin neg v lt P' y9 a1 a2); [exact HP' | exact H9 | exact Ha1 | exact Ha2 | exact Hv | exact HC |].
    unfold finish in K. rewrite <- Hz in K. exact K.
Qed.

(* 0x13208: the digit loop, v = v * 10 + d, with the early `return cur` once v > 2^31 *)
Lemma digit_loop : forall (neg : bool) (a1 a3 a4 a5 : word),
  bv_unsigned a1 = (if neg then 0 else 1) -> bv_unsigned a3 = 9 -> bv_unsigned a4 = 10 -> bv_unsigned a5 = 2 ^ 31 ->
  INT_MIN <= cur <= INT_MAX ->
  forall k (lb : list byte) (P v : Z) (s1 a2 a6 a7 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> bv_unsigned s1 = P ->
  bv_unsigned a2 = v -> 0 <= v <= 2 ^ 31 ->
  KR (match digits_rp v (zbytes lb) with None => cur | Some (v', rest) => finish neg v' rest cur end) ->
  evt rsegs Q (ST 0x13208 (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros neg a1 a3 a4 a5 Ha1 Ha3 Ha4 Ha5 HC k. induction k as [|k IH];
    intros [|b lb] P v s1 a2 a6 a7 HL HB HPE H1 Ha2 Hv K; try discriminate.
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: cbn [length] in HL, HPE, BB.
  all: pose proof (byte_range b) as Rb.
  all: pose proof (rdw0 m s1 _ _ (bytes_at_hd m P b lb HB) H1) as R.
  all: step; clear R.
  all: step. all: step.
  all: destruct (is_digit (bv_unsigned b)) eqn:DG.
  2,4: take_by true ltac:(rewrite (digit_cond a3 b Ha3), DG; reflexivity);
       rewrite zbytes_cons, digits_stop in K by exact DG;
       exact (tail neg v (b :: lb) P s1 a1 a2 _ _ _ _ _ HB HPE H1 Ha1 Ha2 Hv HC K).
  all: take_by false ltac:(rewrite (digit_cond a3 b Ha3), DG; reflexivity).
  all: step; step; step; step.
  all: assert (DGb : 48 <= bv_unsigned b <= 57)
         by (unfold is_digit in DG; apply andb_true_iff in DG as [D1 D2]; apply Z.leb_le in D1, D2; lia).
  all: unfold zxb; rewrite (unsigned_lit (bv_unsigned b)) by lia; rewrite (land_digit (bv_unsigned b)) by lia.
  all: rewrite Ha2, Ha4.
  all: rewrite zbytes_cons, digits_go in K by exact DG.
  all: destruct (Z.ltb_spec (2 ^ 31) (v * 10 + (bv_unsigned b - 48))) as [Hov|Hok].
  (* v > INT_MAX + 1: the early `return cur` of 0x13220 *)
  1,3: take true; unfold KR in K; apply K.
  all: take false.
  all: step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    cbn [length Z.of_nat] in HPE.
    take false. step.
    eapply (tail neg (v * 10 + (bv_unsigned b - 48)) [] E aE a1);
      [exact (bytes_at_nil rsegs m E ltac:(lia)) | cbn; lia | exact HEw | exact Ha1 | fact | lia | exact HC | exact K].
  - take true.
    apply (IH lb (P + 1) (v * 10 + (bv_unsigned b - 48)));
      [lia | exact (bytes_at_tl m P b lb HB) | lia | fact | fact | lia | exact K].
Qed.

(* 0x131dc: past the optional sign; `p == end` or a non-digit returns cur, else the digit loop from v = 0 *)
Lemma post_sign : forall (neg : bool) (lb : list byte) (P : Z) (s1 a1 a2 a3 a4 a5 a6 a7 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> bv_unsigned s1 = P ->
  bv_unsigned a1 = (if neg then 0 else 1) -> INT_MIN <= cur <= INT_MAX ->
  KR (after_sign neg (zbytes lb) cur) ->
  evt rsegs Q (ST 0x131dc (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros neg lb P s1 a1 a2 a3 a4 a5 a6 a7 HB HPE H1 Ha1 HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE. take true. unfold KR in K. apply K.
  - cbn [length] in HPE, BB. take false.
    pose proof (byte_range b) as Rb.
    pose proof (rdw0 m s1 _ _ (bytes_at_hd m P b lb HB) H1) as R.
    step; clear R. step. step. step.
    destruct (is_digit (bv_unsigned b)) eqn:DG.
    + take_by false ltac:(rewrite digit_cond2, DG; reflexivity).
      step. step. take false.
      do 4 step.
      rewrite zbytes_cons, after_sign_digit in K by exact DG.
      eapply (digit_loop neg a1) with (k := length lb) (lb := b :: lb) (P := P) (v := 0).
      all: first [ exact Ha1 | exact HC | exact HB | exact HPE | exact H1 | exact K | reflexivity | fact
                 | (vm_compute; reflexivity) | lia ].
    + take_by true ltac:(rewrite digit_cond2, DG; reflexivity).
      rewrite zbytes_cons, after_sign_nondigit in K by exact DG. unfold KR in K. apply K.
Qed.

(* 0x1319c: one byte of the leading-blank loop, and the sign check it falls into (0x131c0-0x131d8) *)
Lemma lead_body : forall (a1 a2 a3 a4 : word),
  bv_unsigned a1 = 1 -> bv_unsigned a2 = 31 -> bv_unsigned a3 = 9 -> bv_unsigned a4 = 32 -> INT_MIN <= cur <= INT_MAX ->
  forall (b : byte) (lb : list byte) (P : Z) (s1 a5 a6 a7 : word),
  bytes_at rsegs m P (b :: lb) -> P + Z.of_nat (length (b :: lb)) = E -> bv_unsigned s1 = P ->
  KR (parse_m (zbytes (b :: lb)) cur) ->
  (is_lead_blank (bv_unsigned b) = true -> forall a5' : word,
     evt rsegs Q (ST 0x131b0 (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5' a6 a7)) ->
  evt rsegs Q (ST 0x1319c (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 HC b lb P s1 a5 a6 a7 HB HPE H1 K KA.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  cbn [length] in HPE, BB.
  pose proof (byte_range b) as Rb.
  pose proof (rdw0 m s1 _ _ (bytes_at_hd m P b lb HB) H1) as R.
  step; clear R. step.
  rewrite zbytes_cons in K.
  destruct (Z.leb_spec (bv_unsigned b) 31) as [Lo|Hi].
  - take true. step.
    destruct (Z.eq_dec (bv_unsigned b) 9) as [E9|N9].
    + take false. apply KA. unfold is_lead_blank. rewrite E9. reflexivity.
    + take true.
      rewrite parse_nosign in K by (first [unfold is_lead_blank; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity | lia]).
      exact (post_sign false (b :: lb) P s1 a1 _ _ _ _ _ _ HB HPE H1 Ha1 HC K).
  - take false. step.
    destruct (Z.eq_dec (bv_unsigned b) 32) as [E32|N32].
    + take false. step. apply KA. unfold is_lead_blank. rewrite E32. reflexivity.
    + take true. step. step.
      destruct (Z.eq_dec (bv_unsigned b) 43) as [E43|N43].
      * (* '+': a1 = (c - '-' != 0) = 1, p++ *)
        take true. step. step. step.
        eapply (post_sign false lb (P + 1));
          [ exact (bytes_at_tl m P b lb HB) | lia | fact | unfold zxb; rewrite E43; vm_compute; reflexivity
          | exact HC | rewrite E43, parse_plus in K; exact K ].
      * take false. step. step.
        destruct (Z.eq_dec (bv_unsigned b) 45) as [E45|N45].
        -- (* '-': a1 = 0, p++ *)
           take false. step. step. step.
           eapply (post_sign true lb (P + 1));
             [ exact (bytes_at_tl m P b lb HB) | lia | fact | unfold zxb; rewrite E45; vm_compute; reflexivity
             | exact HC | rewrite E45, parse_minus in K; exact K ].
        -- take true.
           rewrite parse_nosign in K by (first [unfold is_lead_blank; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity | lia]).
           exact (post_sign false (b :: lb) P s1 a1 _ _ _ _ _ _ HB HPE H1 Ha1 HC K).
Qed.

(* the leading-blank loop (0x1319c-0x131bc), by induction on the bytes left *)
Lemma lead_loop : forall (a1 a2 a3 a4 : word),
  bv_unsigned a1 = 1 -> bv_unsigned a2 = 31 -> bv_unsigned a3 = 9 -> bv_unsigned a4 = 32 -> INT_MIN <= cur <= INT_MAX ->
  forall k (lb : list byte) (P : Z) (s1 a5 a6 a7 : word),
  length lb = S k -> bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> bv_unsigned s1 = P ->
  KR (parse_m (zbytes lb) cur) ->
  evt rsegs Q (ST 0x1319c (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 HC k. induction k as [|k IH];
    intros [|b lb] P s1 a5 a6 a7 HL HB HPE H1 K; try discriminate.
  all: pose proof (u64_range aE) as RE; rewrite HEw in RE.
  all: pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  all: apply (lead_body a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 HC b lb P s1 a5 a6 a7 HB HPE H1 K).
  all: intros TB a5'.
  all: cbn [length] in HL, HPE, BB.
  all: rewrite zbytes_cons, parse_blank in K by exact TB.
  all: step; step.
  - assert (lb = []) by (destruct lb; [reflexivity | cbn in HL; lia]). subst lb.
    cbn [length Z.of_nat] in HPE.
    take false. step. step.
    eapply (post_sign false [] E aE a1);
      [ exact (bytes_at_nil rsegs m E ltac:(lia)) | cbn; lia | exact HEw | exact Ha1 | exact HC | exact K ].
  - take true.
    apply (IH lb (P + 1)); [lia | exact (bytes_at_tl m P b lb HB) | lia | fact | exact K].
Qed.

(* 0x13188: neg = 0; `p < end` enters the leading-blank loop, else straight to 0x131dc *)
Lemma entry : forall (lb : list byte) (P : Z) (s1 a1 a2 a3 a4 a5 a6 a7 : word),
  bytes_at rsegs m P lb -> P + Z.of_nat (length lb) = E -> bv_unsigned s1 = P -> INT_MIN <= cur <= INT_MAX ->
  KR (parse_m (zbytes lb) cur) ->
  evt rsegs Q (ST 0x13188 (Z_to_bv 64 cur) s1 aE a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros lb P s1 a1 a2 a3 a4 a5 a6 a7 HB HPE H1 HC K.
  pose proof (u64_range aE) as RE; rewrite HEw in RE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  step. step. destruct lb as [|b lb].
  - cbn [length Z.of_nat] in HPE. take true.
    eapply (post_sign false [] P s1); [exact HB | exact HPE | exact H1 | fact | exact HC | exact K].
  - cbn [length] in HPE, BB. take false. step. step. step.
    eapply (lead_loop _ _ _ _) with (k := length lb) (lb := b :: lb) (P := P).
    all: first [ exact HC | exact HB | exact HPE | exact H1 | exact K | reflexivity | fact ].
Qed.

End Parse.

(* ---- the model side: memchr's end pointer and first_line ---- *)

Lemma first_line_find : forall bs,
  first_line (zbytes bs) = zbytes (match find_byte 10 bs with Some i => firstn i bs | None => bs end).
Proof.
  induction bs as [|b t IH]; [reflexivity|].
  rewrite zbytes_cons. cbn [first_line find_byte].
  destruct (bv_unsigned b =? 10); [reflexivity|].
  rewrite IH. destruct (find_byte 10 t); reflexivity.
Qed.

Lemma model_line : forall bs cur, bs <> [] ->
  rp_uci_int_m (zbytes bs) cur = parse_m (zbytes (match find_byte 10 bs with Some i => firstn i bs | None => bs end)) cur.
Proof.
  intros bs cur H. rewrite <- first_line_find. destruct bs as [|b t]; [congruence|]. reflexivity.
Qed.

Lemma parse_m_lf : forall t cur, parse_m (10 :: t) cur = cur.
Proof. reflexivity. Qed.

Lemma swrap_int : forall r, INT_MIN <= r <= INT_MAX -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 r) + 0)) = Z_to_bv 64 r.
Proof.
  intros r Hr. unfold INT_MIN, INT_MAX in Hr. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  Z.div_mod_to_equations; lia.
Qed.

(* 0x13288-0x132a0: a0 = (int)s0, restore ra/s0/s1/s2 from the frame, sp += 32, ret *)
Lemma epilogue : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m1 : word -> option byte) (bs : list byte) (A lo r : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -32) -> lo + 32 <= bv_unsigned sp ->
  munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  bytes_at rsegs m1 A bs -> INT_MIN <= r <= INT_MAX ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
       mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ bytes_at rsegs m' A bs)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13288) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 bs A lo r
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 FR ST HLO MU WM MI HB Hr.
  pose proof (u64_range sp) as Rsp.
  step. rewrite (swrap_int r Hr).
  do 6 step.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact HB].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma bytes_at_firstn : forall m P bs k, bytes_at rsegs m P bs -> bytes_at rsegs m P (firstn k bs).
Proof.
  intros m P bs k H. rewrite <- (firstn_skipn k bs) in H.
  apply (proj1 (bytes_at_app rsegs m P _ _)) in H. destruct H as [H _]. exact H.
Qed.

Ltac kr_done ML :=
  unfold KR; intros ? ? ? ? ? ? ? ? ?; rewrite ML;
  eapply epilogue; first [ eassumption | apply rp_uci_int_range; assumption ].

Theorem rp_uci_int_holds : rp_uci_int_contract.
Proof.
  unfold rp_uci_int_contract, RP_UCI_INT, RP_UCI_INT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs cur lo HB HE HL Ha2 HC MI ST HLO HSP DR.
  subst a2.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* the prologue's four `sd` go to the carved frame; DR keeps the reply bytes (HB) across them *)
  do 7 step.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [Hn0|Hn0].
  { (* n == 0: return cur *)
    if_true.
    assert (bs = []) by (destruct bs; [reflexivity | cbn in HL; lia]). subst bs.
    change (rp_uci_int_m (zbytes []) cur) with cur.
    eapply epilogue; first [ eassumption | exact HC ]. }
  if_false.
  do 5 step.
  (* memchr (reply, '\n', n) at 0x1317c, against memchr_contract (memchr_holds). Its three premises hold here:
     - bytes_at rsegs m1 (bv_unsigned a0) bs: HB, the contract's n reply bytes (buf = bs), kept across the four
       frame stores by the disjointness premise DR;
     - memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) bs with a1 = 10 (10 mod 256 = 10) and
       a2 = s2 = n = length bs (HL): firstn n bs = bs, and both its cases (None, Some j) ask only n <= length bs;
     - mem_inv rsegs m1: MI, kept across the stores (each `sd` hits the writable frame). *)
  call memchr_holds.
  1: exact HB.
  1: { rewrite (unsigned_lit 10) by lia. change (10 mod 256) with 10. rewrite <- HL.
       unfold memchr_ok. rewrite Nat2Z.id, firstn_all. destruct (find_byte 10 bs); [left|]; lia. }
  1: exact MI.
  (* memchr_res = reply + (index of the first LF), or 0 when there is none *)
  assert (MR : memchr_res (bv_unsigned a0) (bv_unsigned (Z_to_bv 64 10) mod 256) (bv_unsigned a1) bs =
               match find_byte 10 bs with Some i => bv_unsigned a0 + Z.of_nat i | None => 0 end).
  { rewrite (unsigned_lit 10) by lia. unfold memchr_res. rewrite <- HL, Nat2Z.id, firstn_all. reflexivity. }
  rewrite MR. clear MR.
  assert (Hbs : bs <> []) by (intros ->; cbn in HL; lia).
  step.
  destruct (find_byte 10 bs) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hi & (b0 & Hb0 & Hb0v) & _).
    destruct (Z.eq_dec (bv_unsigned a0 + Z.of_nat i) 0) as [Z0|NZ].
    + (* the LF's address is 0, so memchr's result reads as NULL: then reply = 0 and the LF is byte 0. The binary
         parses up to reply + n; the LF it meets first is no blank, no sign and no digit, so it returns cur, which
         is also rp_uci_int_m's value (the first line is empty). *)
      assert (Ei : i = 0%nat) by lia. subst i.
      take false. step.
      assert (PL : parse_m (zbytes bs) cur = rp_uci_int_m (zbytes bs) cur).
      { rewrite (model_line bs cur Hbs), FB. destruct bs as [|b t]; [congruence|].
        cbn in Hb0. injection Hb0 as <-. rewrite zbytes_cons, Hb0v, parse_m_lf. reflexivity. }
      eapply entry with (E := bv_unsigned a0 + bv_unsigned a1) (lb := bs) (P := bv_unsigned a0);
        [ rewrite unsigned_lit by lia; reflexivity | exact HB | lia | reflexivity | exact HC | kr_done PL ].
    + (* the LF is at reply + i: the line is the first i bytes *)
      take true.
      assert (PL : parse_m (zbytes (firstn i bs)) cur = rp_uci_int_m (zbytes bs) cur)
        by (rewrite (model_line bs cur Hbs), FB; reflexivity).
      eapply entry with (E := bv_unsigned a0 + Z.of_nat i) (lb := firstn i bs) (P := bv_unsigned a0);
        [ rewrite unsigned_lit by lia; reflexivity | exact (bytes_at_firstn _ _ _ i HB)
        | rewrite length_firstn; lia | reflexivity | exact HC | kr_done PL ].
  - (* no LF: end = reply + n, the line is all n bytes *)
    take false. step.
    assert (PL : parse_m (zbytes bs) cur = rp_uci_int_m (zbytes bs) cur)
      by (rewrite (model_line bs cur Hbs), FB; reflexivity).
    eapply entry with (E := bv_unsigned a0 + bv_unsigned a1) (lb := bs) (P := bv_unsigned a0);
      [ rewrite unsigned_lit by lia; reflexivity | exact HB | lia | reflexivity | exact HC | kr_done PL ].
Qed.
