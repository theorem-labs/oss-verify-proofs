(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition same5 (r r' : iregs) : Prop :=
  ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r.

Lemma same5_refl : forall r, same5 r r.
Proof. intros r. repeat split; reflexivity. Qed.
Lemma same5_trans : forall r1 r2 r3, same5 r1 r2 -> same5 r2 r3 -> same5 r1 r3.
Proof. intros r1 r2 r3 (A1&A2&A3&A4&A5) (B1&B2&B3&B4&B5). unfold same5. rewrite B1, B2, B3, B4, B5. auto. Qed.

Definition tcons (r r' : iregs) : Prop := ir_bits r' + 8 * ir_have r' = ir_bits r + 8 * ir_have r.
Lemma tcons_refl : forall r, tcons r r.
Proof. intros r. unfold tcons. reflexivity. Qed.
Lemma tcons_trans : forall r1 r2 r3, tcons r1 r2 -> tcons r2 r3 -> tcons r1 r3.
Proof. intros r1 r2 r3 A B. unfold tcons in *. lia. Qed.

Lemma pow2_le_mono : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. apply Z.pow_le_mono_r; lia. Qed.

Lemma pull_acc : forall hold bits b, 0 <= bits -> bits + 8 <= 64 -> 0 <= hold < 2 ^ bits -> 0 <= b < 256 ->
  wrap64 (hold + shl64 b bits) = hold + b * 2 ^ bits /\ 0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8).
Proof.
  intros hold bits b Hb Hb8 Hh Hbb.
  assert (P : 0 < 2 ^ bits) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ (bits + 8) = 2 ^ bits * 256) by (rewrite Z.pow_add_r by lia; reflexivity).
  assert (R : 0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8)) by (rewrite E; nia).
  split; [| exact R].
  unfold shl64. rewrite Z.shiftl_mul_pow2 by lia.
  assert (B64 : 2 ^ (bits + 8) <= 2 ^ 64) by (apply pow2_le_mono; lia).
  rewrite (wrap64_id (b * 2 ^ bits)) by nia. apply wrap64_id. lia.
Qed.

Lemma drop_acc : forall hold bits n, 0 <= n <= bits -> bits < 64 -> 0 <= hold < 2 ^ bits ->
  wrap32 (bits - n) = bits - n /\ 0 <= Z.shiftr hold n < 2 ^ (bits - n).
Proof.
  intros hold bits n Hn Hb Hh. split; [apply wrap32_id; lia|].
  rewrite Z.shiftr_div_pow2 by lia.
  assert (P : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (bits - n)) with bits by lia. lia.
Qed.

Lemma land7_le : forall b, 0 <= b -> 0 <= Z.land b 7 <= b /\ Z.land b 7 < 8.
Proof.
  intros b Hb. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound b 8 ltac:(lia)). pose proof (Z.mod_le b 8 ltac:(lia) ltac:(lia)). cbn. lia.
Qed.

Lemma BITSv_le : forall hold n, 0 <= n -> BITSv hold n <= Z.shiftl 1 n - 1.
Proof. intros hold n Hn. rewrite Z.shiftl_1_l. pose proof (BITSv_bound hold n Hn). lia. Qed.

Lemma mod_pow2_le : forall a b B, 0 <= b <= B -> (a mod 2 ^ B) mod 2 ^ b = a mod 2 ^ b.
Proof.
  intros a b B H.
  assert (P : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (PB : 0 < 2 ^ B) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ B = 2 ^ (B - b) * 2 ^ b) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_eq a (2 ^ B)) by lia. rewrite E at 1.
  replace (a - 2 ^ (B - b) * 2 ^ b * (a / 2 ^ B)) with (a + (- (2 ^ (B - b) * (a / 2 ^ B))) * 2 ^ b) by lia.
  apply Z.mod_add. lia.
Qed.
Lemma pull_prefix : forall hold bits b, 0 <= bits -> 0 <= hold < 2 ^ bits -> (hold + b * 2 ^ bits) mod 2 ^ bits = hold.
Proof.
  intros hold bits b Hb Hh. rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 bits); lia). apply Z.mod_small. exact Hh.
Qed.
Definition htrunc (h b : Z) : Z := h mod 2 ^ b.
Definition hpre (h' b h : Z) : Prop := htrunc h' b = h.
Lemma hpre_same : forall h b, 0 <= h < 2 ^ b -> hpre h b h.
Proof. intros h b H. unfold hpre, htrunc. apply Z.mod_small. exact H. Qed.
Lemma hpre_down : forall h2 h1 h b b1, 0 <= b <= b1 -> hpre h2 b1 h1 -> hpre h1 b h -> hpre h2 b h.
Proof. intros h2 h1 h b b1 Hb A B. unfold hpre, htrunc in *. rewrite <- (mod_pow2_le h2 b b1) by lia. rewrite A. exact B. Qed.

Section R.
  Variables (NI NO : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation RINV := (RINV NI NO).

  Lemma PULLBYTE_run : forall s c r, RINV r -> ir_bits r + 8 < 64 ->
    arr_len (ic_input c) = NI -> (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256) ->
    match PULLBYTE (mkW s c r) with
    | ARun _ w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r'
                   /\ ir_bits r' = ir_bits r + 8 /\ ir_have r' = ir_have r - 1 /\ ir_next r' = ir_next r + 1 /\ 0 < ir_have r
                   /\ ir_hold r' = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r
    | ALeave w' => w' = mkW s c r /\ ir_have r = 0
    | ARet _ _ => False
    end.
  Proof.
    intros s c r HR Hb8 HNI Hinp. unfold PULLBYTE. cbn [w_r w_c].
    destruct (Z.eqb_spec (ir_have r) 0) as [E|NE]; [split; [reflexivity | exact E]|].
    destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
    pose proof (Hinp (ir_next r) ltac:(lia)) as Hb.
    destruct (pull_acc (ir_hold r) (ir_bits r) (arr_get (ic_input c) (ir_next r)) ltac:(lia) ltac:(lia) R11 Hb) as [EW RG].
    eexists. split; [reflexivity|]. cbn.
    rewrite EW. rewrite (wrap32_id (ir_have r - 1)) by lia. rewrite (wrap32_id (ir_bits r + 8)) by lia.
    split.
    { unfold InflateInv.RINV. cbn. repeat split; try lia. }
    split; [repeat split; reflexivity|]. split; [unfold tcons; cbn; lia|]. repeat split; try reflexivity. lia.
  Qed.

  Lemma NEEDBITS_k_run : forall k n s c r, RINV r -> 0 <= n <= 56 -> n <= ir_bits r + 8 * Z.of_nat k ->
    arr_len (ic_input c) = NI -> (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256) ->
    match NEEDBITS_k k n (mkW s c r) with
    | ARun _ w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r' /\ n <= ir_bits r'
                   /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8) /\ ir_have r' <= ir_have r
                   /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
    | ALeave w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r' /\ ir_have r' = 0
                   /\ ir_bits r' < n /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros n s c r HR Hn Hk HNI Hinp.
    - pose proof HR as HR'. destruct HR' as (_&_&_&_&_&_&_&_&_&R10&R11).
      cbn. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl|]. split; [apply tcons_refl|]. cbn in Hk. split; [lia|]. split; [left; reflexivity |].
      split; [lia|]. split; [apply hpre_same; exact R11 | lia].
    - pose proof HR as HR'. destruct HR' as (_&_&_&_&_&_&_&_&_&R10&R11).
      cbn [NEEDBITS_k abind gr w_r]. destruct (Z.ltb_spec (ir_bits r) n) as [LT|GE].
      + pose proof (PULLBYTE_run s c r HR ltac:(lia) HNI Hinp) as P. unfold abind.
        destruct (PULLBYTE (mkW s c r)) as [u w1|w1|rc w1]; [| | destruct P].
        * destruct P as (r1 & -> & HR1 & S1 & T1 & B1 & H1 & N1 & Hpos & Hh1).
          pose proof (IH n s c r1 HR1 Hn ltac:(rewrite B1; lia) HNI Hinp) as Q.
          destruct (NEEDBITS_k k n (mkW s c r1)) as [u2 w2|w2|rc2 w2]; [| | destruct Q].
          -- destruct Q as (r2 & -> & HR2 & S2 & T2 & B2 & C2 & Hh2 & M2 & L2). exists r2. split; [reflexivity|]. split; [exact HR2|].
             split; [exact (same5_trans _ _ _ S1 S2)|]. split; [exact (tcons_trans _ _ _ T1 T2)|]. split; [exact B2|]. split; [right; destruct C2 as [C2 | C2]; lia|].
             split; [lia|]. split; [| lia].
             apply (hpre_down (ir_hold r2) (ir_hold r1) (ir_hold r) (ir_bits r) (ir_bits r1) ltac:(lia) M2). unfold hpre, htrunc. rewrite Hh1. apply pull_prefix; [lia | exact R11].
          -- destruct Q as (r2 & -> & HR2 & S2 & T2 & Hz & LT2 & M2 & L2). exists r2. split; [reflexivity|]. split; [exact HR2|].
             split; [exact (same5_trans _ _ _ S1 S2) |]. split; [exact (tcons_trans _ _ _ T1 T2)|]. split; [exact Hz|]. split; [exact LT2|]. split; [| lia].
             apply (hpre_down (ir_hold r2) (ir_hold r1) (ir_hold r) (ir_bits r) (ir_bits r1) ltac:(lia) M2). unfold hpre, htrunc. rewrite Hh1. apply pull_prefix; [lia | exact R11].
        * destruct P as [-> Hz]. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl |]. split; [apply tcons_refl|]. split; [exact Hz|].
          split; [exact LT|]. split; [apply hpre_same; exact R11 | lia].
      + cbn. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl|]. split; [apply tcons_refl|]. split; [lia|]. split; [left; reflexivity |].
        split; [lia|]. split; [apply hpre_same; exact R11 | lia].
  Qed.

  Lemma NEEDBITS_run : forall n s c r, RINV r -> 0 <= n <= 56 ->
    arr_len (ic_input c) = NI -> (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256) ->
    match NEEDBITS n (mkW s c r) with
    | ARun _ w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r' /\ n <= ir_bits r'
                   /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8) /\ ir_have r' <= ir_have r
                   /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
    | ALeave w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r' /\ ir_have r' = 0
                   /\ ir_bits r' < n /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
    | ARet _ _ => False
    end.
  Proof.
    intros n s c r HR Hn HNI Hinp. unfold NEEDBITS. apply NEEDBITS_k_run; try assumption.
    destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & _). cbn. lia.
  Qed.

  Lemma DECODE_k_run : forall k p index need NB s c r, RINV r -> 0 <= NB <= 56 -> NB <= ir_bits r + 8 * Z.of_nat k ->
    (forall h, 0 <= h -> need (code_at s p (index h)) <= NB) ->
    arr_len (ic_input c) = NI -> (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256) ->
    match DECODE_k k p index need (mkW s c r) with
    | ARun here w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r'
                      /\ here = code_at s p (index (ir_hold r')) /\ need here <= ir_bits r' /\ ir_have r' <= ir_have r
                      /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
                      /\ (ir_bits r' = ir_bits r
                          \/ (ir_bits r + 8 <= ir_bits r' /\ ir_bits r' - 8 < need (code_at s p (index (htrunc (ir_hold r') (ir_bits r' - 8))))))
    | ALeave w' => exists r', w' = mkW s c r' /\ RINV r' /\ same5 r r' /\ tcons r r' /\ ir_have r' = 0
                   /\ ir_bits r' < need (code_at s p (index (ir_hold r'))) /\ hpre (ir_hold r') (ir_bits r) (ir_hold r) /\ ir_bits r <= ir_bits r'
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros p index need NB s c r HR HNB Hk Hneed HNI Hinp.
    - pose proof HR as HR'. destruct HR' as (_&_&_&_&_&_&_&_&_&R10&R11).
      cbn. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl|]. split; [apply tcons_refl|]. split; [reflexivity|].
      cbn in Hk. pose proof (Hneed (ir_hold r) ltac:(lia)). split; [lia|]. split; [lia|]. split; [apply hpre_same; exact R11|]. split; [lia|]. left; reflexivity.
    - pose proof HR as HR'. destruct HR' as (_&_&_&_&_&_&_&_&_&R10&R11).
      cbn [DECODE_k abind HOLD gr gs w_r w_s].
      destruct (Z.leb_spec (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [LE|GT].
      + cbn. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl|]. split; [apply tcons_refl|]. split; [reflexivity|]. split; [exact LE |].
        split; [lia|]. split; [apply hpre_same; exact R11|]. split; [lia|]. left; reflexivity.
      + pose proof (Hneed (ir_hold r) ltac:(lia)) as NH.
        pose proof (PULLBYTE_run s c r HR ltac:(lia) HNI Hinp) as P. unfold abind.
        destruct (PULLBYTE (mkW s c r)) as [u w1|w1|rc w1]; [| | destruct P].
        * destruct P as (r1 & -> & HR1 & S1 & T1 & B1 & H1 & N1 & Hpos & Hh1).
          assert (PF : forall h2, hpre h2 (ir_bits r1) (ir_hold r1) -> hpre h2 (ir_bits r) (ir_hold r)).
          { intros h2 M2. apply (hpre_down h2 (ir_hold r1) (ir_hold r) (ir_bits r) (ir_bits r1) ltac:(lia) M2). unfold hpre, htrunc. rewrite Hh1. apply pull_prefix; [lia | exact R11]. }
          pose proof (IH p index need NB s c r1 HR1 HNB ltac:(rewrite B1; lia) Hneed HNI Hinp) as Q.
          destruct (DECODE_k k p index need (mkW s c r1)) as [h2 w2|w2|rc2 w2]; [| | destruct Q].
          -- destruct Q as (r2 & -> & HR2 & S2 & T2 & E2 & B2 & Hh2 & M2 & L2 & D2). exists r2. split; [reflexivity|]. split; [exact HR2|].
             split; [exact (same5_trans _ _ _ S1 S2)|]. split; [exact (tcons_trans _ _ _ T1 T2)|]. split; [exact E2|]. split; [exact B2 |]. split; [lia|].
             split; [exact (PF _ M2)|]. split; [lia|].
             right. destruct D2 as [D2 | [D2a D2b]].
             ++ assert (EB : ir_bits r2 - 8 = ir_bits r) by lia. split; [lia|]. rewrite EB. pose proof (PF _ M2) as PM. unfold hpre in PM. rewrite PM. exact GT.
             ++ split; [lia | exact D2b].
          -- destruct Q as (r2 & -> & HR2 & S2 & T2 & Hz & LT2 & M2 & L2). exists r2. split; [reflexivity|]. split; [exact HR2|].
             split; [exact (same5_trans _ _ _ S1 S2) |]. split; [exact (tcons_trans _ _ _ T1 T2)|]. split; [exact Hz|]. split; [exact LT2|]. split; [exact (PF _ M2) | lia].
        * destruct P as [-> Hz]. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply same5_refl |]. split; [apply tcons_refl|]. split; [exact Hz|].
          split; [lia|]. split; [apply hpre_same; exact R11 | lia].
  Qed.

  Lemma RINV_drop : forall r n, RINV r -> 0 <= n <= ir_bits r ->
    wrap32 (ir_bits r - n) = ir_bits r - n
    /\ RINV (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (ir_bits r - n)).
  Proof.
    intros r n HR Hn. destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
    destruct (drop_acc (ir_hold r) (ir_bits r) n Hn ltac:(lia) R11) as [EW RG].
    destruct r; cbn in *. split; [exact EW|]. unfold InflateInv.RINV; cbn; repeat split; lia.
  Qed.

  Lemma RINV_init : forall r, RINV r -> RINV (irset_bits (irset_hold r 0) 0) /\ same5 r (irset_bits (irset_hold r 0) 0).
  Proof.
    intros r HR. destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
    destruct r; cbn in *. split; [unfold InflateInv.RINV; cbn; repeat split; lia | repeat split; reflexivity].
  Qed.

End R.


Lemma lxor_mask32_range : forall a, 0 <= a < 4294967296 -> 0 <= Z.lxor a MASK32 < 4294967296.
Proof. intros a Ha. unfold MASK32. apply lxor_bound32; lia. Qed.

Lemma icrc32_upd_range : forall c bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= icrc32_upd c bs < 2 ^ 64.
Proof.
  intros c bs Hbs. unfold icrc32_upd, crc32_model.
  assert (H : 0 <= Z.lxor (crc_fold (Z.lxor (wrap32 c) MASK32) bs) MASK32 < 4294967296).
  { apply lxor_mask32_range. apply crc_fold_range.
    - apply lxor_mask32_range. pose proof (wrap32_range c). lia.
    - intros b Hb. rewrite Forall_forall in Hbs. apply Hbs. exact Hb. }
  lia.
Qed.

Lemma iadler32_upd_range : forall a bs, 0 <= iadler32_upd a bs < 2 ^ 64.
Proof.
  intros a bs. unfold iadler32_upd, adler32_model.
  destruct (adl bs _ _) as [x y] eqn:E.
  pose proof (adl_canon bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)
                ltac:(apply Z.mod_pos_bound; unfold ABASE; lia) ltac:(apply Z.mod_pos_bound; unfold ABASE; lia)) as [Hx Hy].
  rewrite E in Hx, Hy. cbn [fst snd] in Hx, Hy. unfold ABASE in *.
  assert (Hs : 0 <= Z.shiftl y 16 < 2 ^ 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (lxor_bound32 (Z.shiftl y 16) x ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma UPDATE_CHECK_range : forall s ck bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= UPDATE_CHECK_bytes s ck bs < 2 ^ 64.
Proof.
  intros s ck bs H. unfold UPDATE_CHECK_bytes. destruct (negb _); [apply icrc32_upd_range; exact H | apply iadler32_upd_range].
Qed.

Lemma wrap8_byte : forall z, 0 <= wrap8 z < 256.
Proof. intros z. pose proof (wrap8_range z). lia. Qed.

Lemma CRC2_range : forall c w, 0 <= icrc32_upd c [wrap8 w; wrap8 (Z.shiftr w 8)] < 2 ^ 64.
Proof. intros c w. apply icrc32_upd_range. repeat constructor; pose proof (wrap8_byte w); pose proof (wrap8_byte (Z.shiftr w 8)); lia. Qed.
Lemma CRC4_range : forall c w,
  0 <= icrc32_upd c [wrap8 w; wrap8 (Z.shiftr w 8); wrap8 (Z.shiftr w 16); wrap8 (Z.shiftr w 24)] < 2 ^ 64.
Proof.
  intros c w. apply icrc32_upd_range.
  pose proof (wrap8_byte w); pose proof (wrap8_byte (Z.shiftr w 8)); pose proof (wrap8_byte (Z.shiftr w 16)); pose proof (wrap8_byte (Z.shiftr w 24)).
  repeat constructor; lia.
Qed.

Lemma ZSWAP32_range : forall q, 0 <= ZSWAP32 q < 2 ^ 64.
Proof. intros q. unfold ZSWAP32. apply wrap64_range. Qed.

Lemma slice_bytes : forall (a : arr) N ofs n, (forall i, 0 <= i < N -> 0 <= arr_get a i < 256) ->
  0 <= ofs -> 0 <= n -> ofs + n <= N -> Forall (fun b => 0 <= b < 256) (arr_slice a ofs n).
Proof.
  intros a N ofs n Ha Ho Hn Hle. apply bytes_ok_slice_at; [exact Ho|]. intros i Hi. apply Ha. lia.
Qed.


Lemma scan_zero_loop : forall k inp next have cl,
  0 <= fst cl < have -> have < 2 ^ 32 ->
  0 <= fst (loopZ (Z.of_nat k) (fun cl : Z * Z => let '(copy, _) := cl in
         let len := arr_get inp (next + copy) in
         let copy := wrap32 (copy + 1) in
         (negb (len =? 0) && (copy <? have), (copy, len))) cl) <= have.
Proof.
  induction k as [|k IH]; intros inp next have [copy len] Hc Hh; cbn [fst] in Hc.
  - rewrite loopZ_le0 by lia. cbn. lia.
  - rewrite (loopZ_step (Z.of_nat (S k))) by lia. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    cbv beta iota zeta. rewrite (wrap32_id (copy + 1)) by lia.
    destruct (negb (arr_get inp (next + copy) =? 0) && (copy + 1 <? have)) eqn:E.
    + apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. apply IH; cbn; lia.
    + cbn [fst]. lia.
Qed.

Lemma scan_zero_bound : forall inp next have, 0 < have < 2 ^ 32 ->
  0 <= fst (scan_zero inp next have) <= have.
Proof.
  intros inp next have Hh.
  pose proof (scan_zero_loop (Z.to_nat have) inp next have (0, 0) ltac:(cbn; lia) ltac:(lia)) as H.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma blit_bytes : forall (dst src : arr) N NI dofs sofs n,
  (forall i, 0 <= i < N -> 0 <= arr_get dst i < 256) -> (forall i, 0 <= i < NI -> 0 <= arr_get src i < 256) ->
  0 <= sofs -> 0 <= n -> sofs + n <= NI ->
  forall i, 0 <= i < N -> 0 <= arr_get (arr_blit dst dofs src sofs n) i < 256.
Proof.
  intros dst src N NI dofs sofs n Hd Hs Ho Hn Hle i Hi. rewrite arr_get_blit.
  destruct ((dofs <=? i) && (i <? dofs + Z.max 0 n) && arr_inb dst i) eqn:E; [| apply Hd; exact Hi].
  apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  apply Hs. lia.
Qed.

Lemma land_mask_range : forall x n, 0 <= n -> 0 <= Z.land x (Z.ones n) <= Z.ones n.
Proof.
  intros x n Hn. rewrite Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
  pose proof (Z.mod_pos_bound x (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.
Lemma land_65535_range : forall x, 0 <= Z.land x 65535 <= 65535.
Proof. intros x. change 65535 with (Z.ones 16). apply land_mask_range. lia. Qed.


Definition obytes (N : Z) (ob : arr) : Prop := forall i, 0 <= i < N -> 0 <= arr_get ob i < 256.

Lemma obytes_set : forall N ob i v, obytes N ob -> 0 <= v < 256 -> obytes N (arr_set ob i v).
Proof.
  intros N ob i v H Hv j Hj. rewrite arr_get_set. destruct (_ && _); [exact Hv | apply H; exact Hj].
Qed.

Definition mc_step (win : arr) (st : arr * Z * fromptr * Z) : bool * (arr * Z * fromptr * Z) :=
  let '(ob, put, from, copy) := st in
  let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
  let ob := arr_set ob put v in
  let copy := wrap32 (copy - 1) in
  (negb (copy =? 0), (ob, put + 1, from_succ from, copy)).

Lemma match_copy_mc : forall win st, match_copy win st = loopZ (snd st) (mc_step win) st.
Proof. intros win st. reflexivity. Qed.

Definition from_fits (from : fromptr) (c put W : Z) : Prop :=
  match from with FWin i => 0 <= i /\ i + c <= W | FOut i => 0 <= i <= put end.

Lemma mc_loop_spec : forall n win ob put from c N W ob' put' fr' c',
  Z.of_nat n = c -> 1 <= c < 2 ^ 32 -> 0 <= put -> put + c <= N -> obytes N ob ->
  (forall i, 0 <= i < W -> 0 <= arr_get win i < 256) -> from_fits from c put W ->
  loopZ c (mc_step win) (ob, put, from, c) = (ob', put', fr', c') ->
  put' = put + c /\ arr_len ob' = arr_len ob /\ obytes N ob'.
Proof.
  induction n as [|n IH]; intros win ob put from c N W ob' put' fr' c' Hn Hc Hp HN HB HW HF E; [lia|].
  rewrite loopZ_step in E by lia. unfold mc_step at 1 in E.
  set (v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end) in E.
  assert (Hv : 0 <= v < 256).
  { subst v. destruct from as [i|i]; cbn in HF; [apply HW; lia | apply HB; lia]. }
  rewrite (wrap32_id (c - 1)) in E by lia.
  destruct (Z.eqb_spec (c - 1) 0) as [E0|NE]; cbn [negb] in E.
  - injection E; intros _ _ <- <-. split; [lia|]. split; [apply arr_len_set | apply obytes_set; assumption].
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in Hn by lia.
    assert (HF' : from_fits (from_succ from) (c - 1) (put + 1) W) by (destruct from as [i|i]; cbn in HF |- *; lia).
    pose proof (IH win (arr_set ob put v) (put + 1) (from_succ from) (c - 1) N W ob' put' fr' c'
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (obytes_set _ _ _ _ HB Hv) HW HF' E) as (A & B & C).
    split; [lia|]. split; [rewrite B; apply arr_len_set | exact C].
Qed.

Lemma match_copy_spec : forall win ob put from c N W ob' put' fr' c',
  1 <= c < 2 ^ 32 -> 0 <= put -> put + c <= N -> obytes N ob ->
  (forall i, 0 <= i < W -> 0 <= arr_get win i < 256) -> from_fits from c put W ->
  match_copy win (ob, put, from, c) = (ob', put', fr', c') ->
  put' = put + c /\ arr_len ob' = arr_len ob /\ obytes N ob'.
Proof.
  intros win ob put from c N W ob' put' fr' c' Hc Hp HN HB HW HF E. rewrite match_copy_mc in E. cbn [snd] in E.
  eapply (mc_loop_spec (Z.to_nat c)); try eassumption. lia.
Qed.



Definition bkv (iv : ivariant) (n bk : Z) : Z := if iv_aux iv then swrap32 (bk + n) else bk.
Definition sbv (iv : ivariant) (v bk : Z) : Z := if iv_aux iv then v else bk.

Lemma add_back_eq : forall iv n s c r,
  add_back iv n (mkW s c r) = ARun tt (mkW (iset_back s (bkv iv n (is_back s))) c r).
Proof. intros iv n s c r. unfold add_back, aux, bkv. destruct (iv_aux iv); [reflexivity | destruct s; reflexivity]. Qed.
Lemma set_back_eq : forall iv v s c r,
  set_back iv v (mkW s c r) = ARun tt (mkW (iset_back s (sbv iv v (is_back s))) c r).
Proof. intros iv v s c r. unfold set_back, aux, sbv. destruct (iv_aux iv); [reflexivity | destruct s; reflexivity]. Qed.
Lemma bkv_range : forall iv n bk, - 2 ^ 31 <= bk < 2 ^ 31 -> - 2 ^ 31 <= bkv iv n bk < 2 ^ 31.
Proof. intros iv n bk H. unfold bkv. destruct (iv_aux iv); [apply swrap32_range | exact H]. Qed.
Lemma sbv_range : forall iv v bk, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= bk < 2 ^ 31 -> - 2 ^ 31 <= sbv iv v bk < 2 ^ 31.
Proof. intros iv v bk Hv H. unfold sbv. destruct (iv_aux iv); [exact Hv | exact H]. Qed.
