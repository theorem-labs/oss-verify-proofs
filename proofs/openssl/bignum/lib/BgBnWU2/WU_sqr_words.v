(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_words_entry := 0x103044%Z.

Lemma sqr64_decomp : forall x, (0 <= x < 18446744073709551616)%Z ->
  let xl := (x mod 4294967296)%Z in let xh := (x / 4294967296)%Z in
  (x * x = xh * xh * 18446744073709551616 + (xl * xh) * 8589934592 + xl * xl)%Z.
Proof.
  intros x Hx xl xh. assert (E : x = (xh * 4294967296 + xl)%Z) by (subst xl xh; Z.div_mod_to_equations; lia).
  rewrite E at 1. rewrite E at 1. subst xl xh. nia.
Qed.

Lemma sqr64_lohi : forall x, (0 <= x < 18446744073709551616)%Z ->
  let xl := (x mod 4294967296)%Z in let xh := (x / 4294967296)%Z in let mid := (xl * xh)%Z in
  let t := ((mid * 8589934592) mod 18446744073709551616)%Z in
  let lo := ((t + xl * xl) mod 18446744073709551616)%Z in
  lo = ((x * x) mod 18446744073709551616)%Z /\
  (xh * xh + mid / 2147483648 + (if lo <? t then 1 else 0) = (x * x) / 18446744073709551616)%Z.
Proof.
  intros x Hx xl xh mid t lo.
  pose proof (sqr64_decomp x Hx) as D. cbv zeta in D. fold xl xh in D. fold mid in D.
  assert (Bl : (0 <= xl < 4294967296)%Z) by (subst xl; Z.div_mod_to_equations; lia).
  assert (Bh : (0 <= xh < 4294967296)%Z) by (subst xh; Z.div_mod_to_equations; lia).
  assert (Bm : (0 <= mid <= 4294967295 * 4294967295)%Z) by (subst mid; nia).
  set (ll := (xl * xl)%Z) in *. set (hh := (xh * xh)%Z) in *.
  assert (Bll : (0 <= ll <= 4294967295 * 4294967295)%Z) by (subst ll; nia).
  assert (Bhh : (0 <= hh <= 4294967295 * 4294967295)%Z) by (subst hh; nia).
  set (xx := (x * x)%Z) in *.
  clearbody ll hh mid xx. clear Bl Bh.
  assert (Em : (mid * 8589934592 = (mid / 2147483648) * 18446744073709551616 + (mid mod 2147483648) * 8589934592)%Z).
  { Z.div_mod_to_equations. lia. }
  assert (Et : (t = (mid mod 2147483648) * 8589934592)%Z).
  { subst t. rewrite Em. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. Z.div_mod_to_equations. lia. }
  assert (X2 : (xx = (hh + mid / 2147483648) * 18446744073709551616 + (t + ll))%Z).
  { rewrite D. rewrite Et. clear - Em. lia. }
  assert (Elo : lo = ((t + ll) mod 18446744073709551616)%Z) by reflexivity.
  clearbody t lo. clear Em D. rewrite X2. clear X2.
  destruct (Z.ltb_spec lo t) as [C|C]; Z.div_mod_to_equations; lia.
Qed.

Lemma land32_mod : forall x, Z.land x 4294967295 = (x mod 4294967296)%Z.
Proof. intros x. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shr32_div : forall x, Z.shiftr x 32 = (x / 4294967296)%Z.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shr31_div : forall x, Z.shiftr x 31 = (x / 2147483648)%Z.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shl33_mul : forall x, Z.shiftl x 33 = (x * 8589934592)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma sqr64_hi_eq : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (Z.shiftr ((Z.land x 4294967295 * Z.shiftr x 32) mod 18446744073709551616) 31 + Z.shiftr x 32 * Z.shiftr x 32 +
              Z.b2z ((Z.shiftl ((Z.land x 4294967295 * Z.shiftr x 32) mod 18446744073709551616) 33 + Z.land x 4294967295 * Z.land x 4294967295) mod 18446744073709551616 <?
                     (Z.shiftl ((Z.land x 4294967295 * Z.shiftr x 32) mod 18446744073709551616) 33) mod 18446744073709551616))
  = Z_to_bv 64 ((x * x) / 18446744073709551616).
Proof.
  intros x Hx. pose proof (sqr64_lohi x Hx) as [_ H].
  rewrite !land32_mod, !shr32_div, shr31_div, !shl33_mul in *.
  assert (Bl : 0 <= x mod 4294967296 < 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Bh : 0 <= x / 4294967296 < 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Bm : 0 <= x mod 4294967296 * (x / 4294967296) < 18446744073709551616) by nia.
  rewrite (Z.mod_small (x mod 4294967296 * (x / 4294967296))) by exact Bm.
  f_equal. rewrite Zplus_mod_idemp_l in H. rewrite <- H.
  match goal with |- context [Z.b2z (?a <? ?b)] => destruct (a <? b) end; cbn [Z.b2z]; lia.
Qed.

Lemma sqr64_lo_eqm : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (Z.shiftl ((Z.land x 4294967295 * Z.shiftr x 32) mod 18446744073709551616) 33 + Z.land x 4294967295 * Z.land x 4294967295)
  = Z_to_bv 64 ((x * x) mod 18446744073709551616).
Proof.
  intros x Hx. pose proof (sqr64_lohi x Hx) as [L _].
  rewrite !land32_mod, !shr32_div, shl33_mul in *.
  assert (Bl : 0 <= x mod 4294967296 < 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Bh : 0 <= x / 4294967296 < 4294967296) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (x mod 4294967296 * (x / 4294967296))) by nia.
  apply Z_to_bv_eqm. change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite <- L. rewrite <- Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma sqr_words_length : forall a, length (sqr_words a) = (2 * length a)%nat.
Proof. induction a as [|x a IH]; [reflexivity|]. cbn [sqr_words length]. rewrite IH. lia. Qed.

Lemma sqr_words_limbs : forall a, limbs a -> limbs (sqr_words a).
Proof.
  induction a as [|x a IH]; intros H; [apply limbs_nil|]. apply limbs_cons_lit in H. destruct H as [Hx Ha].
  cbn [sqr_words]. apply limbs_cons; [| apply limbs_cons; [| apply IH; exact Ha]].
  - unfold limb. rewrite BW_lit. Z.div_mod_to_equations. lia.
  - unfold limb. rewrite BW_lit in *. Z.div_mod_to_equations. nia.
Qed.

Lemma sqr_words_nth_lo : forall a i, (i < length a)%nat ->
  nth (2 * i) (sqr_words a) 0%Z = ((nth i a 0 * nth i a 0) mod 18446744073709551616)%Z.
Proof.
  induction a as [|x a IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [cbn; rewrite BW_lit; reflexivity|].
  replace (2 * S i)%nat with (S (S (2 * i))) by lia. cbn [sqr_words nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma sqr_words_nth_hi : forall a i, (i < length a)%nat ->
  nth (2 * i + 1) (sqr_words a) 0%Z = ((nth i a 0 * nth i a 0) / 18446744073709551616)%Z.
Proof.
  induction a as [|x a IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [cbn; rewrite BW_lit; reflexivity|].
  replace (2 * S i + 1)%nat with (S (S (2 * i + 1))) by lia. cbn [sqr_words nth]. apply IH. cbn in Hi. lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0%Z].
Proof.
  induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Definition sqw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch [(rp, rp + 16 * Z.of_nat (length a)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m m'
    /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ limbs_at bgusegs m' rp (sqr_words a)
    /\ stk bgusegs m' lo (bv_unsigned sp).

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1060980 => 1
  | 1060984 => 1
  | 1060988 => 1
  | 1060996 => 1
  | 1061000 => 1
  | 1061008 => 1
  | 1061012 => 1
  | 1061016 => 1
  | 1061020 => 1
  | 1061024 => 1
  | 1061028 => 1
  | 1061032 => 1
  | 1061036 => 1
  | 1061040 => 1
  | 1061044 => 1
  | 1061048 => 1
  | 1061052 => 1
  | 1061056 => 1
  | 1061060 => 2
  | 1061064 => 2
  | 1061068 => 1
  | 1061072 => 2
  | 1061076 => 2
  | 1061080 => 1
  | 1061088 => 1
  | 1061092 => 1
  | 1061096 => 1
  | 1061100 => 1
  | 1061104 => 1
  | 1061108 => 1
  | 1061116 => 2
  | 1061120 => 1
  | 1061124 => 1
  | 1061128 => 1
  | 1061132 => 1
  | 1061136 => 1
  | 1061144 => 2
  | 1061148 => 2
  | 1061156 => 1
  | 1061160 => 1
  | 1061164 => 1
  | 1061168 => 1
  | 1061172 => 1
  | 1061176 => 1
  | 1061184 => 2
  | 1061188 => 1
  | 1061192 => 1
  | 1061196 => 1
  | 1061200 => 1
  | 1061204 => 1
  | 1061212 => 2
  | 1061216 => 2
  | 1061224 => 1
  | 1061228 => 1
  | 1061232 => 1
  | 1061236 => 1
  | 1061240 => 1
  | 1061244 => 1
  | 1061252 => 2
  | 1061256 => 1
  | 1061260 => 1
  | 1061264 => 1
  | 1061268 => 1
  | 1061272 => 1
  | 1061280 => 2
  | 1061284 => 2
  | 1061292 => 1
  | 1061296 => 1
  | 1061300 => 1
  | 1061304 => 1
  | 1061308 => 1
  | 1061312 => 1
  | 1061320 => 2
  | 1061324 => 1
  | 1061328 => 1
  | 1061332 => 1
  | 1061336 => 1
  | 1061340 => 1
  | 1061348 => 2
  | 1061352 => 2
  | 1061356 => 1
  | 1061360 => 2
  | 1061364 => 1
  | 1061368 => 1
  | 1061372 => 1
  | 1061376 => 1
  | 1061380 => 1
  | 1061392 => 1
  | 1061396 => 1
  | 1061400 => 1
  | 1061404 => 1
  | 1061408 => 1
  | 1061412 => 1
  | 1061416 => 1
  | 1061420 => 2
  | 1061424 => 2
  | 1061428 => 2
  | 1061432 => 2
  | 1061440 => 1
  | 1061444 => 1
  | 1061448 => 1
  | 1061452 => 1
  | 1061456 => 1
  | 1061460 => 1
  | 1061468 => 2
  | 1061472 => 1
  | 1061476 => 1
  | 1061480 => 1
  | 1061484 => 1
  | 1061488 => 1
  | 1061496 => 2
  | 1061500 => 2
  | 1061504 => 1
  | 1061508 => 2
  | 1061512 => 1
  | 1061516 => 1
  | 1061520 => 1
  | 1061564 => 1
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Ltac cur_store_val :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Store _ _ ?rs2 _, _) =>
        let rz := eval vm_compute in (bv_unsigned rs2) in
        reg_val rz
    end end end.


Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 16 * Z.of_nat (length a)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis WR : wr_at bgusegs m rp (16 * n).
  Hypothesis DISJ : (ap + 8 * n <= rp \/ rp + 16 * n <= ap)%Z.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 80)%Z.
  Hypothesis SEPR : (rp + 16 * n <= SP - 80 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 80 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.

  Notation POST := (sqw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a lo m).

  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation FCELLS jb := [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (jb : list byte) (m1 : word -> option byte) (k : nat) : Prop :=
    limbs_at bgusegs m1 rp (firstn k (sqr_words a)) /\ limbs_at bgusegs m1 ap a /\ wr_at bgusegs m1 rp (16 * n) /\
    rw_cells bgusegs m1 (SP + -80) (FCELLS jb) /\ stk bgusegs m1 lo (SP + -80) /\ mem_inv bgusegs m1 /\
    munch W m m1 /\ wmono bgusegs m m1.

  Lemma SINV_store : forall jb m1 k wv ad,
    SINV jb m1 k -> (Z.of_nat k < 2 * n)%Z -> wv = Z_to_bv 64 (nth k (sqr_words a) 0%Z) -> ad = (rp + 8 * Z.of_nat k)%Z ->
    store_ok bgusegs m1 (Z_to_bv 64 ad) 8 = true /\
    SINV jb (write_to_mem m1 (Z_to_bv 64 ad) (le8 wv)) (k + 1)%nat.
  Proof.
    intros jb m1 k wv ad (HW & HA & WT & FR & ST & MI & MU & WM) Hk -> ->. rewrite Nat.add_1_r.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    assert (T0 : (0 <= rp)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgusegs m1 rp (16 * n) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    pose proof (sqr_words_length a) as LS.
    assert (L8 : length (le8 (Z_to_bv 64 (nth k (sqr_words a) 0%Z))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgusegs m1 (Z_to_bv 64 (rp + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)). apply (wr_at_store_ok bgusegs m1 rp (16 * n)); [exact WT | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)).
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP.
    unfold SINV.
    split. { rewrite firstn_S_snoc by (rewrite LS; lia).
             replace (rp + 8 * Z.of_nat k)%Z with (rp + 8 * Z.of_nat (length (firstn k (sqr_words a))))%Z by (rewrite length_firstn, LS; f_equal; lia).
             apply limbs_at_snoc_write; [exact HW | rewrite length_firstn, LS; lia]. }
    split. { apply limbs_at_write_other; [exact HA | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { apply wr_at_write. exact WT. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Ltac sq_load I k Rx :=
    let HA := fresh "HA" in let NI := fresh "NI" in let RD := fresh "RD" in
    pose proof (proj1 (proj2 I)) as HA;
    assert (NI : nth_error a k = Some (nth k a 0%Z)) by (apply nth_error_nth'; lia);
    assert (Rx : (0 <= nth k a 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA);
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgusegs _ ap a k _ ad HA NI ltac:(unfold wa; f_equal; lia)) as RD);
    zstep; clear RD NI HA.
  Ltac sq_store I j tac :=
    let ad := cur_mem_addr in
    let wv := cur_store_val in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    destruct (SINV_store _ _ j wv E I ltac:(lia) ltac:(tac) ltac:(lia)) as [SOK I2];
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.
  Ltac sq_lo i Rx := rewrite (sqr_words_nth_lo a i) by lia; apply (sqr64_lo_eqm _ Rx).
  Ltac sq_hi i Rx := rewrite (sqr_words_nth_hi a i) by lia; apply (sqr64_hi_eq _ Rx).

  Lemma NZ2 : (0 < n)%Z -> (0 < rp /\ 0 < ap /\ rp mod 8 = 0 /\ ap mod 8 = 0)%Z.
  Proof. intros Hn. destruct (UBR Hn) as (H1 & H3). destruct (UBA Hn) as (H2 & H4). auto. Qed.

  Lemma SINV_top : forall jb m1 k, SINV jb m1 k -> (0 < n)%Z ->
    (rp + 16 * n <= UTOP /\ ap + 8 * n <= UTOP)%Z.
  Proof.
    intros jb m1 k (HW & HA & WT & FR & ST & MI & MU & WM) Hn.
    pose proof (wr_at_below bgusegs m1 rp _ MI WT ltac:(lia)) as TR.
    assert (NA : lbytes a <> []).
    { intros E. pose proof (lbytes_lengthZ a) as L. rewrite E in L. cbn [length] in L. lia. }
    pose proof (bytes_at_below bgusegs m1 ap _ MI HA NA) as TA. rewrite lbytes_lengthZ in TA.
    split; assumption.
  Qed.

  Lemma sqw_epi : forall jb m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    limbs_at bgusegs m1 rp (sqr_words a) ->
    rw_cells bgusegs m1 (SP + -80)%Z (FCELLS jb) -> stk bgusegs m1 lo (SP + -80)%Z ->
    mem_inv bgusegs m1 -> munch W m m1 -> wmono bgusegs m m1 ->
    evt bgusegs POST (ST 0x103298 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HP FR ST MI MU WM.
    do 10 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    unfold sqw_post. finish.
  Qed.

  Lemma sqw_done : forall jb m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    SINV jb m1 (2 * length a) ->
    evt bgusegs POST (ST 0x103298 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (HW & HA & WT & FR & ST & MI & MU & WM).
    rewrite firstn_all2 in HW by (rewrite sqr_words_length; lia).
    eapply sqw_epi; eassumption.
  Qed.

  Lemma sqw_tail : forall K (i : nat) jb m1 x1 x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    (length a - i = K)%nat -> (i < length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgusegs POST (ST 0x10322c m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i))
                         (Z_to_bv 64 (n - Z.of_nat i)) (Z_to_bv 64 4294967295) (Z_to_bv 64 0) (Z_to_bv 64 0)
                         (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    induction K as [|K IH]; intros i jb m1 x1 x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 HK Hi I; [lia|].
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    destruct (NZ2 ltac:(lia)) as (NZR & NZA & AR8 & AA8).
    destruct (SINV_top _ _ _ I ltac:(lia)) as (TR & TA). unfold UTOP in TR, TA.
    ub. sq_load I i Rx. ub. sq_store I (2 * i)%nat ltac:(sq_lo i Rx). ub. sq_store I (2 * i + 1)%nat ltac:(sq_hi i Rx).
    ub.
    rewrite (bn_swrap32_small (n - Z.of_nat i + -1)) by lia.
    replace (rp + 16 * Z.of_nat i + 16)%Z with (rp + 16 * Z.of_nat (S i))%Z by lia.
    replace (ap + 8 * Z.of_nat i + 8)%Z with (ap + 8 * Z.of_nat (S i))%Z by lia.
    replace (n - Z.of_nat i + -1)%Z with (n - Z.of_nat (S i))%Z by lia.
    replace (2 * i + 1 + 1)%nat with (2 * S i)%nat in I by lia.
    zstep. if_cases KB; zify_cond KB.
    - eapply IH; [lia | | exact I]. rewrite ?unsigned_lit in KB by lia. lia.
    - assert (Ei : S i = length a) by (rewrite ?unsigned_lit in KB by lia; lia).
      rewrite Ei in I. eapply sqw_done. exact I.
  Qed.

  Lemma sqw_tail_setup : forall (i : nat) jb m1 x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    (i < length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgusegs POST (ST 0x10321c m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i))
                         (Z_to_bv 64 (n - Z.of_nat i)) (Z_to_bv 64 4294967295) (Z_to_bv 64 (ap + 8 * Z.of_nat i))
                         (Z_to_bv 64 (rp + 16 * Z.of_nat i)) x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hi I.
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    destruct (NZ2 ltac:(lia)) as (NZR & NZA & AR8 & AA8).
    destruct (SINV_top _ _ _ I ltac:(lia)) as (TR & TA). unfold UTOP in TR, TA.
    do 4 zstep.
    setreg 14%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - AA8; Z.div_mod_to_equations; lia).
    setreg 15%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - AR8; Z.div_mod_to_equations; lia).
    eapply (sqw_tail (length a - i)); [reflexivity | exact Hi | exact I].
  Qed.

  Lemma sqw_loop4 : forall K (i : nat) jb m1 x20 x21 x22 x23,
    (length a - i = K)%nat -> (i + 4 <= length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgusegs POST (ST 0x1030c4 m1 ra (Z_to_bv 64 0) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-9)) sp (Z_to_bv 64 (-49))
                         (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i))
                         (Z_to_bv 64 (n - Z.of_nat i)) (Z_to_bv 64 4294967295) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (rp + 16 * Z.of_nat i))
                         (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 (-57)) (Z_to_bv 64 (-65)) x20 x21 x22 x23
                         (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) (Z_to_bv 64 (-41))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i jb m1 x20 x21 x22 x23 HK Hi I.
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    destruct (NZ2 ltac:(lia)) as (NZR & NZA & AR8 & AA8).
    destruct (SINV_top _ _ _ I ltac:(lia)) as (TR & TA). unfold UTOP in TR, TA.
    ub. sq_load I i Rx0. ub. sq_store I (2 * i)%nat ltac:(sq_lo i Rx0). ub. sq_store I (2 * i + 1)%nat ltac:(sq_hi i Rx0).
    ub.
    replace (2 * i + 1 + 1)%nat with (2 * (i + 1))%nat in I by lia.
    sq_load I (i + 1)%nat Rx1. ub. sq_store I (2 * (i + 1))%nat ltac:(sq_lo (i + 1)%nat Rx1). ub. sq_store I (2 * (i + 1) + 1)%nat ltac:(sq_hi (i + 1)%nat Rx1).
    ub.
    replace (2 * (i + 1) + 1 + 1)%nat with (2 * (i + 2))%nat in I by lia.
    sq_load I (i + 2)%nat Rx2. ub. sq_store I (2 * (i + 2))%nat ltac:(sq_lo (i + 2)%nat Rx2). ub. sq_store I (2 * (i + 2) + 1)%nat ltac:(sq_hi (i + 2)%nat Rx2).
    ub.
    replace (2 * (i + 2) + 1 + 1)%nat with (2 * (i + 3))%nat in I by lia.
    sq_load I (i + 3)%nat Rx3. ub. sq_store I (2 * (i + 3))%nat ltac:(sq_lo (i + 3)%nat Rx3). ub. sq_store I (2 * (i + 3) + 1)%nat ltac:(sq_hi (i + 3)%nat Rx3).
    ub.
    replace (2 * (i + 3) + 1 + 1)%nat with (2 * (i + 4))%nat in I by lia.
    replace (rp + 16 * Z.of_nat i + 64)%Z with (rp + 16 * Z.of_nat (i + 4))%Z by lia.
    replace (ap + 8 * Z.of_nat i + 32)%Z with (ap + 8 * Z.of_nat (i + 4))%Z by lia.
    replace (n - Z.of_nat i + -4)%Z with (n - Z.of_nat (i + 4))%Z by lia.
    zstep. if_cases K1; zify_cond K1.
    - eapply (IH (length a - (i + 4))%nat); [lia | reflexivity | | exact I]. rewrite ?unsigned_lit in K1 by lia. lia.
    - zstep. if_cases K2; zify_cond K2.
      + assert (Ei : (i + 4)%nat = length a) by (rewrite ?unsigned_lit in K2 by lia; lia).
        rewrite Ei in I. eapply sqw_done. exact I.
      + do 3 zstep.
        replace (rp + 16 * Z.of_nat i + 64)%Z with (rp + 16 * Z.of_nat (i + 4))%Z by lia.
        replace (ap + 8 * Z.of_nat i + 32)%Z with (ap + 8 * Z.of_nat (i + 4))%Z by lia.
        eapply (sqw_tail_setup (i + 4)%nat); [| exact I]. rewrite ?unsigned_lit in K1, K2 by lia. lia.
  Qed.

  Lemma bn_sqr_words_spec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x103044) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, RSP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA.
    carve_frame 80%nat STK.
    apply (rw_cells_split_CB bgusegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 11 zstep.
    zstep. if_cases K; zify_cond K.
    - assert (Ea : a = []).
      { destruct a as [|x a']; [reflexivity|]. exfalso. rewrite A2 in K. cbn [length] in *.
        apply andb_false_iff in K. destruct K as [K|K]; apply Z.ltb_ge in K; lia. }
      eapply sqw_epi; try eassumption.
      rewrite Ea. cbn. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z).
      { rewrite <- A2. lia. }
      destruct (NZ2 Hn) as (NZR & NZA & AR8 & AA8).
      do 3 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : SINV jb mm (2 * 0));
        [ unfold SINV; cbn [Nat.mul firstn]; split; [apply limbs_at_nil; lia|];
          split; [eapply limbs_at_transport; [exact RA | exact MU |]; cbn [disjoint_from]; lia|]; split; [exact WR|];
          split; [exact FR|]; split; [exact STK|]; split; [exact MI0|]; split; [exact MU | exact WM] | ]
      end end.
      clear RA WR FR STK MI0 MU WM.
      zstep. if_cases K4; zify_cond K4.
      + do 13 zstep.
        setreg 5%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; exact AR8).
        setreg 17%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; exact AA8).
        eapply evt_eq; [ | eapply (sqw_loop4 (length a - 0)%nat 0%nat); [ reflexivity | lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, !Z.add_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      + do 3 zstep.
        eapply evt_eq; [ | eapply (sqw_tail_setup 0%nat); [ lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, !Z.add_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.
