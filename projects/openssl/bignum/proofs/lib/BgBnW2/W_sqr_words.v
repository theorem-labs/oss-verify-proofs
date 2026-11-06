(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_words_entry := 0xf95fc%Z.

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
             F (ret_pc ra) fc None m' (seg_rom bgpsegs)
    /\ munch [(rp, rp + 16 * Z.of_nat (length a)); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono bgpsegs m m' /\ mem_inv bgpsegs m'
    /\ limbs_at bgpsegs m' rp (sqr_words a)
    /\ stk bgpsegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 16 * Z.of_nat (length a)); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgpsegs m ap a.
  Hypothesis WR : wr_at bgpsegs m rp (16 * n).
  Hypothesis DISJ : (ap + 8 * n <= rp \/ rp + 16 * n <= ap)%Z.
  Hypothesis STK : stk bgpsegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPR : (rp + 16 * n <= SP - 16 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.

  Notation POST := (sqw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a lo m).

  Definition SINV (m1 : word -> option byte) (k : nat) : Prop :=
    limbs_at bgpsegs m1 rp (firstn k (sqr_words a)) /\ limbs_at bgpsegs m1 ap a /\ wr_at bgpsegs m1 rp (16 * n) /\
    rw_cells bgpsegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgpsegs m1 lo (SP + -16) /\ mem_inv bgpsegs m1 /\
    munch W m m1 /\ wmono bgpsegs m m1.

  Lemma SINV_store : forall m1 k v ad,
    SINV m1 k -> (Z.of_nat k < 2 * n)%Z -> v = nth k (sqr_words a) 0%Z -> ad = (rp + 8 * Z.of_nat k)%Z ->
    store_ok bgpsegs m1 (Z_to_bv 64 ad) 8 = true /\
    SINV (write_to_mem m1 (Z_to_bv 64 ad) (le8 (Z_to_bv 64 v))) (k + 1)%nat.
  Proof.
    intros m1 k v ad (HW & HA & WT & FR & ST & MI & MU & WM) Hk -> ->. rewrite Nat.add_1_r.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    assert (T0 : (0 <= rp)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgpsegs m1 rp (16 * n) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    pose proof (sqr_words_length a) as LS.
    assert (L8 : length (le8 (Z_to_bv 64 (nth k (sqr_words a) 0%Z))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgpsegs m1 (Z_to_bv 64 (rp + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)). apply (wr_at_store_ok bgpsegs m1 rp (16 * n)); [exact WT | lia | lia]. }
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

  Notation ST pc mm x5 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 t1 t2 sp s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Ltac sq_load I k Rx :=
    let HA := fresh "HA" in let NI := fresh "NI" in let RD := fresh "RD" in
    pose proof (proj1 (proj2 I)) as HA;
    assert (NI : nth_error a k = Some (nth k a 0%Z)) by (apply nth_error_nth'; lia);
    assert (Rx : (0 <= nth k a 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA);
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgpsegs _ ap a k _ ad HA NI ltac:(unfold wa; f_equal; lia)) as RD);
    zstep; clear RD NI HA.

  Ltac sq_regs x Rx := rewrite (sqr64_lo_eqm x Rx), (sqr64_hi_eq x Rx).

  Ltac sq_store I j v Hv :=
    let ad := cur_mem_addr in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    destruct (SINV_store _ j v E I ltac:(lia) Hv ltac:(lia)) as [SOK I2];
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.

  Ltac sq_limb I i x Rx :=
    let Hl := fresh "Hl" in let Hh := fresh "Hh" in
    sq_regs x Rx;
    pose proof (eq_sym (sqr_words_nth_lo a i ltac:(lia))) as Hl;
    pose proof (eq_sym (sqr_words_nth_hi a i ltac:(lia))) as Hh;
    sq_store I (2 * i)%nat ((x * x) mod 18446744073709551616)%Z Hl;
    sq_store I (2 * i + 1)%nat ((x * x) / 18446744073709551616)%Z Hh;
    clear Hl Hh.

  Lemma sqw_epilogue : forall m1 x5 x10 x11 x12 x13 x14 x15 x16 x17,
    SINV m1 (2 * length a) ->
    evt bgpsegs POST (ST 0xf976c m1 x5 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x10 x11 x12 x13 x14 x15 x16 x17 (HW & HA & WT & FR & ST & MI & MU & WM).
    rewrite firstn_all2 in HW by (rewrite sqr_words_length; lia).
    zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    unfold sqw_post. finish.
  Qed.

  Lemma sqw_tail : forall K (i : nat) m1 x5 x14 x15 x16 x17,
    (length a - i = K)%nat -> (i < length a)%nat -> SINV m1 (2 * i) ->
    evt bgpsegs POST (ST 0xf9728 m1 x5 (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * n))
                         (Z_to_bv 64 4294967295) x14 x15 x16 x17).
  Proof.
    induction K as [|K IH]; intros i m1 x5 x14 x15 x16 x17 HK Hi I; [lia|].
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    sq_load I i Rx.
    zstep.
    do 11 zstep.
    sq_limb I i (nth i a 0%Z) Rx.
    zstep.
    replace (rp + 16 * Z.of_nat i + 16)%Z with (rp + 16 * Z.of_nat (S i))%Z by lia.
    replace (ap + 8 * Z.of_nat i + 8)%Z with (ap + 8 * Z.of_nat (S i))%Z by lia.
    replace (2 * i + 1 + 1)%nat with (2 * S i)%nat in I by lia.
    zstep. if_cases KB; zify_cond KB.
    - eapply IH; [lia | | exact I]. rewrite ?unsigned_lit in KB by lia. lia.
    - assert (Ei : S i = length a) by (rewrite ?unsigned_lit in KB by lia; lia).
      rewrite Ei in I. eapply sqw_epilogue. exact I.
  Qed.

  Lemma sqw_tail_setup : forall i m1 x5 x14 x15 x16 x17,
    (i < length a)%nat -> SINV m1 (2 * i) ->
    evt bgpsegs POST (ST 0xf9714 m1 x5 (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i))
                         (Z_to_bv 64 4294967295) x14 x15 x16 x17).
  Proof.
    intros i m1 x5 x14 x15 x16 x17 Hi I.
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    do 5 zstep.
    setreg 12%Z (Z_to_bv 64 (ap + 8 * n)) ltac:(f_equal; rewrite shl32_shr29 by lia; lia).
    eapply (sqw_tail (length a - i)); [reflexivity | exact Hi | exact I].
  Qed.

  Lemma sqw_loop4 : forall K (i : nat) m1 x5 x15 x16 x17,
    (length a - i = K)%nat -> (i + 4 <= length a)%nat -> SINV m1 (2 * i) ->
    evt bgpsegs POST (ST 0xf9620 m1 x5 (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i))
                         (Z_to_bv 64 4294967295) (Z_to_bv 64 4) x15 x16 x17).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i m1 x5 x15 x16 x17 HK Hi I.
    pose proof (limbs_at_bound _ _ _ _ (proj1 (proj2 I))) as BA.
    sq_load I i Rx0. do 11 zstep. sq_limb I i (nth i a 0%Z) Rx0.
    sq_load I (i + 1)%nat Rx1. do 11 zstep.
    replace (2 * i + 1 + 1)%nat with (2 * (i + 1))%nat in I by lia.
    sq_limb I (i + 1)%nat (nth (i + 1) a 0%Z) Rx1.
    sq_load I (i + 2)%nat Rx2. do 11 zstep.
    replace (2 * (i + 1) + 1 + 1)%nat with (2 * (i + 2))%nat in I by lia.
    sq_limb I (i + 2)%nat (nth (i + 2) a 0%Z) Rx2.
    sq_load I (i + 3)%nat Rx3.
    zstep. rewrite (bn_swrap32_small (n - Z.of_nat i + -4)) by lia.
    zstep.
    do 11 zstep.
    replace (2 * (i + 2) + 1 + 1)%nat with (2 * (i + 3))%nat in I by lia.
    sq_limb I (i + 3)%nat (nth (i + 3) a 0%Z) Rx3.
    zstep.
    replace (2 * (i + 3) + 1 + 1)%nat with (2 * (i + 4))%nat in I by lia.
    replace (rp + 16 * Z.of_nat i + 64)%Z with (rp + 16 * Z.of_nat (i + 4))%Z by lia.
    replace (ap + 8 * Z.of_nat i + 32)%Z with (ap + 8 * Z.of_nat (i + 4))%Z by lia.
    replace (n - Z.of_nat i + -4)%Z with (n - Z.of_nat (i + 4))%Z by lia.
    zstep. if_cases K1; zify_cond K1.
    - eapply (IH (length a - (i + 4))%nat); [lia | reflexivity | | exact I]. rewrite ?unsigned_lit in K1 by lia. lia.
    - zstep. if_cases K2; zify_cond K2.
      + assert (Ei : (i + 4)%nat = length a) by (rewrite ?unsigned_lit in K2 by lia; lia).
        rewrite Ei in I. eapply sqw_epilogue. exact I.
      + eapply sqw_tail_setup; [| exact I]. rewrite ?unsigned_lit in K1, K2 by lia. lia.
  Qed.

  Lemma bn_sqr_words_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf95fc) fc None m (seg_rom bgpsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, RSP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA.
    zstep. if_cases K; zify_cond K.
    -
      assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]). subst a.
      zstep.
      unfold sqw_post. finish. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z) by lia.
      carve_frame 16%nat STK.
      do 7 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (I : SINV m1 (2 * 0)).
      { unfold SINV. cbn [Nat.mul firstn]. split; [apply limbs_at_nil; lia|].
        split; [eapply limbs_at_transport; [exact RA | exact MU |]; cbn [disjoint_from]; lia|]. split; [exact WR|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
      clear FR STK.
      zstep. if_cases K4; zify_cond K4.
      + eapply evt_eq; [ | eapply (sqw_tail_setup 0%nat m1); [ lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, !Z.add_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      + eapply evt_eq; [ | eapply (sqw_loop4 (length a - 0)%nat 0%nat m1); [ reflexivity | lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, !Z.add_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.
