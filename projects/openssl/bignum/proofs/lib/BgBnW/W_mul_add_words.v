(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_add_words_entry := 0xf9174%Z.

Definition maw_fl (w x y c : Z) : Z := (x * w + y + c) mod BW.
Definition maw_fc (w x y c : Z) : Z := (x * w + y + c) / BW.

Lemma mul_add_words_gen : forall w r la c, mul_add_words_c r la w c = gen_words_c (maw_fl w) (maw_fc w) la r c.
Proof.
  intros w. induction r as [|y r IH]; intros [|x la] c; try reflexivity.
  cbn [mul_add_words_c gen_words_c]. rewrite IH. reflexivity.
Qed.

Lemma maw_fc_range : forall w, (0 <= w < 18446744073709551616)%Z ->
  forall x y c, (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> (0 <= c <= 18446744073709551615)%Z ->
  (0 <= maw_fc w x y c <= 18446744073709551615)%Z.
Proof.
  intros w Hw x y c Hx Hy Hc. unfold maw_fc. rewrite BW_lit.
  assert (0 <= x * w <= 18446744073709551615 * 18446744073709551615)%Z by nia.
  Z.div_mod_to_equations; lia.
Qed.

Definition maw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (r a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 32%Z
          (fst (mul_add_words r a w)) (snd (mul_add_words r a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a r : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 32, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LR : limbs r.
  Hypothesis LEN : length r = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgpsegs m ap a.
  Hypothesis RR : limbs_at bgpsegs m rp r.
  Hypothesis WR : wr_at bgpsegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bgpsegs m lo SP.
  Hypothesis LO : (lo <= SP - 32)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 32 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 32 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.

  Notation POST := (maw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) r a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.
  Lemma ALR : alias_ok rp rp n. Proof. left. reflexivity. Qed.
  Lemma FBE : (bv_unsigned sp + -32 = bv_unsigned sp - 32)%Z. Proof. lia. Qed.

  Notation ST pc mm x2 x5 x6 x7 x8 x9 x10 x11 x12 x14 x18 x28 x29 x30 x31 :=
    (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 a3 x14 (Z_to_bv 64 4294967295) (Z_to_bv 64 (bv_unsigned a3 mod 4294967296))
             (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32)) x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).

  Notation FCR := (maw_fc_range (bv_unsigned a3) RW).
  Notation KINV := (INV bgpsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        32%Z (bv_unsigned sp + -32)%Z [C8 s2; C8 s1; C8 s0; C8 ra]
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation KIT L := (L bgpsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a r
                        32%Z (bv_unsigned sp + -32)%Z [C8 s2; C8 s1; C8 s0; C8 ra] eq_refl FBE
                        LEN ALA ALR SEPR SEPA SEPR (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation K_rdA := (KIT INV_rdA).   Notation K_rdB := (KIT INV_rdB).   Notation K_rdBk := (KIT INV_rdB_k).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_rangeB := (KIT INV_rangeB).   Notation K_ptrs := (KIT INV_ptrs).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac ldB I := let L := constr:(K_rdB) in ldB_with L I.
  Ltac ldBk I k := let L := constr:(K_rdBk) in ldB_k_with L I k.
  Ltac w64eq := unfold maw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  Ltac carry r x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 cn)
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx Ry RWv Hc Ecn; subst cn; unfold maw_fc; rewrite BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply FCR; assumption);
    clear Ecn.

  Lemma maw_epilogue : forall m1 pre c pa pb pr x5 x6 x7 x8 x9 x10 x11 x12 x18 x28 x29 x30 x31,
    KINV m1 pre [] [] c pa pb pr ->
    evt bgpsegs POST (ST 0xf93c4 m1 SPF x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x18 x28 x29 x30 x31).
  Proof.
    intros m1 pre c pa pb pr x5 x6 x7 x8 x9 x10 x11 x12 x18 x28 x29 x30 x31 I.
    pose proof (K_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
    do 8 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    unfold maw_post. finish.
  Qed.

  Lemma maw_tail : forall la m1 pre lb c pa pr x5 x6 x7 x8 x9 x18 x28 x29 x30 x31,
    la <> [] -> KINV m1 pre la lb c pa pr pr ->
    evt bgpsegs POST (ST 0xf9358 m1 SPF x5 x6 x7 x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 (ap + 8 * n)) (Z_to_bv 64 c) x18 x28 x29 x30 x31).
  Proof.
    induction la as [|x la IH]; intros m1 pre lb c pa pr x5 x6 x7 x8 x9 x18 x28 x29 x30 x31 NE I; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & A1). pose proof (zr_word a1) as A0. unfold inr64 in A0.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    ldA I. ldB I.
    do 16 zstep.
    st_limb I l c' Ec'.
    do 6 zstep.
    carry 14%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep. zstep.
    if_cases K; zify_cond K.
    - eapply IH; [ | exact I ]. destruct la; [ exfalso; cbn [length] in *; lia | discriminate ].
    - destruct la as [|x' la']. 2:{ exfalso. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. cbn [length] in *. lia. }
      eapply maw_epilogue. exact I.
  Qed.

  Lemma maw_tail_setup : forall la m1 pre lb c pa pr q x5 x6 x7 x8 x9 x18 x28 x29 x30 x31,
    la <> [] -> KINV m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bgpsegs POST (ST 0xf9344 m1 SPF x5 x6 x7 x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q) (Z_to_bv 64 c) x18 x28 x29 x30 x31).
  Proof.
    intros la m1 pre lb c pa pr q x5 x6 x7 x8 x9 x18 x28 x29 x30 x31 NE I Hq.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & A1).
    assert (R1 : (1 <= q < 2^31)%Z) by (destruct la; [congruence | cbn [length] in *; lia]).
    zstep. zstep. zstep. zstep. zstep.
    setreg 12%Z (Z_to_bv 64 (ap + 8 * n)) ltac:(f_equal; rewrite shl32_shr29 by lia; lia).
    eapply maw_tail; [exact NE | exact I].
  Qed.

  Lemma maw_loop4 : forall (K : nat) la m1 pre lb c pa pr q x6 x7 x8 x9 x18 x28 x29 x30 x31,
    length la = K -> KINV m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) -> (4 <= q)%Z ->
    evt bgpsegs POST (ST 0xf91b0 m1 SPF (Z_to_bv 64 4) x6 x7 x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q) (Z_to_bv 64 c) x18 x28 x29 x30 x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la m1 pre lb c pa pr q x6 x7 x8 x9 x18 x28 x29 x30 x31 HK I Hq R4.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    destruct la as [|x0 [|x1 [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (q < 2^31)%Z) by (clear - Hq En N31; lia).
    clear En Epr TOP R0.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.

    ldA I. do 6 zstep.
    ldBk I 0%nat. ldBk I 1%nat. ldBk I 2%nat. ldBk I 3%nat.
    do 7 zstep.
    st_limb I l0 c1 Ec1.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    do 5 zstep. ldA I. do 3 zstep.
    carry 6%Z x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.

    do 10 zstep.
    st_limb I l1 c2 Ec2.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    do 7 zstep. ldA I. do 4 zstep.
    carry 6%Z x1 y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.

    do 10 zstep.
    st_limb I l2 c3 Ec3.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    do 3 zstep.
    rewrite (bn_swrap32_small (q + -4)) by (clear - R4 R31; lia).
    do 5 zstep. ldA I. do 5 zstep.
    carry 6%Z x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.

    do 12 zstep.
    st_limb I l3 c4 Ec4.
    do 9 zstep.
    carry 14%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    zstep. zstep.
    assert (Hq' : (q + -4 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    if_cases K1; zify_cond K1.
    - eapply (IH (length la)); [ clear - HK; cbn [length] in HK; lia | reflexivity | exact I | exact Hq' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      + destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K2. cbn [length] in Hq'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
        eapply maw_epilogue. exact I.
      + eapply maw_tail_setup; [ | exact I | exact Hq' ].
        destruct la; [ exfalso; clear - Hq' K2; cbn [length] in Hq'; lia | discriminate ].
  Qed.

  Lemma bn_mul_add_words_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf9174) fc None m (seg_rom bgpsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 32, SP)]%Z m) as MUF. pose proof (wmono_refl bgpsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    zstep. if_cases K; zify_cond K.
    - assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]). subst a.
      assert (r = []) by (destruct r; [reflexivity | exfalso; cbn [length] in *; lia]). subst r.
      zstep. zstep. zstep.
      unfold maw_post. finish.
    - assert (Hn : (0 < n)%Z) by lia.
      carve_frame 32%nat STK.
      do 14 zstep.
      assert (I : KINV m1 [] a r 0 ap rp rp).
      { apply (KIT INV_init); try assumption; try lia.
        - unfold mul_add_words. rewrite mul_add_words_gen. reflexivity.
        - unfold mul_add_words. rewrite mul_add_words_gen. reflexivity. }
      clear RA RR WR FR STK MI0 MU MUF WM.
      if_cases K4; zify_cond K4.
      + eapply evt_eq; [ | eapply (maw_tail_setup a m1 [] r 0 ap rp n (Z_to_bv 64 4) t1 t2 sp s1 s2 t3 t4 t5 t6); [ | exact I | reflexivity ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
      + eapply evt_eq; [ | eapply (maw_loop4 (length a) a m1 [] r 0 ap rp n t1 t2 sp s1 s2 t3 t4 t5 t6); [ reflexivity | exact I | reflexivity | lia ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.
