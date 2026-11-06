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

Definition bn_sub_words_entry := 0xf9a00%Z.

Definition sub_fl (x y c : Z) : Z := (x - y - c) mod BW.
Definition sub_fc (x y c : Z) : Z := if (x - y - c <? 0)%Z then 1%Z else 0%Z.

Lemma sub_words_gen : forall la lb c, sub_words_c la lb c = gen_words_c sub_fl sub_fc la lb c.
Proof. induction la as [|x la IH]; intros [|y lb] c; try reflexivity. Qed.

Lemma sub_fc_range : forall x y c, (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> (0 <= c <= 1)%Z ->
  (0 <= sub_fc x y c <= 1)%Z.
Proof. intros. unfold sub_fc. destruct (x - y - c <? 0)%Z; lia. Qed.

Definition sw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a b : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 16%Z
          (fst (sub_words a b)) (snd (sub_words a b)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis LEN : length b = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A3 : bv_unsigned a3 = n.
  Hypothesis RA : limbs_at bgpsegs m ap a.
  Hypothesis RB : limbs_at bgpsegs m bp b.
  Hypothesis WR : wr_at bgpsegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis ALB : alias_ok rp bp n.
  Hypothesis STK : stk bgpsegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 16 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.

  Notation POST := (sw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a b lo m).
  Notation ST pc mm x2 x5 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra x2 gp tp x5 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -16)).

  Lemma FBE : (bv_unsigned sp + -16 = bv_unsigned sp - 16)%Z. Proof. lia. Qed.
  Notation KINV := (INV bgpsegs sub_fl sub_fc 1 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 16%Z (bv_unsigned sp + -16)%Z [C8 s0; C8 ra]
                        (fst (sub_words a b)) (snd (sub_words a b))).
  Notation KIT L := (L bgpsegs sub_fl sub_fc 1%Z sub_fc_range m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b 16%Z (bv_unsigned sp + -16)%Z [C8 s0; C8 ra] eq_refl FBE
                        LEN ALA ALB SEPR SEPA SEPB (fst (sub_words a b)) (snd (sub_words a b))).
  Notation K_rdA := (KIT INV_rdA).   Notation K_rdB := (KIT INV_rdB).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_rangeB := (KIT INV_rangeB).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac ldB I := let L := constr:(K_rdB) in ldB_with L I.
  Ltac w64eq := unfold sub_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  Ltac borrow_arith Rx Ry Hc Ecn cn :=
    clear - Rx Ry Hc Ecn; subst cn; unfold sub_fc; case_ltb; Z.div_mod_to_equations; lia.
  Ltac carry r x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : e = cn) by (borrow_arith Rx Ry Hc Ecn cn);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply sub_fc_range; assumption);
    clear Ecn.

  Lemma sw_epilogue : forall m1 pre c pa pb pr x5 x8 x10 x11 x12 x13 x15 x16 x17,
    KINV m1 pre [] [] c pa pb pr ->
    evt bgpsegs POST (ST 0xf9b04 m1 SPF x5 x8 x10 x11 x12 x13 (Z_to_bv 64 c) x15 x16 x17).
  Proof.
    intros m1 pre c pa pb pr x5 x8 x10 x11 x12 x13 x15 x16 x17 I.
    pose proof (K_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    finish.
  Qed.

  Lemma sw_tail : forall la m1 pre lb c pa pb pr x5 x8 x15 x16 x17,
    la <> [] -> KINV m1 pre la lb c pa pb pr ->
    evt bgpsegs POST (ST 0xf9ad0 m1 SPF x5 x8 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 (rp + 8 * n))
                       (Z_to_bv 64 c) x15 x16 x17).
  Proof.
    induction la as [|x la IH]; intros m1 pre lb c pa pb pr x5 x8 x15 x16 x17 NE I; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    ldA I. zstep.
    rewrite (bn_swrap32_small (c + 0)) by (clear - Hc; lia). rewrite Z.add_0_r.
    ldB I. zstep. zstep. zstep. zstep. zstep.
    st_limb I l c' Ec'.
    zstep.
    carry 14%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - eapply IH; [ | exact I ]. destruct la; [ exfalso; cbn [length] in *; lia | discriminate ].
    - destruct la as [|x' la']. 2:{ exfalso. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. cbn [length] in *. lia. }
      eapply sw_epilogue. exact I.
  Qed.

  Lemma sw_tail_setup : forall la m1 pre lb c pa pb pr r x5 x8 x15 x16 x17,
    la <> [] -> KINV m1 pre la lb c pa pb pr -> r = Z.of_nat (length la) ->
    evt bgpsegs POST (ST 0xf9abc m1 SPF x5 x8 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x15 x16 x17).
  Proof.
    intros la m1 pre lb c pa pb pr r x5 x8 x15 x16 x17 NE I Hr.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    assert (R1 : (1 <= r < 2^31)%Z) by (destruct la; [congruence | cbn [length] in *; lia]).
    zstep. zstep. zstep. zstep. zstep.
    setreg 13%Z (Z_to_bv 64 (rp + 8 * n)) ltac:(f_equal; rewrite shl32_shr29 by lia; lia).
    eapply sw_tail; [exact NE | exact I].
  Qed.

  Ltac norm_t2 r xn x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 (xn - cn))
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; borrow_arith Rx Ry Hc Ecn cn);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply sub_fc_range; assumption);
    clear Ecn.

  Lemma sw_loop4 : forall (K : nat) la m1 pre lb c pa pb pr r x5 x8 x16 x17,
    length la = K -> KINV m1 pre la lb c pa pb pr -> r = Z.of_nat (length la) -> (4 <= r)%Z ->
    evt bgpsegs POST (ST 0xf9a20 m1 SPF x5 x8 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 r)
                       (Z_to_bv 64 c) (Z_to_bv 64 4) x16 x17).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la m1 pre lb c pa pb pr r x5 x8 x16 x17 HK I Hr R4.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    destruct la as [|x0 [|x1 [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (r < 2^31)%Z) by (clear - Hr En N31; lia).
    clear En Epr TOP R0.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.
    ldA I. ldB I. zstep.
    rewrite (bn_swrap32_small (c + 0)) by (clear - Hc; lia). rewrite Z.add_0_r.
    zstep. zstep. zstep.
    st_limb I l0 c1 Ec1.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    ldA I. zstep. ldB I. zstep.
    rewrite (bn_swrap32_small (r + -4)) by (clear - R4 R31; lia).
    zstep. zstep.
    norm_t2 14%Z x1 x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    zstep.
    st_limb I l1 c2 Ec2.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    ldA I. zstep. zstep. ldB I. zstep. zstep.
    norm_t2 14%Z x2 x1 y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    zstep. zstep. zstep.
    st_limb I l2 c3 Ec3.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    ldA I. ldB I. zstep. zstep. zstep. zstep.
    norm_t2 14%Z x3 x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    zstep. zstep. zstep.
    st_limb I l3 c4 Ec4.
    zstep.
    carry 14%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    zstep. zstep.
    assert (Hr' : (r + -4 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    if_cases K1; zify_cond K1.
    - eapply (IH (length la)); [ clear - HK; cbn [length] in HK; lia | reflexivity | exact I | exact Hr' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      + destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K2. cbn [length] in Hr'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
        eapply sw_epilogue. exact I.
      + eapply sw_tail_setup; [ | exact I | exact Hr' ].
        destruct la; [ exfalso; clear - Hr' K2; cbn [length] in Hr'; lia | discriminate ].
  Qed.

  Lemma bn_sub_words_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf9a00) fc None m (seg_rom bgpsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 16, SP)]%Z m) as MUF. pose proof (wmono_refl bgpsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    zstep. if_cases K; zify_cond K.
    - assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]). subst a.
      assert (b = []) by (destruct b; [reflexivity | exfalso; cbn [length] in *; lia]). subst b.
      zstep. zstep. zstep.
      unfold sw_post. finish. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z) by lia.
      carve_frame 16%nat STK.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      assert (I : KINV m1 [] a b 0 ap bp rp).
      { apply (KIT INV_init); try assumption; try lia.
        - unfold sub_words. rewrite sub_words_gen. reflexivity.
        - unfold sub_words. rewrite sub_words_gen. reflexivity. }
      clear RA RB WR FR STK MI0 MU MUF WM.
      if_cases K4; zify_cond K4.
      + eapply evt_eq; [ | eapply (sw_tail_setup a m1 [] b 0 ap bp rp n t0 sp (Z_to_bv 64 4) a6 a7); [ | exact I | reflexivity ] ].
        * rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
      + eapply evt_eq; [ | eapply (sw_loop4 (length a) a m1 [] b 0 ap bp rp n t0 sp a6 a7); [ reflexivity | exact I | reflexivity | lia ] ].
        rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.
