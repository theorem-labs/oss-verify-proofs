(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_add_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_add_words_aentry := 0x22ae1c%Z.

Definition maw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (r a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 80%Z
          (fst (mul_add_words r a w)) (snd (mul_add_words r a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a r : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 80, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LR : limbs r.
  Hypothesis LEN : length r = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgasegs m ap a.
  Hypothesis RR : limbs_at bgasegs m rp r.
  Hypothesis WR : wr_at bgasegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bgasegs m lo SP.
  Hypothesis LO : (lo <= SP - 80)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 80 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 80 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgasegs m.

  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgasegs m rp (8 * n).
  Hypothesis ACA : acc bgasegs m ap (8 * n).
  Hypothesis APT : aptrs3 rp ap rp n lo.

  Notation POST := (maw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) r a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.
  Lemma ALR : alias_ok rp rp n. Proof. left. reflexivity. Qed.
  Lemma FBE : (bv_unsigned sp + -80 = bv_unsigned sp - 80)%Z. Proof. lia. Qed.

  Notation ST pc mm x2 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR ra x2 gp tp (Z_to_bv 64 4294967295) (Z_to_bv 64 (bv_unsigned a3 mod 4294967296)) (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32))
             x8 x9 x10 x11 x12 a3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation FCELLS := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation FCR := (maw_fc_range (bv_unsigned a3) RW).
  Notation KINV := (INV bgasegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        80%Z (bv_unsigned sp + -80)%Z FCELLS
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation KIT L := (L bgasegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a r
                        80%Z (bv_unsigned sp + -80)%Z FCELLS eq_refl FBE
                        LEN ALA ALR SEPR SEPA SEPR (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation PB := (apure (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (Z.of_nat (length a)) (bv_unsigned sp) 80%Z).
  Notation K_shA := (INV_shA bgasegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        80%Z (bv_unsigned sp + -80)%Z FCELLS
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation K_shR := (INV_shR bgasegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        80%Z (bv_unsigned sp + -80)%Z FCELLS
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).

  Ltac ldA I := let L := constr:(KIT INV_rdA) in ldA_with L I.
  Ltac ldB I := let L := constr:(KIT INV_rdB) in ldB_with L I.
  Ltac w64eq := unfold maw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb I l cn Ecn := let L1 := constr:(KIT INV_store_ok) in let L2 := constr:(KIT INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
  Ltac lshA P I k := let L := constr:(K_shA P) in ld_sh_with L I ACA k.
  Ltac lshR P I k := let L := constr:(K_shR P) in ld_sh_with L I ACR k.

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

  Lemma maw_epi : forall m1 c x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    limbs_at bgasegs m1 rp (fst (mul_add_words r a w)) -> snd (mul_add_words r a w) = c ->
    rw_cells bgasegs m1 (SP + -80)%Z FCELLS -> stk bgasegs m1 lo (SP + -80)%Z ->
    mem_inv bgasegs m1 -> munch W m m1 -> wmono bgasegs m m1 ->
    evt bgasegs POST (MS (mkR ra SPF gp tp x5 x6 x7 x8 x9 x10 x11 x12 a3 x14 x15 (Z_to_bv 64 c) x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x22b178) fc None m1 (seg_rom bgasegs)).
  Proof.
    intros until x31. intros HP CY FR ST MI MU WM.
    do 13 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    unfold maw_apost. finish.
  Qed.

  Lemma maw_tail : forall la m1 pre lb c pa pr q x8 x9 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x30 x31,
    PB -> la <> [] -> KINV m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bgasegs POST (ST 0x22b0ec m1 SPF x8 x9 x10 x11 (Z_to_bv 64 q) x14 (Z_to_bv 64 (shad pr)) (Z_to_bv 64 c) (Z_to_bv 64 pr)
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (shad pa)) (Z_to_bv 64 pa) x30 x31).
  Proof.
    induction la as [|x la IH]; intros m1 pre lb c pa pr q x8 x9 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x30 x31 P NE I Hq; [congruence|].
    pose proof (KIT INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (KIT INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry.
    pose proof (KIT INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (R1 : (1 <= q < 2^31)%Z) by (clear - Hq En N31; cbn [length] in *; lia).
    lshA P I 0%nat. chk0. lshR P I 0%nat. chk0.
    ldA I. ldB I.
    do 2 zstep.
    rewrite (bn_swrap32_small (q + -1)) by (clear - R1; lia).
    do 17 zstep.
    st_limb I l c' Ec'.
    do 7 zstep.
    carry 16%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep.
    setreg 15%Z (Z_to_bv 64 (shad (pr + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 28%Z (Z_to_bv 64 (shad (pa + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep.
    if_cases K; zify_cond K.
    - eapply IH; [ exact P | | exact I | clear - Hq; cbn [length] in Hq; lia ].
      destruct la; [ exfalso; clear - Hq K; cbn [length] in *; lia | discriminate ].
    - destruct la as [|x' la']. 2:{ exfalso. clear - Hq K R1. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
      pose proof (KIT INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
      eapply maw_epi; try eassumption.
  Qed.

  Lemma maw_tail_setup : forall la m1 pre lb c pa pr q x8 x9 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x29 x30 x31,
    PB -> la <> [] -> KINV m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bgasegs POST (ST 0x22b0d0 m1 SPF x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 c) x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHB) x29 x30 x31).
  Proof.
    intros la m1 pre lb c pa pr q x8 x9 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x29 x30 x31 P NE I Hq.
    pose proof (KIT INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (BND : (0 <= pa < 140737488355328 /\ 0 <= pr < 140737488355328)%Z)
      by (clear - Epa Epr En BR BA NE; destruct la; [congruence | cbn [length] in *; lia]).
    clear El En Epr TOP R0 Epa Epb TOPA BR BA BB.
    do 7 zstep.
    setreg 15%Z (Z_to_bv 64 (shad pr)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 28%Z (Z_to_bv 64 (shad pa)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    eapply maw_tail; [exact P | exact NE | exact I | exact Hq].
  Qed.

  Lemma maw_loop4 : forall (K : nat) la m1 pre lb c off q x8 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24,
    PB -> length la = K -> KINV m1 pre la lb c (ap + off) (rp + off) (rp + off) -> q = Z.of_nat (length la) -> (4 <= q)%Z ->
    evt bgasegs POST (ST 0x22aea0 m1 SPF x8 (Z_to_bv 64 (shad (ap + off))) a0 a1 (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 c) x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHB) (Z_to_bv 64 off) (Z_to_bv 64 4) (Z_to_bv 64 (shad (rp + off)))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la m1 pre lb c off q x8 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 P HK I Hq R4.
    pose proof (KIT INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (KIT INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    destruct la as [|x0 [|x1 [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (q < 2^31)%Z) by (clear - Hq En N31; lia).
    assert (BND : (0 <= off /\ ap + off + 32 <= 140737488355328 /\ rp + off + 32 <= 140737488355328)%Z)
      by (clear - Epa Epr En BR BA; cbn [length] in *; lia).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. unfold inr64 in Z0, Z1.
    clear En Epr TOP R0 Epa Epb TOPA BR BA BB.
    pose proof (KIT INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (KIT INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.

    lshA P I 0%nat. zstep. chk0.
    lshR P I 0%nat. zstep. chk0.
    ldA I. ldB I. do 5 zstep.
    st_limb I l0 c1 Ec1.
    pose proof (KIT INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (KIT INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.

    zstep. lshA P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    do 4 zstep. ldA I. do 7 zstep. ldB I. do 10 zstep.
    carry 18%Z x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    do 2 zstep.
    st_limb I l1 c2 Ec2.
    pose proof (KIT INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (KIT INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.

    zstep. lshA P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    do 4 zstep. ldA I. do 5 zstep. ldB I. do 12 zstep.
    carry 19%Z x1 y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    do 2 zstep.
    st_limb I l2 c3 Ec3.
    pose proof (KIT INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (KIT INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.

    zstep. lshA P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    do 4 zstep. ldA I. ldB I.
    zstep. rewrite (bn_swrap32_small (q + -4)) by (clear - R4 R31; lia).
    do 26 zstep.
    carry 16%Z x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    do 10 zstep.
    st_limb I l3 c4 Ec4.
    zstep.
    carry 16%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    zstep.
    assert (Hq' : (q + -4 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    replace (ap + off + 32)%Z with (ap + (off + 32))%Z in I by (clear; lia).
    replace (rp + off + 32)%Z with (rp + (off + 32))%Z in I by (clear; lia).
    zstep. if_cases K1; zify_cond K1.
    - setreg 9%Z (Z_to_bv 64 (shad (ap + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 31%Z (Z_to_bv 64 (shad (rp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply (IH (length la)); [ clear - HK; cbn [length] in HK; lia | exact P | reflexivity | exact I | exact Hq' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      + destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K2. cbn [length] in Hq'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
        pose proof (KIT INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
        eapply maw_epi; try eassumption.
      + do 2 zstep.
        eapply maw_tail_setup; [ exact P | | exact I | exact Hq' ].
        destruct la; [ exfalso; clear - Hq' K2; cbn [length] in Hq'; lia | discriminate ].
  Qed.

  Lemma bn_mul_add_words_aspec :
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22ae1c) fc None m (seg_rom bgasegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 80, SP)]%Z m) as MUF. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    assert (PBn : hide ((0 < n)%Z -> PB)).
    { apply hide_intro. intros Hn. eapply (apure_intro bgasegs m _ _ _ a r); try eassumption; lia. }
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 80%nat STK.
    do 12 zstep.
    zstep. if_cases K; zify_cond K.
    -
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      assert (Er : r = []) by (destruct r; [reflexivity | exfalso; rewrite Ea in LEN; cbn [length] in *; lia]).
      zstep. zstep.
      eapply maw_epi; try eassumption.
      + rewrite Ea, Er. cbn. apply limbs_at_nil. lia.
      + rewrite Ea, Er. reflexivity.
    -
      assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 9 zstep.
      assert (I : KINV m1 [] a r 0 ap rp rp).
      { apply (KIT INV_init); try assumption; try lia.
        - unfold mul_add_words. rewrite mul_add_words_gen. reflexivity.
        - unfold mul_add_words. rewrite mul_add_words_gen. reflexivity. }
      clear RA RR WR FR STK MI0 MU MUF WM G1 G2.
      zstep. if_cases K4; zify_cond K4.
      + do 6 zstep.
        setreg 9%Z (Z_to_bv 64 (shad (ap + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 31%Z (Z_to_bv 64 (shad (rp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (maw_loop4 (length a) a m1 [] r 0 0 n sp (Z_to_bv 64 (w ≪ 32)) (Z_to_bv 64 (-1)) a7 s2 s3 s4 s5 s6 s7 s8);
                           [ exact P | reflexivity | rewrite !Z.add_0_r; exact I | reflexivity | lia ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evt_eq; [ | eapply (maw_tail_setup a m1 [] r 0 ap rp n sp s1 (Z_to_bv 64 (w ≪ 32)) (Z_to_bv 64 (-1)) a7 s2 s3 s4 s5 s6 s7 s8 t4 (Z_to_bv 64 4) t6);
                           [ exact P | | exact I | reflexivity ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
  Qed.
End Proofs.
