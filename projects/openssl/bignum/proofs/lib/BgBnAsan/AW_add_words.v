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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_add_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_add_words_aentry := 0x22ba4c%Z.

Definition aw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a b : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 48%Z
          (fst (add_words a b)) (snd (add_words a b)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 48, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis LEN : length b = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A3 : bv_unsigned a3 = n.
  Hypothesis RA : limbs_at bgasegs m ap a.
  Hypothesis RB : limbs_at bgasegs m bp b.
  Hypothesis WR : wr_at bgasegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis ALB : alias_ok rp bp n.
  Hypothesis STK : stk bgasegs m lo SP.
  Hypothesis LO : (lo <= SP - 48)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 48 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 48 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 48 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgasegs m.

  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgasegs m rp (8 * n).
  Hypothesis ACA : acc bgasegs m ap (8 * n).
  Hypothesis ACB : acc bgasegs m bp (8 * n).
  Hypothesis APT : aptrs3 rp ap bp n lo.

  Notation POST := (aw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a b lo m).

  Notation ST pc mm x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation FCELLS := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma FBE : (bv_unsigned sp + -48 = bv_unsigned sp - 48)%Z. Proof. lia. Qed.
  Notation KINV := (INV bgasegs add_fl add_fc 1 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 48%Z (bv_unsigned sp + -48)%Z FCELLS
                        (fst (add_words a b)) (snd (add_words a b))).
  Notation KIT L := (L bgasegs add_fl add_fc 1%Z add_fc_range m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b 48%Z (bv_unsigned sp + -48)%Z FCELLS eq_refl FBE
                        LEN ALA ALB SEPR SEPA SEPB (fst (add_words a b)) (snd (add_words a b))).
  Notation K_rdA := (KIT INV_rdA).   Notation K_rdB := (KIT INV_rdB).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_rangeB := (KIT INV_rangeB).   Notation K_ptrs := (KIT INV_ptrs).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac ldB I := let L := constr:(K_rdB) in ldB_with L I.
  Ltac w64eq := unfold add_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  Ltac carry r x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : e = cn)
          by (clear - Rx Ry Hc Ecn; subst cn; unfold add_fc; rewrite BW_lit;
              lazymatch e with
              | context [((x + c) mod _)%Z] => pose proof (adc_carry x y c Rx Ry Hc)
              | context [((c + x) mod _)%Z] => pose proof (adc_carry' x y c Rx Ry Hc)
              end; lia);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply add_fc_range; assumption);
    clear Ecn.

  Notation PB := (apure (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (Z.of_nat (length a)) (bv_unsigned sp) 48%Z).
  Notation K_munch := (INV_munch bgasegs add_fl add_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 48%Z (bv_unsigned sp + -48)%Z FCELLS
                        (fst (add_words a b)) (snd (add_words a b))).

  Lemma aw_epi : forall m1 c x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    limbs_at bgasegs m1 rp (fst (add_words a b)) -> snd (add_words a b) = c ->
    rw_cells bgasegs m1 (SP + -48)%Z FCELLS -> stk bgasegs m1 lo (SP + -48)%Z ->
    mem_inv bgasegs m1 -> munch W m m1 -> wmono bgasegs m m1 ->
    evt bgasegs POST (ST 0x22bcb8 m1 SPF x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 c) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros m1 c x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HP CY FR ST MI MU WM.
    do 9 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    unfold aw_apost. finish.
  Qed.

  Notation K_shA := (INV_shA bgasegs add_fl add_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 48%Z (bv_unsigned sp + -48)%Z FCELLS
                        (fst (add_words a b)) (snd (add_words a b))).
  Notation K_shB := (INV_shB bgasegs add_fl add_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 48%Z (bv_unsigned sp + -48)%Z FCELLS
                        (fst (add_words a b)) (snd (add_words a b))).
  Notation K_shR := (INV_shR bgasegs add_fl add_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 48%Z (bv_unsigned sp + -48)%Z FCELLS
                        (fst (add_words a b)) (snd (add_words a b))).
  Ltac lshA P I k := let L := constr:(K_shA P) in ld_sh_with L I ACA k.
  Ltac lshB P I k := let L := constr:(K_shB P) in ld_sh_with L I ACB k.
  Ltac lshR P I k := let L := constr:(K_shR P) in ld_sh_with L I ACR k.
  Ltac shA P I k := lshA P I k; chk0.
  Ltac shB P I k := lshB P I k; chk0.
  Ltac shR P I k := lshR P I k; chk0.

  Lemma aw_tail : forall la m1 pre lb c pa pb pr r x8 x9 x10 x11 x12 x15 x18 x19 x20 x29 x30 x31,
    PB -> la <> [] -> KINV m1 pre la lb c pa pb pr -> r = Z.of_nat (length la) ->
    evt bgasegs POST (ST 0x22bc5c m1 SPF (Z_to_bv 64 pb) (Z_to_bv 64 (shad pr)) (Z_to_bv 64 pa) x8 x9 x10 x11 x12 (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x15 (Z_to_bv 64 (shad pb)) (Z_to_bv 64 (shad pa)) x18 x19 x20 (Z_to_bv 64 pr) x29 x30 x31).
  Proof.
    induction la as [|x la IH]; intros m1 pre lb c pa pb pr r x8 x9 x10 x11 x12 x15 x18 x19 x20 x29 x30 x31 P NE I Hr; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    shA P I 0%nat. shB P I 0%nat. shR P I 0%nat.
    ldA I. ldB I.
    assert (R1 : (1 <= r < 2^31)%Z) by (clear - Hr En N31; cbn [length] in *; lia).
    do 6 zstep.
    rewrite (bn_swrap32_small (r + -1)) by (clear - R1; lia).
    do 4 zstep.
    st_limb I l c' Ec'.
    zstep. zstep.
    carry 14%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep.
    setreg 6%Z (Z_to_bv 64 (shad (pr + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 16%Z (Z_to_bv 64 (shad (pb + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 17%Z (Z_to_bv 64 (shad (pa + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep.
    if_cases K; zify_cond K.
    -
      eapply IH; [ exact P | | exact I | clear - Hr; cbn [length] in Hr; lia ].
      destruct la; [ exfalso; clear - Hr K; cbn [length] in *; lia | discriminate ].
    -
      destruct la as [|x' la']. 2:{ exfalso. clear - Hr K R1. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
      pose proof (K_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
      eapply aw_epi; try eassumption.
  Qed.

  Lemma aw_tail_setup : forall la m1 pre lb c pa pb pr r x5 x7 x8 x9 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    PB -> la <> [] -> KINV m1 pre la lb c pa pb pr -> r = Z.of_nat (length la) ->
    evt bgasegs POST (ST 0x22bc34 m1 SPF x5 (Z_to_bv 64 SHB) x7 x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros la m1 pre lb c pa pb pr r x5 x7 x8 x9 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 P NE I Hr.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (BND : (0 <= pa < 140737488355328 /\ 0 <= pb < 140737488355328 /\ 0 <= pr < 140737488355328)%Z)
      by (clear - Epa Epb Epr En BR BA BB NE; destruct la; [congruence | cbn [length] in *; lia]).
    clear El En Epr TOP R0 Epa Epb TOPA BR BA BB.
    do 10 zstep.
    setreg 6%Z (Z_to_bv 64 (shad pr)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 16%Z (Z_to_bv 64 (shad pb)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 17%Z (Z_to_bv 64 (shad pa)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    eapply aw_tail; [exact P | exact NE | exact I | exact Hr].
  Qed.

  Lemma aw_loop4 : forall (K : nat) la m1 pre lb c off r x5 x8 x9 x15 x16 x17 x18 x19 x20,
    PB -> length la = K -> KINV m1 pre la lb c (ap + off) (bp + off) (rp + off) -> r = Z.of_nat (length la) -> (4 <= r)%Z ->
    evt bgasegs POST (ST 0x22bab4 m1 SPF x5 (Z_to_bv 64 SHB) (Z_to_bv 64 off) x8 x9 a0 a1 a2 (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x15 x16 x17 x18 x19 x20 (Z_to_bv 64 4) (Z_to_bv 64 (shad (bp + off))) (Z_to_bv 64 (shad (ap + off)))
                       (Z_to_bv 64 (shad (rp + off)))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la m1 pre lb c off r x5 x8 x9 x15 x16 x17 x18 x19 x20 P HK I Hr R4.
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    destruct la as [|x0 [|x1 [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (r < 2^31)%Z) by (clear - Hr En N31; lia).
    assert (BND : (0 <= off /\ ap + off + 32 <= 140737488355328 /\ bp + off + 32 <= 140737488355328 /\ rp + off + 32 <= 140737488355328)%Z)
      by (clear - Epa Epb Epr En BR BA BB; cbn [length] in *; lia).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. pose proof (zr_word a2) as Z2. unfold inr64 in Z0, Z1, Z2.
    clear En Epr TOP R0 Epa Epb TOPA BR BA BB.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.

    lshA P I 0%nat. zstep. chk0.
    lshB P I 0%nat. zstep. chk0.
    lshR P I 0%nat. zstep. chk0.
    ldA I. ldB I.
    do 4 zstep.
    st_limb I l0 c1 Ec1.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    zstep.
    lshA P I 0%nat. chk0. do 3 zstep. lshB P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    zstep. zstep.
    ldA I. ldB I.
    zstep. zstep.
    carry 5%Z x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    do 3 zstep.
    st_limb I l1 c2 Ec2.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    zstep.
    lshA P I 0%nat. chk0. do 3 zstep. lshB P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    zstep. zstep.
    ldA I. ldB I.
    zstep. zstep.
    carry 5%Z x1 y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    do 3 zstep.
    st_limb I l2 c3 Ec3.
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (K_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    zstep.
    lshA P I 0%nat. chk0. do 3 zstep. lshB P I 0%nat. chk0. do 3 zstep. lshR P I 0%nat. chk0.
    zstep. zstep.
    ldA I. ldB I.
    zstep.
    rewrite (bn_swrap32_small (r + -4)) by (clear - R4 R31; lia).
    do 4 zstep.
    carry 14%Z x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    do 4 zstep.
    st_limb I l3 c4 Ec4.
    zstep.
    carry 14%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    zstep.
    assert (Hr' : (r + -4 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    replace (ap + off + 32)%Z with (ap + (off + 32))%Z in I by (clear; lia).
    replace (bp + off + 32)%Z with (bp + (off + 32))%Z in I by (clear; lia).
    replace (rp + off + 32)%Z with (rp + (off + 32))%Z in I by (clear; lia).
    zstep. if_cases K1; zify_cond K1.
    -
      setreg 29%Z (Z_to_bv 64 (shad (bp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 30%Z (Z_to_bv 64 (shad (ap + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 31%Z (Z_to_bv 64 (shad (rp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply (IH (length la)); [ clear - HK; cbn [length] in HK; lia | exact P | reflexivity | exact I | exact Hr' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      +
        destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K2. cbn [length] in Hr'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
        pose proof (K_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
        eapply aw_epi; try eassumption.
      +
        do 3 zstep.
        eapply aw_tail_setup; [ exact P | | exact I | exact Hr' ].
        destruct la; [ exfalso; clear - Hr' K2; cbn [length] in Hr'; lia | discriminate ].
  Qed.

  Lemma bn_add_words_aspec :
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22ba4c) fc None m (seg_rom bgasegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 48, SP)]%Z m) as MUF. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    assert (PBn : hide ((0 < n)%Z -> PB)).
    { apply hide_intro. intros Hn. eapply (apure_intro bgasegs m); try eassumption; lia. }
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 48%nat STK.
    do 8 zstep.
    zstep. if_cases K; zify_cond K.
    -
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      zstep. zstep.
      eapply aw_epi; try eassumption.
      + rewrite Ea. cbn. apply limbs_at_nil. lia.
      + rewrite Ea. reflexivity.
    -
      assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 4 zstep.
      assert (I : KINV m1 [] a b 0 ap bp rp).
      { apply (KIT INV_init); try assumption; try lia.
        - unfold add_words. rewrite add_words_gen. reflexivity.
        - unfold add_words. rewrite add_words_gen. reflexivity. }
      clear RA RB WR FR STK MI0 MU MUF WM G1 G2.
      zstep. if_cases K4; zify_cond K4.
      +
        do 8 zstep.
        setreg 29%Z (Z_to_bv 64 (shad (bp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 30%Z (Z_to_bv 64 (shad (ap + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 31%Z (Z_to_bv 64 (shad (rp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (aw_loop4 (length a) a m1 [] b 0 0 n t0 sp s1 a5 a6 a7 s2 s3 s4);
                           [ exact P | reflexivity | rewrite !Z.add_0_r; exact I | reflexivity | lia ] ].
        rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
      +
        zstep. zstep.
        eapply evt_eq; [ | eapply (aw_tail_setup a m1 [] b 0 ap bp rp n t0 t2 sp s1 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 4) t4 t5 t6);
                           [ exact P | | exact I | reflexivity ] ].
        * rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
  Qed.
End Proofs.
