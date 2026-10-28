(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import W_mul_words.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2250964 => 1
  | 2250968 => 1
  | 2250980 => 1
  | 2250984 => 1
  | 2250988 => 1
  | 2250992 => 1
  | 2251004 => 1
  | 2251012 => 2
  | 2251016 => 2
  | 2251032 => 2
  | 2251036 => 2
  | 2251064 => 2
  | 2251088 => 2
  | 2251192 => 2
  | 2251216 => 2
  | 2251320 => 2
  | 2251344 => 2
  | 2251448 => 2
  | 2251452 => 2
  | 2251460 => 2
  | 2251568 => 1
  | 2251572 => 1
  | 2251592 => 1
  | 2251604 => 2
  | 2251608 => 2
  | 2251620 => 2
  | 2251624 => 2
  | 2251652 => 2
  | 2251656 => 2
  | 2251664 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_mul_words_aentry := 0x225854%Z.

Definition mw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 112%Z
          (fst (mul_words a w)) (snd (mul_words a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 112, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bsegs m ap a.
  Hypothesis WR : wr_at bsegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bsegs m lo SP.
  Hypothesis LO : (lo <= SP - 112)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 112 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 112 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bsegs m.
  (* [comment removed for export] *)
  Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bsegs m rp (8 * n).
  Hypothesis ACA : acc bsegs m ap (8 * n).
  Hypothesis APT : aptrs3 rp ap ap n lo.

  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.

  Notation POST := (mw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x2 x7 x8 x9 x10 x11 x12 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 (bv_unsigned a3 mod 4294967296)) (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32)) x7
             x8 x9 x10 x11 x12 a3 x14 x15 x16 (Z_to_bv 64 4294967295) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma LEN : length a = length a. Proof. reflexivity. Qed.
  Notation FCR := (mw_fc_range (bv_unsigned a3) RW).
  Lemma FBE : (bv_unsigned sp + -112 = bv_unsigned sp - 112)%Z. Proof. lia. Qed.
  Notation KINV jb := (INV bsegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).
  Notation KIT jb L := (L bsegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) eq_refl FBE
                        LEN ALA ALA SEPR SEPA SEPA (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).
  Notation PB := (apure (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (Z.of_nat (length a)) (bv_unsigned sp) 112%Z).
  Notation K_shA jb := (INV_shA bsegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).
  Notation K_shR jb := (INV_shR bsegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).

  Ltac ldA jb I := let L := constr:(KIT jb INV_rdA) in ldA_with L I.
  Ltac w64eq := unfold mw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb jb I l cn Ecn := let L1 := constr:(KIT jb INV_store_ok) in let L2 := constr:(KIT jb INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
  Ltac lshA jb P I k := let L := constr:(K_shA jb P) in ld_sh_with L I ACA k.
  Ltac lshR jb P I k := let L := constr:(K_shR jb P) in ld_sh_with L I ACR k.

  (* [comment removed for export] *)
  Ltac carry r x c Rx Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 cn)
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx RWv Hc Ecn; subst cn; unfold mw_fl, mw_fc; rewrite ?BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Hc Ecn; subst cn; apply FCR; assumption);
    clear Ecn.

  Ltac limb_val r xn x c Rx Rxn Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 (mw_fl (bv_unsigned a3) xn xn cn))
          by (unfold mw_fl; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx Rxn RWv Hc Ecn; subst cn; unfold mw_fl, mw_fc; rewrite ?BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              let q := fresh "q" in first [ set (q := (xn * wv)%Z) in * | set (q := (wv * xn)%Z) in * ]; clearbody q;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Hc Ecn; subst cn; apply FCR; assumption);
    clear Ecn.
  (* [comment removed for export] *)
  Lemma mw_epi : forall jb m1 c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    limbs_at bsegs m1 rp (fst (mul_words a w)) -> snd (mul_words a w) = c ->
    rw_cells bsegs m1 (SP + -112)%Z (FCELLS jb) -> stk bsegs m1 lo (SP + -112)%Z ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    evt bsegs POST (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 c) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x225bf0) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until x31. intros HP CY FR ST MI MU WM.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    rewrite <- CY.
    unfold mw_apost. finish.
  Qed.

  Lemma NZ2 : (0 < n)%Z -> (0 < rp /\ 0 < ap)%Z.
  Proof. intros Hn. destruct (UBR Hn) as (H1 & _). destruct (UBA Hn) as (H2 & _). auto. Qed.
  (* [comment removed for export] *)
  Lemma PFACTS : forall jb m1 pre la c pa pr, PB -> KINV jb m1 pre la la c pa pa pr -> la <> [] ->
    ((0 < pa /\ pa + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pr /\ pr + 8 * Z.of_nat (length la) <= 140737488355328))%Z.
  Proof.
    intros jb m1 pre la c pa pr P I NE.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (Hn : (0 < n)%Z) by (destruct la; [congruence | cbn [length] in En; lia]).
    destruct (NZ2 Hn) as (NZR & NZA).
    clear - BR BA Epa Epr En NZR NZA. lia.
  Qed.

  Lemma ALIGN : (rp mod 8 = 0 /\ ap mod 8 = 0)%Z.
  Proof. unfold aptrs3 in APT. tauto. Qed.

  Lemma mw_tail : forall la jb m1 pre c pa pr r x1 x8 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27,
    PB -> la <> [] -> KINV jb m1 pre la la c pa pa pr -> r = Z.of_nat (length la) ->
    evt bsegs POST (ST 0x225b54 m1 x1 SPF (Z_to_bv 64 (shad pa)) x8 (Z_to_bv 64 pa) x10 x11 (Z_to_bv 64 r) x14 (Z_to_bv 64 0) (Z_to_bv 64 c)
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 0) (Z_to_bv 64 (shad pr)) (Z_to_bv 64 (-9)) (Z_to_bv 64 pr)).
  Proof.
    induction la as [|x la IH]; intros jb m1 pre c pa pr r x1 x8 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 P NE I Hr; [congruence|].
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (PP : ((0 < pa /\ pa + 8 <= 140737488355328) /\ (0 < pr /\ pr + 8 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ P I NE) as Q. clear - Q. cbn [length] in Q. lia. }
    destruct PP as (PA & PR).
    assert (R1 : (1 <= r < 2147483648)%Z) by (clear - Hr En N31; cbn [length] in *; lia).
    assert (Hr' : (r + -1 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    clear En Epr TOP R0 Hr NE.
    ub. lshA jb P I 0%nat. chk0.
    ub. lshR jb P I 0%nat. chk0.
    ldA jb I. do 2 zstep.
    st_limb jb I l c' Ec'.
    ub. zstep. rewrite (bn_swrap32_small (r + -1)) by (clear - R1; lia).
    ub. do 20 zstep.
    carry 16%Z x c Rx Hc c' Ec' Hc'.
    setreg 29%Z (Z_to_bv 64 (shad (pr + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep. setreg 7%Z (Z_to_bv 64 (shad (pa + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep.
    zstep. if_cases K; zify_cond K.
    -
      eapply IH; [ exact P | | exact I | exact Hr' ].
      destruct la; [ exfalso; clear - Hr' K; cbn [length] in *; lia | discriminate ].
    -
      destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K R1. cbn [length] in *. lia. }
      pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
      eapply mw_epi; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma mw_tail_setup : forall la jb m1 pre c pa pr r x1 x8 x9 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    PB -> la <> [] -> KINV jb m1 pre la la c pa pa pr -> r = Z.of_nat (length la) ->
    evt bsegs POST (ST 0x225b2c m1 x1 SPF (Z_to_bv 64 SHB) x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 r) x14 x15 (Z_to_bv 64 c)
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros P NE I Hr.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (BND : (0 <= pa < 140737488355328 /\ 0 <= pr < 140737488355328)%Z)
      by (clear - Epa Epr En BR BA NE; destruct la; [congruence | cbn [length] in *; lia]).
    assert (AL3 : (pr mod 8 = 0 /\ pa mod 8 = 0)%Z).
    { destruct ALIGN as (A1 & A2'). clear - Epa Epr A1 A2'. subst pa pr. split; Z.div_mod_to_equations; lia. }
    clear El En Epr TOP R0 Epa Epb TOPA BR BA BB.
    zstep. ub.
    destruct AL3 as (AR8 & AA8). rewrite (land7 _ AR8), (land7 _ AA8). clear AR8 AA8.
    do 4 zstep.
    setreg 29%Z (Z_to_bv 64 (shad pr)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 7%Z (Z_to_bv 64 (shad pa)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    ub. do 2 zstep.
    eapply mw_tail; [exact P | exact NE | exact I | exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma mw_loop4 : forall (K : nat) la jb m1 pre c off r x1 x8 x14 x15 x24 x25 x26 x27,
    PB -> length la = K -> KINV jb m1 pre la la c (ap + off) (ap + off) (rp + off) -> r = Z.of_nat (length la) -> (4 <= r)%Z ->
    evt bsegs POST (ST 0x225900 m1 x1 SPF (Z_to_bv 64 SHB) x8 (Z_to_bv 64 (-8)) a0 a1 (Z_to_bv 64 r) x14 x15 (Z_to_bv 64 c)
                       (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (shad (rp + off))) (Z_to_bv 64 (shad (ap + off))) (Z_to_bv 64 (-33))
                       x24 x25 x26 x27 (Z_to_bv 64 off) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 0)).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m1 pre c off r x1 x8 x14 x15 x24 x25 x26 x27 P HK I Hr R4.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    destruct la as [|x0 [|x1' [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (r < 2^31)%Z) by (clear - Hr En N31; lia).
    assert (PP : ((0 < ap + off /\ ap + off + 32 <= 140737488355328) /\ (0 < rp + off /\ rp + off + 32 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ P I ltac:(discriminate)) as Q. clear - Q. cbn [length] in Q. lia. }
    assert (OFF0 : (0 <= off)%Z) by (clear - Epa; lia).
    destruct PP as (PA & PR).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. unfold inr64 in Z0, Z1.
    assert (Hr' : (r + -4 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    assert (HK' : (length la < K)%nat) by (clear - HK; cbn [length] in HK; lia).
    clear En Epr TOP R0 Epa Epb TOPA Hr HK El.
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0.
    (* [comment removed for export] *)
    zstep. ub. lshA jb P I 0%nat. chk0.
    zstep. ub. lshR jb P I 0%nat. chk0.
    ldA jb I. do 2 zstep.
    st_limb jb I l0 c1 Ec1.
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1.
    ub. do 3 zstep. lshA jb P I 0%nat. chk0. ub. do 3 zstep. lshR jb P I 0%nat. chk0.
    do 3 zstep. ldA jb I. do 15 zstep.
    limb_val 26%Z x1' x0 c Rx0 Rx1 Hc c1 Ec1 Hc1.
    st_limb jb I l1 c2 Ec2.
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2.
    ub. do 3 zstep. lshA jb P I 0%nat. chk0. ub. do 3 zstep. lshR jb P I 0%nat. chk0.
    do 8 zstep. ldA jb I. do 10 zstep.
    limb_val 25%Z x2 x1' c1 Rx1 Rx2 Hc1 c2 Ec2 Hc2.
    st_limb jb I l2 c3 Ec3.
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3.
    ub. do 3 zstep. lshA jb P I 0%nat. chk0. ub. do 3 zstep. lshR jb P I 0%nat. chk0.
    do 8 zstep. ldA jb I. do 10 zstep.
    limb_val 24%Z x3 x2 c2 Rx2 Rx3 Hc2 c3 Ec3 Hc3.
    st_limb jb I l3 c4 Ec4.

    ub. zstep. rewrite (bn_swrap32_small (r + -4)) by (clear - R4 R31; lia).
    ub. do 18 zstep.
    carry 16%Z x3 c3 Rx3 Hc3 c4 Ec4 Hc4.
    zstep.
    replace (ap + off + 32)%Z with (ap + (off + 32))%Z in I by (clear; lia).
    replace (rp + off + 32)%Z with (rp + (off + 32))%Z in I by (clear; lia).
    setreg 21%Z (Z_to_bv 64 (shad (rp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 22%Z (Z_to_bv 64 (shad (ap + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply (IH (length la)); [ exact HK' | exact P | reflexivity | exact I | exact Hr' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K2. cbn [length] in Hr'. lia. }
        pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
        eapply mw_epi; try eassumption.
      + (* [comment removed for export] *)
        do 3 zstep.
        eapply mw_tail_setup; [ exact P | | exact I | exact Hr' ].
        destruct la; [ exfalso; clear - Hr' K2; cbn [length] in Hr'; lia | discriminate ].
  Qed.

  (* [comment removed for export] *)
  Lemma bn_mul_words_aspec :
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x225854) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 112, SP)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    assert (PBn : hide ((0 < n)%Z -> PB)).
    { apply hide_intro. intros Hn. eapply (apure_intro bsegs m _ _ _ a a); try eassumption; try reflexivity; lia. }
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 112%nat STK.
    do 15 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      zstep. zstep.
      eapply mw_epi; try eassumption.
      + rewrite Ea. cbn. apply limbs_at_nil. lia.
      + rewrite Ea. reflexivity.
    - (* [comment removed for export] *)
      assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 9 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : KINV jb mm [] a a 0 ap ap rp);
        [ apply (KIT jb INV_init); try assumption; try lia;
          [ unfold mul_words; rewrite mul_words_gen; reflexivity | unfold mul_words; rewrite mul_words_gen; reflexivity ] | ]
      end end.
      clear RA WR FR STK MI0 MU MUF WM G1 G2.
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        zstep. zstep. ub. zstep. zstep. ub. zstep. zstep. ub.
        destruct ALIGN as (AR8 & AA8). rewrite (land7 _ AR8), (land7 _ AA8). clear AR8 AA8.
        setreg 21%Z (Z_to_bv 64 (shad (rp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 22%Z (Z_to_bv 64 (shad (ap + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (mw_loop4 (length a) a _ _ [] 0 0 n);
                           [ exact P | reflexivity | rewrite !Z.add_0_r; exact I | reflexivity | lia ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
      + (* [comment removed for export] *)
        zstep. zstep.
        eapply evt_eq; [ | eapply (mw_tail_setup a _ _ [] 0 ap rp n);
                           [ exact P | | exact I | reflexivity ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
  Qed.

End Proofs.
