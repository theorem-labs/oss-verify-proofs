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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import W_mul_add_words.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2249800 => 1
  | 2249804 => 1
  | 2249816 => 1
  | 2249824 => 2
  | 2249832 => 1
  | 2249836 => 2
  | 2249844 => 2
  | 2249848 => 1
  | 2249852 => 2
  | 2249896 => 1
  | 2249900 => 2
  | 2249904 => 1
  | 2249908 => 2
  | 2250048 => 2
  | 2250052 => 2
  | 2250192 => 2
  | 2250196 => 2
  | 2250336 => 2
  | 2250340 => 2
  | 2250348 => 2
  | 2250472 => 1
  | 2250480 => 1
  | 2250500 => 1
  | 2250516 => 2
  | 2250520 => 2
  | 2250524 => 2
  | 2250528 => 2
  | 2250572 => 2
  | 2250576 => 2
  | 2250584 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_mul_add_words_aentry := 0x2253ac%Z.

Definition maw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (r a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 128%Z
          (fst (mul_add_words r a w)) (snd (mul_add_words r a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a r : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 128, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LR : limbs r.
  Hypothesis LEN : length r = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bsegs m ap a.
  Hypothesis RR : limbs_at bsegs m rp r.
  Hypothesis WR : wr_at bsegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bsegs m lo SP.
  Hypothesis LO : (lo <= SP - 128)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 128 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 128 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bsegs m.
  (* [comment removed for export] *)
  Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bsegs m rp (8 * n).
  Hypothesis ACA : acc bsegs m ap (8 * n).
  Hypothesis APT : aptrs3 rp ap rp n lo.

  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.

  Notation POST := (maw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) r a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.
  Lemma ALR : alias_ok rp rp n. Proof. left. reflexivity. Qed.
  Lemma FBE : (bv_unsigned sp + -128 = bv_unsigned sp - 128)%Z. Proof. lia. Qed.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x2 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 4294967295) (Z_to_bv 64 (bv_unsigned a3 mod 4294967296)) (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32))
             x8 x9 x10 x11 x12 a3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Notation FC24 jb := [CB 24 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation FC3 jb := [CB 8 jb; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation FCR := (maw_fc_range (bv_unsigned a3) RW).
  Notation KINV FC := (INV bsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        128%Z (bv_unsigned sp + -128)%Z FC
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation KIT FC L := (L bsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a r
                        128%Z (bv_unsigned sp + -128)%Z FC eq_refl FBE
                        LEN ALA ALR SEPR SEPA SEPR (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation PB := (apure (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (Z.of_nat (length a)) (bv_unsigned sp) 128%Z).
  Notation K_shA FC := (INV_shA bsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        128%Z (bv_unsigned sp + -128)%Z FC
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation K_shR FC := (INV_shR bsegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        128%Z (bv_unsigned sp + -128)%Z FC
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).

  Ltac ldA FC I := let L := constr:(KIT FC INV_rdA) in ldA_with L I.
  Ltac ldB FC I := let L := constr:(KIT FC INV_rdB) in ldB_with L I.
  Ltac w64eq := unfold maw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb FC I l cn Ecn := let L1 := constr:(KIT FC INV_store_ok) in let L2 := constr:(KIT FC INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
  Ltac lshA FC P I k := let L := constr:(K_shA FC P) in ld_sh_with L I ACA k.
  Ltac lshR FC P I k := let L := constr:(K_shR FC P) in ld_sh_with L I ACR k.

  Ltac carry r x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 cn)
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx Ry RWv Hc Ecn; subst cn; unfold maw_fl, maw_fc; rewrite ?BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply FCR; assumption);
    clear Ecn.

  Lemma INV_fr : forall jb m1 pre la lb c pa pb pr, KINV (FC3 jb) m1 pre la lb c pa pb pr -> rw_cells bsegs m1 (SP + -128)%Z (FC3 jb).
  Proof. intros until pr. intros (_ & _ & _ & _ & FR & _). exact FR. Qed.
  (* [comment removed for export] *)
  Lemma INV_fc24 : forall jb m1 pre la lb c pa pb pr, KINV (FC3 jb) m1 pre la lb c pa pb pr ->
    KINV (FC24 (jb ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ [])) m1 pre la lb c pa pb pr.
  Proof.
    intros until pr. intros (HA & HB & HP & HW & FR & REST).
    pose proof (rw_cells_merge bsegs m1 (SP + -128)%Z [] [CB 8 jb; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FR'.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in FR'.
    exact (conj HA (conj HB (conj HP (conj HW (conj FR' REST))))).
  Qed.

  Lemma maw_epi : forall jb m1 c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    limbs_at bsegs m1 rp (fst (mul_add_words r a w)) -> snd (mul_add_words r a w) = c ->
    rw_cells bsegs m1 (SP + -128)%Z (FC24 jb) -> stk bsegs m1 lo (SP + -128)%Z ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    evt bsegs POST (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 c) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x2257c0) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until x31. intros HP CY FR ST MI MU WM.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    rewrite <- CY.
    unfold maw_apost. finish.
  Qed.

  Lemma NZ2 : (0 < n)%Z -> (0 < rp /\ 0 < ap)%Z.
  Proof. intros Hn. destruct (UBR Hn) as (H1 & _). destruct (UBA Hn) as (H2 & _). auto. Qed.
  (* [comment removed for export] *)
  Lemma PFACTS3 : forall jb m1 pre la lb c pa pr, PB -> KINV (FC3 jb) m1 pre la lb c pa pr pr -> la <> [] ->
    ((0 < pa /\ pa + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pr /\ pr + 8 * Z.of_nat (length la) <= 140737488355328))%Z.
  Proof.
    intros jb m1 pre la lb c pa pr P I NE.
    pose proof (KIT (FC3 jb) INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT (FC3 jb) INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (Hn : (0 < n)%Z) by (destruct la; [congruence | cbn [length] in En; lia]).
    destruct (NZ2 Hn) as (NZR & NZA).
    clear - BR BA Epa Epr En NZR NZA. lia.
  Qed.
  Lemma PFACTS24 : forall jb m1 pre la lb c pa pr, PB -> KINV (FC24 jb) m1 pre la lb c pa pr pr -> la <> [] ->
    ((0 < pa /\ pa + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pr /\ pr + 8 * Z.of_nat (length la) <= 140737488355328))%Z.
  Proof.
    intros jb m1 pre la lb c pa pr P I NE.
    pose proof (KIT (FC24 jb) INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT (FC24 jb) INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (Hn : (0 < n)%Z) by (destruct la; [congruence | cbn [length] in En; lia]).
    destruct (NZ2 Hn) as (NZR & NZA).
    clear - BR BA Epa Epr En NZR NZA. lia.
  Qed.

  Lemma ALIGN : (rp mod 8 = 0 /\ ap mod 8 = 0)%Z.
  Proof. unfold aptrs3 in APT. tauto. Qed.

  Lemma maw_tail : forall la jb m1 pre lb c pa pr q x1 x8 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27,
    PB -> la <> [] -> KINV (FC24 jb) m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bsegs POST (ST 0x225714 m1 x1 SPF x8 (Z_to_bv 64 pa) x10 x11 (Z_to_bv 64 q) x14 (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 0)
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (shad pa)) (Z_to_bv 64 (shad pr)) (Z_to_bv 64 (-9)) (Z_to_bv 64 pr)).
  Proof.
    induction la as [|x la IH]; intros jb m1 pre lb c pa pr q x1 x8 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 P NE I Hq; [congruence|].
    pose proof (KIT (FC24 jb) INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (KIT (FC24 jb) INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT (FC24 jb) INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry.
    pose proof (KIT (FC24 jb) INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (PP : ((0 < pa /\ pa + 8 <= 140737488355328) /\ (0 < pr /\ pr + 8 <= 140737488355328))%Z).
    { pose proof (PFACTS24 _ _ _ _ _ _ _ _ P I NE) as Q. clear - Q. cbn [length] in Q. lia. }
    destruct PP as (PA & PR).
    assert (R1 : (1 <= q < 2147483648)%Z) by (clear - Hq En N31; cbn [length] in *; lia).
    assert (Hq' : (q + -1 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    assert (El' : length lb = length la) by (clear - El; cbn [length] in El; lia).
    clear En Epr TOP R0 Hq NE El.
    ub. lshA (FC24 jb) P I 0%nat. chk0. lshR (FC24 jb) P I 0%nat. chk0.
    ldA (FC24 jb) I. ldB (FC24 jb) I. do 3 zstep.
    st_limb (FC24 jb) I l c' Ec'.
    ub. zstep. rewrite (bn_swrap32_small (q + -1)) by (clear - R1; lia).
    ub. do 22 zstep.
    carry 16%Z x y c Rx Ry Hc c' Ec' Hc'.
    setreg 29%Z (Z_to_bv 64 (shad (pr + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep. setreg 28%Z (Z_to_bv 64 (shad (pa + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep.
    zstep. if_cases K; zify_cond K.
    -
      eapply IH; [ exact P | | exact I | exact Hq' ].
      destruct la; [ exfalso; clear - Hq' K; cbn [length] in *; lia | discriminate ].
    -
      destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K R1. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. clear - El'. cbn [length] in El'. lia. }
      pose proof (KIT (FC24 jb) INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
      eapply maw_epi; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma maw_tail_setup : forall la jb m1 pre lb c pa pr q x1 x8 x9 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    PB -> la <> [] -> KINV (FC24 jb) m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bsegs POST (ST 0x2256e4 m1 x1 SPF x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 c) x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 SHB) x29 x30 x31).
  Proof.
    intros until x31. intros P NE I Hq.
    pose proof (KIT (FC24 jb) INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT (FC24 jb) INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (BND : (0 <= pa < 140737488355328 /\ 0 <= pr < 140737488355328)%Z)
      by (clear - Epa Epr En BR BA NE; destruct la; [congruence | cbn [length] in *; lia]).
    assert (AL3 : (pr mod 8 = 0 /\ pa mod 8 = 0)%Z).
    { destruct ALIGN as (A1 & A2'). clear - Epa Epr A1 A2'. subst pa pr. split; Z.div_mod_to_equations; lia. }
    clear El En Epr TOP R0 Epa Epb TOPA BR BA BB.
    zstep. ub. zstep. ub. do 4 zstep. ub. do 3 zstep.
    destruct AL3 as (AR8 & AA8). rewrite (land7 _ AR8), (land7 _ AA8). clear AR8 AA8.
    setreg 29%Z (Z_to_bv 64 (shad pr)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 28%Z (Z_to_bv 64 (shad pa)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    eapply maw_tail; [exact P | exact NE | exact I | exact Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma maw_loop4 : forall (K : nat) la jb m1 pre lb c off q x1 x10 x14 x15 x17 x18 x19 x25 x26 x27 x30 x31,
    PB -> length la = K -> KINV (FC3 jb) m1 pre la lb c (ap + off) (rp + off) (rp + off) -> q = Z.of_nat (length la) -> (4 <= q)%Z ->
    evt bsegs POST (ST 0x22545c m1 x1 SPF sp a0 x10 a1 (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 c) x17
                       x18 x19 (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (shad (rp + off))) (Z_to_bv 64 (shad (ap + off))) (Z_to_bv 64 (-33))
                       x25 x26 x27 (Z_to_bv 64 SHB) (Z_to_bv 64 off) x30 x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m1 pre lb c off q x1 x10 x14 x15 x17 x18 x19 x25 x26 x27 x30 x31 P HK I Hq R4.
    pose proof (KIT (FC3 jb) INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT (FC3 jb) INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (KIT (FC3 jb) INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    destruct la as [|x0 [|x1' [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (q < 2^31)%Z) by (clear - Hq En N31; lia).
    assert (PP : ((0 < ap + off /\ ap + off + 32 <= 140737488355328) /\ (0 < rp + off /\ rp + off + 32 <= 140737488355328))%Z).
    { pose proof (PFACTS3 _ _ _ _ _ _ _ _ P I ltac:(discriminate)) as Q. clear - Q. cbn [length] in Q. lia. }
    assert (OFF0 : (0 <= off)%Z) by (clear - Epa; lia).
    destruct PP as (PA & PR).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. pose proof (zr_word sp) as ZSP. unfold inr64 in Z0, Z1, ZSP.
    assert (Hq' : (q + -4 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    assert (HK' : (length la < K)%nat) by (clear - HK; cbn [length] in HK; lia).
    assert (El' : length lb = length la) by (clear - El; cbn [length] in El; lia).
    clear En Epr TOP R0 Epa Epb TOPA Hq HK El.
    pose proof (KIT (FC3 jb) INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (KIT (FC3 jb) INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.
    pose proof (INV_fr _ _ _ _ _ _ _ _ _ I) as FRI.
    (* [comment removed for export] *)
    zstep. ub. zstep. ub. zstep. ub.
    lshA (FC3 jb) P I 0%nat. chk0. lshR (FC3 jb) P I 0%nat. chk0.
    clear FRI.
    ldA (FC3 jb) I. ldB (FC3 jb) I. do 3 zstep.
    st_limb (FC3 jb) I l0 c1 Ec1.
    (* [comment removed for export] *)
    pose proof (KIT (FC3 jb) INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (KIT (FC3 jb) INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    ub. do 3 zstep. lshA (FC3 jb) P I 0%nat. chk0. do 3 zstep. lshR (FC3 jb) P I 0%nat. chk0.
    ldA (FC3 jb) I. do 4 zstep. ldB (FC3 jb) I. do 15 zstep.
    carry 27%Z x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    do 2 zstep.
    st_limb (FC3 jb) I l1 c2 Ec2.
    (* [comment removed for export] *)
    pose proof (KIT (FC3 jb) INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (KIT (FC3 jb) INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    ub. do 3 zstep. lshA (FC3 jb) P I 0%nat. chk0. ub. do 3 zstep. lshR (FC3 jb) P I 0%nat. chk0.
    ldA (FC3 jb) I. do 3 zstep. ldB (FC3 jb) I. do 16 zstep.
    carry 25%Z x1' y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    do 2 zstep.
    st_limb (FC3 jb) I l2 c3 Ec3.
    (* [comment removed for export] *)
    pose proof (KIT (FC3 jb) INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (KIT (FC3 jb) INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    ub. do 3 zstep. lshA (FC3 jb) P I 0%nat. chk0. ub. do 3 zstep. lshR (FC3 jb) P I 0%nat. chk0.
    ldA (FC3 jb) I. do 3 zstep. ldB (FC3 jb) I. do 16 zstep.
    carry 11%Z x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    do 2 zstep.
    st_limb (FC3 jb) I l3 c4 Ec4.

    ub. zstep. rewrite (bn_swrap32_small (q + -4)) by (clear - R4 R31; lia).
    ub. do 20 zstep.
    carry 16%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    zstep.
    replace (ap + off + 32)%Z with (ap + (off + 32))%Z in I by (clear; lia).
    replace (rp + off + 32)%Z with (rp + (off + 32))%Z in I by (clear; lia).
    setreg 22%Z (Z_to_bv 64 (shad (rp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 23%Z (Z_to_bv 64 (shad (ap + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    do 3 zstep.
    zstep. if_cases K1; zify_cond K1.
    -
      eapply (IH (length la)); [ exact HK' | exact P | reflexivity | exact I | exact Hq' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      +
        destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K2. cbn [length] in Hq'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El'. cbn [length] in El'. lia. }
        pose proof (KIT (FC24 (jb ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ [])) INV_done _ _ _ _ _ _ (INV_fc24 _ _ _ _ _ _ _ _ _ I)) as (HP & CY & FR & ST & MI & MU & WM).
        eapply maw_epi; try eassumption.
      +
        do 3 zstep.
        eapply maw_tail_setup; [ exact P | | exact (INV_fc24 _ _ _ _ _ _ _ _ _ I) | exact Hq' ].
        destruct la; [ exfalso; clear - Hq' K2; cbn [length] in Hq'; lia | discriminate ].
  Qed.

  (* [comment removed for export] *)
  Lemma bn_mul_add_words_aspec :
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2253ac) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 128, SP)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    assert (PBn : hide ((0 < n)%Z -> PB)).
    { apply hide_intro. intros Hn. eapply (apure_intro bsegs m _ _ _ a r); try eassumption; lia. }
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 128%nat STK.
    do 15 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      assert (Er : r = []) by (destruct r; [reflexivity | exfalso; rewrite Ea in LEN; cbn [length] in *; lia]).
      zstep. zstep.
      eapply maw_epi; try eassumption.
      + rewrite Ea, Er. cbn. apply limbs_at_nil. lia.
      + rewrite Ea, Er. reflexivity.
    - (* [comment removed for export] *)
      assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 9 zstep.
      zstep. if_cases K4; zify_cond K4.
      +
        destruct ALIGN as (AR8 & AA8).
        apply (rw_cells_split_CB bsegs _ _ [] 24 _ _ [8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
        zstep. zstep. zstep. zstep. zstep. zstep. rewrite (land7 _ AA8), (land7 _ AR8) in *.
        zstep. zstep. zstep. ub. zstep. zstep. ub.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
          assert (I : KINV (FC3 jb) mm [] a r 0 ap rp rp);
          [ apply (KIT (FC3 jb) INV_init); try assumption; try lia;
            [ unfold mul_add_words; rewrite mul_add_words_gen; reflexivity | unfold mul_add_words; rewrite mul_add_words_gen; reflexivity ] | ]
        end end.
        clear RA RR WR FR STK MI0 MU MUF WM G1 G2.
        setreg 22%Z (Z_to_bv 64 (shad (rp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 23%Z (Z_to_bv 64 (shad (ap + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (maw_loop4 (length a) a _ _ [] r 0 0 n);
                           [ exact P | reflexivity | rewrite !Z.add_0_r; exact I | reflexivity | lia ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
      +
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jb :: _) =>
          assert (I : KINV (FC24 jb) mm [] a r 0 ap rp rp);
          [ apply (KIT (FC24 jb) INV_init); try assumption; try lia;
            [ unfold mul_add_words; rewrite mul_add_words_gen; reflexivity | unfold mul_add_words; rewrite mul_add_words_gen; reflexivity ] | ]
        end end.
        clear RA RR WR FR STK MI0 MU MUF WM G1 G2.
        eapply evt_eq; [ | eapply (maw_tail_setup a _ _ [] r 0 ap rp n);
                           [ exact P | | exact I | reflexivity ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
  Qed.

End Proofs.
