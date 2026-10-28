(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop W_sub_words.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2254528 => 1
  | 2254532 => 1
  | 2254536 => 1
  | 2254552 => 1
  | 2254556 => 1
  | 2254560 => 1
  | 2254564 => 1
  | 2254580 => 1
  | 2254588 => 2
  | 2254592 => 2
  | 2254600 => 2
  | 2254604 => 2
  | 2254612 => 2
  | 2254616 => 2
  | 2254668 => 2
  | 2254692 => 2
  | 2254696 => 2
  | 2254776 => 2
  | 2254800 => 2
  | 2254804 => 2
  | 2254884 => 2
  | 2254908 => 2
  | 2254912 => 2
  | 2254992 => 2
  | 2254996 => 2
  | 2255000 => 2
  | 2255008 => 2
  | 2255072 => 1
  | 2255076 => 1
  | 2255080 => 1
  | 2255108 => 1
  | 2255116 => 2
  | 2255120 => 2
  | 2255128 => 2
  | 2255132 => 2
  | 2255140 => 2
  | 2255144 => 2
  | 2255196 => 2
  | 2255200 => 2
  | 2255204 => 2
  | 2255212 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_sub_words_aentry := 0x226654%Z.

Definition sw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a b : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 112%Z
          (fst (sub_words a b)) (snd (sub_words a b)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 112, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis LEN : length b = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A3 : bv_unsigned a3 = n.
  Hypothesis RA : limbs_at bsegs m ap a.
  Hypothesis RB : limbs_at bsegs m bp b.
  Hypothesis WR : wr_at bsegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis ALB : alias_ok rp bp n.
  Hypothesis STK : stk bsegs m lo SP.
  Hypothesis LO : (lo <= SP - 112)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 112 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 112 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 112 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bsegs m.
  (* [comment removed for export] *)
  Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bsegs m rp (8 * n).
  Hypothesis ACA : acc bsegs m ap (8 * n).
  Hypothesis ACB : acc bsegs m bp (8 * n).
  Hypothesis APT : aptrs3 rp ap bp n lo.

  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.
  Hypothesis UBB : ub_ptr_ok n bp.

  Notation POST := (sw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a b lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma FBE : (bv_unsigned sp + -112 = bv_unsigned sp - 112)%Z. Proof. lia. Qed.
  Notation KINV jb := (INV bsegs sub_fl sub_fc 1 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (sub_words a b)) (snd (sub_words a b))).
  Notation KIT jb L := (L bsegs sub_fl sub_fc 1%Z sub_fc_range m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) eq_refl FBE
                        LEN ALA ALB SEPR SEPA SEPB (fst (sub_words a b)) (snd (sub_words a b))).

  Ltac ldA jb I := let L := constr:(KIT jb INV_rdA) in ldA_with L I.
  Ltac ldB jb I := let L := constr:(KIT jb INV_rdB) in ldB_with L I.
  Ltac w64eq := unfold sub_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb jb I l cn Ecn := let L1 := constr:(KIT jb INV_store_ok) in let L2 := constr:(KIT jb INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  Ltac cy_arith Rx Ry Hc Ecn cn := clear - Rx Ry Hc Ecn; subst cn; unfold sub_fc; case_ltb; Z.div_mod_to_equations; lia.
  Ltac carry r x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e => let E := fresh "E" in assert (E : e = cn) by (cy_arith Rx Ry Hc Ecn cn); rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply sub_fc_range; assumption);
    clear Ecn.
  (* [comment removed for export] *)
  Ltac norm_bw r xn x y c Rx Ry Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 (xn - cn))
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; cy_arith Rx Ry Hc Ecn cn);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Ry Hc Ecn; subst cn; apply sub_fc_range; assumption);
    clear Ecn.

  Notation PB := (apure (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (Z.of_nat (length a)) (bv_unsigned sp) 112%Z).
  Notation K_shA jb := (INV_shA bsegs sub_fl sub_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (sub_words a b)) (snd (sub_words a b))).
  Notation K_shB jb := (INV_shB bsegs sub_fl sub_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (sub_words a b)) (snd (sub_words a b))).
  Notation K_shR jb := (INV_shR bsegs sub_fl sub_fc 1%Z m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (sub_words a b)) (snd (sub_words a b))).
  Ltac lshA jb P I k := let L := constr:(K_shA jb P) in ld_sh_with L I ACA k.
  Ltac lshB jb P I k := let L := constr:(K_shB jb P) in ld_sh_with L I ACB k.
  Ltac lshR jb P I k := let L := constr:(K_shR jb P) in ld_sh_with L I ACR k.

  (* [comment removed for export] *)
  Lemma sw_epi : forall jb m1 c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    limbs_at bsegs m1 rp (fst (sub_words a b)) -> snd (sub_words a b) = c ->
    rw_cells bsegs m1 (SP + -112)%Z (FCELLS jb) -> stk bsegs m1 lo (SP + -112)%Z ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    evt bsegs POST (ST 0x226994 m1 x1 SPF x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 c) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HP CY FR ST MI MU WM.
    do 14 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep. zstep.
    rewrite <- CY.
    unfold sw_apost. finish.
  Qed.

  Lemma NZ3 : (0 < n)%Z -> (0 < rp /\ 0 < ap /\ 0 < bp)%Z.
  Proof. intros Hn. destruct (UBR Hn) as (H1 & _). destruct (UBA Hn) as (H2 & _). destruct (UBB Hn) as (H3 & _). auto. Qed.

  (* [comment removed for export] *)
  Lemma PFACTS : forall jb m1 pre la lb c pa pb pr, PB -> KINV jb m1 pre la lb c pa pb pr -> la <> [] ->
    ((0 < pa /\ pa + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pb /\ pb + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pr /\ pr + 8 * Z.of_nat (length la) <= 140737488355328))%Z.
  Proof.
    intros jb m1 pre la lb c pa pb pr P I NE.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (Hn : (0 < n)%Z) by (destruct la; [congruence | cbn [length] in En; lia]).
    destruct (NZ3 Hn) as (NZR & NZA & NZB).
    clear - BR BA BB Epa Epb Epr En NZR NZA NZB. lia.
  Qed.

  Lemma sw_tail : forall la jb m1 pre lb c pa pb pr off r x1 x8 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27,
    PB -> la <> [] -> KINV jb m1 pre la lb c (pa + off) (pb + off) (pr + off) -> r = Z.of_nat (length la) ->
    (0 <= off)%Z -> (0 <= pa /\ 0 <= pb /\ 0 <= pr)%Z ->
    evt bsegs POST (ST 0x226908 m1 x1 SPF (Z_to_bv 64 (shad (pr + off))) (Z_to_bv 64 off) (Z_to_bv 64 0) x8 (Z_to_bv 64 (-9))
                       (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 r) (Z_to_bv 64 c) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (shad (pb + off))) (Z_to_bv 64 (shad (pa + off)))).
  Proof.
    induction la as [|x la IH]; intros jb m1 pre lb c pa pb pr off r x1 x8 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 P NE I Hr OFF0 PTR0; [congruence|].
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]. { exfalso. cbn [length] in El. lia. }
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry.
    pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (PP : ((0 < pa + off /\ pa + off + 8 <= 140737488355328) /\ (0 < pb + off /\ pb + off + 8 <= 140737488355328)
                  /\ (0 < pr + off /\ pr + off + 8 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ P I NE) as Q. clear - Q. cbn [length] in Q. lia. }
    destruct PP as (PA & PB' & PR).
    assert (R31 : (1 <= r < 2147483648)%Z) by (clear - Hr En N31; cbn [length] in *; lia).
    assert (Hr' : (r + -1 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    clear En Epr TOP R0 Hr NE.
    zstep. ub; zstep. ub; zstep.
    ub; lshA jb P I 0%nat. chk0. lshB jb P I 0%nat. chk0. lshR jb P I 0%nat. chk0.
    ldA jb I. ldB jb I. zstep.
    rewrite (bn_swrap32_small (c + 0)) by (clear - Hc; lia). rewrite Z.add_0_r.
    zstep. zstep.
    st_limb jb I l c' Ec'.
    ub; zstep. rewrite (bn_swrap32_small (r + -1)) by (clear - R31; lia).
    ub; zstep. zstep. do 3 zstep. zstep.
    carry 14%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep. zstep.
    replace (pa + off + 8)%Z with (pa + (off + 8))%Z in I by (clear; lia).
    replace (pb + off + 8)%Z with (pb + (off + 8))%Z in I by (clear; lia).
    replace (pr + off + 8)%Z with (pr + (off + 8))%Z in I by (clear; lia).
    setreg 5%Z (Z_to_bv 64 (shad (pr + (off + 8)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 30%Z (Z_to_bv 64 (shad (pb + (off + 8)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 31%Z (Z_to_bv 64 (shad (pa + (off + 8)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      eapply IH; [ exact P | | exact I | exact Hr' | clear - OFF0; lia | exact PTR0 ].
      destruct la; [ exfalso; clear - Hr' K; cbn [length] in *; lia | discriminate ].
    - (* [comment removed for export] *)
      destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K R31. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. clear - El. cbn [length] in El. lia. }
      pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
      eapply sw_epi; try eassumption.
  Qed.

  Lemma ALIGN : (rp mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)%Z.
  Proof. unfold aptrs3 in APT. tauto. Qed.

  (* [comment removed for export] *)
  Lemma sw_tail_setup : forall la jb m1 pre lb c pa pb pr r x1 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    PB -> la <> [] -> KINV jb m1 pre la lb c pa pb pr -> r = Z.of_nat (length la) ->
    evt bsegs POST (ST 0x2268dc m1 x1 SPF (Z_to_bv 64 SHB) x6 x7 x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 pb) (Z_to_bv 64 r) (Z_to_bv 64 c) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros P NE I Hr.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & BB).
    assert (BND : (0 <= pa < 140737488355328 /\ 0 <= pb < 140737488355328 /\ 0 <= pr < 140737488355328)%Z)
      by (clear - Epa Epb Epr En BR BA BB NE; destruct la; [congruence | cbn [length] in *; lia]).
    assert (AL3 : (pr mod 8 = 0 /\ pa mod 8 = 0 /\ pb mod 8 = 0)%Z).
    { destruct ALIGN as (A1 & A2 & A3'). clear - Epa Epb Epr A1 A2 A3'. subst pa pb pr. repeat split; Z.div_mod_to_equations; lia. }
    clear El En Epr TOP R0 Epa Epb TOPA BR BA BB.
    zstep. ub; zstep.
    destruct AL3 as (AR8 & AA8 & AB8). rewrite (land7 _ AR8), (land7 _ AA8), (land7 _ AB8). clear AR8 AA8 AB8.
    do 5 zstep. ub.
    setreg 5%Z (Z_to_bv 64 (shad (pr + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
    setreg 30%Z (Z_to_bv 64 (shad (pb + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
    setreg 31%Z (Z_to_bv 64 (shad (pa + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
    eapply (sw_tail la jb m1 pre lb c pa pb pr 0 r); [exact P | exact NE | rewrite !Z.add_0_r; exact I | exact Hr | clear; lia | clear - BND; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sw_loop4 : forall (K : nat) la jb m1 pre lb c off r x1 x8 x15 x16 x17 x24 x25 x26 x27,
    PB -> length la = K -> KINV jb m1 pre la lb c (ap + off) (bp + off) (rp + off) -> r = Z.of_nat (length la) -> (4 <= r)%Z ->
    evt bsegs POST (ST 0x2266f8 m1 x1 SPF (Z_to_bv 64 SHB) (Z_to_bv 64 off) (Z_to_bv 64 4) x8 (Z_to_bv 64 (-9)) a0 a1 a2 (Z_to_bv 64 r) (Z_to_bv 64 c) x15 x16 x17
                       (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (shad (bp + off))) (Z_to_bv 64 (shad (ap + off))) (Z_to_bv 64 (shad (rp + off)))
                       (Z_to_bv 64 (-33)) x24 x25 x26 x27 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-8))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m1 pre lb c off r x1 x8 x15 x16 x17 x24 x25 x26 x27 P HK I Hr R4.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & TOPA).
    destruct la as [|x0 [|x1' [|x2 [|x3 la]]]]; try (exfalso; cbn [length] in *; lia).
    destruct lb as [|y0 [|y1 [|y2 [|y3 lb]]]]; try (exfalso; cbn [length] in *; lia).
    assert (R31 : (r < 2^31)%Z) by (clear - Hr En N31; lia).
    assert (PP : ((0 < ap + off /\ ap + off + 32 <= 140737488355328) /\ (0 < bp + off /\ bp + off + 32 <= 140737488355328)
                  /\ (0 < rp + off /\ rp + off + 32 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ P I ltac:(discriminate)) as Q. clear - Q. cbn [length] in Q. lia. }
    assert (OFF0 : (0 <= off)%Z) by (clear - Epa; lia).
    destruct PP as (PA & PB' & PR).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. pose proof (zr_word a2) as Z2. unfold inr64 in Z0, Z1, Z2.
    assert (Hr' : (r + -4 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    assert (HK' : (length la < K)%nat) by (clear - HK; cbn [length] in HK; lia).
    assert (El' : length lb = length la) by (clear - El; cbn [length] in El; lia).
    clear En Epr TOP R0 Epa Epb TOPA Hr HK El.
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.
    (* [comment removed for export] *)
    zstep. ub; zstep. ub; zstep.
    ub; lshA jb P I 0%nat. chk0. lshB jb P I 0%nat. chk0. lshR jb P I 0%nat. chk0.
    ldA jb I. ldB jb I. zstep.
    rewrite (bn_swrap32_small (c + 0)) by (clear - Hc; lia). rewrite Z.add_0_r.
    zstep. zstep.
    st_limb jb I l0 c1 Ec1.

    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    ub; do 3 zstep. lshA jb P I 0%nat. chk0. ub; do 3 zstep. lshB jb P I 0%nat. chk0. ub; do 3 zstep. lshR jb P I 0%nat. chk0.
    zstep. zstep. ldA jb I. ldB jb I. zstep. zstep. zstep.
    norm_bw 26%Z x1' x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    zstep.
    st_limb jb I l1 c2 Ec2.

    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    ub; do 3 zstep. lshA jb P I 0%nat. chk0. ub; do 3 zstep. lshB jb P I 0%nat. chk0. ub; do 3 zstep. lshR jb P I 0%nat. chk0.
    zstep. ldA jb I. zstep. ldB jb I. zstep. zstep. zstep.
    norm_bw 26%Z x2 x1' y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    zstep.
    st_limb jb I l2 c3 Ec3.

    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    ub; do 3 zstep. lshA jb P I 0%nat. chk0. ub; do 3 zstep. lshB jb P I 0%nat. chk0. ub; do 3 zstep. lshR jb P I 0%nat. chk0.
    zstep. ldA jb I. zstep. ldB jb I. zstep. zstep. zstep.
    norm_bw 25%Z x3 x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    zstep.
    st_limb jb I l3 c4 Ec4.

    ub; zstep. rewrite (bn_swrap32_small (r + -4)) by (clear - R4 R31; lia).
    ub; zstep. do 5 zstep.
    carry 14%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    do 2 zstep.
    replace (ap + off + 32)%Z with (ap + (off + 32))%Z in I by (clear; lia).
    replace (bp + off + 32)%Z with (bp + (off + 32))%Z in I by (clear; lia).
    replace (rp + off + 32)%Z with (rp + (off + 32))%Z in I by (clear; lia).
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      setreg 20%Z (Z_to_bv 64 (shad (bp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 21%Z (Z_to_bv 64 (shad (ap + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 22%Z (Z_to_bv 64 (shad (rp + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply (IH (length la)); [ exact HK' | exact P | reflexivity | exact I | exact Hr' | clear - K1; lia ].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K2. cbn [length] in Hr'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El'. cbn [length] in El'. lia. }
        pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
        eapply sw_epi; try eassumption.
      + (* [comment removed for export] *)
        do 4 zstep.
        eapply sw_tail_setup; [ exact P | | exact I | exact Hr' ].
        destruct la; [ exfalso; clear - Hr' K2; cbn [length] in Hr'; lia | discriminate ].
  Qed.

  (* [comment removed for export] *)
  Lemma bn_sub_words_aspec :
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x226654) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 112, SP)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    assert (PBn : hide ((0 < n)%Z -> PB)).
    { apply hide_intro. intros Hn. eapply (apure_intro bsegs m); try eassumption; lia. }
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 112%nat STK.
    do 15 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      zstep. zstep.
      eapply sw_epi; try eassumption.
      + rewrite Ea. cbn. apply limbs_at_nil. lia.
      + rewrite Ea. reflexivity.
    - (* [comment removed for export] *)
      assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 4 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : KINV jb mm [] a b 0 ap bp rp);
        [ apply (KIT jb INV_init); try assumption; try lia;
          [ unfold sub_words; rewrite sub_words_gen; reflexivity | unfold sub_words; rewrite sub_words_gen; reflexivity ] | ]
      end end.
      clear RA RB WR FR STK MI0 MU MUF WM G1 G2.
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        zstep. zstep. ub; zstep. zstep. zstep. ub; zstep. zstep. zstep. ub.
        destruct ALIGN as (AR8 & AA8 & AB8). rewrite (land7 _ AR8), (land7 _ AA8), (land7 _ AB8). clear AR8 AA8 AB8.
        setreg 20%Z (Z_to_bv 64 (shad (bp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 21%Z (Z_to_bv 64 (shad (ap + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        setreg 22%Z (Z_to_bv 64 (shad (rp + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (sw_loop4 (length a) a _ _ [] b 0 0 n);
                           [ exact P | reflexivity | rewrite !Z.add_0_r; exact I | reflexivity | lia ] ].
        rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
      + (* [comment removed for export] *)
        zstep. zstep.
        eapply evt_eq; [ | eapply (sw_tail_setup a _ _ [] b 0 ap bp rp n);
                           [ exact P | | exact I | reflexivity ] ].
        * rewrite <- A3, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
  Qed.
End Proofs.
