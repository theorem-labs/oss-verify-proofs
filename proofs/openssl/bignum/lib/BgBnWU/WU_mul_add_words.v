(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_add_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_add_words_uentry := 0x1029c4%Z.

Definition maw_upost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (r a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 112%Z
          (fst (mul_add_words r a w)) (snd (mul_add_words r a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a r : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 112, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis LR : limbs r.
  Hypothesis LEN : length r = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis RR : limbs_at bgusegs m rp r.
  Hypothesis WR : wr_at bgusegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 112)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 112 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 112 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  (* [comment removed for export] *)
  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.

  Notation POST := (maw_upost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) r a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.
  Lemma ALR : alias_ok rp rp n. Proof. left. reflexivity. Qed.
  Lemma FBE : (bv_unsigned sp + -112 = bv_unsigned sp - 112)%Z. Proof. lia. Qed.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 a3 x14 (Z_to_bv 64 4294967295) (Z_to_bv 64 (bv_unsigned a3 mod 4294967296))
             (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation FCR := (maw_fc_range (bv_unsigned a3) RW).
  Notation KINV jb := (INV bgusegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a
                        112%Z (bv_unsigned sp + -112)%Z (FCELLS jb)
                        (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).
  Notation KIT jb L := (L bgusegs (maw_fl (bv_unsigned a3)) (maw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned sp) lo a r
                        112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) eq_refl FBE
                        LEN ALA ALR SEPR SEPA SEPR (fst (mul_add_words r a (bv_unsigned a3))) (snd (mul_add_words r a (bv_unsigned a3)))).

  Ltac ldA jb I := let L := constr:(KIT jb INV_rdA) in ldA_with L I.
  Ltac ldB jb I := let L := constr:(KIT jb INV_rdB) in ldB_with L I.
  Ltac w64eq := unfold maw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb jb I l cn Ecn := let L1 := constr:(KIT jb INV_store_ok) in let L2 := constr:(KIT jb INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  (* [comment removed for export] *)
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

  Lemma PTOP : ub_top n ap ap.
  Proof.
    intros Hn.
    assert (NEa : lbytes a <> []) by (destruct a; [cbn [length] in Hn; lia | cbn; discriminate]).
    pose proof (bytes_at_below bgusegs m ap (lbytes a) MI0 RA NEa) as TA.
    rewrite lbytes_lengthZ in TA. unfold UTOP in TA. split; assumption.
  Qed.

  Lemma PFACTS : forall jb m1 pre la lb c pa pb pr, ub_top n ap ap -> KINV jb m1 pre la lb c pa pb pr -> la <> [] ->
    ((0 < pa /\ pa + 8 * Z.of_nat (length la) <= 140737488355328) /\
     (0 < pr /\ pr + 8 * Z.of_nat (length la) <= 140737488355328))%Z.
  Proof.
    intros jb m1 pre la lb c pa pb pr PT I NE.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & Epb & _).
    assert (Hn : (0 < n)%Z) by (destruct la; [congruence | cbn [length] in En; lia]).
    destruct (PT Hn) as (TA & _).
    destruct (UBR Hn) as (NZR & _). destruct (UBA Hn) as (NZA & _).
    clear - TA TOP Epa Epr En NZR NZA. lia.
  Qed.

  Lemma ALIGN : (0 < n)%Z -> (rp mod 8 = 0 /\ ap mod 8 = 0)%Z.
  Proof. intros Hn. destruct (UBR Hn) as (_ & H1). destruct (UBA Hn) as (_ & H2). auto. Qed.

  (* [comment removed for export] *)
  Lemma mawu_epilogue : forall jb m1 pre c pa pb pr x1 x5 x6 x7 x8 x9 x10 x11 x12 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KINV jb m1 pre [] [] c pa pb pr ->
    evt bgusegs POST (ST 0x102cf0 m1 x1 SPF x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I.
    pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
    do 16 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    unfold maw_upost. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma mawu_tail : forall la jb m1 pre lb c pa pr q x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    ub_top n ap ap -> la <> [] -> KINV jb m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    evt bgusegs POST (ST 0x102c60 m1 x1 SPF (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-9)) x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q)
                       (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction la as [|x la IH]; intros jb m1 pre lb c pa pr q x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PT NE I Hq; [congruence|].
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    destruct lb as [|y lb]; [discriminate El|].
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry.
    pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (PP : ((0 < pa /\ pa + 8 <= 140737488355328) /\ (0 < pr /\ pr + 8 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ PT I NE) as P. clear - P. cbn [length] in P. lia. }
    destruct PP as (PA & PR).
    assert (R31 : (1 <= q < 2147483648)%Z) by (clear - Hq En N31; cbn [length] in *; lia).
    assert (Hq' : (q + -1 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    assert (El' : length lb = length la) by (clear - El; cbn [length] in El; lia).
    clear En Epr TOP R0 Hq NE El.
    chk ltac:(fun C => chkP C PA). chk_lit. chk ltac:(fun C => chkP C PR). chk_lit.
    ldA jb I. ldB jb I. do 3 zstep.
    st_limb jb I l c' Ec'.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    zstep. rewrite (bn_swrap32_small (q + -1)) by (clear - R31; lia).
    zstep. rewrite lts_small by (clear - R31; lia).
    rewrite (proj2 (Z.ltb_lt (q + -1) q)) by (clear; lia). cbv iota beta delta [negb].
    do 20 zstep.
    carry 14%Z x y c Rx Ry Hc c' Ec' Hc'.
    zstep. rewrite (bn_swrap32_small (q + -1)) by (clear - R31; lia).
    zstep. if_cases K; zify_cond K.
    - eapply IH; [ exact PT | | exact I | exact Hq' ].
      destruct la; [ exfalso; clear - Hq' K; cbn [length] in *; lia | discriminate ].
    - destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K. cbn [length] in *. lia. }
      destruct lb as [|y' lb']. 2:{ exfalso. clear - El'. cbn [length] in *. lia. }
      eapply mawu_epilogue. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mawu_tail_setup : forall la jb m1 pre lb c pa pr q (wa' wr : word) x1 x5 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    ub_top n ap ap -> la <> [] -> KINV jb m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) ->
    Z.land (bv_unsigned wa') 7 = 0%Z -> Z.land (bv_unsigned wr) 7 = 0%Z ->
    evt bgusegs POST (ST 0x102c54 m1 x1 SPF x5 wa' wr x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 q)
                       (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros PT NE I Hq La Lr.
    zstep. rewrite La. zstep. rewrite Lr. zstep.
    eapply mawu_tail; [exact PT | exact NE | exact I | exact Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma mawu_loop4 : forall (K : nat) la jb m1 pre lb c pa pr q o x1 x8 x19 x20 x21 x24 x25 x26 x27 x29 x30,
    ub_top n ap ap -> length la = K -> KINV jb m1 pre la lb c pa pr pr -> q = Z.of_nat (length la) -> (4 <= q)%Z -> (o mod 8 = 0)%Z ->
    evt bgusegs POST (ST 0x102a5c m1 x1 SPF (Z_to_bv 64 o) (Z_to_bv 64 4) (Z_to_bv 64 0) x8 (Z_to_bv 64 (-25)) a0 a1 (Z_to_bv 64 q)
                       (Z_to_bv 64 c) (Z_to_bv 64 (-33)) x19 x20 x21 (Z_to_bv 64 pa) (Z_to_bv 64 pr) x24 x25 x26 x27
                       (Z_to_bv 64 0) x29 x30 (Z_to_bv 64 (-17))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m1 pre lb c pa pr q o x1 x8 x19 x20 x21 x24 x25 x26 x27 x29 x30 PT HK I Hq R4 Ho.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (H4 : (4 <= length la)%nat) by (clear - Hq R4; lia).
    destruct la as [|x0 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x1' la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x2 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x3 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct lb as [|y0 lb]; [discriminate El|]. destruct lb as [|y1 lb]; [discriminate El|].
    destruct lb as [|y2 lb]; [discriminate El|]. destruct lb as [|y3 lb]; [discriminate El|].
    assert (R31 : (q < 2147483648)%Z) by (clear - Hq En N31; lia).
    assert (Hn : (0 < n)%Z) by (clear - En; cbn [length] in En; lia).
    assert (PP : ((0 < pa /\ pa + 32 <= 140737488355328) /\ (0 < pr /\ pr + 32 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ PT I ltac:(discriminate)) as P. clear - P. cbn [length] in P. lia. }
    destruct PP as (PA & PR).
    assert (Hq' : (q + -4 = Z.of_nat (length la))%Z) by (clear - Hq; cbn [length] in Hq; lia).
    assert (HK' : (length la < K)%nat) by (clear - HK; cbn [length] in HK; lia).
    assert (El' : length lb = length la) by (clear - El; cbn [length] in El; lia).
    assert (Ho' : hide ((o + -32) mod 8 = 0)%Z) by (apply hide_intro; clear - Ho; Z.div_mod_to_equations; lia).
    clear En Epr TOP R0 H4 Hq HK El Ho.
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry0.
    (* [comment removed for export] *)
    chk ltac:(fun C => chkP C PA). chk_lit. zstep. chk ltac:(fun C => chkP C PR). chk_lit. zstep.
    (* [comment removed for export] *)
    ldA jb I. ldB jb I. do 3 zstep.
    st_limb jb I l0 c1 Ec1.
    zstep. chk ltac:(fun C => chkP C PA). zstep. chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry1.
    ldA jb I. do 4 zstep. ldB jb I. do 15 zstep.
    carry 14%Z x0 y0 c Rx0 Ry0 Hc c1 Ec1 Hc1.
    do 2 zstep.
    st_limb jb I l1 c2 Ec2.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry2.
    ldA jb I. do 3 zstep. ldB jb I. do 16 zstep.
    carry 25%Z x1' y1 c1 Rx1 Ry1 Hc1 c2 Ec2 Hc2.
    do 2 zstep.
    st_limb jb I l2 c3 Ec3.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3. pose proof (KIT jb INV_rangeB _ _ _ _ _ _ _ _ _ I) as Ry3.
    ldA jb I. do 3 zstep. ldB jb I. do 16 zstep.
    carry 14%Z x2 y2 c2 Rx2 Ry2 Hc2 c3 Ec3 Hc3.
    do 2 zstep.
    st_limb jb I l3 c4 Ec4.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    zstep. rewrite (bn_swrap32_small (q + -4)) by (clear - R4 R31; lia).
    zstep. rewrite lts_small by (clear - R4 R31; lia).
    rewrite (proj2 (Z.ltb_lt (q + -4) q)) by (clear; lia). cbv iota beta delta [negb].
    do 20 zstep.
    carry 14%Z x3 y3 c3 Rx3 Ry3 Hc3 c4 Ec4 Hc4.
    do 2 zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply (IH (length la)); [ exact HK' | exact PT | reflexivity | exact I | exact Hq' | clear - K1; lia | exact (hide_elim _ Ho') ].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct la as [|x' la']. 2:{ exfalso. clear - Hq' K2. cbn [length] in Hq'. lia. }
        destruct lb as [|y' lb']. 2:{ exfalso. clear - El'. cbn [length] in El'. lia. }
        eapply mawu_epilogue. exact I.
      + (* [comment removed for export] *)
        do 6 zstep.
        apply hide_elim in Ho'. destruct (ALIGN Hn) as (AR8 & AA8).
        eapply mawu_tail_setup; [ exact PT | | exact I | exact Hq' | | ].
        * destruct la; [ exfalso; clear - Hq' K2; cbn [length] in Hq'; lia | discriminate ].
        * apply land7_wrap. clear - AA8 Ho'. Z.div_mod_to_equations. lia.
        * apply land7_wrap. clear - AR8 Ho'. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_mul_add_words_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1029c4) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 112, SP)]%Z m) as MUF. pose proof (wmono_refl bgusegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    pose proof PTOP as PT.
    carve_frame 112%nat STK.
    do 15 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]). subst a.
      assert (r = []) by (destruct r; [reflexivity | exfalso; cbn [length] in *; lia]). subst r.
      do 18 zstep.
      release_frame FR STK (bv_unsigned sp).
      unfold maw_upost. finish. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z) by lia.
      do 6 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : KINV jb mm [] a r 0 ap rp rp);
        [ apply (KIT jb INV_init); try assumption; try lia;
          [ unfold mul_add_words; rewrite mul_add_words_gen; reflexivity | unfold mul_add_words; rewrite mul_add_words_gen; reflexivity ] | ]
      end end.
      clear FR MU MUF WM.
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        do 9 zstep.
        destruct (ALIGN Hn) as (AR8 & AA8). rewrite (land7 _ AR8), (land7 _ AA8). clear AR8 AA8.
        eapply evt_eq; [ | eapply (mawu_loop4 (length a) a _ _ [] r 0 ap rp n 0); [ exact PT | reflexivity | exact I | reflexivity | lia | reflexivity ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
      + (* [comment removed for export] *)
        do 4 zstep.
        eapply evt_eq; [ | eapply (mawu_tail_setup a _ _ [] r 0 ap rp n a1 a0); [ exact PT | | exact I | reflexivity | | ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
        * apply land7. exact (proj2 (ALIGN Hn)).
        * apply land7. exact (proj1 (ALIGN Hn)).
  Qed.
End Proofs.
