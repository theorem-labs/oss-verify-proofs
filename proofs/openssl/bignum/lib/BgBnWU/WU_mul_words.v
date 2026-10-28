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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_words_uentry := 0x102d34%Z.

Definition mw_upost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a : list Z) (w : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp (Z.of_nat (length a)) 96%Z
          (fst (mul_words a w)) (snd (mul_words a w)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation w := (bv_unsigned a3).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length a)); (bv_unsigned sp - 96, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis WR : wr_at bgusegs m rp (8 * n).
  Hypothesis ALA : alias_ok rp ap n.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 96)%Z.
  Hypothesis SEPR : (rp + 8 * n <= SP - 96 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 96 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  (* [comment removed for export] *)
  Hypothesis UBR : ub_ptr_ok n rp.
  Hypothesis UBA : ub_ptr_ok n ap.

  Notation POST := (mw_upost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a (bv_unsigned a3) lo m).

  Lemma RW : (0 <= w < 18446744073709551616)%Z.
  Proof. pose proof (zr_word a3) as H. unfold inr64 in H. change (2 ^ 64)%Z with 18446744073709551616%Z in H. exact H. Qed.

  (* [comment removed for export] *)
  Notation ST pc mm x2 x5 x6 x7 x8 x9 x10 x11 x12 x14 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 a3 x14 (Z_to_bv 64 4294967295) (Z_to_bv 64 (bv_unsigned a3 mod 4294967296))
             (Z_to_bv 64 (Z.shiftr (bv_unsigned a3) 32)) x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Notation FCELLS jb := [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma LEN : length a = length a. Proof. reflexivity. Qed.
  Notation FCR := (mw_fc_range (bv_unsigned a3) RW).
  Lemma FBE : (bv_unsigned sp + -96 = bv_unsigned sp - 96)%Z. Proof. lia. Qed.
  Notation KINV jb := (INV bgusegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615 m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a 96%Z (bv_unsigned sp + -96)%Z (FCELLS jb)
                        (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).
  Notation KIT jb L := (L bgusegs (mw_fl (bv_unsigned a3)) (mw_fc (bv_unsigned a3)) 18446744073709551615%Z FCR m (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a 96%Z (bv_unsigned sp + -96)%Z (FCELLS jb) eq_refl FBE
                        LEN ALA ALA SEPR SEPA SEPA (fst (mul_words a (bv_unsigned a3))) (snd (mul_words a (bv_unsigned a3)))).

  Ltac ldA jb I := let L := constr:(KIT jb INV_rdA) in ldA_with L I.
  Ltac w64eq := unfold mw_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac st_limb jb I l cn Ecn := let L1 := constr:(KIT jb INV_store_ok) in let L2 := constr:(KIT jb INV_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  (* [comment removed for export] *)
  Ltac carry r x c Rx Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 cn)
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx RWv Hc Ecn; subst cn; unfold mw_fc; rewrite BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Hc Ecn; subst cn; apply FCR; assumption);
    clear Ecn.
  (* [comment removed for export] *)
  Ltac norm_st r xn x c Rx Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : Z_to_bv 64 e = Z_to_bv 64 (xn * bv_unsigned a3 + cn))
          by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z;
              pose proof RW as RWv; clear - Rx RWv Hc Ecn; subst cn; unfold mw_fc; rewrite BW_lit;
              let wv := fresh "wv" in set (wv := bv_unsigned a3) in *; clearbody wv;
              let pn := fresh "pn" in set (pn := (xn * wv)%Z) in *; clearbody pn;
              mul64_solve x wv Rx RWv);
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 18446744073709551615)%Z) by (clear - Rx Hc Ecn; subst cn; apply FCR; assumption);
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
  Lemma mwu_epilogue : forall jb m1 pre c pa pb pr x5 x6 x7 x8 x9 x10 x11 x12 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    KINV jb m1 pre [] [] c pa pb pr ->
    evt bgusegs POST (ST 0x103008 m1 SPF x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I.
    pose proof (KIT jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU & WM).
    do 14 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- CY.
    unfold mw_upost. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma mwu_tail : forall la jb m1 pre c pa pr r x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    ub_top n ap ap -> la <> [] -> KINV jb m1 pre la la c pa pa pr -> r = Z.of_nat (length la) ->
    evt bgusegs POST (ST 0x102f88 m1 SPF (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-9)) x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    induction la as [|x la IH]; intros jb m1 pre c pa pr r x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 PT NE I Hr; [congruence|].
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (PP : ((0 < pa /\ pa + 8 <= 140737488355328) /\ (0 < pr /\ pr + 8 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ PT I NE) as P. clear - P. cbn [length] in P. lia. }
    destruct PP as (PA & PR).
    assert (R31 : (1 <= r < 2147483648)%Z) by (clear - Hr En N31; cbn [length] in *; lia).
    assert (Hr' : (r + -1 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    clear En Epr TOP R0 Hr NE El.
    chk ltac:(fun C => chkP C PA). chk_lit. chk ltac:(fun C => chkP C PR). chk_lit.
    ldA jb I. zstep. zstep.
    st_limb jb I l c' Ec'.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    zstep. rewrite (bn_swrap32_small (r + -1)) by (clear - R31; lia).
    zstep. rewrite lts_small by (clear - R31; lia).
    rewrite (proj2 (Z.ltb_lt (r + -1) r)) by (clear; lia). cbv iota beta delta [negb].
    do 18 zstep.
    carry 14%Z x c Rx Hc c' Ec' Hc'.
    zstep. rewrite (bn_swrap32_small (r + -1)) by (clear - R31; lia).
    zstep. if_cases K; zify_cond K.
    - eapply IH; [ exact PT | | exact I | exact Hr' ].
      destruct la; [ exfalso; clear - Hr' K; cbn [length] in *; lia | discriminate ].
    - destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K. cbn [length] in *. lia. }
      eapply mwu_epilogue. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mwu_tail_setup : forall la jb m1 pre c pa pr r (wa' wr : word) x5 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    ub_top n ap ap -> la <> [] -> KINV jb m1 pre la la c pa pa pr -> r = Z.of_nat (length la) ->
    Z.land (bv_unsigned wa') 7 = 0%Z -> Z.land (bv_unsigned wr) 7 = 0%Z ->
    evt bgusegs POST (ST 0x102f7c m1 SPF x5 wa' wr x8 x9 (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 r)
                       (Z_to_bv 64 c) x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros until x31. intros PT NE I Hr La Lr.
    zstep. rewrite La. zstep. rewrite Lr. zstep.
    eapply mwu_tail; [exact PT | exact NE | exact I | exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma mwu_loop4 : forall (K : nat) la jb m1 pre c pa pr r o x8 x19 x20 x21 x24 x25,
    ub_top n ap ap -> length la = K -> KINV jb m1 pre la la c pa pa pr -> r = Z.of_nat (length la) -> (4 <= r)%Z -> (o mod 8 = 0)%Z ->
    evt bgusegs POST (ST 0x102dcc m1 SPF (Z_to_bv 64 o) (Z_to_bv 64 4) (Z_to_bv 64 0) x8 (Z_to_bv 64 (-25)) a0 a1 (Z_to_bv 64 r)
                       (Z_to_bv 64 c) (Z_to_bv 64 (-33)) x19 x20 x21 (Z_to_bv 64 pa) (Z_to_bv 64 pr) x24 x25
                       (Z_to_bv 64 0) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m1 pre c pa pr r o x8 x19 x20 x21 x24 x25 PT HK I Hr R4 Ho.
    pose proof (KIT jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0). pose proof (KIT jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (H4 : (4 <= length la)%nat) by (clear - Hr R4; lia).
    destruct la as [|x0 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x1 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x2 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    destruct la as [|x3 la]; [exfalso; clear - H4; cbn [length] in H4; lia|].
    assert (R31 : (r < 2147483648)%Z) by (clear - Hr En N31; lia).
    assert (Hn : (0 < n)%Z) by (clear - En; cbn [length] in En; lia).
    assert (PP : ((0 < pa /\ pa + 32 <= 140737488355328) /\ (0 < pr /\ pr + 32 <= 140737488355328))%Z).
    { pose proof (PFACTS _ _ _ _ _ _ _ _ _ PT I ltac:(discriminate)) as P. clear - P. cbn [length] in P. lia. }
    destruct PP as (PA & PR).
    assert (Hr' : (r + -4 = Z.of_nat (length la))%Z) by (clear - Hr; cbn [length] in Hr; lia).
    assert (HK' : (length la < K)%nat) by (clear - HK; cbn [length] in HK; lia).
    assert (Ho' : hide ((o + -32) mod 8 = 0)%Z) by (apply hide_intro; clear - Ho; Z.div_mod_to_equations; lia).
    clear En Epr TOP R0 H4 Hr HK El Ho.
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx0.
    (* [comment removed for export] *)
    chk ltac:(fun C => chkP C PA). chk_lit. zstep. chk ltac:(fun C => chkP C PR). chk_lit. zstep.
    (* [comment removed for export] *)
    ldA jb I. zstep. zstep.
    st_limb jb I l0 c1 Ec1.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx1.
    do 3 zstep. ldA jb I. do 15 zstep.
    norm_st 21%Z x1 x0 c Rx0 Hc c1 Ec1 Hc1.
    st_limb jb I l1 c2 Ec2.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx2.
    do 8 zstep. ldA jb I. do 10 zstep.
    norm_st 21%Z x2 x1 c1 Rx1 Hc1 c2 Ec2 Hc2.
    st_limb jb I l2 c3 Ec3.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    pose proof (KIT jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Rx3.
    do 8 zstep. ldA jb I. do 10 zstep.
    norm_st 22%Z x3 x2 c2 Rx2 Hc2 c3 Ec3 Hc3.
    st_limb jb I l3 c4 Ec4.
    chk ltac:(fun C => chkP C PA). chk ltac:(fun C => chkP C PR).
    (* [comment removed for export] *)
    zstep. rewrite (bn_swrap32_small (r + -4)) by (clear - R4 R31; lia).
    zstep. rewrite lts_small by (clear - R4 R31; lia).
    rewrite (proj2 (Z.ltb_lt (r + -4) r)) by (clear; lia). cbv iota beta delta [negb].
    do 18 zstep.
    carry 14%Z x3 c3 Rx3 Hc3 c4 Ec4 Hc4.
    do 2 zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply (IH (length la)); [ exact HK' | exact PT | reflexivity | exact I | exact Hr' | clear - K1; lia | exact (hide_elim _ Ho') ].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct la as [|x' la']. 2:{ exfalso. clear - Hr' K2. cbn [length] in Hr'. lia. }
        eapply mwu_epilogue. exact I.
      + (* [comment removed for export] *)
        do 6 zstep.
        apply hide_elim in Ho'. destruct (ALIGN Hn) as (AR8 & AA8).
        eapply mwu_tail_setup; [ exact PT | | exact I | exact Hr' | | ].
        * destruct la; [ exfalso; clear - Hr' K2; cbn [length] in Hr'; lia | discriminate ].
        * apply land7_wrap. clear - AA8 Ho'. Z.div_mod_to_equations. lia.
        * apply land7_wrap. clear - AR8 Ho'. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_mul_words_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x102d34) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (munch_refl [(SP - 96, SP)]%Z m) as MUF. pose proof (wmono_refl bgusegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word sp) as RSP. unfold inr64 in R0, RSP.
    pose proof PTOP as PT.
    carve_frame 96%nat STK.
    do 13 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]). subst a.
      do 16 zstep.
      release_frame FR STK (bv_unsigned sp).
      unfold mw_upost. finish. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z) by lia.
      do 6 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : KINV jb mm [] a a 0 ap ap rp);
        [ apply (KIT jb INV_init); try assumption; try lia;
          [ unfold mul_words; rewrite mul_words_gen; reflexivity | unfold mul_words; rewrite mul_words_gen; reflexivity ] | ]
      end end.
      clear FR MU MUF WM.
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        do 11 zstep.
        destruct (ALIGN Hn) as (AR8 & AA8). rewrite (land7 _ AR8), (land7 _ AA8). clear AR8 AA8.
        eapply evt_eq; [ | eapply (mwu_loop4 (length a) a _ _ [] 0 ap rp n 0); [ exact PT | reflexivity | exact I | reflexivity | lia | reflexivity ] ].
        rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
      + (* [comment removed for export] *)
        do 4 zstep.
        eapply evt_eq; [ | eapply (mwu_tail_setup a _ _ [] 0 ap rp n a1 a0); [ exact PT | | exact I | reflexivity | | ] ].
        * rewrite <- A2, !Z_to_bv_bv_unsigned. reflexivity.
        * destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
        * apply land7. exact (proj2 (ALIGN Hn)).
        * apply land7. exact (proj1 (ALIGN Hn)).
  Qed.
End Proofs.
