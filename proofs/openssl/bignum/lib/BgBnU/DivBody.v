(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_add_words WU_sub_words WU_mul_words WU_div_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import DivQhatPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require Import DivBody.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import DivQhat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition udb_bnd (wp TD VD rp TA VA lo SP dn : Z) : Prop :=
  (0 <= wp /\ 0 <= TD /\ 0 <= VD /\ 0 <= rp /\ 0 <= TA /\ 0 <= VA /\
   wp + 8 * (dn + 1) <= lo /\ TD + 8 * (dn + 1) <= lo /\ VD + 8 * dn <= lo /\ rp + 8 <= lo /\ TA + 24 <= lo /\ VA + 24 <= lo /\
   lo <= SP - 352 /\ SP < 18446744073709551616)%Z.

(* [comment removed for export] *)
Definition ualign (wp TD VD rp TA : Z) : Prop :=
  (0 < wp /\ 0 < TD /\ 0 < VD /\ 0 < rp /\ 0 < TA /\ wp mod 8 = 0 /\ TD mod 8 = 0 /\ VD mod 8 = 0 /\ rp mod 8 = 0 /\ TA mod 8 = 0)%Z.

Lemma ulimbs_tr : forall W m m' A ls n, limbs_at bgusegs m A ls -> munch W m m' -> Z.of_nat (length ls) = n ->
  disjoint_from W A (8 * n) -> limbs_at bgusegs m' A ls.
Proof. intros W m m' A ls n H MU <- D. eapply limbs_at_transport; eauto. Qed.

Section Body.
  Variables (sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (d0 d1 dn : Z) (V : list Z).
  Variables (wp TD VD rp TA VA lo : Z).
  Variable c0 : list byte.   (* [comment removed for export] *)
  Variables (c1 c2 c3 c8 c14 c15 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : word).
  Variables (ta1 ta2 ta3 ta4 va1 va2 va3 va4 : word).
  Variable m0 : word -> option byte.
  Notation SP := (bv_unsigned sp).
  Hypothesis Hd0 : (9223372036854775808 <= d0 < 18446744073709551616)%Z.
  Hypothesis Hd1 : (0 <= d1 < 18446744073709551616)%Z.
  Hypothesis Hdn : (1 <= dn < 2147483647)%Z.
  Hypothesis HV : limbs V.
  Hypothesis HVl : Z.of_nat (length V) = dn.
  Hypothesis DJB : udb_bnd wp TD VD rp TA VA lo SP dn.
  Hypothesis DJP : db_pair wp TD VD rp TA VA dn.
  Hypothesis UAL : ualign wp TD VD rp TA.

  (* [comment removed for export] *)
  Notation FRAME wt :=
    [CB 8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32));
     C8 (Z_to_bv 64 0); C8 c8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (8 * dn)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (dn + 1)); C8 c14; C8 c15;
     C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 wt); C8 (Z_to_bv 64 dn); C8 c19; C8 c20; C8 c21; C8 c22; C8 c23; C8 c24; C8 c25; C8 c26; C8 c27; C8 c28; C8 c29; C8 c30; C8 c31].
  Notation WF := [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 352, bv_unsigned sp)]%Z.

  (* [comment removed for export] *)
  Definition UBST (wt : Z) (mm : word -> option byte) (WIN TL RL : list Z) : Prop :=
    limbs_at bgusegs mm wp WIN /\ limbs_at bgusegs mm TD TL /\ limbs_at bgusegs mm rp RL /\ limbs_at bgusegs mm VD V /\
    wr_at bgusegs mm wp (8 * (dn + 1)) /\ wr_at bgusegs mm TD (8 * (dn + 1)) /\ wr_at bgusegs mm rp 8 /\
    rw_cells bgusegs mm TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4] /\
    rw_cells bgusegs mm VA [C8 (Z_to_bv 64 VD); C4 va1; C4 va2; C4 va3; C4 va4] /\
    rw_cells bgusegs mm (bv_unsigned sp + -256) (FRAME wt) /\
    stk bgusegs mm lo (bv_unsigned sp + -256) /\ mem_inv bgusegs mm /\
    munch WF m0 mm /\ wmono bgusegs m0 mm.

  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = (bv_unsigned sp + -256)%Z.
  Proof using DJB Hdn.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    unfold udb_bnd in DJB. clear - DJB Hdn. lia.
  Qed.
  Lemma ulit : forall z, (0 <= z)%Z -> (z <= lo)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof using DJB Hdn.
    intros z H1 H2. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    unfold udb_bnd in DJB. clear - DJB Hdn H1 H2. lia.
  Qed.
  Ltac bnd := unfold udb_bnd in DJB; clear - DJB Hdn; lia.

  (* [comment removed for export] *)
  Lemma UBST_store : forall wt mm WIN TL RL a w WIN' TL' RL',
    UBST wt mm WIN TL RL ->
    ((wp <= a /\ a + 8 <= wp + 8 * (dn + 1)) \/ (TD <= a /\ a + 8 <= TD + 8 * (dn + 1)) \/ a = rp)%Z ->
    (let mm' := write_to_mem mm (Z_to_bv 64 a) (le8 w) in
     limbs_at bgusegs mm' wp WIN' /\ limbs_at bgusegs mm' TD TL' /\ limbs_at bgusegs mm' rp RL' /\ limbs_at bgusegs mm' VD V) ->
    store_ok bgusegs mm (Z_to_bv 64 a) 8 = true /\
    UBST wt (write_to_mem mm (Z_to_bv 64 a) (le8 w)) WIN' TL' RL'.
  Proof using DJB DJP Hdn.
    intros wt mm WIN TL RL a w WIN' TL' RL' B HA HL.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    cbv zeta in HL. destruct HL as (L1 & L2 & L3 & L4).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    unfold udb_bnd in DJB.
    assert (L8 : length (le8 w) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgusegs mm (Z_to_bv 64 a) 8 = true).
    { change (Z_to_bv 64 a) with (wa a). destruct HA as [HA|[HA|HA]].
      - replace a with (wp + (a - wp))%Z by (clear; lia). apply (wr_at_store_ok bgusegs mm wp (8 * (dn + 1))); [exact WW | clear - HA; lia | clear - HA; lia].
      - replace a with (TD + (a - TD))%Z by (clear; lia). apply (wr_at_store_ok bgusegs mm TD (8 * (dn + 1))); [exact WT | clear - HA; lia | clear - HA; lia].
      - subst a. replace rp with (rp + 0)%Z by (clear; lia). apply (wr_at_store_ok bgusegs mm rp 8); [exact WRs | clear; lia | clear; lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 a) with (wa a) in *.
    assert (A0 : (0 <= a /\ a + 8 <= lo)%Z) by (clear - HA DJB Hdn; lia).
    unfold UBST.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
    split. { apply wr_at_write. exact WW. }
    split. { apply wr_at_write. exact WT. }
    split. { apply wr_at_write. exact WRs. }
    split. { apply rw_cells_frame; [exact CTA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - HA P4 P8 P11; lia]. }
    split. { apply rw_cells_frame; [exact CVA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - HA P5 P9 P12; lia]. }
    split. { apply rw_cells_frame; [exact FR | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - A0 DJB; lia]. }
    split. { apply stk_write; [exact ST | clear - A0; lia | rewrite L8; clear - A0 DJB; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn [inside]; clear - HA; lia]. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma UBST_stack : forall wt mm m2 WIN TL RL a b,
    UBST wt mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    (bv_unsigned sp - 352 <= a)%Z -> (b <= bv_unsigned sp + -256)%Z ->
    munch [(a, b)] mm m2 -> wmono bgusegs mm m2 -> mem_inv bgusegs m2 -> stk bgusegs m2 lo (bv_unsigned sp + -256) ->
    UBST wt m2 WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt mm m2 WIN TL RL a b B HWl HTl HRl Ha Hb MUc WMc MIc STc.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold udb_bnd in DJB. unfold UBST.
    split. { eapply ulimbs_tr; [exact HWIN | exact MUc | exact HWl | ]. cbn. clear - DJB Hdn Ha Hb. lia. }
    split. { eapply ulimbs_tr; [exact HTL | exact MUc | reflexivity | ]. cbn. clear - DJB Hdn Ha Hb HTl. lia. }
    split. { eapply ulimbs_tr; [exact HRL | exact MUc | reflexivity | ]. cbn. clear - DJB Hdn Ha Hb HRl. lia. }
    split. { eapply ulimbs_tr; [exact HVD | exact MUc | exact HVl | ]. cbn. clear - DJB Hdn Ha Hb. lia. }
    split. { eapply wr_at_transport; eauto. }
    split. { eapply wr_at_transport; eauto. }
    split. { eapply wr_at_transport; eauto. }
    split. { eapply rw_cells_transport; [exact CTA | exact MUc | exact WMc | cbn; clear - DJB Hdn Ha Hb; lia]. }
    split. { eapply rw_cells_transport; [exact CVA | exact MUc | exact WMc | cbn; clear - DJB Hdn Ha Hb; lia]. }
    split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn; clear - DJB Hdn Ha Hb; lia]. }
    split; [exact STc|]. split; [exact MIc|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
             unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. clear - DJB Hdn Ha Hb Hx. lia. }
    eapply wmono_trans; eauto.
  Qed.


  (* [comment removed for export] *)
  Notation ULST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 d1) x19 (Z_to_bv 64 TA) x21 x22 x23
             (Z_to_bv 64 (8 * dn)) x25 (Z_to_bv 64 d0) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Lemma UBST_wt : forall wt wt' mm WIN TL RL,
    UBST wt mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    store_ok bgusegs mm (Z_to_bv 64 (bv_unsigned sp + -120)) 8 = true /\
    UBST wt' (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + -120)) (le8 (Z_to_bv 64 wt'))) WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt wt' mm WIN TL RL B HWl HTl HRl.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold udb_bnd in DJB.
    assert (L8 : length (le8 (Z_to_bv 64 wt')) = 8%nat) by apply length_le8.
    replace (bv_unsigned sp + -120)%Z with (bv_unsigned sp + -256 + Z.of_nat 136)%Z by (clear; lia).
    change (Z_to_bv 64 (bv_unsigned sp + -256 + Z.of_nat 136)) with (wa (bv_unsigned sp + -256 + Z.of_nat 136)).
    assert (SOK : store_ok bgusegs mm (wa (bv_unsigned sp + -256 + Z.of_nat 136)) 8 = true)
      by (apply (rw_cells_store_ok bgusegs mm _ _ 136%nat (C8 (Z_to_bv 64 wt)) 8%nat FR); reflexivity).
    split; [exact SOK|].
    assert (A0 : (0 <= bv_unsigned sp + -256 + Z.of_nat 136 /\ bv_unsigned sp + -256 + Z.of_nat 136 + 8 <= bv_unsigned sp)%Z) by (clear - DJB Hdn; lia).
    unfold UBST.
    split. { apply limbs_at_write_other; [exact HWIN | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8, HWl; clear - DJB Hdn; lia]. }
    split. { apply limbs_at_write_other; [exact HTL | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; clear - DJB Hdn HTl; lia]. }
    split. { apply limbs_at_write_other; [exact HRL | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; clear - DJB Hdn HRl; lia]. }
    split. { apply limbs_at_write_other; [exact HVD | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8, HVl; clear - DJB Hdn; lia]. }
    split. { apply wr_at_write. exact WW. }
    split. { apply wr_at_write. exact WT. }
    split. { apply wr_at_write. exact WRs. }
    split. { apply rw_cells_frame; [exact CTA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - DJB Hdn; lia]. }
    split. { apply rw_cells_frame; [exact CVA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - DJB Hdn; lia]. }
    split. { exact (rw_cells_write bgusegs mm _ _ 136%nat (C8 (Z_to_bv 64 wt)) (C8 (Z_to_bv 64 wt')) FR eq_refl eq_refl I). }
    split. { apply stk_write; [exact ST | clear - A0; lia | rewrite L8; clear - A0 DJB Hdn; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn [inside]; clear - A0 DJB Hdn; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Ltac ubnd := unfold udb_bnd in DJB; clear - DJB Hdn; lia.
  Ltac ual := unfold ualign in UAL; unfold udb_bnd in DJB; clear - UAL DJB Hdn; lia.

  (* [comment removed for export] *)
  Lemma udb_qhat : forall mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x27 x28 x29 x30 x31,
    UBST (wp + 8 * dn) mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) <= dn + 1 -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN ->
    nth_error WIN (Z.to_nat dn) = Some n0 -> nth_error WIN (Z.to_nat (dn - 1)) = Some n1 ->
    (dn = 1%Z /\ n2 = 0%Z \/ (2 <= dn)%Z /\ nth_error WIN (Z.to_nat (dn - 2)) = Some n2) ->
    (n0 <= d0)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31,
       UBST (wp + 8 * dn + -8) mm' WIN TL RL ->
       evt bgusegs POST (ULST 0x109d18 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1)) x21
                            (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 (wp + 8)) x27 x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109c18 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21
                         (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 (wp + 8)) x27 x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x27 x28 x29 x30 x31 B HWl HTl HRl LW N0 N1 N2 Hn0 K.
    pose proof B as (HWIN & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (apply nth_error_In in N0; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N0)).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (apply nth_error_In in N1; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N1)).
    assert (R2 : (0 <= n2 < 18446744073709551616)%Z).
    { destruct N2 as [[_ ->]|[_ N2]]; [clear; lia|]. apply nth_error_In in N2. rewrite <- BW_lit. exact (proj1 (Forall_forall _ _) LW _ N2). }
    assert (BWP : (0 < wp /\ wp + 8 * dn + 8 < 18446744073709551616)%Z) by ual.
    chk ltac:(fun C => clear - C BWP Hdn; lia).
    step. clear FR.
    chk_lit.
    zstep.
    chk ltac:(fun C => clear - C BWP Hdn; lia).
    (* [comment removed for export] *)
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs mm wp WIN (Z.to_nat dn) n0 ad HWIN N0 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.
    zstep.
    (* [comment removed for export] *)
    destruct (UBST_wt (wp + 8 * dn) (wp + 8 * dn + -8) mm WIN TL RL B HWl HTl HRl) as [SOK B1].
    zstep. clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m1 eqn:Em1 end. clear Em1 B HWIN. try clear mm.
    pose proof B1 as (HWIN & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _).
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
      do 2 zstep.
      setreg 19%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_eq n0 d0) ltac:(clear - KE; lia)); clear; weqm).
      apply K. exact B1. }
    (* [comment removed for export] *)
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m1 wp WIN (Z.to_nat (dn - 1)) n1 ad HWIN N1 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.
    assert (CONT : forall y11 y22, y22 = Z_to_bv 64 n2 ->
              evt bgusegs POST (ULST 0x109c68 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 n0) y11 x12 x13 x14 x15 x16 x17 x19 x21
                                   y22 (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 (wp + 8)) (Z_to_bv 64 n1) x28 x29 x30 x31)).
    { intros y11 y22 ->.
      do 3 zstep.
      (* [comment removed for export] *)
      assert (E0 : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply unsigned_lit; clear - R0; lia).
      assert (E1 : bv_unsigned (Z_to_bv 64 n1) = n1) by (apply unsigned_lit; clear - R1; lia).
      assert (ED : bv_unsigned (Z_to_bv 64 d0) = d0) by (apply unsigned_lit; clear - Hd0; lia).
      pose proof ESP as ESPv.
      eapply evt_cut.
      { eapply bn_div_words_uspec with (lo := lo) (m := m1).
        - rewrite ED. clear - Hd0. lia.
        - rewrite E0, ED. clear - Hn0 KE. lia.
        - rewrite ESPv. exact ST.
        - rewrite ESPv. ubnd.
        - exact MI. }
      intros ms' PO. unfold dvw_upost in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
      subst ms'. rewrite E0, E1, ED, ESPv in *.
      replace (ret_pc (Z_to_bv 64 1088628)) with (Z_to_bv 64 1088628) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      assert (B2 : UBST (wp + 8 * dn + -8) m2 WIN TL RL).
      { eapply (UBST_stack _ m1 m2 WIN TL RL); [exact B1 | exact HWl | exact HTl | exact HRl | | | exact MUc | exact WMc | exact MIc | exact STc].
        - clear. lia.
        - clear. lia. }
      pose proof B2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
      assert (Hq : (0 <= div_words n0 n1 d0 < 18446744073709551616)%Z) by (apply div_words_lit; [exact Hd0 | clear - R0 Hn0 KE; lia | exact R1]).
      eapply qh_block; [exact Hd0 | exact Hd1 | exact FR2 | exact Hq | exact R1 | exact R2 | ].
      intros y10 z11 y12 y13 y14 y15 y19.
      step.
      setreg 19%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_neq n0 d0) KE); reflexivity).
      apply K. exact B2. }
    zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      zstep. apply CONT.
      destruct N2 as [[_ ->]|[N2 _]]; [reflexivity | exfalso; clear - KN N2 BWP; rewrite ?unsigned_lit in KN by lia; lia].
    - destruct N2 as [[N2 _]|[N2a N2]]; [exfalso; clear - KN N2 BWP; subst dn; apply KN; reflexivity|].
      zstep. chk ltac:(fun C => clear - C BWP N2a; lia).
      zstep. chk ltac:(fun C => clear - C BWP N2a; lia).
      let ad := cur_mem_addr in
        pose proof (limbs_at_read_nth bgusegs m1 wp WIN (Z.to_nat (dn - 2)) n2 ad HWIN N2 ltac:(unfold wa; f_equal; clear - N2a; lia)) as RD.
      zstep. clear RD.
      zstep. apply CONT. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma udb_mul : forall wt mm WIN TL RL q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x25 x27 x28 x29 x30 x31,
    UBST wt mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z -> (0 <= q < 18446744073709551616)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       UBST wt mm' WIN (fst (mul_words V q) ++ [snd (mul_words V q)]) RL ->
       evt bgusegs POST (ULST 0x109d74 mm' x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 (Z_to_bv 64 q) x21 x22 x23 x25 x27 x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109d18 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 q) x21 x22 x23 x25 x27 x28 x29 x30 x31).
  Proof.
    intros wt mm WIN TL RL q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x25 x27 x28 x29 x30 x31 B HWl HRl Hq K.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    step. chk_lit.
    do 4 step. do 2 zstep.
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; ubnd).
    assert (EVD : bv_unsigned (Z_to_bv 64 VD) = VD) by (apply ulit; ubnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 dn) = dn) by (apply ulit; ubnd).
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; clear - Hq; lia).
    pose proof ESP as ESPv.
    eapply evt_cut.
    { eapply bn_mul_words_uspec with (a := V) (lo := lo) (m := mm).
      - exact HV.
      - rewrite HVl. clear - Hdn. lia.
      - rewrite EDN, HVl. reflexivity.
      - rewrite EVD. exact HVD.
      - rewrite ETD, HVl. apply (wr_at_sub bgusegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - rewrite ETD, EVD, HVl. unfold alias_ok. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. ubnd.
      - rewrite ETD, ESPv, HVl. ubnd.
      - rewrite EVD, ESPv, HVl. ubnd.
      - exact MI.
      - rewrite ETD. unfold ub_ptr_ok. intros _. ual.
      - rewrite EVD. unfold ub_ptr_ok. intros _. ual. }
    intros ms' PO. unfold mw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ETD, EQ, ESPv, HVl in *.
    replace (ret_pc (Z_to_bv 64 1088824)) with (Z_to_bv 64 1088824) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (HWIN2 : limbs_at bgusegs m2 wp WIN).
    { eapply ulimbs_tr; [exact HWIN | exact MUc | exact HWl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bgusegs m2 VD V).
    { eapply ulimbs_tr; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at bgusegs m2 rp RL).
    { eapply ulimbs_tr; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB P7 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P9 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB Hdn; lia).
    transport_after_call bgusegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    do 2 step. zstep.
    assert (RTD : (0 < TD /\ TD + 8 * (dn + 1) < 18446744073709551616 /\ TD mod 8 = 0)%Z) by ual.
    do 2 zstep.
    replace (0 <? TD)%Z with true by (symmetry; apply Z.ltb_lt; clear - RTD; lia).
    replace (TD + 8 * dn <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - RTD Hdn; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    zstep. step. do 2 zstep.
    replace (TD + 8 * dn <? TD)%Z with false by (symmetry; apply Z.ltb_ge; clear - RTD Hdn; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => clear - C RTD; lia).
    zstep.
    rewrite (land7 (TD + 8 * dn)) by (clear - RTD; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    pose proof (mul_words_length V q) as Lml.
    assert (B2 : UBST wt m2 WIN (fst (mul_words V q)) RL).
    { unfold UBST. repeat (split; [assumption|]). assumption. }
    destruct (UBST_store wt m2 WIN (fst (mul_words V q)) RL (TD + 8 * dn) (Z_to_bv 64 (snd (mul_words V q)))
                WIN (fst (mul_words V q) ++ [snd (mul_words V q)]) RL B2) as [SOK B3].
    { right. left. clear - Hdn. lia. }
    { cbv zeta. unfold udb_bnd in DJB.
      assert (L8 : length (le8 (Z_to_bv 64 (snd (mul_words V q)))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 (TD + 8 * dn)) with (wa (TD + 8 * dn)).
      split. { apply limbs_at_write_other; [exact HWIN2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HWl; clear - P1 Hdn; lia]. }
      split. { replace (TD + 8 * dn)%Z with (TD + 8 * Z.of_nat (length (fst (mul_words V q))))%Z by (rewrite Lml, HVl; reflexivity).
               apply limbs_at_snoc_write; [exact HR | rewrite Lml, HVl; clear - DJB Hdn; lia]. }
      split. { apply limbs_at_write_other; [exact HRL2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8; clear - P7 HRl Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P6 Hdn; lia]. }
    clear FR CTA CVA.
    zstep.
    apply K. exact B3.
  Qed.

  (* [comment removed for export] *)
  Lemma udb_sub : forall wt mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x21 x22 x23 x27 x28 x29 x30 x31,
    UBST wt mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> limbs TL ->
    (forall mm' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       UBST wt mm' (fst (sub_words WIN TL)) TL RL ->
       evt bgusegs POST (ULST 0x109d90 mm' x1 x5 x6 x7 x9 (Z_to_bv 64 (snd (sub_words WIN TL))) x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 (Z_to_bv 64 wp) x27 x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109d74 mm x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x19 x21 x22 x23 (Z_to_bv 64 (wp + 8)) x27 x28 x29 x30 x31).
  Proof.
    intros wt mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x21 x22 x23 x27 x28 x29 x30 x31 B HWl HTl HRl LW LT K.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (RWP : (0 < wp /\ wp + 8 * (dn + 1) < 18446744073709551616 /\ wp mod 8 = 0 /\ 0 < TD /\ TD mod 8 = 0)%Z) by ual.
    zstep. chk ltac:(fun C => clear - C RWP; lia).
    zstep. replace (wp + 8 + -8)%Z with wp by (clear; lia).
    do 2 zstep. step. zstep.
    assert (EWP : bv_unsigned (Z_to_bv 64 wp) = wp) by (apply ulit; ubnd).
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; ubnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 (dn + 1)) = (dn + 1)%Z) by (apply ulit; ubnd).
    pose proof ESP as ESPv.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (LEN : length TL = length WIN) by (clear - HWl HTl; lia).
    eapply evt_cut.
    { eapply bn_sub_words_uspec with (a := WIN) (b := TL) (lo := lo) (m := mm).
      - exact LW.
      - exact LT.
      - exact LEN.
      - rewrite HWl. clear - Hdn. lia.
      - rewrite EDN, HWl. reflexivity.
      - rewrite EWP. exact HWIN.
      - rewrite ETD. exact HTL.
      - rewrite EWP, HWl. exact WW.
      - rewrite EWP. unfold alias_ok. left. reflexivity.
      - rewrite EWP, ETD, HWl. unfold alias_ok. clear - P1. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. ubnd.
      - rewrite EWP, ESPv, HWl. ubnd.
      - rewrite EWP, ESPv, HWl. ubnd.
      - rewrite ETD, ESPv, HWl. ubnd.
      - exact MI.
      - rewrite EWP. unfold ub_ptr_ok. intros _. clear - RWP. lia.
      - rewrite EWP. unfold ub_ptr_ok. intros _. clear - RWP. lia.
      - rewrite ETD. unfold ub_ptr_ok. intros _. clear - RWP. lia. }
    intros ms' PO. unfold sw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 1088912)) with (Z_to_bv 64 1088912) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HTL2 : limbs_at bgusegs m2 TD TL).
    { eapply ulimbs_tr; [exact HTL | exact MUc | exact HTl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bgusegs m2 VD V).
    { eapply ulimbs_tr; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at bgusegs m2 rp RL).
    { eapply ulimbs_tr; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB Hdn; lia).
    transport_after_call bgusegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    apply K. unfold UBST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Section Mask.
    Variables (mk : word -> option byte) (msk wt : Z).
    Hypothesis Hmsk : (0 <= msk < 18446744073709551616)%Z.
    Lemma UMLEN : length V = length V. Proof. reflexivity. Qed.
    Lemma UMFBE : (bv_unsigned sp + -256 = bv_unsigned sp - 256)%Z. Proof. lia. Qed.
    Lemma UMALA : alias_ok TD VD (Z.of_nat (length V)).
    Proof using DJP HVl Hdn. unfold alias_ok. rewrite HVl. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia. Qed.
    Lemma UMSEPR : (TD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 256 \/ bv_unsigned sp <= TD)%Z.
    Proof using DJB HVl Hdn. rewrite HVl. left. ubnd. Qed.
    Lemma UMSEPA : (VD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 256 \/ bv_unsigned sp <= VD)%Z.
    Proof using DJB HVl Hdn. rewrite HVl. left. ubnd. Qed.
    Notation MRES := (map (fun x => Z.land x msk) V).
    Notation KINV := (INV bgusegs (mk_fl msk) (mk_fc msk) 0 mk TD VD VD (bv_unsigned sp) lo V 256%Z (bv_unsigned sp + -256)%Z (FRAME wt) MRES 0%Z).
    Notation KIT L := (L bgusegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mk TD VD VD (bv_unsigned sp) lo V V 256%Z (bv_unsigned sp + -256)%Z (FRAME wt) eq_refl UMFBE
                          UMLEN UMALA UMALA UMSEPR UMSEPA UMSEPA MRES 0%Z).
    Notation K_rdA := (KIT INV_rdA).
    Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
    Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
    Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).
    Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
    Ltac w64eq := unfold mk_fl; reflexivity.
    Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
    Hypothesis CTAK : forall m', munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 256, bv_unsigned sp)]%Z mk m' -> wmono bgusegs mk m' ->
      rw_cells bgusegs m' TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4].

    Lemma umask_loop : forall la m1 pre c pa pr x1 x5 x6 x7 x9 x12 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31,
      la <> [] -> KINV m1 pre la la c pa pa pr ->
      (forall m2 x5 x6 x10 x11 x13 x14 x15 x16 x17,
         limbs_at bgusegs m2 TD MRES -> rw_cells bgusegs m2 (bv_unsigned sp + -256) (FRAME wt) -> stk bgusegs m2 lo (bv_unsigned sp + -256) -> mem_inv bgusegs m2 ->
         munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 256, bv_unsigned sp)]%Z mk m2 -> wmono bgusegs mk m2 ->
         evt bgusegs POST (ULST 0x109e24 m2 x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31)) ->
      evt bgusegs POST (ULST 0x109dc0 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (pa - VD)) (Z_to_bv 64 VD) x12 (Z_to_bv 64 msk) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 pa) x17
                           x19 x21 x22 x23 x25 x27 x28 x29 x30 x31).
    Proof.
      induction la as [|x la IH]; intros m1 pre c pa pr x1 x5 x6 x7 x9 x12 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 NE I K; [congruence|].
      pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
      pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TOP64).
      pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx.
      assert (RPA : (0 < VD /\ VD <= pa /\ pa + 8 <= VD + 8 * dn /\ pa - VD = pr - TD /\ 0 < TD /\ TD + 8 * (dn + 1) < 18446744073709551616 /\
                     VD + 8 * dn < 18446744073709551616 /\ TD mod 8 = 0 /\ (pa - VD) mod 8 = 0)%Z).
      { cbn [length] in *. rewrite HVl in *. unfold ualign in UAL. unfold udb_bnd in DJB. clear - UAL DJB Hdn Epa Epr En. 
        assert ((8 * Z.of_nat (length pre)) mod 8 = 0)%Z by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
        replace (pa - VD)%Z with (8 * Z.of_nat (length pre))%Z by lia. lia. }
      pose proof I as (_ & _ & _ & _ & _ & _ & _ & MUI & WMI & _).
      pose proof (CTAK m1 MUI WMI) as CTA. clear MUI WMI.
      chk ltac:(fun C => clear - C RPA; lia).
      zstep. replace (pa <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - RPA; lia). cbn [Z.b2z].
      zstep. cbn [Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => clear - C; lia).
      step. clear CTA.
      zstep. replace (TD + (pa - VD))%Z with pr by (clear - RPA; lia).
      chk ltac:(fun C => clear - C RPA; lia).
      zstep. replace (0 <? TD)%Z with true by (symmetry; apply Z.ltb_lt; clear - RPA; lia).
      zstep. replace (pr <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - RPA; lia).
      cbn [Z.b2z]. zstep. cbn [Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => clear - C RPA; lia).
      do 2 zstep.
      rewrite (land7 (pa - VD + TD)) by (clear - RPA; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      zstep. replace (VD + (pa - VD))%Z with pa by (clear; lia).
      ldA I.
      do 2 zstep.
      st_limb I l c' Ec'. clear Ec'.
      zstep.
      replace (pa - VD + 8)%Z with (pa + 8 - VD)%Z by (clear; lia).
      zstep. if_cases KB; zify_cond KB.
      - (* [comment removed for export] *)
        eapply IH; [ | exact I | exact K ].
        destruct la; [ exfalso | discriminate ].
        pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *.
        clear - KB En2 Epr2 HVl RPA. lia.
      - (* [comment removed for export] *)
        zstep.
        destruct la as [|x' la'].
        + pose proof (K_done _ _ _ _ _ _ I) as (HP & CYE & FR & ST & MI & MU & WM).
          apply K; assumption.
        + exfalso. pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa2 & _).
          cbn [length] in *. clear - KB En2 Epr2 HVl RPA. lia.
    Qed.
  End Mask.

  (* [comment removed for export] *)
  Lemma udb_mask : forall wt mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31,
    UBST wt mm WIN (TLp ++ [tl]) RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    (0 <= bw <= 1)%Z ->
    (forall mm' x5 x6 x10 x11 x13 x14 x15 x16 x17,
       UBST wt mm' WIN (map (fun x => Z.land x (negw bw)) V ++ [tl]) RL ->
       evt bgusegs POST (ULST 0x109e24 mm' x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 (Z_to_bv 64 bw) x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109d90 mm x1 x5 x6 x7 x9 (Z_to_bv 64 bw) x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31).
  Proof.
    intros wt mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 B HWl HTl HRl Hbw K.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (RVD : (0 < VD /\ VD + 8 * dn < 18446744073709551616 /\ VD mod 8 = 0)%Z) by ual.
    zstep. step.
    zstep. if_cases KZ; zify_cond KZ.
    { exfalso. clear - KZ Hdn. destruct (Z.ltb_spec 0 dn); [|lia]. destruct (Z.ltb_spec dn 9223372036854775808); [discriminate | lia]. }
    try clear KZ.
    zstep. do 2 step. zstep.
    setreg 13%Z (Z_to_bv 64 (negw bw)) ltac:(clear; unfold negw; weqm).
    zstep. replace (0 <? VD)%Z with true by (symmetry; apply Z.ltb_lt; clear - RVD; lia). cbn [Z.b2z].
    zstep. rewrite (land7 VD) by (clear - RVD; lia).
    zstep. cbn [Z.ltb Z.compare Z.b2z].
    do 2 zstep.
    assert (Hmsk : (0 <= negw bw < 18446744073709551616)%Z) by apply negw_limb.
    remember (negw bw) as msk eqn:Emsk.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    apply limbs_at_app in HTL. destruct HTL as [HTLp HTLl].
    assert (ETL : (TD + 8 * Z.of_nat (length TLp) = TD + 8 * dn)%Z) by (rewrite HTl; reflexivity). rewrite ETL in HTLl. clear ETL.
    assert (I : INV bgusegs (mk_fl msk) (mk_fc msk) 0 mm TD VD VD (bv_unsigned sp) lo V 256%Z (bv_unsigned sp + -256)%Z (FRAME wt)
                    (map (fun x => Z.land x msk) V) 0%Z mm [] V V 0 VD VD TD).
    { apply (INV_init bgusegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mm TD VD VD (bv_unsigned sp) lo V V 256%Z (bv_unsigned sp + -256)%Z (FRAME wt) eq_refl UMFBE
                          UMLEN UMALA UMALA UMSEPR UMSEPA UMSEPA); try assumption.
      - rewrite HVl. clear - Hdn. lia.
      - clear. lia.
      - rewrite HVl. apply (wr_at_sub bgusegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - apply munch_refl.
      - apply munch_refl.
      - apply wmono_refl.
      - rewrite mask_gen. reflexivity.
      - rewrite mask_gen. reflexivity. }
    assert (CTAK : forall m', munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 256, bv_unsigned sp)]%Z mm m' -> wmono bgusegs mm m' ->
              rw_cells bgusegs m' TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4]).
    { intros m' MU' WM'. eapply rw_cells_transport; [exact CTA | exact MU' | exact WM' |]. cbn. rewrite HVl. unfold udb_bnd in DJB. clear - DJB P8 Hdn. lia. }
    eapply evt_eq; [ | eapply (umask_loop mm msk wt Hmsk CTAK V mm [] 0 VD TD); [ | exact I | ] ].
    { replace (VD - VD)%Z with 0%Z by (clear; lia). reflexivity. }
    { destruct V; [ exfalso; cbn [length] in HVl; clear - HVl Hdn; lia | discriminate ]. }
    intros m2 y5 y6 y10 y11 y13 y14 y15 y16 y17 HP FR2 ST2 MI2 MUk WMk. rewrite HVl in MUk.
    assert (HWIN2 : limbs_at bgusegs m2 wp WIN).
    { eapply ulimbs_tr; [exact HWIN | exact MUk | exact HWl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bgusegs m2 VD V).
    { eapply ulimbs_tr; [exact HVD | exact MUk | exact HVl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at bgusegs m2 rp RL).
    { eapply ulimbs_tr; [exact HRL | exact MUk | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB P7 Hdn HRl. lia. }
    assert (HTLl2 : limbs_at bgusegs m2 (TD + 8 * dn) [tl]).
    { eapply ulimbs_tr; [exact HTLl | exact MUk | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB Hdn. lia. }
    assert (HTL2 : limbs_at bgusegs m2 TD (map (fun x => Z.land x msk) V ++ [tl])).
    { apply limbs_at_app. split; [exact HP|]. rewrite length_map, HVl. exact HTLl2. }
    clear HWIN HVD HRL HTLp HTLl HTLl2 HP ST FR I CTAK.
    tr_cells CTA MUk WMk ltac:(unfold udb_bnd in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUk WMk ltac:(unfold udb_bnd in DJB; clear - DJB P9 Hdn; lia).
    transport_after_call bgusegs mm m2 MUk WMk.
    clear MUk WMk MI. try clear mm.
    apply K. unfold UBST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma udb_add : forall wt0 mm WINp wt TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    UBST wt0 mm (WINp ++ [wt]) (TLp ++ [tl]) RL -> Z.of_nat (length WINp) = dn -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WINp -> limbs TLp -> (0 <= wt < 18446744073709551616)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31,
       UBST wt0 mm' (fst (add_words WINp TLp) ++ [addw wt (snd (add_words WINp TLp))]) (TLp ++ [tl]) [subw q bw] ->
       evt bgusegs POST (ULST 0x109c0c mm' x1 x5 x6 x7 (Z_to_bv 64 rp) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (i + 1))
                            (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 wp) x27 x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109e24 mm x1 x5 x6 x7 (Z_to_bv 64 (rp + 8)) x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 (Z_to_bv 64 q) (Z_to_bv 64 i)
                         (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 wp) (Z_to_bv 64 bw) x28 x29 x30 x31).
  Proof.
    intros wt0 mm WINp wt TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 B HWl HTl HRl LW LT Hwt Hi K.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (RWP : (0 < wp /\ wp + 8 * (dn + 1) < 18446744073709551616 /\ wp mod 8 = 0 /\ 0 < TD /\ TD mod 8 = 0 /\ 0 < rp /\ rp + 8 < 18446744073709551616)%Z) by ual.
    do 2 zstep. step. zstep.
    assert (EWP : bv_unsigned (Z_to_bv 64 wp) = wp) by (apply ulit; ubnd).
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; ubnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 dn) = dn) by (apply ulit; ubnd).
    pose proof ESP as ESPv.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (LEN : length TLp = length WINp) by (clear - HWl HTl; lia).
    apply limbs_at_app in HWIN. destruct HWIN as [HWp HWt]. rewrite HWl in HWt.
    apply limbs_at_app in HTL. destruct HTL as [HTp HTt]. rewrite HTl in HTt.
    eapply evt_cut.
    { eapply bn_add_words_uspec with (a := WINp) (b := TLp) (lo := lo) (m := mm).
      - exact LW.
      - exact LT.
      - exact LEN.
      - rewrite HWl. clear - Hdn. lia.
      - rewrite EDN, HWl. reflexivity.
      - rewrite EWP. exact HWp.
      - rewrite ETD. exact HTp.
      - rewrite EWP, HWl. apply (wr_at_sub bgusegs mm wp (8 * (dn + 1)) 0 (8 * dn)) in WW; [rewrite Z.add_0_r in WW; exact WW | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - rewrite EWP. unfold alias_ok. left. reflexivity.
      - rewrite EWP, ETD, HWl. unfold alias_ok. clear - P1 Hdn. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. ubnd.
      - rewrite EWP, ESPv, HWl. ubnd.
      - rewrite EWP, ESPv, HWl. ubnd.
      - rewrite ETD, ESPv, HWl. ubnd.
      - exact MI.
      - rewrite EWP. unfold ub_ptr_ok. intros _. clear - RWP. lia.
      - rewrite EWP. unfold ub_ptr_ok. intros _. clear - RWP. lia.
      - rewrite ETD. unfold ub_ptr_ok. intros _. clear - RWP. lia. }
    intros ms' PO. unfold aw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 1089076)) with (Z_to_bv 64 1089076) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HWt2 : limbs_at bgusegs m2 (wp + 8 * dn) [wt]).
    { eapply ulimbs_tr; [exact HWt | exact MUc | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB Hdn. lia. }
    assert (HTp2 : limbs_at bgusegs m2 TD TLp).
    { eapply ulimbs_tr; [exact HTp | exact MUc | exact HTl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P1 Hdn. lia. }
    assert (HTt2 : limbs_at bgusegs m2 (TD + 8 * dn) [tl]).
    { eapply ulimbs_tr; [exact HTt | exact MUc | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bgusegs m2 VD V).
    { eapply ulimbs_tr; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold udb_bnd in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at bgusegs m2 rp RL).
    { eapply ulimbs_tr; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold udb_bnd in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWp HWt HTp HTt HVD HRL ST.
    tr_cells CTA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold udb_bnd in DJB; clear - DJB Hdn; lia).
    transport_after_call bgusegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    (* [comment removed for export] *)
    ld_hd HWt2.
    pose proof (add_words_spec WINp TLp LW LT ltac:(clear - LEN; lia)) as AS.
    pose proof (add_words_length WINp TLp) as Lal.
    destruct (add_words WINp TLp) as [al cy]. cbn [fst snd] in *. destruct AS as (_ & Lal2 & Hcy & _).
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw wt cy)) ltac:(clear; weqm).
    assert (B2 : UBST wt0 m2 (al ++ [wt]) (TLp ++ [tl]) RL).
    { unfold UBST.
      split. { apply limbs_at_app. split; [exact HR|]. rewrite Lal2, HWl. exact HWt2. }
      split. { apply limbs_at_app. split; [exact HTp2|]. rewrite HTl. exact HTt2. }
      repeat (split; [assumption|]). assumption. }
    destruct (UBST_store wt0 m2 (al ++ [wt]) (TLp ++ [tl]) RL (wp + 8 * dn) (Z_to_bv 64 (addw wt cy))
                (al ++ [addw wt cy]) (TLp ++ [tl]) RL B2) as [SOK B3].
    { left. clear - Hdn. lia. }
    { cbv zeta. unfold udb_bnd in DJB.
      assert (L8 : length (le8 (Z_to_bv 64 (addw wt cy))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 (wp + 8 * dn)) with (wa (wp + 8 * dn)).
      split. { replace (wp + 8 * dn)%Z with (wp + 8 * Z.of_nat (length al))%Z by (rewrite Lal2, HWl; reflexivity).
               apply limbs_at_snoc_write; [exact HR | rewrite Lal2, HWl; clear - DJB Hdn; lia]. }
      split. { apply limbs_at_write_other; [ | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, length_app, Nat2Z.inj_add, HTl; cbn [length]; clear - P1 Hdn; lia].
               apply limbs_at_app. split; [exact HTp2|]. rewrite HTl. exact HTt2. }
      split. { apply limbs_at_write_other; [exact HRL2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8; clear - P3 HRl Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P2 Hdn; lia]. }
    clear FR CTA CVA.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m3 end.
    clear B2 SOK HR HWt2 HTp2 HTt2 HVD2 HRL2 WW WT WRs STc MIc MU WM. try clear m2.
    zstep. chk ltac:(fun C => clear - C RWP; lia).
    chk ltac:(fun C => clear - C; lia).
    do 3 zstep.
    replace (rp + 8 + -8)%Z with rp by (clear; lia).
    rewrite (bn_swrap32_small (i + 1)) by (clear - Hi; lia).
    setreg 11%Z (Z_to_bv 64 (subw q bw)) ltac:(clear; weqm).
    destruct (UBST_store wt0 m3 (al ++ [addw wt cy]) (TLp ++ [tl]) RL rp (Z_to_bv 64 (subw q bw))
                (al ++ [addw wt cy]) (TLp ++ [tl]) [subw q bw] B3) as [SOK B4].
    { right. right. reflexivity. }
    { cbv zeta. unfold udb_bnd in DJB.
      destruct B3 as (HWIN & HTL & HRL & HVD & _).
      assert (L8 : length (le8 (Z_to_bv 64 (subw q bw))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 rp) with (wa rp).
      split. { apply limbs_at_write_other; [exact HWIN | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia
               | rewrite L8, length_app, Nat2Z.inj_add, Lal2, HWl; cbn [length]; clear - P3 Hdn; lia]. }
      split. { apply limbs_at_write_other; [exact HTL | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia
               | rewrite L8, length_app, Nat2Z.inj_add, HTl; cbn [length]; clear - P7 Hdn; lia]. }
      split. { replace rp with (rp + 8 * Z.of_nat (length (@nil Z)))%Z at 1 by (cbn [length]; clear; lia).
               apply (limbs_at_snoc_write bgusegs m3 rp [] (subw q bw)); [apply limbs_at_nil; clear - DJB Hdn; lia | cbn [length]; clear - DJB Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P10 Hdn; lia]. }
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m4 end.
    clear B3 SOK. try clear m3.
    zstep. rewrite lts_signed by (clear - Hi; lia).
    if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. }
    clear KO.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    2:{ exfalso. clear - KB RWP Hdn. rewrite ?unsigned_lit in KB by lia. lia. }
    apply K. exact B4.
  Qed.

  (* [comment removed for export] *)
  Lemma udb_body : forall mm WIN TL RL i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31,
    UBST (wp + 8 * dn) mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> (nth (length V) WIN 0 <= d0)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31,
       UBST (wp + 8 * dn + -8) mm' (sc_win d0 d1 V WIN) (sc_tmp d0 d1 V WIN) [sc_q d0 d1 V WIN] ->
       evt bgusegs POST (ULST 0x109c0c mm' x1 x5 x6 x7 (Z_to_bv 64 rp) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (i + 1))
                            (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 wp) x27 x28 x29 x30 x31)) ->
    evt bgusegs POST (ULST 0x109c18 mm x1 x5 x6 x7 (Z_to_bv 64 (rp + 8)) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 i)
                         (Z_to_bv 64 0) (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 (wp + 8)) x27 x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 B HWl HTl HRl LW Hn0 Hi K.
    assert (EV : length V = Z.to_nat dn) by (clear - HVl; lia).
    assert (EW : length WIN = S (Z.to_nat dn)) by (clear - HWl Hdn; lia).
    set (n0 := nth (length V) WIN 0%Z) in *.
    set (n1 := nth (length V - 1) WIN 0%Z).
    set (n2 := if (length V =? 1)%nat then 0%Z else nth (length V - 2) WIN 0%Z).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    eapply (udb_qhat mm WIN TL RL n0 n1 n2); try eassumption.
    { subst n0. rewrite EV. apply nth_error_nth0. clear - EW. lia. }
    { subst n1. rewrite EV. replace (Z.to_nat (dn - 1)) with (Z.to_nat dn - 1)%nat by (clear - Hdn; lia). apply nth_error_nth0. clear - EW. lia. }
    { subst n2. rewrite EV. destruct (Nat.eqb_spec (Z.to_nat dn) 1) as [E1|NE1].
      - left. split; [clear - E1 Hdn; lia | reflexivity].
      - right. split; [clear - NE1 Hdn; lia|]. replace (Z.to_nat (dn - 2)) with (Z.to_nat dn - 2)%nat by (clear - Hdn; lia).
        apply nth_error_nth0. clear - EW. lia. }
    intros m1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y27 y28 y29 y30 y31 B1.
    pose proof (div_qhat_lit n0 n1 n2 d0 d1 Hd0 ltac:(clear - R0 Hn0; lia) R1) as Rq.
    set (q := div_qhat n0 n1 n2 d0 d1) in *.
    eapply (udb_mul _ m1 WIN TL RL q); try eassumption.
    intros m2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z28 z29 z30 z31 B2.
    pose proof (mul_words_spec V q HV ltac:(unfold limb; rewrite BW_lit; exact Rq)) as MS.
    pose proof (mul_words_length V q) as Lml.
    destruct (mul_words V q) as [ml l0] eqn:EMW. cbn [fst snd] in *. destruct MS as (Lml1 & _ & Ll0 & _).
    assert (LT1 : limbs (ml ++ [l0])) by (apply limbs_app; [exact Lml1 | apply limbs_cons; [exact Ll0 | apply limbs_nil]]).
    assert (HT1 : Z.of_nat (length (ml ++ [l0])) = (dn + 1)%Z) by (rewrite length_app, Lml; cbn [length]; clear - HVl; lia).
    eapply (udb_sub _ m2 WIN (ml ++ [l0]) RL); try eassumption.
    intros m3 u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 B3.
    pose proof (sub_words_spec WIN (ml ++ [l0]) LW LT1 ltac:(clear - HWl HT1; lia)) as SS.
    destruct (sub_words WIN (ml ++ [l0])) as [sl bw] eqn:ESW. cbn [fst snd] in *. destruct SS as (Lsl & Lsl2 & Hbw & _).
    eapply (udb_mask _ m3 sl ml l0 RL bw); try eassumption.
    { rewrite Lsl2. exact HWl. }
    { rewrite Lml. exact HVl. }
    intros m4 v5 v6 v10 v11 v13 v14 v15 v16 v17 B4.
    set (msk := map (fun x => Z.land x (negw bw)) V) in *.
    assert (Esl : sl = firstn (Z.to_nat dn) sl ++ [nth (Z.to_nat dn) sl 0%Z]) by (apply split_last; rewrite Lsl2; exact EW).
    rewrite Esl in B4.
    eapply (udb_add _ m4 (firstn (Z.to_nat dn) sl) (nth (Z.to_nat dn) sl 0%Z) msk l0 RL bw q i); try eassumption.
    { rewrite length_firstn, Lsl2, EW. clear - Hdn. lia. }
    { subst msk. rewrite length_map. exact HVl. }
    { apply limbs_firstn. exact Lsl. }
    { subst msk. apply mask_limbs; assumption. }
    { rewrite <- BW_lit. apply limbs_nth. exact Lsl. }
    intros m5 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 B5.
    assert (ESC : step_core V d0 d1 WIN =
                  (fst (add_words (firstn (Z.to_nat dn) sl) msk) ++ [addw (nth (Z.to_nat dn) sl 0%Z) (snd (add_words (firstn (Z.to_nat dn) sl) msk))],
                   ml ++ [l0], msk, subw q bw)).
    { unfold step_core. fold n0. fold n1. fold n2. fold q. rewrite EMW, ESW. fold msk. rewrite EV.
      destruct (add_words (firstn (Z.to_nat dn) sl) msk) as [al cy]. reflexivity. }
    assert (E1 : sc_win d0 d1 V WIN = fst (add_words (firstn (Z.to_nat dn) sl) msk) ++ [addw (nth (Z.to_nat dn) sl 0%Z) (snd (add_words (firstn (Z.to_nat dn) sl) msk))])
      by (unfold sc_win; rewrite ESC; reflexivity).
    assert (E2 : sc_tmp d0 d1 V WIN = msk ++ [l0]).
    { unfold sc_tmp. rewrite ESC. cbn [fst snd]. f_equal. rewrite skipn_app, <- Lml, skipn_all, Nat.sub_diag. reflexivity. }
    assert (E3 : sc_q d0 d1 V WIN = subw q bw) by (unfold sc_q; rewrite ESC; reflexivity).
    apply K. rewrite E1, E2, E3. exact B5.
  Qed.
(* [comment removed for export] *)
End Body.
