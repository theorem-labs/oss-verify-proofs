(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivLoop.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import DivQhatPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require DivBody.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf AW_add_words AW_sub_words AW_mul_words AW_div_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Ltac weqm := apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; unfold subw, addw, mulw, BW; Z.div_mod_to_equations; lia.

Notation mk_fl := DivBody.mk_fl.
Notation mk_fc := DivBody.mk_fc.
Notation mask_gen := DivBody.mask_gen.
Notation mk_fc_range := DivBody.mk_fc_range.
Notation div_words_lit := DivBody.div_words_lit.
Notation div_qhat_lit := DivBody.div_qhat_lit.
Notation mask_limbs := DivBody.mask_limbs.
Notation nth_error_nth0 := DivBody.nth_error_nth0.
Notation split_last := DivBody.split_last.

(* [comment removed for export] *)
Definition db_bndA (wp TD VD rp TA VA lo SP dn : Z) : Prop :=
  (0 <= wp /\ 0 <= TD /\ 0 <= VD /\ 0 <= rp /\ 0 <= TA /\ 0 <= VA /\
   wp + 8 * (dn + 1) <= lo /\ TD + 8 * (dn + 1) <= lo /\ VD + 8 * dn <= lo /\ rp + 8 <= lo /\ TA + 24 <= lo /\ VA + 24 <= lo /\
   lo <= SP - 352 /\ SP <= 140737488355328)%Z.
Notation db_pair := DivBody.db_pair.
Definition db_al (wp TD VD rp TA VA : Z) : Prop :=
  (wp mod 8 = 0 /\ TD mod 8 = 0 /\ VD mod 8 = 0 /\ rp mod 8 = 0 /\ TA mod 8 = 0 /\ VA mod 8 = 0)%Z.

Lemma limbs_trA : forall W m m' A ls n, limbs_at asegs m A ls -> munch W m m' -> Z.of_nat (length ls) = n ->
  disjoint_from W A (8 * n) -> limbs_at asegs m' A ls.
Proof. intros W m m' A ls n H MU <- D. eapply limbs_at_transport; eauto. Qed.

(* [comment removed for export] *)
Ltac tr_cells H MUc WMc tac :=
  eapply rw_cells_transport in H; [ | exact MUc | exact WMc | cbn; tac ].

(* [comment removed for export] *)
Lemma qh_s1 : forall n1 d0 q,
  ((n1 + d0 * ((1 - q) mod 18446744073709551616)) mod 18446744073709551616 = addw (subw n1 (mulw q d0)) d0)%Z.
Proof.
  intros n1 d0 q. unfold addw, subw, mulw, BW. change (2 ^ 64)%Z with 18446744073709551616%Z.
  set (M := 18446744073709551616%Z).
  rewrite <- (Zplus_mod_idemp_r (d0 * ((1 - q) mod M))), Zmult_mod_idemp_r, Zplus_mod_idemp_r.
  rewrite Zminus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. ring.
Qed.

Section Body.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (d0 d1 dn : Z) (V : list Z).
  Variables (wp TD VD rp TA VA lo : Z).
  Variables (c0 c1 c2 c3 c4 c5 c6 c14 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 : word) (loopw : word).
  Variables (ta1 ta2 ta3 ta4 va1 va2 va3 va4 : word).
  Variable m0 : word -> option byte.
  Notation SP := (bv_unsigned sp).
  Hypothesis Hd0 : (9223372036854775808 <= d0 < 18446744073709551616)%Z.
  Hypothesis Hd1 : (0 <= d1 < 18446744073709551616)%Z.
  Hypothesis Hdn : (1 <= dn < 2147483647)%Z.
  Hypothesis HV : limbs V.
  Hypothesis HVl : Z.of_nat (length V) = dn.
  Hypothesis DJB : db_bndA wp TD VD rp TA VA lo SP dn.
  Hypothesis DJP : db_pair wp TD VD rp TA VA dn.
  Hypothesis DAL : db_al wp TD VD rp TA VA.

  (* [comment removed for export] *)
  Notation FRAME :=
    [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6;
     C8 (Z_to_bv 64 (d1 mod 4294967296));       (* [comment removed for export] *)
     C8 (Z_to_bv 64 4294967295);                (* [comment removed for export] *)
     C8 (Z_to_bv 64 (Z.shiftr d1 32));          (* [comment removed for export] *)
     C8 (Z_to_bv 64 d1);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 dn);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 (dn + 1));                  (* [comment removed for export] *)
     C8 (Z_to_bv 64 (8 * dn));                  (* [comment removed for export] *)
     C8 c14;                                    (* [comment removed for export] *)
     C8 (Z_to_bv 64 TA);                        (* [comment removed for export] *)
     C8 loopw;                                  (* [comment removed for export] *)
     C8 (Z_to_bv 64 (shad VA));                 (* [comment removed for export] *)
     C8 (Z_to_bv 64 VA);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 dn);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 (shad TA));                 (* [comment removed for export] *)
     C8 c21; C8 c22; C8 c23; C8 c24; C8 c25; C8 c26; C8 c27; C8 c28; C8 c29; C8 c30; C8 c31; C8 c32; C8 c33].
  Notation WF := [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 352, bv_unsigned sp)]%Z.
  (* [comment removed for export] *)
  Hypothesis ACW : acc asegs m0 wp (8 * (dn + 1)).
  Hypothesis ACT : acc asegs m0 TD (8 * (dn + 1)).
  Hypothesis ACV : acc asegs m0 VD (8 * dn).
  Hypothesis ACQ : acc asegs m0 rp 8.
  Hypothesis ACTA : acc asegs m0 TA 24.
  Hypothesis ACVA : acc asegs m0 VA 24.
  Hypothesis SHB0 : shb_cells asegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m0.
  Hypothesis OFFW : offshW WF.
  Hypothesis DG1 : disjoint_from WF g_GOT_shadow_offset_cell 8.
  Hypothesis DG2 : disjoint_from WF g_shadow_memory_dynamic_address 8.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  (* [comment removed for export] *)
  Definition BST (mm : word -> option byte) (WIN TL RL : list Z) : Prop :=
    limbs_at asegs mm wp WIN /\ limbs_at asegs mm TD TL /\ limbs_at asegs mm rp RL /\ limbs_at asegs mm VD V /\
    wr_at asegs mm wp (8 * (dn + 1)) /\ wr_at asegs mm TD (8 * (dn + 1)) /\ wr_at asegs mm rp 8 /\
    rw_cells asegs mm TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4] /\
    rw_cells asegs mm VA [C8 (Z_to_bv 64 VD); C4 va1; C4 va2; C4 va3; C4 va4] /\
    rw_cells asegs mm (bv_unsigned sp + -272) FRAME /\
    stk asegs mm lo (bv_unsigned sp + -272) /\ mem_inv asegs mm /\
    munch WF m0 mm /\ wmono asegs m0 mm.

  (* [comment removed for export] *)
  Notation LST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 SHB) x21 x22
             x23 x24 (Z_to_bv 64 d0) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = (bv_unsigned sp + -272)%Z.
  Proof using DJB Hdn.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    unfold db_bndA in DJB. clear - DJB Hdn. lia.
  Qed.
  Lemma ulit : forall z, (0 <= z)%Z -> (z <= lo)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof using DJB Hdn.
    intros z H1 H2. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    unfold db_bndA in DJB. clear - DJB Hdn H1 H2. lia.
  Qed.
  Ltac bnd := unfold db_bndA in DJB; clear - DJB Hdn; lia.

  (* [comment removed for export] *)
  Lemma BST_store : forall mm WIN TL RL a w WIN' TL' RL',
    BST mm WIN TL RL ->
    ((wp <= a /\ a + 8 <= wp + 8 * (dn + 1)) \/ (TD <= a /\ a + 8 <= TD + 8 * (dn + 1)) \/ a = rp)%Z ->
    (let mm' := write_to_mem mm (Z_to_bv 64 a) (le8 w) in
     limbs_at asegs mm' wp WIN' /\ limbs_at asegs mm' TD TL' /\ limbs_at asegs mm' rp RL' /\ limbs_at asegs mm' VD V) ->
    store_ok asegs mm (Z_to_bv 64 a) 8 = true /\
    BST (write_to_mem mm (Z_to_bv 64 a) (le8 w)) WIN' TL' RL'.
  Proof using DJB DJP Hdn.
    intros mm WIN TL RL a w WIN' TL' RL' B HA HL.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    cbv zeta in HL. destruct HL as (L1 & L2 & L3 & L4).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    unfold db_bndA in DJB.
    assert (L8 : length (le8 w) = 8%nat) by apply length_le8.
    assert (SOK : store_ok asegs mm (Z_to_bv 64 a) 8 = true).
    { change (Z_to_bv 64 a) with (wa a). destruct HA as [HA|[HA|HA]].
      - replace a with (wp + (a - wp))%Z by (clear; lia). apply (wr_at_store_ok asegs mm wp (8 * (dn + 1))); [exact WW | clear - HA; lia | clear - HA; lia].
      - replace a with (TD + (a - TD))%Z by (clear; lia). apply (wr_at_store_ok asegs mm TD (8 * (dn + 1))); [exact WT | clear - HA; lia | clear - HA; lia].
      - subst a. replace rp with (rp + 0)%Z by (clear; lia). apply (wr_at_store_ok asegs mm rp 8); [exact WRs | clear; lia | clear; lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 a) with (wa a) in *.
    assert (A0 : (0 <= a /\ a + 8 <= lo)%Z) by (clear - HA DJB Hdn; lia).
    unfold BST.
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
  Lemma BST_stack : forall mm m2 WIN TL RL a b,
    BST mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    (bv_unsigned sp - 352 <= a)%Z -> (b <= bv_unsigned sp + -272)%Z ->
    munch [(a, b)] mm m2 -> wmono asegs mm m2 -> mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -272) ->
    BST m2 WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros mm m2 WIN TL RL a b B HWl HTl HRl Ha Hb MUc WMc MIc STc.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold db_bndA in DJB. unfold BST.
    split. { eapply limbs_trA; [exact HWIN | exact MUc | exact HWl | ]. cbn. clear - DJB Hdn Ha Hb. lia. }
    split. { eapply limbs_trA; [exact HTL | exact MUc | reflexivity | ]. cbn. clear - DJB Hdn Ha Hb HTl. lia. }
    split. { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. clear - DJB Hdn Ha Hb HRl. lia. }
    split. { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. clear - DJB Hdn Ha Hb. lia. }
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
  Notation KQ mm v x18 x19 x22 x23 x24 x27 :=
    (forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31,
       evt asegs POST (LST 0x24fa80 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 (Z_to_bv 64 v) x27
                           x28 x29 x30 x31)).

  (* [comment removed for export] *)
  Lemma qh_loop : forall (fuel : nat) mm q rem t2l t2h n2 x1 x5 x6 x7 x13 x14 x15 x18 x19 x22 x23 x24 x27 x28 x29 x30 x31,
    rw_cells asegs mm (bv_unsigned sp + -272) FRAME ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= rem < 18446744073709551616)%Z ->
    (0 <= t2l < 18446744073709551616)%Z -> (0 <= t2h < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    (rem <= t2h)%Z -> (18446744073709551616 <= rem + Z.of_nat fuel * d0 - d0)%Z ->
    KQ mm (qhat_corr fuel q rem t2l t2h n2 d0 d1) x18 x19 x22 x23 x24 x27 ->
    evt asegs POST (LST 0x24fa44 mm x1 x5 x6 x7 (Z_to_bv 64 (addw rem d0)) (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) x13 x14 x15 (Z_to_bv 64 dn)
                        (Z_to_bv 64 d1) x18 x19 (Z_to_bv 64 n2) x22 x23 x24 (Z_to_bv 64 q) x27 x28 x29 x30 x31).
  Proof.
    induction fuel as [|f IH]; intros mm q rem t2l t2h n2 x1 x5 x6 x7 x13 x14 x15 x18 x19 x22 x23 x24 x27 x28 x29 x30 x31 FR Hq Hrem Ht2l Ht2h Hn2 HT HF K.
    { exfalso. clear - HF Hrem Hd0. lia. }
    pose proof (addw_lit rem d0) as R1.
    assert (B6e0 : (t2h <> rem \/ n2 < t2l)%Z ->
              evt asegs POST (LST 0x24fa50 mm x1 x5 x6 x7 (Z_to_bv 64 (addw rem d0)) (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 dn)
                                  (Z_to_bv 64 d1) x18 x19 (Z_to_bv 64 n2) x22 x23 x24 (Z_to_bv 64 q) x27 x28 x29 x30 x31)).
    { intros HC.
      remember (addw rem d0) as rem1 eqn:Erem1.
      zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        do 2 zstep.
        rewrite (qhat_corr_exit2 f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        setreg 26%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        zstep.
        apply K.
      - (* [comment removed for export] *)
        do 6 zstep.
        rewrite (qhat_corr_cont f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        pose proof (subw_lit q 1) as Rq'. pose proof (subw_lit t2l d1) as Rl'. pose proof (t2h_step_lit t2l t2h d1 Ht2h) as Rh'.
        setreg 26%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        setreg 10%Z (Z_to_bv 64 (subw t2l d1)) ltac:(clear; weqm).
        setreg 12%Z (Z_to_bv 64 (if (t2l <? d1)%Z then subw t2h 1 else t2h)) ltac:(clear; destruct (t2l <? d1)%Z; cbn [Z.b2z]; weqm).
        setreg 11%Z (Z_to_bv 64 rem1) ltac:(clear - Erem1; subst rem1; weqm).
        setreg 9%Z (Z_to_bv 64 (addw rem1 d0)) ltac:(clear; weqm).
        rewrite <- Erem1 in K.
        remember (subw q 1) as q' eqn:Eq'. remember (subw t2l d1) as t2l' eqn:Et2l'.
        remember (if (t2l <? d1)%Z then subw t2h 1 else t2h) as t2h' eqn:Et2h'.
        zstep. if_cases K4; zify_cond K4.
        + (* [comment removed for export] *)
          eapply IH; try eassumption.
          clear - HF K3 Erem1 Hrem Hd0 R1. unfold addw in Erem1. rewrite BW_lit in Erem1.
          assert (rem1 = rem + d0)%Z by (Z.div_mod_to_equations; lia). lia.
        + (* [comment removed for export] *)
          do 2 zstep.
          rewrite (qhat_corr_exit0 f q' rem1 t2l' t2h' n2 d0 d1) in K by (clear - K4; lia).
          setreg 26%Z (Z_to_bv 64 q') ltac:(clear - Eq'; subst q'; weqm).
          zstep.
          apply K. }
    zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      apply B6e0. left. clear - K1. lia.
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        do 2 zstep.
        rewrite (qhat_corr_exit1 (S f) q rem t2l t2h n2 d0 d1) in K by (clear - K1 K2; lia).
        apply K.
      + apply B6e0. right. clear - K2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma qh_block : forall mm q n1 n2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    rw_cells asegs mm (bv_unsigned sp + -272) FRAME ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= n1 < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    KQ mm (qhat_corr QHAT_FUEL q (subw n1 (mulw q d0)) ((d1 * q) mod BW) ((d1 * q) / BW) n2 d0 d1) x18 x19 x22 x23 x24 x27 ->
    evt asegs POST (LST 0x24f9c8 mm x1 x5 x6 x7 (Z_to_bv 64 n1) (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 n2) x22 x23 x24 x26 x27
                        x28 x29 x30 x31).
  Proof.
    intros mm q n1 n2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x27 x28 x29 x30 x31 FR Hq Hn1 Hn2 K.
    do 22 zstep.
    pose proof (subw_lit n1 (mulw q d0)) as Rrem. pose proof (mod_BW_lit (d1 * q)) as Rl.
    pose proof (mul_hi_lit d1 q Hd1 Hq) as Rh.
    setreg 11%Z (Z_to_bv 64 (subw n1 (mulw q d0))) ltac:(clear; weqm).
    setreg 10%Z (Z_to_bv 64 ((d1 * q) mod BW)) ltac:(clear; weqm).
    setreg 12%Z (Z_to_bv 64 ((d1 * q) / BW)) ltac:(f_equal; rewrite (qh_t2h q d1 Hq Hd1); rewrite (Z.mul_comm d1 q); reflexivity).
    remember (subw n1 (mulw q d0)) as rem eqn:Erem. remember ((d1 * q) mod BW)%Z as t2l eqn:Et2l. remember ((d1 * q) / BW)%Z as t2h eqn:Et2h.
    zstep. if_cases K0; zify_cond K0.
    - do 5 zstep.
      setreg 9%Z (Z_to_bv 64 (addw rem d0)) ltac:(apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite (qh_s1 n1 d0 q), <- Erem;
                                                   apply Z.mod_small; apply addw_lit).
      eapply (qh_loop QHAT_FUEL); try eassumption.
      clear - Hd0 Rrem. unfold QHAT_FUEL. lia.
    - (* [comment removed for export] *)
      do 3 zstep.
      rewrite (qhat_corr_exit0 QHAT_FUEL q rem t2l t2h n2 d0 d1) in K by (clear - K0; lia).
      apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_rd : forall mm WIN TL RL a n g ad,
    BST mm WIN TL RL -> acc asegs m0 a n -> (g mod 8 = 0)%Z -> (a <= g)%Z -> (g + 8 <= a + n)%Z -> (0 <= g < 140737488355328)%Z ->
    ad = wa (shad g) -> ov_read_bytes asegs mm ad 1 = Some [z8].
  Proof.
    intros mm WIN TL RL a n g ad (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _) AC G8 G1 G2 GR E.
    exact (acc_rd0 asegs _ m0 mm a n g ad AC MU OFFW G8 G1 G2 GR E).
  Qed.
  Lemma al8 : forall p k, (p mod 8 = 0)%Z -> ((p + 8 * k) mod 8 = 0)%Z.
  Proof. intros p k H. Z.div_mod_to_equations. lia. Qed.
  Lemma al8m : forall p k j, (p mod 8 = 0)%Z -> ((p + 8 * k + -8 * j) mod 8 = 0)%Z.
  Proof. intros p k j H. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Ltac shchk_with B AC g Hal tac :=
    let ad := cur_mem_addr in let RD := fresh "RD" in
    pose proof (sh_rd _ _ _ _ _ _ g ad B AC Hal ltac:(tac) ltac:(tac) ltac:(tac) ltac:(sh_addr)) as RD; zstep; clear RD; chk0.
  Ltac shchk B AC g Hal := shchk_with B AC g Hal ltac:(bnd).

  (* [comment removed for export] *)
  Lemma db_qhat : forall mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31,
    BST mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) <= dn + 1 -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN ->
    nth_error WIN (Z.to_nat dn) = Some n0 -> nth_error WIN (Z.to_nat (dn - 1)) = Some n1 ->
    (dn = 1%Z /\ n2 = 0%Z \/ (2 <= dn)%Z /\ nth_error WIN (Z.to_nat (dn - 2)) = Some n2) ->
    (n0 <= d0)%Z ->
    (forall mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31,
       BST mm' WIN TL RL ->
       evt asegs POST (LST 0x24fa80 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 (Z_to_bv 64 (wp + 8 * dn + -8)) (Z_to_bv 64 (wp + 8 * dn))
                           (Z_to_bv 64 TA) (Z_to_bv 64 (shad (wp + 8 * dn))) x23 x24 (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1)) (Z_to_bv 64 (wp + 8))
                           x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24f960 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 x18 (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 TA) x22 x23 x24 x26
                        (Z_to_bv 64 (wp + 8)) x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31 B HWl HTl HRl LW N0 N1 N2 Hn0 K.
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (apply nth_error_In in N0; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N0)).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (apply nth_error_In in N1; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N1)).
    assert (R2 : (0 <= n2 < 18446744073709551616)%Z).
    { destruct N2 as [[_ ->]|[_ N2]]; [clear; lia|]. apply nth_error_In in N2. rewrite <- BW_lit. exact (proj1 (Forall_forall _ _) LW _ N2). }
    assert (BWP : (0 <= wp /\ wp + 8 * dn + 8 <= 140737488355328)%Z) by bnd.
    do 2 zstep.
    setreg 22%Z (Z_to_bv 64 (shad (wp + 8 * dn))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    shchk B ACW (wp + 8 * dn)%Z (al8 wp dn AW8).
    do 3 zstep.
    shchk B ACW (wp + 8 * dn + -8 * 1)%Z (al8m wp dn 1 AW8).
    (* [comment removed for export] *)
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth asegs mm wp WIN (Z.to_nat dn) n0 ad HWIN N0 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
      do 2 zstep.
      setreg 26%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_eq n0 d0) KE); clear; weqm).
      apply K. exact B. }
    assert (CONT : forall y11 y12 y21, y21 = Z_to_bv 64 n2 ->
              evt asegs POST (LST 0x24f9bc mm x1 x5 x6 x7 (Z_to_bv 64 n1) (Z_to_bv 64 n0) y11 y12 x13 x14 x15 (Z_to_bv 64 dn) x17 (Z_to_bv 64 (wp + 8 * dn + -8))
                                  (Z_to_bv 64 (wp + 8 * dn)) y21 (Z_to_bv 64 (shad (wp + 8 * dn))) x23 x24 x26 (Z_to_bv 64 (wp + 8)) x28 x29 x30 x31)).
    { intros y11 y12 y21 ->.
      do 3 zstep.
      (* [comment removed for export] *)
      assert (E0 : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply unsigned_lit; clear - R0; lia).
      assert (E1 : bv_unsigned (Z_to_bv 64 n1) = n1) by (apply unsigned_lit; clear - R1; lia).
      assert (ED : bv_unsigned (Z_to_bv 64 d0) = d0) by (apply unsigned_lit; clear - Hd0; lia).
      pose proof ESP as ESPv.
      eapply evt_cut.
      { eapply bn_div_words_aspec with (lo := lo) (m := mm).
        - rewrite ED. clear - Hd0. lia.
        - rewrite E0, ED. clear - Hn0 KE. lia.
        - rewrite ESPv. exact ST.
        - rewrite ESPv. bnd.
        - exact MI. }
      intros ms' PO. unfold dvw_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
      subst ms'. rewrite E0, E1, ED, ESPv in *.
      replace (ret_pc (Z_to_bv 64 2423240)) with (Z_to_bv 64 2423240) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      assert (B2 : BST m2 WIN TL RL).
      { eapply (BST_stack mm m2 WIN TL RL); [exact B | exact HWl | exact HTl | exact HRl | | | exact MUc | exact WMc | exact MIc | exact STc].
        - clear. lia.
        - clear. lia. }
      pose proof B2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
      assert (Hq : (0 <= div_words n0 n1 d0 < 18446744073709551616)%Z) by (apply div_words_lit; [exact Hd0 | clear - R0 Hn0 KE; lia | exact R1]).
      eapply qh_block; [exact FR2 | exact Hq | exact R1 | exact R2 | ].
      intros y1 y5 y6 y7 y9 y10 z11 z12 y13 y14 y15 y17 y28 y29 y30 y31.
      setreg 26%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_neq n0 d0) KE); reflexivity).
      apply K. exact B2. }
    (* [comment removed for export] *)
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth asegs mm wp WIN (Z.to_nat (dn - 1)) n1 ad HWIN N1 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.
    zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      zstep. apply CONT.
      destruct N2 as [[_ ->]|[N2 _]]; [reflexivity | exfalso; clear - KN N2 BWP; lia].
    - destruct N2 as [[N2 _]|[N2a N2]]; [exfalso; clear - KN N2; lia|].
      do 3 zstep.
      shchk_with B ACW (wp + 8 * dn + -8 * 2)%Z (al8m wp dn 2 AW8) ltac:(unfold db_bndA in DJB; clear - DJB Hdn N2a; lia).
      let ad := cur_mem_addr in
        pose proof (limbs_at_read_nth asegs mm wp WIN (Z.to_nat (dn - 2)) n2 ad HWIN N2 ltac:(unfold wa; f_equal; clear - N2a; lia)) as RD.
      zstep. clear RD.
      zstep. apply CONT. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma shb_mm : forall mm WIN TL RL, BST mm WIN TL RL -> shb_cells asegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address mm.
  Proof.
    intros mm WIN TL RL (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _).
    exact (shb_cells_munch asegs _ _ _ m0 mm SHB0 MU DG1 DG2).
  Qed.
  Lemma acc_mm : forall mm WIN TL RL a n k n', BST mm WIN TL RL -> acc asegs m0 a n ->
    (0 <= a + k /\ a + k + n' <= 140737488355328)%Z -> (0 <= k)%Z -> (k + n' <= n)%Z -> acc asegs mm (a + k) n'.
  Proof.
    intros mm WIN TL RL a n k n' (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _) AC B Hk Hle.
    apply (acc_tr asegs _ m0 mm a n k n' AC MU OFFW); [intros _; exact B | exact Hk | exact Hle].
  Qed.
  Lemma offsh_T : (TD + 8 * (dn + 1) <= SHLO \/ SHHI <= TD)%Z.
  Proof. cbn [offshW] in OFFW. tauto. Qed.
  Lemma offsh_W : (wp + 8 * (dn + 1) <= SHLO \/ SHHI <= wp)%Z.
  Proof. cbn [offshW] in OFFW. tauto. Qed.

  (* [comment removed for export] *)
  Lemma db_mul : forall mm WIN TL RL q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x22 x23 x24 x27 x28 x29 x30 x31,
    BST mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z -> (0 <= q < 18446744073709551616)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       BST mm' WIN (fst (mul_words V q) ++ [snd (mul_words V q)]) RL ->
       evt asegs POST (LST 0x24fadc mm' x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 (Z_to_bv 64 q) x27
                           x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24fa80 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 (Z_to_bv 64 q) x27
                        x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x22 x23 x24 x27 x28 x29 x30 x31 B HWl HRl Hq K.
    pose proof (shb_mm _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACTm : acc asegs mm TD (8 * dn)).
    { pose proof (acc_mm mm WIN TL RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACVm : acc asegs mm VD (8 * dn)).
    { pose proof (acc_mm mm WIN TL RL VD (8 * dn) 0 (8 * dn) B ACV) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    zstep. shchk B ACTA TA ATA8.
    zstep. shchk B ACVA VA AVA8.
    do 6 zstep.
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; bnd).
    assert (EVD : bv_unsigned (Z_to_bv 64 VD) = VD) by (apply ulit; bnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 dn) = dn) by (apply ulit; bnd).
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; clear - Hq; lia).
    pose proof ESP as ESPv.
    pose proof offsh_T as OT.
    eapply evt_cut.
    { eapply bn_mul_words_aspec with (a := V) (lo := lo) (m := mm).
      - exact HV.
      - rewrite HVl. clear - Hdn. lia.
      - rewrite EDN, HVl. reflexivity.
      - rewrite EVD. exact HVD.
      - rewrite ETD, HVl. apply (wr_at_sub asegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - rewrite ETD, EVD, HVl. unfold alias_ok. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. bnd.
      - rewrite ETD, ESPv, HVl. bnd.
      - rewrite EVD, ESPv, HVl. bnd.
      - exact MI.
      - exact SHm.
      - rewrite ETD, HVl. exact ACTm.
      - rewrite EVD, HVl. exact ACVm.
      - rewrite ETD, EVD, HVl. unfold aptrs3. split; [exact AT8|]. split; [exact AV8|]. split; [exact AV8|]. split; [clear - OT Hdn; lia | exact SHLO_LO]. }
    intros ms' PO. unfold mw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ETD, EQ, ESPv, HVl in *.
    replace (ret_pc (Z_to_bv 64 2423472)) with (Z_to_bv 64 2423472) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (HWIN2 : limbs_at asegs m2 wp WIN).
    { eapply limbs_trA; [exact HWIN | exact MUc | exact HWl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at asegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at asegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P7 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P9 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call asegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    pose proof (mul_words_length V q) as Lml.
    assert (B2 : BST m2 WIN (fst (mul_words V q)) RL).
    { unfold BST. repeat (split; [assumption|]). assumption. }
    clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 OT.
    assert (BT : (0 <= TD /\ TD + 8 * dn + 8 <= 140737488355328)%Z) by bnd.
    zstep. shchk B2 ACTA TA ATA8.
    do 5 zstep.
    shchk B2 ACT (TD + 8 * dn)%Z (al8 TD dn AT8).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    destruct (BST_store m2 WIN (fst (mul_words V q)) RL (TD + 8 * dn) (Z_to_bv 64 (snd (mul_words V q)))
                WIN (fst (mul_words V q) ++ [snd (mul_words V q)]) RL B2) as [SOK B3].
    { right. left. clear - Hdn. lia. }
    { cbv zeta. unfold db_bndA in DJB.
      assert (L8 : length (le8 (Z_to_bv 64 (snd (mul_words V q)))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 (TD + 8 * dn)) with (wa (TD + 8 * dn)).
      split. { apply limbs_at_write_other; [exact HWIN2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HWl; clear - P1 Hdn; lia]. }
      split. { replace (TD + 8 * dn)%Z with (TD + 8 * Z.of_nat (length (fst (mul_words V q))))%Z by (rewrite Lml, HVl; reflexivity).
               apply limbs_at_snoc_write; [exact HR | rewrite Lml, HVl; clear - DJB Hdn; lia]. }
      split. { apply limbs_at_write_other; [exact HRL2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8; clear - P7 HRl Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P6 Hdn; lia]. }
    clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12.
    zstep.
    apply K. exact B3.
  Qed.

  (* [comment removed for export] *)
  Lemma db_sub : forall mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x28 x29 x30 x31,
    BST mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> limbs TL ->
    (forall mm' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       BST mm' (fst (sub_words WIN TL)) TL RL ->
       evt asegs POST (LST 0x24faf0 mm' x1 x5 x6 x7 x9 (Z_to_bv 64 (snd (sub_words WIN TL))) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 x26
                           (Z_to_bv 64 wp) x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24fadc mm x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 x26 (Z_to_bv 64 (wp + 8))
                        x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x28 x29 x30 x31 B HWl HTl HRl LW LT K.
    pose proof (shb_mm _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACWm : acc asegs mm wp (8 * (dn + 1))).
    { pose proof (acc_mm mm WIN TL RL wp (8 * (dn + 1)) 0 (8 * (dn + 1)) B ACW) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc asegs mm TD (8 * (dn + 1))).
    { pose proof (acc_mm mm WIN TL RL TD (8 * (dn + 1)) 0 (8 * (dn + 1)) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    do 5 zstep.
    assert (EWP : bv_unsigned (Z_to_bv 64 wp) = wp) by (apply ulit; bnd).
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; bnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 (dn + 1)) = (dn + 1)%Z) by (apply ulit; bnd).
    pose proof ESP as ESPv.
    pose proof offsh_W as OW.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (LEN : length TL = length WIN) by (clear - HWl HTl; lia).
    eapply evt_cut.
    { eapply bn_sub_words_aspec with (a := WIN) (b := TL) (lo := lo) (m := mm).
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
      - rewrite ESPv. bnd.
      - rewrite EWP, ESPv, HWl. bnd.
      - rewrite EWP, ESPv, HWl. bnd.
      - rewrite ETD, ESPv, HWl. bnd.
      - exact MI.
      - exact SHm.
      - rewrite EWP, HWl. exact ACWm.
      - rewrite EWP, HWl. exact ACWm.
      - rewrite ETD, HWl. exact ACTm.
      - rewrite EWP, ETD, HWl. unfold aptrs3. split; [exact AW8|]. split; [exact AW8|]. split; [exact AT8|]. split; [exact OW | exact SHLO_LO]. }
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 2423536)) with (Z_to_bv 64 2423536) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HTL2 : limbs_at asegs m2 TD TL).
    { eapply limbs_trA; [exact HTL | exact MUc | exact HTl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at asegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at asegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call asegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    apply K. unfold BST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Section Mask.
    Variables (mk : word -> option byte) (msk : Z).
    Hypothesis Hmsk : (0 <= msk < 18446744073709551616)%Z.
    Hypothesis ACVk : acc asegs mk VD (8 * Z.of_nat (length V)).
    Hypothesis ACTk : acc asegs mk TD (8 * Z.of_nat (length V)).
    Lemma MLEN : length V = length V. Proof. reflexivity. Qed.
    Lemma MFBE : (bv_unsigned sp + -272 = bv_unsigned sp - 272)%Z. Proof. lia. Qed.
    Lemma MALA : alias_ok TD VD (Z.of_nat (length V)).
    Proof. unfold alias_ok. rewrite HVl. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia. Qed.
    Lemma MSEPR : (TD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 272 \/ bv_unsigned sp <= TD)%Z.
    Proof. rewrite HVl. left. bnd. Qed.
    Lemma MSEPA : (VD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 272 \/ bv_unsigned sp <= VD)%Z.
    Proof. rewrite HVl. left. bnd. Qed.
    Notation MRES := (map (fun x => Z.land x msk) V).
    Notation KINV := (INV asegs (mk_fl msk) (mk_fc msk) 0 mk TD VD VD (bv_unsigned sp) lo V 272%Z (bv_unsigned sp + -272)%Z FRAME MRES 0%Z).
    Notation KIT L := (L asegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mk TD VD VD (bv_unsigned sp) lo V V 272%Z (bv_unsigned sp + -272)%Z FRAME eq_refl MFBE
                          MLEN MALA MALA MSEPR MSEPA MSEPA MRES 0%Z).
    Notation K_rdA := (KIT INV_rdA).
    Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
    Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
    Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).
    Notation PBm := (apure TD VD VD (Z.of_nat (length V)) (bv_unsigned sp) 272%Z).
    Notation K_shA := (INV_shA asegs (mk_fl msk) (mk_fc msk) 0%Z mk TD VD VD (bv_unsigned sp) lo V 272%Z (bv_unsigned sp + -272)%Z FRAME MRES 0%Z).
    Notation K_shR := (INV_shR asegs (mk_fl msk) (mk_fc msk) 0%Z mk TD VD VD (bv_unsigned sp) lo V 272%Z (bv_unsigned sp + -272)%Z FRAME MRES 0%Z).
    Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
    Ltac w64eq := unfold DivBody.mk_fl; reflexivity.
    Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
    Ltac mshA P I := let L := constr:(K_shA P) in ld_sh_with L I ACVk 0%nat; chk0.
    Ltac mshR P I := let L := constr:(K_shR P) in ld_sh_with L I ACTk 0%nat; chk0.

    Lemma mask_loop : forall la m1 pre c pa pr x1 x6 x7 x9 x17 x18 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31,
      PBm -> la <> [] -> KINV m1 pre la la c pa pa pr ->
      (forall m2 x5 x10 x11 x12 x15 x16 x17,
         limbs_at asegs m2 TD MRES -> rw_cells asegs m2 (bv_unsigned sp + -272) FRAME -> stk asegs m2 lo (bv_unsigned sp + -272) -> mem_inv asegs m2 ->
         munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 272, bv_unsigned sp)]%Z mk m2 -> wmono asegs mk m2 ->
         evt asegs POST (LST 0x24fb78 m2 x1 x5 x6 x7 x9 x10 x11 x12 (Z_to_bv 64 dn) (Z_to_bv 64 msk) x15 x16 x17 x18 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31)) ->
      evt asegs POST (LST 0x24fb38 m1 x1 (Z_to_bv 64 pr) x6 x7 x9 (Z_to_bv 64 pa) (Z_to_bv 64 pr) (Z_to_bv 64 pa) (Z_to_bv 64 dn) (Z_to_bv 64 msk)
                          (Z_to_bv 64 (shad pa)) (Z_to_bv 64 (Z.of_nat (length la))) x17 x18 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31).
    Proof.
      induction la as [|x la IH]; intros m1 pre c pa pr x1 x6 x7 x9 x17 x18 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 P NE I K; [congruence|].
      pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
      pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _).
      pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
      pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx.
      assert (BND : (0 <= pa /\ pa + 8 * Z.of_nat (length (x :: la)) <= 140737488355328 /\ 0 <= pr /\ pr + 8 * Z.of_nat (length (x :: la)) <= 140737488355328)%Z)
        by (clear - En Epa Epr BR BA; lia).
      assert (L31 : (Z.of_nat (length (x :: la)) < 2147483647)%Z) by (clear - En HVl Hdn; lia).
      clear En Epr TOP R0 Epa BR BA.
      mshA P I.
      do 2 zstep. mshR P I.
      ldA I.
      do 5 zstep.
      st_limb I l c' Ec'. clear Ec'.
      do 2 zstep.
      setreg 15%Z (Z_to_bv 64 (shad (pa + 8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 16%Z (Z_to_bv 64 (Z.of_nat (length la))) ltac:(f_equal; cbn [length]; clear; lia).
      zstep. if_cases KB; zify_cond KB.
      - (* [comment removed for export] *)
        eapply IH; [ exact P | | exact I | exact K ].
        destruct la; [ exfalso; apply KB; reflexivity | discriminate ].
      - (* [comment removed for export] *)
        destruct la as [|x' la'].
        + pose proof (K_done _ _ _ _ _ _ I) as (HP & CYE & FR & ST & MI & MU & WM).
          apply K; assumption.
        + exfalso. clear - KB L31. cbn [length] in *. rewrite Z.mod_small in KB by lia. lia.
    Qed.
  End Mask.

  (* [comment removed for export] *)
  Lemma db_mask : forall mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x28 x29 x30 x31,
    BST mm WIN (TLp ++ [tl]) RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    (0 <= bw <= 1)%Z ->
    (forall mm' x5 x10 x11 x12 x14 x15 x16 x17,
       BST mm' WIN (map (fun x => Z.land x (negw bw)) V ++ [tl]) RL ->
       evt asegs POST (LST 0x24fb78 mm' x1 x5 x6 x7 (Z_to_bv 64 bw) x10 x11 x12 (Z_to_bv 64 dn) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 x26
                           (Z_to_bv 64 wp) x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24faf0 mm x1 x5 x6 x7 x9 (Z_to_bv 64 bw) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TA) x22 x23 x24 x26 (Z_to_bv 64 wp)
                        x28 x29 x30 x31).
  Proof.
    intros mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x26 x28 x29 x30 x31 B HWl HTl HRl Hbw K.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACVm : acc asegs mm VD (8 * Z.of_nat (length V))).
    { rewrite HVl. pose proof (acc_mm mm WIN _ RL VD (8 * dn) 0 (8 * dn) B ACV) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc asegs mm TD (8 * Z.of_nat (length V))).
    { rewrite HVl. pose proof (acc_mm mm WIN _ RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (PBm : apure TD VD VD (Z.of_nat (length V)) (bv_unsigned sp) 272%Z).
    { rewrite HVl. pose proof offsh_T as OT. unfold apure. split; [tauto|]. split; [bnd|]. split; [bnd|]. split; [bnd|].
      cbn [offshW]. split; [clear - OT Hdn; lia|]. split; [right; unfold db_bndA in DJB; clear - DJB SHLO_LO; lia | exact I]. }
    assert (BV : (0 <= VD /\ VD + 8 * dn <= 140737488355328 /\ 0 <= TD /\ TD + 8 * dn <= 140737488355328)%Z) by bnd.
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    do 2 zstep.
    zstep. if_cases KZ; zify_cond KZ.
    { exfalso. clear - KZ Hdn. destruct (Z.ltb_spec 0 dn); [|lia]. destruct (Z.ltb_spec dn 9223372036854775808); [discriminate | lia]. }
    try clear KZ.
    zstep. shchk B ACVA VA AVA8.
    zstep. shchk B ACTA TA ATA8.
    do 9 zstep.
    setreg 14%Z (Z_to_bv 64 (negw bw)) ltac:(clear; unfold negw; weqm).
    setreg 15%Z (Z_to_bv 64 (shad VD)) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    assert (Hmsk : (0 <= negw bw < 18446744073709551616)%Z) by apply negw_limb.
    remember (negw bw) as msk eqn:Emsk.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    apply limbs_at_app in HTL. destruct HTL as [HTLp HTLl].
    assert (ETL : (TD + 8 * Z.of_nat (length TLp) = TD + 8 * dn)%Z) by (rewrite HTl; reflexivity). rewrite ETL in HTLl. clear ETL.
    assert (I : INV asegs (mk_fl msk) (mk_fc msk) 0 mm TD VD VD (bv_unsigned sp) lo V 272%Z (bv_unsigned sp + -272)%Z FRAME
                    (map (fun x => Z.land x msk) V) 0%Z mm [] V V 0 VD VD TD).
    { apply (INV_init asegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mm TD VD VD (bv_unsigned sp) lo V V 272%Z (bv_unsigned sp + -272)%Z FRAME eq_refl MFBE
                          MLEN MALA MALA MSEPR MSEPA MSEPA); try assumption.
      - rewrite HVl. clear - Hdn. lia.
      - clear. lia.
      - rewrite HVl. apply (wr_at_sub asegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - apply munch_refl.
      - apply munch_refl.
      - apply wmono_refl.
      - rewrite mask_gen. reflexivity.
      - rewrite mask_gen. reflexivity. }
    eapply evt_eq; [ | eapply (mask_loop mm msk Hmsk ACVm ACTm V mm [] 0 VD TD); [ exact PBm | | exact I | ] ].
    { rewrite HVl. reflexivity. }
    { destruct V; [ exfalso; cbn [length] in HVl; clear - HVl Hdn; lia | discriminate ]. }
    intros m2 y5 y10 y11 y12 y15 y16 y17 HP FR2 ST2 MI2 MUk WMk. rewrite HVl in MUk.
    assert (HWIN2 : limbs_at asegs m2 wp WIN).
    { eapply limbs_trA; [exact HWIN | exact MUk | exact HWl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at asegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUk | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at asegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUk | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P7 Hdn HRl. lia. }
    assert (HTLl2 : limbs_at asegs m2 (TD + 8 * dn) [tl]).
    { eapply limbs_trA; [exact HTLl | exact MUk | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB Hdn. lia. }
    assert (HTL2 : limbs_at asegs m2 TD (map (fun x => Z.land x msk) V ++ [tl])).
    { apply limbs_at_app. split; [exact HP|]. rewrite length_map, HVl. exact HTLl2. }
    clear HWIN HVD HRL HTLp HTLl HTLl2 HP ST FR I.
    tr_cells CTA MUk WMk ltac:(unfold db_bndA in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUk WMk ltac:(unfold db_bndA in DJB; clear - DJB P9 Hdn; lia).
    transport_after_call asegs mm m2 MUk WMk.
    clear MUk WMk MI. try clear mm.
    apply K. unfold BST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma db_add : forall mm WINp wt TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31,
    BST mm (WINp ++ [wt]) (TLp ++ [tl]) RL -> Z.of_nat (length WINp) = dn -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WINp -> limbs TLp -> (0 <= wt < 18446744073709551616)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x22 x26 x28 x29 x30 x31,
       BST mm' (fst (add_words WINp TLp) ++ [addw wt (snd (add_words WINp TLp))]) (TLp ++ [tl]) [subw q bw] ->
       evt asegs POST (LST 0x24fbd4 mm' x1 x5 x6 x7 x9 loopw x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 (Z_to_bv 64 (wp + 8 * dn + -8)) (Z_to_bv 64 (wp + 8 * dn + -8))
                           (Z_to_bv 64 TA) x22 (Z_to_bv 64 rp) (Z_to_bv 64 (i + 1)) x26 (Z_to_bv 64 wp) x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24fb78 mm x1 x5 x6 x7 (Z_to_bv 64 bw) x10 x11 x12 (Z_to_bv 64 dn) x14 x15 x16 x17 (Z_to_bv 64 (wp + 8 * dn + -8)) (Z_to_bv 64 (wp + 8 * dn))
                        (Z_to_bv 64 TA) (Z_to_bv 64 (shad (wp + 8 * dn))) (Z_to_bv 64 (rp + 8)) (Z_to_bv 64 i) (Z_to_bv 64 q) (Z_to_bv 64 wp) x28 x29 x30 x31).
  Proof.
    intros mm WINp wt TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 B HWl HTl HRl LW LT Hwt Hi K.
    pose proof (shb_mm _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACWm : acc asegs mm wp (8 * dn)).
    { pose proof (acc_mm mm _ _ RL wp (8 * (dn + 1)) 0 (8 * dn) B ACW) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc asegs mm TD (8 * dn)).
    { pose proof (acc_mm mm _ _ RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    zstep. shchk B ACTA TA ATA8.
    do 4 zstep.
    assert (EWP : bv_unsigned (Z_to_bv 64 wp) = wp) by (apply ulit; bnd).
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; bnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 dn) = dn) by (apply ulit; bnd).
    pose proof ESP as ESPv.
    pose proof offsh_W as OW.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (LEN : length TLp = length WINp) by (clear - HWl HTl; lia).
    apply limbs_at_app in HWIN. destruct HWIN as [HWp HWt]. rewrite HWl in HWt.
    apply limbs_at_app in HTL. destruct HTL as [HTp HTt]. rewrite HTl in HTt.
    eapply evt_cut.
    { eapply bn_add_words_aspec with (a := WINp) (b := TLp) (lo := lo) (m := mm).
      - exact LW.
      - exact LT.
      - exact LEN.
      - rewrite HWl. clear - Hdn. lia.
      - rewrite EDN, HWl. reflexivity.
      - rewrite EWP. exact HWp.
      - rewrite ETD. exact HTp.
      - rewrite EWP, HWl. apply (wr_at_sub asegs mm wp (8 * (dn + 1)) 0 (8 * dn)) in WW; [rewrite Z.add_0_r in WW; exact WW | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - rewrite EWP. unfold alias_ok. left. reflexivity.
      - rewrite EWP, ETD, HWl. unfold alias_ok. clear - P1 Hdn. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. bnd.
      - rewrite EWP, ESPv, HWl. bnd.
      - rewrite EWP, ESPv, HWl. bnd.
      - rewrite ETD, ESPv, HWl. bnd.
      - exact MI.
      - exact SHm.
      - rewrite EWP, HWl. exact ACWm.
      - rewrite EWP, HWl. exact ACWm.
      - rewrite ETD, HWl. exact ACTm.
      - rewrite EWP, ETD, HWl. unfold aptrs3. split; [exact AW8|]. split; [exact AW8|]. split; [exact AT8|]. split; [clear - OW Hdn; lia | exact SHLO_LO]. }
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 2423700)) with (Z_to_bv 64 2423700) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HWt2 : limbs_at asegs m2 (wp + 8 * dn) [wt]).
    { eapply limbs_trA; [exact HWt | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB Hdn. lia. }
    assert (HTp2 : limbs_at asegs m2 TD TLp).
    { eapply limbs_trA; [exact HTp | exact MUc | exact HTl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HTt2 : limbs_at asegs m2 (TD + 8 * dn) [tl]).
    { eapply limbs_trA; [exact HTt | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at asegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at asegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWp HWt HTp HTt HVD HRL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call asegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    pose proof (add_words_spec WINp TLp LW LT ltac:(clear - LEN; lia)) as AS.
    pose proof (add_words_length WINp TLp) as Lal.
    destruct (add_words WINp TLp) as [al cy]. cbn [fst snd] in *. destruct AS as (_ & Lal2 & Hcy & _).
    assert (B2 : BST m2 (al ++ [wt]) (TLp ++ [tl]) RL).
    { unfold BST.
      split. { apply limbs_at_app. split; [exact HR|]. rewrite Lal2, HWl. exact HWt2. }
      split. { apply limbs_at_app. split; [exact HTp2|]. rewrite HTl. exact HTt2. }
      repeat (split; [assumption|]). assumption. }
    clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 OW.
    assert (BW : (0 <= wp /\ wp + 8 * dn + 8 <= 140737488355328 /\ 8 <= rp + 8 /\ rp + 8 <= 140737488355328)%Z) by bnd.
    (* [comment removed for export] *)
    shchk B2 ACW (wp + 8 * dn)%Z (al8 wp dn AW8).
    ld_hd HWt2.
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 (addw wt cy)) ltac:(clear; weqm).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    destruct (BST_store m2 (al ++ [wt]) (TLp ++ [tl]) RL (wp + 8 * dn) (Z_to_bv 64 (addw wt cy))
                (al ++ [addw wt cy]) (TLp ++ [tl]) RL B2) as [SOK B3].
    { left. clear - Hdn. lia. }
    { cbv zeta. unfold db_bndA in DJB.
      assert (L8 : length (le8 (Z_to_bv 64 (addw wt cy))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 (wp + 8 * dn)) with (wa (wp + 8 * dn)).
      split. { replace (wp + 8 * dn)%Z with (wp + 8 * Z.of_nat (length al))%Z by (rewrite Lal2, HWl; reflexivity).
               apply limbs_at_snoc_write; [exact HR | rewrite Lal2, HWl; clear - DJB Hdn; lia]. }
      split. { apply limbs_at_write_other; [ | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, length_app, Nat2Z.inj_add, HTl; cbn [length]; clear - P1 Hdn; lia].
               apply limbs_at_app. split; [exact HTp2|]. rewrite HTl. exact HTt2. }
      split. { apply limbs_at_write_other; [exact HRL2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8; clear - P3 HRl Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD2 | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P2 Hdn; lia]. }
    clear P1 P2 P4 P5 P6 P8 P9 P11 P12.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m3 end.
    clear B2 SOK HR HWt2 HTp2 HTt2 HVD2 HRL2 WW WT WRs CTA CVA FR STc MIc MU WM. try clear m2.
    zstep.
    shchk B3 ACQ rp AR8.
    do 2 zstep.
    rewrite (bn_swrap32_small (i + 1)) by (clear - Hi; lia).
    setreg 10%Z (Z_to_bv 64 (subw q bw)) ltac:(clear; weqm).
    destruct (BST_store m3 (al ++ [addw wt cy]) (TLp ++ [tl]) RL rp (Z_to_bv 64 (subw q bw))
                (al ++ [addw wt cy]) (TLp ++ [tl]) [subw q bw] B3) as [SOK B4].
    { right. right. reflexivity. }
    { cbv zeta. unfold db_bndA in DJB.
      destruct B3 as (HWIN & HTL & HRL & HVD & _).
      assert (L8 : length (le8 (Z_to_bv 64 (subw q bw))) = 8%nat) by apply length_le8.
      change (Z_to_bv 64 rp) with (wa rp).
      split. { apply limbs_at_write_other; [exact HWIN | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia
               | rewrite L8, length_app, Nat2Z.inj_add, Lal2, HWl; cbn [length]; clear - P3 Hdn; lia]. }
      split. { apply limbs_at_write_other; [exact HTL | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia
               | rewrite L8, length_app, Nat2Z.inj_add, HTl; cbn [length]; clear - P7 Hdn; lia]. }
      split. { replace rp with (rp + 8 * Z.of_nat (length (@nil Z)))%Z at 1 by (cbn [length]; clear; lia).
               apply (limbs_at_snoc_write asegs m3 rp [] (subw q bw)); [apply limbs_at_nil; clear - DJB Hdn; lia | cbn [length]; clear - DJB Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P10 Hdn; lia]. }
    clear P3 P7 P10.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m4 end.
    clear B3 SOK. try clear m3.
    pose proof B4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 3 zstep.
    apply K. exact B4.
  Qed.

  (* [comment removed for export] *)
  Definition sc_win (WIN : list Z) : list Z := fst (fst (fst (step_core V d0 d1 WIN))).
  Definition sc_tmp (WIN : list Z) : list Z :=
    snd (fst (step_core V d0 d1 WIN)) ++ skipn (length V) (snd (fst (fst (step_core V d0 d1 WIN)))).
  Definition sc_q (WIN : list Z) : Z := snd (step_core V d0 d1 WIN).

  Lemma db_body : forall mm WIN TL RL i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x22 x26 x28 x29 x30 x31,
    BST mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> (nth (length V) WIN 0 <= d0)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x22 x26 x28 x29 x30 x31,
       BST mm' (sc_win WIN) (sc_tmp WIN) [sc_q WIN] ->
       evt asegs POST (LST 0x24fbd4 mm' x1 x5 x6 x7 x9 loopw x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 (Z_to_bv 64 (wp + 8 * dn + -8)) (Z_to_bv 64 (wp + 8 * dn + -8))
                           (Z_to_bv 64 TA) x22 (Z_to_bv 64 rp) (Z_to_bv 64 (i + 1)) x26 (Z_to_bv 64 wp) x28 x29 x30 x31)) ->
    evt asegs POST (LST 0x24f960 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 dn) x17 x18 (Z_to_bv 64 (wp + 8 * dn)) (Z_to_bv 64 TA) x22
                        (Z_to_bv 64 (rp + 8)) (Z_to_bv 64 i) x26 (Z_to_bv 64 (wp + 8)) x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x17 x18 x22 x26 x28 x29 x30 x31 B HWl HTl HRl LW Hn0 Hi K.
    assert (EV : length V = Z.to_nat dn) by (clear - HVl; lia).
    assert (EW : length WIN = S (Z.to_nat dn)) by (clear - HWl Hdn; lia).
    set (n0 := nth (length V) WIN 0%Z) in *.
    set (n1 := nth (length V - 1) WIN 0%Z).
    set (n2 := if (length V =? 1)%nat then 0%Z else nth (length V - 2) WIN 0%Z).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    eapply (db_qhat mm WIN TL RL n0 n1 n2); try eassumption.
    { subst n0. rewrite EV. apply nth_error_nth0. clear - EW. lia. }
    { subst n1. rewrite EV. replace (Z.to_nat (dn - 1)) with (Z.to_nat dn - 1)%nat by (clear - Hdn; lia). apply nth_error_nth0. clear - EW. lia. }
    { subst n2. rewrite EV. destruct (Nat.eqb_spec (Z.to_nat dn) 1) as [E1|NE1].
      - left. split; [clear - E1 Hdn; lia | reflexivity].
      - right. split; [clear - NE1 Hdn; lia|]. replace (Z.to_nat (dn - 2)) with (Z.to_nat dn - 2)%nat by (clear - Hdn; lia).
        apply nth_error_nth0. clear - EW. lia. }
    intros m1 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y17 y28 y29 y30 y31 B1.
    pose proof (div_qhat_lit n0 n1 n2 d0 d1 Hd0 ltac:(clear - R0 Hn0; lia) R1) as Rq.
    set (q := div_qhat n0 n1 n2 d0 d1) in *.
    eapply (db_mul m1 WIN TL RL q); try eassumption.
    intros m2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z28 z29 z30 z31 B2.
    pose proof (mul_words_spec V q HV ltac:(unfold limb; rewrite BW_lit; exact Rq)) as MS.
    pose proof (mul_words_length V q) as Lml.
    destruct (mul_words V q) as [ml l0] eqn:EMW. cbn [fst snd] in *. destruct MS as (Lml1 & _ & Ll0 & _).
    assert (LT1 : limbs (ml ++ [l0])) by (apply limbs_app; [exact Lml1 | apply limbs_cons; [exact Ll0 | apply limbs_nil]]).
    assert (HT1 : Z.of_nat (length (ml ++ [l0])) = (dn + 1)%Z) by (rewrite length_app, Lml; cbn [length]; clear - HVl; lia).
    eapply (db_sub m2 WIN (ml ++ [l0]) RL); try eassumption.
    intros m3 u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 B3.
    pose proof (sub_words_spec WIN (ml ++ [l0]) LW LT1 ltac:(clear - HWl HT1; lia)) as SS.
    destruct (sub_words WIN (ml ++ [l0])) as [sl bw] eqn:ESW. cbn [fst snd] in *. destruct SS as (Lsl & Lsl2 & Hbw & _).
    eapply (db_mask m3 sl ml l0 RL bw); try eassumption.
    { rewrite Lsl2. exact HWl. }
    { rewrite Lml. exact HVl. }
    intros m4 v5 v10 v11 v12 v14 v15 v16 v17 B4.
    set (msk := map (fun x => Z.land x (negw bw)) V) in *.
    assert (Esl : sl = firstn (Z.to_nat dn) sl ++ [nth (Z.to_nat dn) sl 0%Z]) by (apply split_last; rewrite Lsl2; exact EW).
    rewrite Esl in B4.
    eapply (db_add m4 (firstn (Z.to_nat dn) sl) (nth (Z.to_nat dn) sl 0%Z) msk l0 RL bw q i); try eassumption.
    { rewrite length_firstn, Lsl2, EW. clear - Hdn. lia. }
    { subst msk. rewrite length_map. exact HVl. }
    { apply limbs_firstn. exact Lsl. }
    { subst msk. apply mask_limbs; assumption. }
    { rewrite <- BW_lit. apply limbs_nth. exact Lsl. }
    intros m5 w1 w5 w6 w7 w9 w11 w12 w13 w14 w15 w17 w22 w26 w28 w29 w30 w31 B5.
    assert (ESC : step_core V d0 d1 WIN =
                  (fst (add_words (firstn (Z.to_nat dn) sl) msk) ++ [addw (nth (Z.to_nat dn) sl 0%Z) (snd (add_words (firstn (Z.to_nat dn) sl) msk))],
                   ml ++ [l0], msk, subw q bw)).
    { unfold step_core. fold n0. fold n1. fold n2. fold q. rewrite EMW, ESW. fold msk. rewrite EV.
      destruct (add_words (firstn (Z.to_nat dn) sl) msk) as [al cy]. reflexivity. }
    assert (E1 : sc_win WIN = fst (add_words (firstn (Z.to_nat dn) sl) msk) ++ [addw (nth (Z.to_nat dn) sl 0%Z) (snd (add_words (firstn (Z.to_nat dn) sl) msk))])
      by (unfold sc_win; rewrite ESC; reflexivity).
    assert (E2 : sc_tmp WIN = msk ++ [l0]).
    { unfold sc_tmp. rewrite ESC. cbn [fst snd]. f_equal. rewrite skipn_app, <- Lml, skipn_all, Nat.sub_diag. reflexivity. }
    assert (E3 : sc_q WIN = subw q bw) by (unfold sc_q; rewrite ESC; reflexivity).
    apply K. rewrite E1, E2, E3. exact B5.
  Qed.
End Body.
