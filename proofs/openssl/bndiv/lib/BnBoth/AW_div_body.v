(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import DivQhatPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require DivBody.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AW_add_words AW_sub_words AW_mul_words AW_div_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2434852 => 1
  | 2434856 => 2
  | 2434912 => 2
  | 2434924 => 1
  | 2434932 => 2
  | 2434940 => 1
  | 2434944 => 1
  | 2434948 => 1
  | 2434952 => 2
  | 2434956 => 2
  | 2434960 => 1
  | 2434964 => 2
  | 2435000 => 1
  | 2435004 => 2
  | 2435064 => 2
  | 2435088 => 2
  | 2435116 => 2
  | 2435192 => 1
  | 2435196 => 2
  | 2435200 => 1
  | 2435204 => 1
  | 2435208 => 2
  | 2435276 => 2
  | 2435328 => 1
  | 2435336 => 2
  | 2435340 => 1
  | 2435344 => 1
  | 2435348 => 1
  | 2435352 => 1
  | 2435356 => 2
  | 2435368 => 1
  | 2435372 => 2
  | 2435376 => 1
  | 2435384 => 2
  | 2435428 => 1
  | 2435436 => 2
  | 2435472 => 1
  | 2435480 => 1
  | 2435484 => 2
  | 2435488 => 1
  | 2435492 => 1
  | 2435496 => 1
  | 2435500 => 1
  | 2435504 => 1
  | 2435508 => 1
  | 2435512 => 2
  | 2435520 => 2
  | 2435536 => 1
  | 2435540 => 2
  | 2435544 => 1
  | 2435548 => 1
  | 2435552 => 1
  | 2435556 => 1
  | 2435560 => 1
  | 2435564 => 2
  | 2435588 => 2
  | 2435608 => 1
  | 2435616 => 2
  | 2435620 => 1
  | 2435624 => 1
  | 2435628 => 1
  | 2435632 => 1
  | 2435636 => 2
  | 2435640 => 2
  | 2435644 => 1
  | 2435648 => 2
  | 2435696 => 2
  | 2435708 => 2
  | 2435712 => 1
  | 2435720 => 1
  | 2435724 => 1
  | 2435728 => 2
  | 2435732 => 1
  | 2435736 => 2
  | 2435784 => 1
  | 2435788 => 2
  | 2435792 => 1
  | 2435796 => 1
  | 2435800 => 2
  | 2435828 => 2
  | 2435832 => 1
  | 2435836 => 2
  | 2435840 => 2
  | 2435844 => 1
  | 2435848 => 2
  | 2435964 => 1
  | 2435968 => 1
  | 2435972 => 2
  | 2435976 => 1
  | 2435980 => 1
  | 2435984 => 1
  | 2435988 => 2
  | 2436148 => 2
  | 2436152 => 1
  | 2436156 => 2
  | 2436176 => 1
  | 2436180 => 2
  | 2436236 => 1
  | 2436240 => 2
  | 2436244 => 1
  | 2436248 => 2
  | 2436464 => 1
  | 2436468 => 2
  | 2436536 => 1
  | 2436540 => 1
  | 2436544 => 2
  | 2436548 => 1
  | 2436556 => 1
  | 2436560 => 1
  | 2436564 => 2
  | 2436568 => 2
  | 2436572 => 1
  | 2436576 => 2
  | 2436600 => 1
  | 2436604 => 1
  | 2436608 => 2
  | 2436696 => 2
  | 2436700 => 1
  | 2436704 => 1
  | 2436708 => 2
  | 2436712 => 2
  | 2436748 => 2
  | 2436752 => 1
  | 2436756 => 1
  | 2436760 => 1
  | 2436764 => 2
  | 2436768 => 2
  | 2436772 => 1
  | 2436776 => 1
  | 2436780 => 2
  | 2436876 => 1
  | 2436880 => 2
  | 2436884 => 1
  | 2436888 => 2
  | 2436928 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

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
   lo <= SP - 416 /\ SP <= 140737488355328)%Z.
Notation db_pair := DivBody.db_pair.
Definition db_al (wp TD VD rp TA VA : Z) : Prop :=
  (wp mod 8 = 0 /\ TD mod 8 = 0 /\ VD mod 8 = 0 /\ rp mod 8 = 0 /\ TA mod 8 = 0 /\ VA mod 8 = 0)%Z.
Definition db_nz (wp TD VD rp : Z) : Prop := (0 < wp /\ 0 < TD /\ 0 < VD /\ 0 < rp)%Z.
Local Ltac ub_unfold ::= unfold db_bndA, db_al, db_nz in *.

Lemma limbs_trA : forall W m m' A ls n, limbs_at bsegs m A ls -> munch W m m' -> Z.of_nat (length ls) = n ->
  disjoint_from W A (8 * n) -> limbs_at bsegs m' A ls.
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
  Variable c0 : list byte.
  Variables (c1 c2 c3 c4 c5 c6 c17 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 : word) (loopw : word).
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
  Notation FRAME wt iw wn :=
    [CB 8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6;
     C8 (Z_to_bv 64 (d1 mod 4294967296));       (* [comment removed for export] *)
     C8 (Z_to_bv 64 4294967295);                (* [comment removed for export] *)
     C8 (Z_to_bv 64 (Z.shiftr d1 32));          (* [comment removed for export] *)
     C8 (Z_to_bv 64 (dn + 1));                  (* [comment removed for export] *)
     C8 (Z_to_bv 64 d1);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
     C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
     C8 (Z_to_bv 64 (8 * dn));                  (* [comment removed for export] *)
     C8 (Z_to_bv 64 1);                         (* [comment removed for export] *)
     C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
     C8 c17;                                    (* [comment removed for export] *)
     C8 loopw;                                  (* [comment removed for export] *)
     C8 (Z_to_bv 64 (shad VA));                 (* [comment removed for export] *)
     C8 (Z_to_bv 64 wt);                        (* [comment removed for export] *)
     C8 (Z_to_bv 64 VA);
     C8 (Z_to_bv 64 iw);
     C8 (Z_to_bv 64 dn);
     C8 (Z_to_bv 64 wn);
     C8 c25; C8 c26; C8 c27; C8 c28; C8 c29; C8 c30; C8 c31; C8 c32; C8 c33; C8 c34; C8 c35; C8 c36; C8 c37].
  Notation WF := [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 416, bv_unsigned sp)]%Z.
  (* [comment removed for export] *)

  Hypothesis ACW : acc bsegs m0 wp (8 * (dn + 1)).
  Hypothesis ACT : acc bsegs m0 TD (8 * (dn + 1)).
  Hypothesis ACV : acc bsegs m0 VD (8 * dn).
  Hypothesis ACQ : acc bsegs m0 rp 8.
  Hypothesis ACTA : acc bsegs m0 TA 24.
  Hypothesis ACVA : acc bsegs m0 VA 24.
  Hypothesis SHB0 : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m0.
  Hypothesis OFFW : offshW WF.
  Hypothesis DG1 : disjoint_from WF g_GOT_shadow_offset_cell 8.
  Hypothesis DG2 : disjoint_from WF g_shadow_memory_dynamic_address 8.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  (* [comment removed for export] *)
  Hypothesis DNZ : db_nz wp TD VD rp.

  Definition BST (wt iw wn : Z) (mm : word -> option byte) (WIN TL RL : list Z) : Prop :=
    limbs_at bsegs mm wp WIN /\ limbs_at bsegs mm TD TL /\ limbs_at bsegs mm rp RL /\ limbs_at bsegs mm VD V /\
    wr_at bsegs mm wp (8 * (dn + 1)) /\ wr_at bsegs mm TD (8 * (dn + 1)) /\ wr_at bsegs mm rp 8 /\
    rw_cells bsegs mm TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4] /\
    rw_cells bsegs mm VA [C8 (Z_to_bv 64 VD); C4 va1; C4 va2; C4 va3; C4 va4] /\
    rw_cells bsegs mm (bv_unsigned sp + -304) (FRAME wt iw wn) /\
    stk bsegs mm lo (bv_unsigned sp + -304) /\ mem_inv bsegs mm /\
    munch WF m0 mm /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Notation LST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 d0) x19 (Z_to_bv 64 TA)
             (Z_to_bv 64 (shad TA)) x22 x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (8 * dn)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = (bv_unsigned sp + -304)%Z.
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
  Ltac ual := unfold db_nz in DNZ; unfold db_al in DAL; unfold db_bndA in DJB; clear - DNZ DAL DJB Hdn; lia.

  (* [comment removed for export] *)
  Lemma BST_store : forall wt iw wn mm WIN TL RL a w WIN' TL' RL',
    BST wt iw wn mm WIN TL RL ->
    ((wp <= a /\ a + 8 <= wp + 8 * (dn + 1)) \/ (TD <= a /\ a + 8 <= TD + 8 * (dn + 1)) \/ a = rp)%Z ->
    (let mm' := write_to_mem mm (Z_to_bv 64 a) (le8 w) in
     limbs_at bsegs mm' wp WIN' /\ limbs_at bsegs mm' TD TL' /\ limbs_at bsegs mm' rp RL' /\ limbs_at bsegs mm' VD V) ->
    store_ok bsegs mm (Z_to_bv 64 a) 8 = true /\
    BST wt iw wn (write_to_mem mm (Z_to_bv 64 a) (le8 w)) WIN' TL' RL'.
  Proof using DJB DJP Hdn.
    intros wt iw wn mm WIN TL RL a w WIN' TL' RL' B HA HL.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    cbv zeta in HL. destruct HL as (L1 & L2 & L3 & L4).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    unfold db_bndA in DJB.
    assert (L8 : length (le8 w) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bsegs mm (Z_to_bv 64 a) 8 = true).
    { change (Z_to_bv 64 a) with (wa a). destruct HA as [HA|[HA|HA]].
      - replace a with (wp + (a - wp))%Z by (clear; lia). apply (wr_at_store_ok bsegs mm wp (8 * (dn + 1))); [exact WW | clear - HA; lia | clear - HA; lia].
      - replace a with (TD + (a - TD))%Z by (clear; lia). apply (wr_at_store_ok bsegs mm TD (8 * (dn + 1))); [exact WT | clear - HA; lia | clear - HA; lia].
      - subst a. replace rp with (rp + 0)%Z by (clear; lia). apply (wr_at_store_ok bsegs mm rp 8); [exact WRs | clear; lia | clear; lia]. }
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
  Lemma BST_stack : forall wt iw wn mm m2 WIN TL RL a b,
    BST wt iw wn mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    (bv_unsigned sp - 416 <= a)%Z -> (b <= bv_unsigned sp + -304)%Z ->
    munch [(a, b)] mm m2 -> wmono bsegs mm m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -304) ->
    BST wt iw wn m2 WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt iw wn mm m2 WIN TL RL a b B HWl HTl HRl Ha Hb MUc WMc MIc STc.
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

  Local Ltac frame_slot_tac DJB Hdn HVl off FR OLD HWIN HTL HRL HVD WW WT WRs CTA CVA ST MI MU WM HWl HTl HRl :=
    let L8 := fresh "L8" in let SOK := fresh "SOK" in let A0 := fresh "A0" in
    lazymatch goal with |- store_ok _ ?mm (Z_to_bv 64 (bv_unsigned ?spv + ?k)) 8 = true /\ BST _ _ _ (write_to_mem _ _ (le8 (Z_to_bv 64 ?nw))) _ _ _ =>
      assert (L8 : length (le8 (Z_to_bv 64 nw)) = 8%nat) by apply length_le8;
      replace (bv_unsigned spv + k)%Z with (bv_unsigned spv + -304 + Z.of_nat off)%Z by (clear; lia);
      change (Z_to_bv 64 (bv_unsigned spv + -304 + Z.of_nat off)) with (wa (bv_unsigned spv + -304 + Z.of_nat off));
      assert (SOK : store_ok bsegs mm (wa (bv_unsigned spv + -304 + Z.of_nat off)) 8 = true)
        by (apply (rw_cells_store_ok bsegs mm _ _ off (C8 (Z_to_bv 64 OLD)) 8%nat FR); reflexivity);
      split; [exact SOK|];
      assert (A0 : (0 <= bv_unsigned spv + -304 + Z.of_nat off /\ bv_unsigned spv + -304 + Z.of_nat off + 8 <= bv_unsigned spv)%Z) by (clear - DJB Hdn; lia);
      unfold BST;
      split; [apply limbs_at_write_other; [exact HWIN | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8, HWl; clear - DJB Hdn; lia]|];
      split; [apply limbs_at_write_other; [exact HTL | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; clear - DJB Hdn HTl; lia]|];
      split; [apply limbs_at_write_other; [exact HRL | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; clear - DJB Hdn HRl; lia]|];
      split; [apply limbs_at_write_other; [exact HVD | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8, HVl; clear - DJB Hdn; lia]|];
      split; [apply wr_at_write; exact WW|];
      split; [apply wr_at_write; exact WT|];
      split; [apply wr_at_write; exact WRs|];
      split; [apply rw_cells_frame; [exact CTA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - DJB Hdn; lia]|];
      split; [apply rw_cells_frame; [exact CVA | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn; clear - DJB Hdn; lia]|];
      split; [exact (rw_cells_write bsegs mm _ _ off (C8 (Z_to_bv 64 OLD)) (C8 (Z_to_bv 64 nw)) FR eq_refl eq_refl I)|];
      split; [apply stk_write; [exact ST | clear - A0; lia | rewrite L8; clear - A0 DJB Hdn; lia]|];
      split; [apply mem_inv_store; [exact MI | rewrite L8; exact SOK]|];
      split; [apply munch_write; [exact MU | clear - A0; lia | rewrite L8; clear - A0 DJB; lia | rewrite L8; cbn [inside]; clear - A0 DJB Hdn; lia]|];
      apply wmono_write; exact WM
    end.

  Lemma BST_wt : forall wt wt' iw wn mm WIN TL RL,
    BST wt iw wn mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    store_ok bsegs mm (Z_to_bv 64 (bv_unsigned sp + -144)) 8 = true /\
    BST wt' iw wn (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + -144)) (le8 (Z_to_bv 64 wt'))) WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt wt' iw wn mm WIN TL RL B HWl HTl HRl.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold db_bndA in DJB.
    frame_slot_tac DJB Hdn HVl 160%nat FR wt HWIN HTL HRL HVD WW WT WRs CTA CVA ST MI MU WM HWl HTl HRl.
  Qed.
  Lemma BST_iw : forall wt iw iw' wn mm WIN TL RL,
    BST wt iw wn mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    store_ok bsegs mm (Z_to_bv 64 (bv_unsigned sp + -128)) 8 = true /\
    BST wt iw' wn (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + -128)) (le8 (Z_to_bv 64 iw'))) WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt iw iw' wn mm WIN TL RL B HWl HTl HRl.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold db_bndA in DJB.
    frame_slot_tac DJB Hdn HVl 176%nat FR iw HWIN HTL HRL HVD WW WT WRs CTA CVA ST MI MU WM HWl HTl HRl.
  Qed.
  Lemma BST_wn : forall wt iw wn wn' mm WIN TL RL,
    BST wt iw wn mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    store_ok bsegs mm (Z_to_bv 64 (bv_unsigned sp + -112)) 8 = true /\
    BST wt iw wn' (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + -112)) (le8 (Z_to_bv 64 wn'))) WIN TL RL.
  Proof using DJB DJP Hdn HVl.
    intros wt iw wn wn' mm WIN TL RL B HWl HTl HRl.
    destruct B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    unfold db_bndA in DJB.
    frame_slot_tac DJB Hdn HVl 192%nat FR wn HWIN HTL HRL HVD WW WT WRs CTA CVA ST MI MU WM HWl HTl HRl.
  Qed.

  Ltac ubnd := unfold db_bndA in DJB; clear - DJB Hdn; lia.

  (* [comment removed for export] *)
  Notation KQ mm v x19 x26 x27 :=
    (forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
       evt bsegs POST (LST 0x252d70 mm x1 x5 x6 x7 (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23 x26 x27
                           x28 x29 x30 x31)).

  (* [comment removed for export] *)
  Lemma qh_loop : forall (fuel : nat) wt iw wn mm q rem t2l t2h n2 x1 x5 x6 x7 x13 x14 x15 x17 x19 x26 x27 x28 x29 x30 x31,
    rw_cells bsegs mm (bv_unsigned sp + -304) (FRAME wt iw wn) ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= rem < 18446744073709551616)%Z ->
    (0 <= t2l < 18446744073709551616)%Z -> (0 <= t2h < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    (rem <= t2h)%Z -> (18446744073709551616 <= rem + Z.of_nat fuel * d0 - d0)%Z ->
    KQ mm (qhat_corr fuel q rem t2l t2h n2 d0 d1) x19 x26 x27 ->
    evt bsegs POST (LST 0x252d34 mm x1 x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) x13 x14 x15 (Z_to_bv 64 d1) x17
                        x19 (Z_to_bv 64 n2) (Z_to_bv 64 (addw rem d0)) x26 x27 x28 x29 x30 x31).
  Proof.
    induction fuel as [|f IH]; intros wt iw wn mm q rem t2l t2h n2 x1 x5 x6 x7 x13 x14 x15 x17 x19 x26 x27 x28 x29 x30 x31 FR Hq Hrem Ht2l Ht2h Hn2 HT HF K.
    { exfalso. clear - HF Hrem Hd0. lia. }
    pose proof (addw_lit rem d0) as R1.
    assert (B6e0 : (t2h <> rem \/ n2 < t2l)%Z ->
              evt bsegs POST (LST 0x252d40 mm x1 x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 d1) x17
                                  x19 (Z_to_bv 64 n2) (Z_to_bv 64 (addw rem d0)) x26 x27 x28 x29 x30 x31)).
    { intros HC.
      remember (addw rem d0) as rem1 eqn:Erem1.
      zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        do 2 zstep.
        rewrite (qhat_corr_exit2 f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        setreg 9%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        zstep.
        apply K.
      - (* [comment removed for export] *)
        do 6 zstep.
        rewrite (qhat_corr_cont f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        pose proof (subw_lit q 1) as Rq'. pose proof (subw_lit t2l d1) as Rl'. pose proof (t2h_step_lit t2l t2h d1 Ht2h) as Rh'.
        setreg 9%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        setreg 10%Z (Z_to_bv 64 (subw t2l d1)) ltac:(clear; weqm).
        setreg 12%Z (Z_to_bv 64 (if (t2l <? d1)%Z then subw t2h 1 else t2h)) ltac:(clear; destruct (t2l <? d1)%Z; cbn [Z.b2z]; weqm).
        setreg 11%Z (Z_to_bv 64 rem1) ltac:(clear - Erem1; subst rem1; weqm).
        setreg 23%Z (Z_to_bv 64 (addw rem1 d0)) ltac:(clear; weqm).
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
          setreg 9%Z (Z_to_bv 64 q') ltac:(clear - Eq'; subst q'; weqm).
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
  Lemma qh_block : forall wt iw wn mm q n1 n2 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x26 x27 x28 x29 x30 x31,
    rw_cells bsegs mm (bv_unsigned sp + -304) (FRAME wt iw wn) ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= n1 < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    KQ mm (qhat_corr QHAT_FUEL q (subw n1 (mulw q d0)) ((d1 * q) mod BW) ((d1 * q) / BW) n2 d0 d1) x19 x26 x27 ->
    evt bsegs POST (LST 0x252cc8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 n2) (Z_to_bv 64 n1) x26 x27
                        x28 x29 x30 x31).
  Proof.
    intros wt iw wn mm q n1 n2 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x26 x27 x28 x29 x30 x31 FR Hq Hn1 Hn2 K.
    do 22 zstep.
    pose proof (subw_lit n1 (mulw q d0)) as Rrem. pose proof (mod_BW_lit (d1 * q)) as Rl.
    pose proof (mul_hi_lit d1 q Hd1 Hq) as Rh.
    setreg 11%Z (Z_to_bv 64 (subw n1 (mulw q d0))) ltac:(clear; weqm).
    setreg 10%Z (Z_to_bv 64 ((d1 * q) mod BW)) ltac:(clear; weqm).
    setreg 12%Z (Z_to_bv 64 ((d1 * q) / BW)) ltac:(f_equal; rewrite (qh_t2h q d1 Hq Hd1); rewrite (Z.mul_comm d1 q); reflexivity).
    remember (subw n1 (mulw q d0)) as rem eqn:Erem. remember ((d1 * q) mod BW)%Z as t2l eqn:Et2l. remember ((d1 * q) / BW)%Z as t2h eqn:Et2h.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep.
      rewrite (qhat_corr_exit0 QHAT_FUEL q rem t2l t2h n2 d0 d1) in K by (clear - K0; lia).
      apply K.
    - do 4 zstep.
      setreg 23%Z (Z_to_bv 64 (addw rem d0)) ltac:(apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite (qh_s1 n1 d0 q), <- Erem;
                                                    apply Z.mod_small; apply addw_lit).
      eapply (qh_loop QHAT_FUEL); try eassumption.
      clear - Hd0 Rrem. unfold QHAT_FUEL. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_rd : forall wt iw wn mm WIN TL RL a n g ad,
    BST wt iw wn mm WIN TL RL -> acc bsegs m0 a n -> (g mod 8 = 0)%Z -> (a <= g)%Z -> (g + 8 <= a + n)%Z -> (0 <= g < 140737488355328)%Z ->
    ad = wa (shad g) -> ov_read_bytes bsegs mm ad 1 = Some [z8].
  Proof.
    intros wt iw wn mm WIN TL RL a n g ad (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _) AC G8 G1 G2 GR E.
    exact (acc_rd0 bsegs _ m0 mm a n g ad AC MU OFFW G8 G1 G2 GR E).
  Qed.
  Lemma al8 : forall p k, (p mod 8 = 0)%Z -> ((p + 8 * k) mod 8 = 0)%Z.
  Proof. intros p k H. Z.div_mod_to_equations. lia. Qed.
  Lemma al8m : forall p k j, (p mod 8 = 0)%Z -> ((p + 8 * k + -8 * j) mod 8 = 0)%Z.
  Proof. intros p k j H. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Ltac shchk_with B AC g Hal tac :=
    let ad := cur_mem_addr in let RD := fresh "RD" in
    pose proof (sh_rd _ _ _ _ _ _ _ _ _ g ad B AC Hal ltac:(tac) ltac:(tac) ltac:(tac) ltac:(sh_addr)) as RD; zstep; clear RD; chk0.
  Ltac shchk B AC g Hal := shchk_with B AC g Hal ltac:(bnd).

  (* [comment removed for export] *)
  Lemma db_qhat : forall iw mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31,
    BST (wp + 8 * dn) iw (wp + 8) mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) <= dn + 1 -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN ->
    nth_error WIN (Z.to_nat dn) = Some n0 -> nth_error WIN (Z.to_nat (dn - 1)) = Some n1 ->
    (dn = 1%Z /\ n2 = 0%Z \/ (2 <= dn)%Z /\ nth_error WIN (Z.to_nat (dn - 2)) = Some n2) ->
    (n0 <= d0)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
       BST (wp + 8 * dn + -8) iw (wp + 8) mm' WIN TL RL ->
       evt bsegs POST (LST 0x252d70 mm' x1 x5 x6 x7 (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1)) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23
                           (Z_to_bv 64 (shad (wp + 8 * dn))) (Z_to_bv 64 (wp + 8 * dn)) x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252c34 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23 x26 (Z_to_bv 64 (wp + 8 * dn))
                        x28 x29 x30 x31).
  Proof.
    intros iw mm WIN TL RL n0 n1 n2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 B HWl HTl HRl LW N0 N1 N2 Hn0 K.
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (apply nth_error_In in N0; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N0)).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (apply nth_error_In in N1; rewrite <- BW_lit; exact (proj1 (Forall_forall _ _) LW _ N1)).
    assert (R2 : (0 <= n2 < 18446744073709551616)%Z).
    { destruct N2 as [[_ ->]|[_ N2]]; [clear; lia|]. apply nth_error_In in N2. rewrite <- BW_lit. exact (proj1 (Forall_forall _ _) LW _ N2). }
    assert (BWP : (0 < wp /\ wp + 8 * dn + 8 <= 140737488355328)%Z) by ual.

    ub.
    do 2 zstep.
    setreg 26%Z (Z_to_bv 64 (shad (wp + 8 * dn))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    shchk B ACW (wp + 8 * dn)%Z (al8 wp dn AW8).

    ub.
    zstep.
    do 2 zstep.
    shchk B ACW (wp + 8 * dn + -8 * 1)%Z (al8m wp dn 1 AW8).
    (* [comment removed for export] *)
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs mm wp WIN (Z.to_nat dn) n0 ad HWIN N0 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.

    clear HWIN HTL HRL HVD WW WT WRs CTA CVA FR ST MI MU WM.
    destruct (BST_wt (wp + 8 * dn) (wp + 8 * dn + -8) iw (wp + 8) mm WIN TL RL B HWl HTl HRl) as [SOK B1].
    zstep. clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m1 eqn:Em1 end. clear Em1 B. try clear mm.
    pose proof B1 as (HWIN & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _).
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
      do 2 zstep.
      setreg 9%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_eq n0 d0) ltac:(clear - KE; lia)); clear; weqm).
      apply K. exact B1. }

    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs m1 wp WIN (Z.to_nat (dn - 1)) n1 ad HWIN N1 ltac:(unfold wa; f_equal; clear - Hdn; lia)) as RD.
    zstep. clear RD.
    zstep.
    assert (CONT : forall y11 y12 y22, y22 = Z_to_bv 64 n2 ->
              evt bsegs POST (LST 0x252cbc m1 x1 x5 x6 x7 x9 (Z_to_bv 64 n0) y11 y12 x13 x14 x15 x16 x17 x19 y22 (Z_to_bv 64 n1)
                                  (Z_to_bv 64 (shad (wp + 8 * dn))) (Z_to_bv 64 (wp + 8 * dn)) x28 x29 x30 x31)).
    { intros y11 y12 y22 ->.
      do 3 zstep.
      (* [comment removed for export] *)
      assert (E0 : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply unsigned_lit; clear - R0; lia).
      assert (E1 : bv_unsigned (Z_to_bv 64 n1) = n1) by (apply unsigned_lit; clear - R1; lia).
      assert (ED : bv_unsigned (Z_to_bv 64 d0) = d0) by (apply unsigned_lit; clear - Hd0; lia).
      pose proof ESP as ESPv.
      eapply evt_cut.
      { eapply bn_div_words_aspec with (lo := lo) (m := m1).
        - rewrite ED. clear - Hd0. lia.
        - rewrite E0, ED. clear - Hn0 KE. lia.
        - rewrite ESPv. exact ST.
        - rewrite ESPv. bnd.
        - exact MI. }
      intros ms' PO. unfold dvw_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
      subst ms'. rewrite E0, E1, ED, ESPv in *.
      replace (ret_pc (Z_to_bv 64 2436296)) with (Z_to_bv 64 2436296) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      assert (B2 : BST (wp + 8 * dn + -8) iw (wp + 8) m2 WIN TL RL).
      { eapply (BST_stack _ _ _ m1 m2 WIN TL RL); [exact B1 | exact HWl | exact HTl | exact HRl | | | exact MUc | exact WMc | exact MIc | exact STc].
        - clear. lia.
        - clear. lia. }
      pose proof B2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
      assert (Hq : (0 <= div_words n0 n1 d0 < 18446744073709551616)%Z) by (apply div_words_lit; [exact Hd0 | clear - R0 Hn0 KE; lia | exact R1]).
      eapply qh_block; [exact FR2 | exact Hq | exact R1 | exact R2 | ].
      intros y1 y5 y6 y7 y10 z11 z12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31.
      setreg 9%Z (Z_to_bv 64 (div_qhat n0 n1 n2 d0 d1))
        ltac:(unfold div_qhat; rewrite (proj2 (Z.eqb_neq n0 d0) KE); reflexivity).
      apply K. exact B2. }
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      zstep. apply CONT.
      destruct N2 as [[_ ->]|[N2 _]]; [reflexivity | exfalso; clear - KN N2 BWP; rewrite ?unsigned_lit in KN by lia; lia].
    - destruct N2 as [[N2 _]|[N2a N2]]; [exfalso; clear - KN N2 BWP; subst dn; apply KN; reflexivity|].

      ub.
      zstep.
      do 2 zstep.
      shchk_with B1 ACW (wp + 8 * dn + -8 * 2)%Z (al8m wp dn 2 AW8) ltac:(unfold db_bndA in DJB; clear - DJB Hdn N2a; lia).
      let ad := cur_mem_addr in
        pose proof (limbs_at_read_nth bsegs m1 wp WIN (Z.to_nat (dn - 2)) n2 ad HWIN N2 ltac:(unfold wa; f_equal; clear - N2a; lia)) as RD.
      zstep. clear RD.
      zstep. apply CONT. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma shb_mm : forall wt iw wn mm WIN TL RL, BST wt iw wn mm WIN TL RL -> shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address mm.
  Proof.
    intros wt iw wn mm WIN TL RL (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _).
    exact (shb_cells_munch bsegs _ _ _ m0 mm SHB0 MU DG1 DG2).
  Qed.
  Lemma acc_mm : forall wt iw wn mm WIN TL RL a n k n', BST wt iw wn mm WIN TL RL -> acc bsegs m0 a n ->
    (0 <= a + k /\ a + k + n' <= 140737488355328)%Z -> (0 <= k)%Z -> (k + n' <= n)%Z -> acc bsegs mm (a + k) n'.
  Proof.
    intros wt iw wn mm WIN TL RL a n k n' (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _) AC B Hk Hle.
    apply (acc_tr bsegs _ m0 mm a n k n' AC MU OFFW); [intros _; exact B | exact Hk | exact Hle].
  Qed.
  Lemma offsh_T : (TD + 8 * (dn + 1) <= SHLO \/ SHHI <= TD)%Z.
  Proof. cbn [offshW] in OFFW. tauto. Qed.
  Lemma offsh_W : (wp + 8 * (dn + 1) <= SHLO \/ SHHI <= wp)%Z.
  Proof. cbn [offshW] in OFFW. tauto. Qed.

  (* [comment removed for export] *)
  Lemma db_mul : forall wt iw wn mm WIN TL RL q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x27 x28 x29 x30 x31,
    BST wt iw wn mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z -> (0 <= q < 18446744073709551616)%Z ->
    (forall mm' x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       BST wt iw wn mm' WIN (fst (mul_words V q) ++ [snd (mul_words V q)]) RL ->
       evt bsegs POST (LST 0x252df8 mm' x1 x5 x6 x7 (Z_to_bv 64 q) x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23 x26 x27
                           x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252d70 mm x1 x5 x6 x7 (Z_to_bv 64 q) x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23 x26 x27 x28 x29 x30 x31).
  Proof.
    intros wt iw wn mm WIN TL RL q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x27 x28 x29 x30 x31 B HWl HRl Hq K.
    pose proof (shb_mm _ _ _ _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACTm : acc bsegs mm TD (8 * dn)).
    { pose proof (acc_mm _ _ _ mm WIN TL RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACVm : acc bsegs mm VD (8 * dn)).
    { pose proof (acc_mm _ _ _ mm WIN TL RL VD (8 * dn) 0 (8 * dn) B ACV) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (BTD : (0 < TD /\ TD + 8 * dn + 8 <= 140737488355328 /\ 0 < VD /\ 0 <= TA /\ TA + 24 <= 140737488355328 /\ 0 <= VA /\ VA + 24 <= 140737488355328)%Z) by ual.

    ub.
    shchk B ACTA TA ATA8.
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
      - rewrite ETD, HVl. apply (wr_at_sub bsegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - rewrite ETD, EVD, HVl. unfold alias_ok. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia.
      - rewrite ESPv. exact ST.
      - rewrite ESPv. bnd.
      - rewrite ETD, ESPv, HVl. bnd.
      - rewrite EVD, ESPv, HVl. bnd.
      - exact MI.
      - exact SHm.
      - rewrite ETD, HVl. exact ACTm.
      - rewrite EVD, HVl. exact ACVm.
      - rewrite ETD, EVD, HVl. unfold aptrs3. split; [exact AT8|]. split; [exact AV8|]. split; [exact AV8|]. split; [clear - OT Hdn; lia | exact SHLO_LO].
      - rewrite ETD. unfold ub_ptr_ok. intros _. split; [clear - BTD; lia | exact AT8].
      - rewrite EVD. unfold ub_ptr_ok. intros _. split; [clear - BTD; lia | exact AV8]. }
    intros ms' PO. unfold mw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ETD, EQ, ESPv, HVl in *.
    replace (ret_pc (Z_to_bv 64 2436516)) with (Z_to_bv 64 2436516) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (HWIN2 : limbs_at bsegs m2 wp WIN).
    { eapply limbs_trA; [exact HWIN | exact MUc | exact HWl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bsegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at bsegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P7 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P9 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call bsegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    pose proof (mul_words_length V q) as Lml.
    assert (B2 : BST wt iw wn m2 WIN (fst (mul_words V q)) RL).
    { unfold BST. repeat (split; [assumption|]). assumption. }
    clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 OT.
    assert (BT : (0 <= TD /\ TD + 8 * dn + 8 <= 140737488355328)%Z) by bnd.
    shchk B2 ACTA TA ATA8.
    do 3 zstep.

    ub. zstep. ub.
    do 2 zstep.
    shchk B2 ACT (TD + 8 * dn)%Z (al8 TD dn AT8).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    destruct (BST_store wt iw wn m2 WIN (fst (mul_words V q)) RL (TD + 8 * dn) (Z_to_bv 64 (snd (mul_words V q)))
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
  Lemma db_sub : forall wt iw mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x23 x26 x27 x28 x29 x30 x31,
    BST wt iw (wp + 8) mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TL) = (dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> limbs TL ->
    (forall mm' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       BST wt iw wp mm' (fst (sub_words WIN TL)) TL RL ->
       evt bsegs POST (LST 0x252e20 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) (Z_to_bv 64 (snd (sub_words WIN TL))) x26 x27
                           x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252df8 mm x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 TD) x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) x23 x26 x27 x28 x29 x30 x31).
  Proof.
    intros wt iw mm WIN TL RL x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x23 x26 x27 x28 x29 x30 x31 B HWl HTl HRl LW LT K.
    pose proof (shb_mm _ _ _ _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACWm : acc bsegs mm wp (8 * (dn + 1))).
    { pose proof (acc_mm _ _ _ mm WIN TL RL wp (8 * (dn + 1)) 0 (8 * (dn + 1)) B ACW) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc bsegs mm TD (8 * (dn + 1))).
    { pose proof (acc_mm _ _ _ mm WIN TL RL TD (8 * (dn + 1)) 0 (8 * (dn + 1)) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (RWP : (0 < wp /\ wp + 8 * (dn + 1) <= 140737488355328 /\ 0 < TD)%Z) by ual.

    ub.
    zstep.
    zstep. replace (wp + 8 + -8)%Z with wp by (clear; lia).
    clear HWIN HTL HRL HVD WW WT WRs CTA CVA FR ST MI MU WM ACWm ACTm SHm.
    destruct (BST_wn wt iw (wp + 8) wp mm WIN TL RL B HWl ltac:(clear - HTl; lia) HRl) as [SOK B1].
    zstep. clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m1 eqn:Em1 end. clear Em1 B. try clear mm.
    pose proof (shb_mm _ _ _ _ _ _ _ B1) as SHm.
    assert (ACWm : acc bsegs m1 wp (8 * (dn + 1))).
    { pose proof (acc_mm _ _ _ m1 WIN TL RL wp (8 * (dn + 1)) 0 (8 * (dn + 1)) B1 ACW) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc bsegs m1 TD (8 * (dn + 1))).
    { pose proof (acc_mm _ _ _ m1 WIN TL RL TD (8 * (dn + 1)) 0 (8 * (dn + 1)) B1 ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B1 as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    do 3 zstep.
    assert (EWP : bv_unsigned (Z_to_bv 64 wp) = wp) by (apply ulit; bnd).
    assert (ETD : bv_unsigned (Z_to_bv 64 TD) = TD) by (apply ulit; bnd).
    assert (EDN : bv_unsigned (Z_to_bv 64 (dn + 1)) = (dn + 1)%Z) by (apply ulit; bnd).
    pose proof ESP as ESPv.
    pose proof offsh_W as OW.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    assert (LEN : length TL = length WIN) by (clear - HWl HTl; lia).
    eapply evt_cut.
    { eapply bn_sub_words_aspec with (a := WIN) (b := TL) (lo := lo) (m := m1).
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
      - rewrite EWP, ETD, HWl. unfold aptrs3. split; [exact AW8|]. split; [exact AW8|]. split; [exact AT8|]. split; [clear - OW Hdn; lia | exact SHLO_LO].
      - rewrite EWP. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AW8].
      - rewrite EWP. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AW8].
      - rewrite ETD. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AT8]. }
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 2436636)) with (Z_to_bv 64 2436636) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HTL2 : limbs_at bsegs m2 TD TL).
    { eapply limbs_trA; [exact HTL | exact MUc | exact HTl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bsegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at bsegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWIN HVD HRL HTL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call bsegs m1 m2 MUc WMc.
    clear MUc WMc MI. try clear m1.
    zstep.
    apply K. unfold BST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Section Mask.
    Variables (mk : word -> option byte) (msk wt iw wn : Z).
    Hypothesis Hmsk : (0 <= msk < 18446744073709551616)%Z.
    Hypothesis ACVk : acc bsegs mk VD (8 * Z.of_nat (length V)).
    Hypothesis ACTk : acc bsegs mk TD (8 * Z.of_nat (length V)).
    Hypothesis ACTAk : acc bsegs mk TA 24.
    Hypothesis CTAK : forall m', munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 304, bv_unsigned sp)]%Z mk m' -> wmono bsegs mk m' ->
      rw_cells bsegs m' TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4].
    Lemma MLEN : length V = length V. Proof. reflexivity. Qed.
    Lemma MFBE : (bv_unsigned sp + -304 = bv_unsigned sp - 304)%Z. Proof. lia. Qed.
    Lemma MALA : alias_ok TD VD (Z.of_nat (length V)).
    Proof. unfold alias_ok. rewrite HVl. pose proof DJP as (_ & _ & _ & _ & _ & P & _). clear - P Hdn. lia. Qed.
    Lemma MSEPR : (TD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 304 \/ bv_unsigned sp <= TD)%Z.
    Proof. rewrite HVl. left. bnd. Qed.
    Lemma MSEPA : (VD + 8 * Z.of_nat (length V) <= bv_unsigned sp - 304 \/ bv_unsigned sp <= VD)%Z.
    Proof. rewrite HVl. left. bnd. Qed.
    Notation MRES := (map (fun x => Z.land x msk) V).
    Notation KINV := (INV bsegs (mk_fl msk) (mk_fc msk) 0 mk TD VD VD (bv_unsigned sp) lo V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn) MRES 0%Z).
    Notation KIT L := (L bsegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mk TD VD VD (bv_unsigned sp) lo V V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn) eq_refl MFBE
                          MLEN MALA MALA MSEPR MSEPA MSEPA MRES 0%Z).
    Notation K_rdA := (KIT INV_rdA).
    Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
    Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
    Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).
    Notation PBm := (apure TD VD VD (Z.of_nat (length V)) (bv_unsigned sp) 304%Z).
    Notation K_shA := (INV_shA bsegs (mk_fl msk) (mk_fc msk) 0%Z mk TD VD VD (bv_unsigned sp) lo V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn) MRES 0%Z).
    Notation K_shR := (INV_shR bsegs (mk_fl msk) (mk_fc msk) 0%Z mk TD VD VD (bv_unsigned sp) lo V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn) MRES 0%Z).
    Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
    Ltac w64eq := unfold DivBody.mk_fl; reflexivity.
    Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
    Ltac mshA P I := let L := constr:(K_shA P) in ld_sh_with L I ACVk 0%nat; chk0.
    Ltac mshR P I := let L := constr:(K_shR P) in ld_sh_with L I ACTk 0%nat; chk0.

    Lemma mask_loop : forall la m1 pre c pa pr x1 x5 x6 x7 x9 x11 x17 x19 x22 x23 x26 x27 x28 x29 x30 x31,
      PBm -> la <> [] -> KINV m1 pre la la c pa pa pr ->
      (forall m2 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17,
         limbs_at bsegs m2 TD MRES -> rw_cells bsegs m2 (bv_unsigned sp + -304) (FRAME wt iw wn) -> stk bsegs m2 lo (bv_unsigned sp + -304) -> mem_inv bsegs m2 ->
         munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 304, bv_unsigned sp)]%Z mk m2 -> wmono bsegs mk m2 ->
         evt bsegs POST (LST 0x252edc m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x27 x28 x29 x30 x31)) ->
      evt bsegs POST (LST 0x252e58 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 pa) x11 (Z_to_bv 64 (pa - VD)) (Z_to_bv 64 VD) (Z_to_bv 64 msk) (Z_to_bv 64 1) (Z_to_bv 64 1) x17
                          x19 x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      induction la as [|x la IH]; intros m1 pre c pa pr x1 x5 x6 x7 x9 x11 x17 x19 x22 x23 x26 x27 x28 x29 x30 x31 P NE I K; [congruence|].
      pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
      pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TOP64).
      pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx.
      pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
      assert (RPA : (0 < VD /\ VD <= pa /\ pa + 8 <= VD + 8 * dn /\ pa - VD = pr - TD /\ 0 < TD /\ TD + 8 * (dn + 1) <= 140737488355328 /\
                     VD + 8 * dn <= 140737488355328 /\ TD mod 8 = 0 /\ VD mod 8 = 0 /\ (pa - VD) mod 8 = 0 /\ 0 <= TA /\ TA + 24 <= 140737488355328)%Z).
      { cbn [length] in *. rewrite HVl in *. unfold db_nz in DNZ. unfold db_bndA in DJB. clear - DNZ AT8 AV8 DJB Hdn Epa Epr En.
        assert ((8 * Z.of_nat (length pre)) mod 8 = 0)%Z by (rewrite Z.mul_comm; apply Z.mod_mul; lia).
        replace (pa - VD)%Z with (8 * Z.of_nat (length pre))%Z by lia. lia. }
      pose proof I as (_ & _ & _ & _ & _ & _ & _ & MUI & WMI & _).
      pose proof (CTAK m1 MUI WMI) as CTA.

      ub.

      do 2 zstep. mshA P I.
      (let ad := cur_mem_addr in
       pose proof (acc_rd0 bsegs _ mk m1 TA 24 TA ad ACTAk MUI (apure_off _ _ _ _ _ _ P) ATA8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - RPA; lia) ltac:(sh_addr)) as RD;
       zstep; clear RD; chk0).
      clear MUI WMI.

      zstep. clear CTA.
      zstep. replace (TD + (pa - VD))%Z with pr by (clear - RPA; lia).

      ub.

      do 2 zstep. mshR P I.
      zstep. replace (VD + (pa - VD))%Z with pa by (clear; lia).
      ldA I.
      do 2 zstep.
      st_limb I l c' Ec'. clear Ec'.
      zstep.
      replace (pa - VD + 8)%Z with (pa + 8 - VD)%Z by (clear; lia).
      zstep. if_cases KB; zify_cond KB.
      - (* [comment removed for export] *)
        eapply IH; [ exact P | | exact I | exact K ].
        destruct la; [ exfalso | discriminate ].
        pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *.
        clear - KB En2 Epr2 HVl RPA. lia.
      - (* [comment removed for export] *)
        destruct la as [|x' la'].
        + pose proof (K_done _ _ _ _ _ _ I) as (HP & CYE & FR & ST & MI & MU & WM).
          apply K; assumption.
        + exfalso. pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa2 & _).
          cbn [length] in *. clear - KB En2 Epr2 HVl RPA. lia.
    Qed.
  End Mask.

  (* [comment removed for export] *)
  Lemma db_mask : forall wt iw wn mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x27 x28 x29 x30 x31,
    BST wt iw wn mm WIN (TLp ++ [tl]) RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    (0 <= bw <= 1)%Z ->
    (forall mm' x5 x6 x10 x11 x12 x13 x14 x15 x16 x17,
       BST wt iw wn mm' WIN (map (fun x => Z.land x (negw bw)) V ++ [tl]) RL ->
       evt bsegs POST (LST 0x252edc mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) (Z_to_bv 64 bw) x26 x27 x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252e20 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1)) (Z_to_bv 64 bw) x26 x27 x28 x29 x30 x31).
  Proof.
    intros wt iw wn mm WIN TLp tl RL bw x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x27 x28 x29 x30 x31 B HWl HTl HRl Hbw K.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACVm : acc bsegs mm VD (8 * Z.of_nat (length V))).
    { rewrite HVl. pose proof (acc_mm _ _ _ mm WIN _ RL VD (8 * dn) 0 (8 * dn) B ACV) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc bsegs mm TD (8 * Z.of_nat (length V))).
    { rewrite HVl. pose proof (acc_mm _ _ _ mm WIN _ RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTAm : acc bsegs mm TA 24).
    { pose proof (acc_mm _ _ _ mm WIN _ RL TA 24 0 24 B ACTA) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (PBm : apure TD VD VD (Z.of_nat (length V)) (bv_unsigned sp) 304%Z).
    { rewrite HVl. pose proof offsh_T as OT. unfold apure. split; [tauto|]. split; [bnd|]. split; [bnd|]. split; [bnd|].
      cbn [offshW]. split; [clear - OT Hdn; lia|]. split; [right; unfold db_bndA in DJB; clear - DJB SHLO_LO; lia | exact I]. }
    assert (RVD : (0 < VD /\ VD + 8 * dn <= 140737488355328 /\ VD mod 8 = 0 /\ 0 <= VA /\ VA + 24 <= 140737488355328)%Z) by ual.
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    { exfalso. clear - KZ Hdn. destruct (Z.ltb_spec 0 dn); [|lia]. destruct (Z.ltb_spec dn 9223372036854775808); [discriminate | lia]. }
    try clear KZ.
    zstep. shchk B ACVA VA AVA8.
    zstep. do 2 zstep.
    zstep. setreg 14%Z (Z_to_bv 64 (negw bw)) ltac:(clear; unfold negw; weqm).
    zstep. replace (0 <? VD)%Z with true by (symmetry; apply Z.ltb_lt; clear - RVD; lia). cbn [Z.b2z].
    zstep. rewrite (land7 VD) by (clear - RVD; lia).
    zstep. cbn [Z.ltb Z.compare Z.b2z].
    do 2 zstep.
    setreg 16%Z (Z_to_bv 64 1) ltac:(reflexivity).
    assert (Hmsk : (0 <= negw bw < 18446744073709551616)%Z) by apply negw_limb.
    remember (negw bw) as msk eqn:Emsk.
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    apply limbs_at_app in HTL. destruct HTL as [HTLp HTLl].
    assert (ETL : (TD + 8 * Z.of_nat (length TLp) = TD + 8 * dn)%Z) by (rewrite HTl; reflexivity). rewrite ETL in HTLl. clear ETL.
    assert (I : INV bsegs (mk_fl msk) (mk_fc msk) 0 mm TD VD VD (bv_unsigned sp) lo V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn)
                    (map (fun x => Z.land x msk) V) 0%Z mm [] V V 0 VD VD TD).
    { apply (INV_init bsegs (mk_fl msk) (mk_fc msk) 0%Z (mk_fc_range msk) mm TD VD VD (bv_unsigned sp) lo V V 304%Z (bv_unsigned sp + -304)%Z (FRAME wt iw wn) eq_refl MFBE
                          MLEN MALA MALA MSEPR MSEPA MSEPA); try assumption.
      - rewrite HVl. clear - Hdn. lia.
      - clear. lia.
      - rewrite HVl. apply (wr_at_sub bsegs mm TD (8 * (dn + 1)) 0 (8 * dn)) in WT; [rewrite Z.add_0_r in WT; exact WT | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
      - apply munch_refl.
      - apply munch_refl.
      - apply wmono_refl.
      - rewrite mask_gen. reflexivity.
      - rewrite mask_gen. reflexivity. }
    assert (CTAK : forall m', munch [(TD, TD + 8 * Z.of_nat (length V)); (bv_unsigned sp - 304, bv_unsigned sp)]%Z mm m' -> wmono bsegs mm m' ->
              rw_cells bsegs m' TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4]).
    { intros m' MU' WM'. eapply rw_cells_transport; [exact CTA | exact MU' | exact WM' |]. cbn. rewrite HVl. unfold db_bndA in DJB. clear - DJB P8 Hdn. lia. }
    eapply evt_eq; [ | eapply (mask_loop mm msk wt iw wn Hmsk ACVm ACTm ACTAm CTAK V mm [] 0 VD TD); [ exact PBm | | exact I | ] ].
    { replace (VD - VD)%Z with 0%Z by (clear; lia). reflexivity. }
    { destruct V; [ exfalso; cbn [length] in HVl; clear - HVl Hdn; lia | discriminate ]. }
    intros m2 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 HP FR2 ST2 MI2 MUk WMk. rewrite HVl in MUk.
    assert (HWIN2 : limbs_at bsegs m2 wp WIN).
    { eapply limbs_trA; [exact HWIN | exact MUk | exact HWl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bsegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUk | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P6 Hdn. lia. }
    assert (HRL2 : limbs_at bsegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUk | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P7 Hdn HRl. lia. }
    assert (HTLl2 : limbs_at bsegs m2 (TD + 8 * dn) [tl]).
    { eapply limbs_trA; [exact HTLl | exact MUk | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB Hdn. lia. }
    assert (HTL2 : limbs_at bsegs m2 TD (map (fun x => Z.land x msk) V ++ [tl])).
    { apply limbs_at_app. split; [exact HP|]. rewrite length_map, HVl. exact HTLl2. }
    clear HWIN HVD HRL HTLp HTLl HTLl2 HP ST FR I CTAK.
    tr_cells CTA MUk WMk ltac:(unfold db_bndA in DJB; clear - DJB P8 Hdn; lia).
    tr_cells CVA MUk WMk ltac:(unfold db_bndA in DJB; clear - DJB P9 Hdn; lia).
    transport_after_call bsegs mm m2 MUk WMk.
    clear MUk WMk MI. try clear mm.
    apply K. unfold BST. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma db_add : forall fwt mm WINp wtop TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    BST fwt i wp mm (WINp ++ [wtop]) (TLp ++ [tl]) RL -> Z.of_nat (length WINp) = dn -> Z.of_nat (length TLp) = dn -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WINp -> limbs TLp -> (0 <= wtop < 18446744073709551616)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
       BST fwt (i + 1) wp mm' (fst (add_words WINp TLp) ++ [addw wtop (snd (add_words WINp TLp))]) (TLp ++ [tl]) [subw q bw] ->
       evt bsegs POST (LST 0x252c24 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 rp) (Z_to_bv 64 (dn + 1)) x23 x26 x27 x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252edc mm x1 x5 x6 x7 (Z_to_bv 64 q) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (rp + 8)) (Z_to_bv 64 (dn + 1)) (Z_to_bv 64 bw)
                        (Z_to_bv 64 (shad (wp + 8 * dn))) (Z_to_bv 64 (wp + 8 * dn)) x28 x29 x30 x31).
  Proof.
    intros fwt mm WINp wtop TLp tl RL bw q i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 B HWl HTl HRl LW LT Hwt Hi K.
    pose proof (shb_mm _ _ _ _ _ _ _ B) as SHm.
    pose proof DAL as (AW8 & AT8 & AV8 & AR8 & ATA8 & AVA8).
    assert (ACWm : acc bsegs mm wp (8 * dn)).
    { pose proof (acc_mm _ _ _ mm _ _ RL wp (8 * (dn + 1)) 0 (8 * dn) B ACW) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    assert (ACTm : acc bsegs mm TD (8 * dn)).
    { pose proof (acc_mm _ _ _ mm _ _ RL TD (8 * (dn + 1)) 0 (8 * dn) B ACT) as X. rewrite Z.add_0_r in X. apply X; bnd. }
    pose proof B as (HWIN & HTL & HRL & HVD & WW & WT & WRs & CTA & CVA & FR & ST & MI & MU & WM).
    assert (RWP : (0 < wp /\ wp + 8 * dn + 8 <= 140737488355328 /\ 0 < TD /\ 0 < rp /\ rp + 8 <= 140737488355328 /\ 0 <= TA /\ TA + 24 <= 140737488355328)%Z) by ual.
    shchk B ACTA TA ATA8.
    do 2 zstep. do 3 zstep.
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
      - rewrite EWP, HWl. apply (wr_at_sub bsegs mm wp (8 * (dn + 1)) 0 (8 * dn)) in WW; [rewrite Z.add_0_r in WW; exact WW | clear; lia | clear - Hdn; lia | clear - Hdn; lia].
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
      - rewrite EWP, ETD, HWl. unfold aptrs3. split; [exact AW8|]. split; [exact AW8|]. split; [exact AT8|]. split; [clear - OW Hdn; lia | exact SHLO_LO].
      - rewrite EWP. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AW8].
      - rewrite EWP. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AW8].
      - rewrite ETD. unfold ub_ptr_ok. intros _. split; [clear - RWP; lia | exact AT8]. }
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EWP, ESPv, HWl in *.
    replace (ret_pc (Z_to_bv 64 2436856)) with (Z_to_bv 64 2436856) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (HWt2 : limbs_at bsegs m2 (wp + 8 * dn) [wtop]).
    { eapply limbs_trA; [exact HWt | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB Hdn. lia. }
    assert (HTp2 : limbs_at bsegs m2 TD TLp).
    { eapply limbs_trA; [exact HTp | exact MUc | exact HTl | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HTt2 : limbs_at bsegs m2 (TD + 8 * dn) [tl]).
    { eapply limbs_trA; [exact HTt | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P1 Hdn. lia. }
    assert (HVD2 : limbs_at bsegs m2 VD V).
    { eapply limbs_trA; [exact HVD | exact MUc | exact HVl | ]. cbn. unfold db_bndA in DJB. clear - DJB P2 Hdn. lia. }
    assert (HRL2 : limbs_at bsegs m2 rp RL).
    { eapply limbs_trA; [exact HRL | exact MUc | reflexivity | ]. cbn. unfold db_bndA in DJB. clear - DJB P3 Hdn HRl. lia. }
    clear HWp HWt HTp HTt HVD HRL ST.
    tr_cells CTA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P4 Hdn; lia).
    tr_cells CVA MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB P5 Hdn; lia).
    tr_cells FR MUc WMc ltac:(unfold db_bndA in DJB; clear - DJB Hdn; lia).
    transport_after_call bsegs mm m2 MUc WMc.
    clear MUc WMc MI. try clear mm.
    pose proof (add_words_spec WINp TLp LW LT ltac:(clear - LEN; lia)) as AS.
    pose proof (add_words_length WINp TLp) as Lal.
    destruct (add_words WINp TLp) as [al cy]. cbn [fst snd] in *. destruct AS as (_ & Lal2 & Hcy & _).
    assert (B2 : BST fwt i wp m2 (al ++ [wtop]) (TLp ++ [tl]) RL).
    { unfold BST.
      split. { apply limbs_at_app. split; [exact HR|]. rewrite Lal2, HWl. exact HWt2. }
      split. { apply limbs_at_app. split; [exact HTp2|]. rewrite HTl. exact HTt2. }
      repeat (split; [assumption|]). assumption. }
    clear P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 OW.
    assert (BW : (0 <= wp /\ wp + 8 * dn + 8 <= 140737488355328 /\ 8 <= rp + 8 /\ rp + 8 <= 140737488355328)%Z) by bnd.
    (* [comment removed for export] *)
    shchk B2 ACW (wp + 8 * dn)%Z (al8 wp dn AW8).
    ld_hd HWt2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw wtop cy)) ltac:(clear; weqm).
    pose proof DJP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    destruct (BST_store fwt i wp m2 (al ++ [wtop]) (TLp ++ [tl]) RL (wp + 8 * dn) (Z_to_bv 64 (addw wtop cy))
                (al ++ [addw wtop cy]) (TLp ++ [tl]) RL B2) as [SOK B3].
    { left. clear - Hdn. lia. }
    { cbv zeta. unfold db_bndA in DJB.
      assert (L8 : length (le8 (Z_to_bv 64 (addw wtop cy))) = 8%nat) by apply length_le8.
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
    pose proof B3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR3 & _).

    ub.
    clear FR3.
    zstep. replace (rp + 8 + -8)%Z with rp by (clear; lia).
    do 2 zstep.
    shchk B3 ACQ rp AR8.
    zstep. setreg 11%Z (Z_to_bv 64 (subw q bw)) ltac:(clear; weqm).
    pose proof B3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR3 & _).
    zstep. clear FR3.
    zstep. rewrite (bn_swrap32_small (i + 1)) by (clear - Hi; lia).
    destruct (BST_store fwt i wp m3 (al ++ [addw wtop cy]) (TLp ++ [tl]) RL rp (Z_to_bv 64 (subw q bw))
                (al ++ [addw wtop cy]) (TLp ++ [tl]) [subw q bw] B3) as [SOK B4].
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
               apply (limbs_at_snoc_write bsegs m3 rp [] (subw q bw)); [apply limbs_at_nil; clear - DJB Hdn; lia | cbn [length]; clear - DJB Hdn; lia]. }
      apply limbs_at_write_other; [exact HVD | clear - DJB Hdn; lia | rewrite L8; clear - DJB Hdn; lia | rewrite L8, HVl; clear - P10 Hdn; lia]. }
    clear P3 P7 P10.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m4 end.
    clear B3 SOK. try clear m3.

    ub.

    destruct (BST_iw fwt i (i + 1) wp m4 (al ++ [addw wtop cy]) (TLp ++ [tl]) [subw q bw] B4
                ltac:(rewrite length_app, Nat2Z.inj_add, Lal2, HWl; cbn [length]; clear; lia)
                ltac:(rewrite length_app, Nat2Z.inj_add, HTl; cbn [length]; clear; lia)
                ltac:(cbn [length]; clear; lia)) as [SOK B5].
    zstep. clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m5 eqn:Em5 end. clear Em5 B4. try clear m4.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    - apply K. exact B5.
    - exfalso. clear - KB BW Hdn. rewrite ?unsigned_lit in KB by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sc_win (WIN : list Z) : list Z := fst (fst (fst (step_core V d0 d1 WIN))).
  Definition sc_tmp (WIN : list Z) : list Z :=
    snd (fst (step_core V d0 d1 WIN)) ++ skipn (length V) (snd (fst (fst (step_core V d0 d1 WIN)))).
  Definition sc_q (WIN : list Z) : Z := snd (step_core V d0 d1 WIN).

  Lemma db_body : forall mm WIN TL RL i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31,
    BST (wp + 8 * dn) i (wp + 8) mm WIN TL RL -> Z.of_nat (length WIN) = (dn + 1)%Z -> (Z.of_nat (length TL) <= dn + 1)%Z -> (Z.of_nat (length RL) <= 1)%Z ->
    limbs WIN -> (nth (length V) WIN 0 <= d0)%Z -> (0 <= i < 2147483647)%Z ->
    (forall mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
       BST (wp + 8 * dn + -8) (i + 1) wp mm' (sc_win WIN) (sc_tmp WIN) [sc_q WIN] ->
       evt bsegs POST (LST 0x252c24 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 rp) (Z_to_bv 64 (dn + 1)) x23 x26 x27 x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252c34 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (rp + 8)) (Z_to_bv 64 (dn + 1)) x23 x26 (Z_to_bv 64 (wp + 8 * dn))
                        x28 x29 x30 x31).
  Proof.
    intros mm WIN TL RL i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 B HWl HTl HRl LW Hn0 Hi K.
    assert (EV : length V = Z.to_nat dn) by (clear - HVl; lia).
    assert (EW : length WIN = S (Z.to_nat dn)) by (clear - HWl Hdn; lia).
    set (n0 := nth (length V) WIN 0%Z) in *.
    set (n1 := nth (length V - 1) WIN 0%Z).
    set (n2 := if (length V =? 1)%nat then 0%Z else nth (length V - 2) WIN 0%Z).
    assert (R0 : (0 <= n0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    assert (R1 : (0 <= n1 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LW).
    eapply (db_qhat i mm WIN TL RL n0 n1 n2); try eassumption.
    { subst n0. rewrite EV. apply nth_error_nth0. clear - EW. lia. }
    { subst n1. rewrite EV. replace (Z.to_nat (dn - 1)) with (Z.to_nat dn - 1)%nat by (clear - Hdn; lia). apply nth_error_nth0. clear - EW. lia. }
    { subst n2. rewrite EV. destruct (Nat.eqb_spec (Z.to_nat dn) 1) as [E1|NE1].
      - left. split; [clear - E1 Hdn; lia | reflexivity].
      - right. split; [clear - NE1 Hdn; lia|]. replace (Z.to_nat (dn - 2)) with (Z.to_nat dn - 2)%nat by (clear - Hdn; lia).
        apply nth_error_nth0. clear - EW. lia. }
    intros m1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 B1.
    pose proof (div_qhat_lit n0 n1 n2 d0 d1 Hd0 ltac:(clear - R0 Hn0; lia) R1) as Rq.
    set (q := div_qhat n0 n1 n2 d0 d1) in *.
    eapply (db_mul _ _ _ m1 WIN TL RL q); try eassumption.
    intros m2 z1 z5 z6 z7 z10 z11 z13 z14 z15 z16 z17 z28 z29 z30 z31 B2.
    pose proof (mul_words_spec V q HV ltac:(unfold limb; rewrite BW_lit; exact Rq)) as MS.
    pose proof (mul_words_length V q) as Lml.
    destruct (mul_words V q) as [ml l0] eqn:EMW. cbn [fst snd] in *. destruct MS as (Lml1 & _ & Ll0 & _).
    assert (LT1 : limbs (ml ++ [l0])) by (apply limbs_app; [exact Lml1 | apply limbs_cons; [exact Ll0 | apply limbs_nil]]).
    assert (HT1 : Z.of_nat (length (ml ++ [l0])) = (dn + 1)%Z) by (rewrite length_app, Lml; cbn [length]; clear - HVl; lia).
    eapply (db_sub _ _ m2 WIN (ml ++ [l0]) RL); try eassumption.
    intros m3 u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 B3.
    pose proof (sub_words_spec WIN (ml ++ [l0]) LW LT1 ltac:(clear - HWl HT1; lia)) as SS.
    destruct (sub_words WIN (ml ++ [l0])) as [sl bw] eqn:ESW. cbn [fst snd] in *. destruct SS as (Lsl & Lsl2 & Hbw & _).
    eapply (db_mask _ _ _ m3 sl ml l0 RL bw); try eassumption.
    { rewrite Lsl2. exact HWl. }
    { rewrite Lml. exact HVl. }
    intros m4 v5 v6 v10 v11 v12 v13 v14 v15 v16 v17 B4.
    set (msk := map (fun x => Z.land x (negw bw)) V) in *.
    assert (Esl : sl = firstn (Z.to_nat dn) sl ++ [nth (Z.to_nat dn) sl 0%Z]) by (apply split_last; rewrite Lsl2; exact EW).
    rewrite Esl in B4.
    eapply (db_add _ m4 (firstn (Z.to_nat dn) sl) (nth (Z.to_nat dn) sl 0%Z) msk l0 RL bw q i); try eassumption.
    { rewrite length_firstn, Lsl2, EW. clear - Hdn. lia. }
    { subst msk. rewrite length_map. exact HVl. }
    { apply limbs_firstn. exact Lsl. }
    { subst msk. apply mask_limbs; assumption. }
    { rewrite <- BW_lit. apply limbs_nth. exact Lsl. }
    intros m5 w1 w5 w6 w7 w9 w10 w11 w12 w13 w14 w15 w16 w17 w23 w26 w27 w28 w29 w30 w31 B5.
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
