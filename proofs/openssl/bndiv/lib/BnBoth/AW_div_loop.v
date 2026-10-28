(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import DivLoopPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require DivBody DivLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AW_div_body.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition dl_bndA (SD TD VD RD TA VA lo SP : Z) (Ls Lt Lv Lr : nat) : Prop :=
  (0 <= SD /\ 0 <= TD /\ 0 <= VD /\ 0 <= RD /\ 0 <= TA /\ 0 <= VA /\
   SD + 8 * Z.of_nat Ls <= lo /\ TD + 8 * Z.of_nat Lt <= lo /\ VD + 8 * Z.of_nat Lv <= lo /\ RD + 8 * Z.of_nat Lr <= lo /\
   TA + 24 <= lo /\ VA + 24 <= lo /\ lo <= SP - 416 /\ SP <= 140737488355328)%Z.
Notation dl_pair := DivLoop.dl_pair.
Notation dj := DivLoop.dj.
Notation dl_to_db_pair := DivLoop.dl_to_db_pair.

Lemma dl_to_db_bndA : forall SD TD VD RD TA VA lo SP Ls Lt Lv Lr (w dnn : nat),
  dl_bndA SD TD VD RD TA VA lo SP Ls Lt Lv Lr -> (w + dnn + 1 <= Ls)%nat -> (dnn + 1 <= Lt)%nat -> (dnn <= Lv)%nat -> (w + 1 <= Lr)%nat ->
  db_bndA (SD + 8 * Z.of_nat w) TD VD (RD + 8 * Z.of_nat w) TA VA lo SP (Z.of_nat dnn).
Proof. intros. unfold dl_bndA, db_bndA in *. lia. Qed.

Lemma dl_to_db_al : forall SD TD VD RD TA VA (w : nat), db_al SD TD VD RD TA VA ->
  db_al (SD + 8 * Z.of_nat w) TD VD (RD + 8 * Z.of_nat w) TA VA.
Proof.
  intros SD TD VD RD TA VA w (A1 & A2 & A3 & A4 & A5 & A6). unfold db_al.
  split; [clear - A1; Z.div_mod_to_equations; lia|]. split; [exact A2|]. split; [exact A3|].
  split; [clear - A4; Z.div_mod_to_equations; lia|]. split; [exact A5 | exact A6].
Qed.

Lemma dl_to_db_nz : forall SD TD VD RD (w : nat), (0 < SD /\ 0 < TD /\ 0 < VD /\ 0 < RD)%Z ->
  db_nz (SD + 8 * Z.of_nat w) TD VD (RD + 8 * Z.of_nat w).
Proof. intros. unfold db_nz. lia. Qed.

Section Loop.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (d0 d1 : Z) (sdiv : list Z) (div_n loop num_n : nat).
  Variables (SD TD VD RD TA VA lo : Z) (Ls Lt Lr : nat) (N0 : Z).
  Variable c0 : list byte.
  Variables (c1 c2 c3 c4 c5 c6 c17 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 : word).
  Variables (ta1 ta2 ta3 ta4 va1 va2 va3 va4 : word).
  Variable m0 : word -> option byte.
  Notation SP := (bv_unsigned sp).
  Notation dn := (Z.of_nat div_n).
  Notation loopw := (Z_to_bv 64 (Z.of_nat loop)).
  Hypothesis Hsdiv : limbs sdiv.
  Hypothesis Hdn : (1 <= div_n)%nat.
  Hypothesis Hsdl : (div_n <= length sdiv)%nat.
  Hypothesis Hnum : num_n = (loop + div_n)%nat.
  Hypothesis Hd0 : d0 = nth (div_n - 1) sdiv 0%Z.
  Hypothesis Hd1 : d1 = if (div_n =? 1)%nat then 0%Z else nth (div_n - 2) sdiv 0%Z.
  Hypothesis Hnorm : (9223372036854775808 <= d0)%Z.
  Hypothesis HLs : (num_n <= Ls)%nat.
  Hypothesis HLt : (div_n + 1 <= Lt)%nat.
  Hypothesis HLr : (loop <= Lr)%nat.
  Hypothesis Hsmall : (Z.of_nat num_n < 2147483647)%Z.
  Hypothesis DLB : dl_bndA SD TD VD RD TA VA lo SP Ls Lt (length sdiv) Lr.
  Hypothesis DLP : dl_pair SD TD VD RD TA VA Ls Lt (length sdiv) Lr.
  Hypothesis DAL : db_al SD TD VD RD TA VA.

  Notation WT i := (SD + 8 * Z.of_nat (num_n - 1 - i))%Z.
  Notation WN i := (SD + 8 * Z.of_nat (loop - i))%Z.
  Notation FRAME wt iw wn :=
    [CB 8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6;
     C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32));
     C8 (Z_to_bv 64 (dn + 1)); C8 (Z_to_bv 64 d1);
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (8 * dn)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0);
     C8 c17; C8 loopw; C8 (Z_to_bv 64 (shad VA));
     C8 (Z_to_bv 64 wt); C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 iw); C8 (Z_to_bv 64 dn); C8 (Z_to_bv 64 wn);
     C8 c25; C8 c26; C8 c27; C8 c28; C8 c29; C8 c30; C8 c31; C8 c32; C8 c33; C8 c34; C8 c35; C8 c36; C8 c37].
  Notation WL := [(SD, SD + 8 * Z.of_nat Ls); (TD, TD + 8 * Z.of_nat Lt); (RD, RD + 8 * Z.of_nat Lr); (bv_unsigned sp - 416, bv_unsigned sp)]%Z.

  (* [comment removed for export] *)
  Hypothesis ACS : acc bsegs m0 SD (8 * Z.of_nat Ls).
  Hypothesis ACT : acc bsegs m0 TD (8 * Z.of_nat Lt).
  Hypothesis ACV : acc bsegs m0 VD (8 * Z.of_nat (length sdiv)).
  Hypothesis ACR : acc bsegs m0 RD (8 * Z.of_nat Lr).
  Hypothesis ACTA : acc bsegs m0 TA 24.
  Hypothesis ACVA : acc bsegs m0 VA 24.
  Hypothesis SHB0 : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m0.
  Hypothesis OFFWL : offshW WL.
  Hypothesis DG1 : disjoint_from WL g_GOT_shadow_offset_cell 8.
  Hypothesis DG2 : disjoint_from WL g_shadow_memory_dynamic_address 8.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  Hypothesis DNZ : (0 < SD /\ 0 < TD /\ 0 < VD /\ 0 < RD)%Z.

  Notation V := (firstn div_n sdiv).
  Notation WBST wp rp mb wt iw wn mm WIN TL RL :=
    (BST sp d1 dn V wp TD VD rp TA VA lo c0 c1 c2 c3 c4 c5 c6 c17 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 loopw
         ta1 ta2 ta3 ta4 va1 va2 va3 va4 mb wt iw wn mm WIN TL RL).

  (* [comment removed for export] *)
  Definition LINVf (wt iw wn : Z) (mm : word -> option byte) (snum tmp res : list Z) : Prop :=
    limbs_at bsegs mm SD snum /\ limbs_at bsegs mm TD tmp /\ limbs_at bsegs mm RD res /\ limbs_at bsegs mm VD sdiv /\
    wr_at bsegs mm SD (8 * Z.of_nat Ls) /\ wr_at bsegs mm TD (8 * Z.of_nat Lt) /\ wr_at bsegs mm RD (8 * Z.of_nat Lr) /\
    rw_cells bsegs mm TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4] /\
    rw_cells bsegs mm VA [C8 (Z_to_bv 64 VD); C4 va1; C4 va2; C4 va3; C4 va4] /\
    rw_cells bsegs mm (bv_unsigned sp + -304) (FRAME wt iw wn) /\
    stk bsegs mm lo (bv_unsigned sp + -304) /\ mem_inv bsegs mm /\
    munch WL m0 mm /\ wmono bsegs m0 mm.
  Definition LINV (i : nat) (mm : word -> option byte) (snum tmp res : list Z) : Prop := LINVf (WT i) (Z.of_nat i) (WN i) mm snum tmp res.

  (* [comment removed for export] *)
  Definition LREST (mm : word -> option byte) (w : nat) (snum tmp res : list Z) : Prop :=
    limbs_at bsegs mm SD (firstn w snum) /\
    limbs_at bsegs mm (SD + 8 * Z.of_nat (w + (div_n + 1))) (skipn (w + (div_n + 1)) snum) /\
    limbs_at bsegs mm (TD + 8 * Z.of_nat (div_n + 1)) (skipn (div_n + 1) tmp) /\
    limbs_at bsegs mm RD (firstn w res) /\
    limbs_at bsegs mm (RD + 8 * Z.of_nat (w + 1)) (skipn (w + 1) res) /\
    limbs_at bsegs mm (VD + 8 * dn) (skipn div_n sdiv) /\
    wr_at bsegs mm SD (8 * Z.of_nat Ls) /\ wr_at bsegs mm TD (8 * Z.of_nat Lt) /\ wr_at bsegs mm RD (8 * Z.of_nat Lr) /\
    munch WL m0 mm /\ wmono bsegs m0 mm.

  Lemma LINV_open : forall wt iw wn mm snum tmp res w,
    LINVf wt iw wn mm snum tmp res -> length snum = Ls -> length tmp = Lt -> length res = Lr -> (w < loop)%nat ->
    WBST (SD + 8 * Z.of_nat w)%Z (RD + 8 * Z.of_nat w)%Z mm wt iw wn mm (slice snum w (div_n + 1)) [] [] /\ LREST mm w snum tmp res.
  Proof.
    intros wt iw wn mm snum tmp res w (HS & HT & HR & HVD & WS & WT & WR & CTA & CVA & FR & ST & MI & MU & WM) ELs ELt ELr Hw.
    unfold dl_bndA in DLB.
    (* [comment removed for export] *)
    assert (ES : snum = firstn w snum ++ slice snum w (div_n + 1) ++ skipn (w + (div_n + 1)) snum).
    { unfold slice. rewrite <- (firstn_skipn w snum) at 1. f_equal. rewrite <- (firstn_skipn (div_n + 1) (skipn w snum)) at 1.
      f_equal. rewrite skipn_skipn. f_equal. lia. }
    pose proof HS as HS0. rewrite ES in HS. apply limbs_at_app in HS. destruct HS as [HS1 HS23].
    apply limbs_at_app in HS23. destruct HS23 as [HS2 HS3].
    rewrite length_firstn in HS2, HS3. rewrite slice_length in HS3 by lia.
    replace (Nat.min w (length snum)) with w in HS2, HS3 by lia.
    rewrite <- (firstn_skipn (div_n + 1) tmp) in HT. apply limbs_at_app in HT. destruct HT as [HT1 HT2].
    rewrite length_firstn in HT2. replace (Nat.min (div_n + 1) (length tmp)) with (div_n + 1)%nat in HT2 by lia.
    assert (ER : res = firstn w res ++ skipn w res) by (symmetry; apply firstn_skipn).
    pose proof HR as HR0. rewrite ER in HR. apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    rewrite length_firstn in HR2. replace (Nat.min w (length res)) with w in HR2 by lia.
    assert (ER2 : skipn w res = firstn 1 (skipn w res) ++ skipn (w + 1) res).
    { rewrite <- (firstn_skipn 1 (skipn w res)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. }
    rewrite ER2 in HR2. apply limbs_at_app in HR2. destruct HR2 as [_ HR3].
    rewrite length_firstn, length_skipn in HR3. replace (Nat.min 1 (length res - w)) with 1%nat in HR3 by lia.
    pose proof HVD as HVD0. rewrite <- (firstn_skipn div_n sdiv) in HVD. apply limbs_at_app in HVD. destruct HVD as [HV1 HV2].
    rewrite length_firstn in HV2. replace (Nat.min div_n (length sdiv)) with div_n in HV2 by lia.
    split.
    - unfold BST.
      split; [exact HS2|].
      split. { apply limbs_at_nil. clear - DLB. lia. }
      split. { apply limbs_at_nil. clear - DLB Hw HLr. lia. }
      split; [exact HV1|].
      split. { replace (8 * (dn + 1))%Z with (8 * Z.of_nat (div_n + 1))%Z by lia.
               apply (wr_at_sub bsegs mm SD (8 * Z.of_nat Ls)); [exact WS | lia | lia | lia]. }
      split. { apply (wr_at_sub bsegs mm TD (8 * Z.of_nat Lt) 0 (8 * (dn + 1))) in WT; [rewrite Z.add_0_r in WT; exact WT | lia | lia | lia]. }
      split. { apply (wr_at_sub bsegs mm RD (8 * Z.of_nat Lr)); [exact WR | lia | lia | lia]. }
      split; [exact CTA|]. split; [exact CVA|]. split; [exact FR|]. split; [exact ST|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl].
    - unfold LREST.
      split; [exact HS1|].
      split. { replace (SD + 8 * Z.of_nat (w + (div_n + 1)))%Z with (SD + 8 * Z.of_nat w + 8 * Z.of_nat (div_n + 1))%Z by lia. exact HS3. }
      split; [exact HT2|]. split; [exact HR1|].
      split. { replace (RD + 8 * Z.of_nat (w + 1))%Z with (RD + 8 * Z.of_nat w + 8 * Z.of_nat 1)%Z by lia. exact HR3. }
      split; [exact HV2|].
      repeat (split; [assumption|]). assumption.
  Qed.

  Lemma LINV_close : forall wt iw wn mm mm' snum tmp res w win' tmp' q',
    LREST mm w snum tmp res ->
    WBST (SD + 8 * Z.of_nat w)%Z (RD + 8 * Z.of_nat w)%Z mm wt iw wn mm' win' tmp' [q'] ->
    length snum = Ls -> length tmp = Lt -> length res = Lr -> (w < loop)%nat ->
    length win' = (div_n + 1)%nat -> length tmp' = (div_n + 1)%nat ->
    LINVf wt iw wn mm' (firstn w snum ++ win' ++ skipn (w + (div_n + 1)) snum) (tmp' ++ skipn (div_n + 1) tmp) (firstn w res ++ [q'] ++ skipn (w + 1) res).
  Proof.
    intros wt iw wn mm mm' snum tmp res w win' tmp' q' (HS1 & HS3 & HT2 & HR1 & HR3 & HV2 & WS & WT & WR & MU & WM)
           (HWIN & HTL & HRL & HVD & _ & _ & _ & CTA & CVA & FR & ST & MI & MUb & WMb) ELs ELt ELr Hw Lw' Lt'.
    unfold dl_bndA in DLB. destruct DLP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12). unfold DivLoop.dj in *.
    assert (Lf : length (firstn w snum) = w) by (rewrite length_firstn; lia).
    assert (Lfr : length (firstn w res) = w) by (rewrite length_firstn; lia).
    assert (HS1' : limbs_at bsegs mm' SD (firstn w snum)).
    { eapply limbs_trA; [exact HS1 | exact MUb | exact (f_equal Z.of_nat Lf) | ]. cbn. clear - DLB P1 P3 Hw HLs HLt HLr Hnum. lia. }
    assert (HS3' : limbs_at bsegs mm' (SD + 8 * Z.of_nat (w + (div_n + 1))) (skipn (w + (div_n + 1)) snum)).
    { eapply limbs_trA; [exact HS3 | exact MUb | reflexivity | ]. rewrite length_skipn, ELs. cbn. clear - DLB P1 P3 Hw HLs HLt HLr Hnum. lia. }
    assert (HT2' : limbs_at bsegs mm' (TD + 8 * Z.of_nat (div_n + 1)) (skipn (div_n + 1) tmp)).
    { eapply limbs_trA; [exact HT2 | exact MUb | reflexivity | ]. rewrite length_skipn, ELt. cbn. clear - DLB P1 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HR1' : limbs_at bsegs mm' RD (firstn w res)).
    { eapply limbs_trA; [exact HR1 | exact MUb | exact (f_equal Z.of_nat Lfr) | ]. cbn. clear - DLB P3 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HR3' : limbs_at bsegs mm' (RD + 8 * Z.of_nat (w + 1)) (skipn (w + 1) res)).
    { eapply limbs_trA; [exact HR3 | exact MUb | reflexivity | ]. rewrite length_skipn, ELr. cbn. clear - DLB P3 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HV2' : limbs_at bsegs mm' (VD + 8 * dn) (skipn div_n sdiv)).
    { eapply limbs_trA; [exact HV2 | exact MUb | reflexivity | ]. rewrite length_skipn. cbn. clear - DLB P2 P6 P10 Hw HLs HLt HLr Hnum Hsdl. lia. }
    unfold LINVf.
    split. { apply limbs_at_app. split; [exact HS1'|]. rewrite Lf. apply limbs_at_app. split; [exact HWIN|]. rewrite Lw'.
             replace (SD + 8 * Z.of_nat w + 8 * Z.of_nat (div_n + 1))%Z with (SD + 8 * Z.of_nat (w + (div_n + 1)))%Z by lia. exact HS3'. }
    split. { apply limbs_at_app. split; [exact HTL|]. rewrite Lt'. exact HT2'. }
    split. { apply limbs_at_app. split; [exact HR1'|]. rewrite Lfr. apply limbs_at_app. split; [exact HRL|]. cbn [length].
             replace (RD + 8 * Z.of_nat w + 8 * Z.of_nat 1)%Z with (RD + 8 * Z.of_nat (w + 1))%Z by lia. exact HR3'. }
    split. { rewrite <- (firstn_skipn div_n sdiv). apply limbs_at_app. split; [exact HVD|]. rewrite length_firstn.
             replace (Nat.min div_n (length sdiv)) with div_n by lia. exact HV2'. }
    split. { eapply wr_at_transport; eauto. }
    split. { eapply wr_at_transport; eauto. }
    split. { eapply wr_at_transport; eauto. }
    split; [exact CTA|]. split; [exact CVA|]. split; [exact FR|]. split; [exact ST|]. split; [exact MI|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUb].
             unfold sub_fp. intros x Hx. cbn [outside] in *. clear - Hx Hw HLs HLt HLr Hnum. lia. }
    eapply wmono_trans; eauto.
  Qed.

  Notation LST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 d0) x19 (Z_to_bv 64 TA)
             (Z_to_bv 64 (shad TA)) x22 x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (8 * dn)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma d0_lit : (9223372036854775808 <= d0 < 18446744073709551616)%Z.
  Proof. split; [exact Hnorm|]. rewrite Hd0, <- BW_lit. apply limbs_nth. exact Hsdiv. Qed.
  Lemma d1_lit : (0 <= d1 < 18446744073709551616)%Z.
  Proof. rewrite Hd1, <- BW_lit. destruct (div_n =? 1)%nat; [exact limb_0 | apply limbs_nth; exact Hsdiv]. Qed.

  (* [comment removed for export] *)
  Lemma win_asan : forall wt iw wn mm snum tmp res (w : nat), LINVf wt iw wn mm snum tmp res -> (w < loop)%nat ->
    let wp := (SD + 8 * Z.of_nat w)%Z in let rp := (RD + 8 * Z.of_nat w)%Z in
    acc bsegs mm wp (8 * (dn + 1)) /\ acc bsegs mm TD (8 * (dn + 1)) /\ acc bsegs mm VD (8 * dn) /\ acc bsegs mm rp 8 /\
    acc bsegs mm TA 24 /\ acc bsegs mm VA 24 /\
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address mm /\
    offshW [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 416, bv_unsigned sp)]%Z /\
    disjoint_from [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 416, bv_unsigned sp)]%Z g_GOT_shadow_offset_cell 8 /\
    disjoint_from [(wp, wp + 8 * (dn + 1)); (TD, TD + 8 * (dn + 1)); (rp, rp + 8); (bv_unsigned sp - 416, bv_unsigned sp)]%Z g_shadow_memory_dynamic_address 8.
  Proof.
    intros wt iw wn mm snum tmp res w (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _) Hw wp rp. subst wp rp.
    unfold dl_bndA in DLB.
    split. { apply (acc_tr bsegs _ m0 mm SD (8 * Z.of_nat Ls) (8 * Z.of_nat w) (8 * (dn + 1)) ACS MU OFFWL); [intros _ | |]; clear - DLB Hw HLs Hnum; lia. }
    split. { pose proof (acc_tr bsegs _ m0 mm TD (8 * Z.of_nat Lt) 0 (8 * (dn + 1)) ACT MU OFFWL) as X. rewrite Z.add_0_r in X.
             apply X; [intros _ | |]; clear - DLB HLt; lia. }
    split. { pose proof (acc_tr bsegs _ m0 mm VD (8 * Z.of_nat (length sdiv)) 0 (8 * dn) ACV MU OFFWL) as X. rewrite Z.add_0_r in X.
             apply X; [intros _ | |]; clear - DLB Hsdl; lia. }
    split. { apply (acc_tr bsegs _ m0 mm RD (8 * Z.of_nat Lr) (8 * Z.of_nat w) 8 ACR MU OFFWL); [intros _ | |]; clear - DLB Hw HLr; lia. }
    split. { pose proof (acc_tr bsegs _ m0 mm TA 24 0 24 ACTA MU OFFWL) as X. rewrite Z.add_0_r in X. apply X; [intros _ | |]; clear - DLB; lia. }
    split. { pose proof (acc_tr bsegs _ m0 mm VA 24 0 24 ACVA MU OFFWL) as X. rewrite Z.add_0_r in X. apply X; [intros _ | |]; clear - DLB; lia. }
    split. { exact (shb_cells_munch bsegs _ _ _ m0 mm SHB0 MU DG1 DG2). }
    cbn [offshW disjoint_from] in *. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
    clear - OFFWL DG1 DG2 Hw HLs HLt HLr Hnum Hdn. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_iter : forall (i : nat) mm snum tmp res x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
    (i < loop)%nat ->
    LINV i mm snum tmp res -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr i (snum, tmp, res) ->
    (forall mm' snum' tmp' res' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
       (snum', tmp', res') = div_step sdiv div_n loop num_n d0 d1 i (snum, tmp, res) ->
       LINV (S i) mm' snum' tmp' res' -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr (S i) (snum', tmp', res') ->
       evt bsegs POST (LST 0x252c24 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - S i))) (Z_to_bv 64 (dn + 1))
                           x23 x26 x27 x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252c24 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - i))) (Z_to_bv 64 (dn + 1))
                        x23 x26 x27 x28 x29 x30 x31).
  Proof.
    intros i mm snum tmp res x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Hi L DI K.
    pose proof DI as (Hsn & Hsnl & Htm & Html & Hrs & Hrsl & Htop & _).
    set (w := (loop - 1 - i)%nat).
    assert (Hw : (w < loop)%nat) by (subst w; lia).
    unfold LINV in L.
    assert (EWT : (WT i = SD + 8 * Z.of_nat w + 8 * dn)%Z) by (subst w; clear - Hnum Hi Hdn; lia).
    assert (EWN : (WN i = SD + 8 * Z.of_nat w + 8)%Z) by (subst w; clear - Hnum Hi Hdn; lia).
    rewrite EWT, EWN in L. clear EWT EWN.
    pose proof L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).

    step. step. step. clear FR.
    zstep. rewrite lts_signed by (clear - Hsmall Hnum Hi; lia).
    if_cases KX; zify_cond KX. { exfalso. clear - KX Hi. lia. }
    clear KX.
    destruct (LINV_open _ _ _ mm snum tmp res w L Hsnl Html Hrsl Hw) as [B R].
    destruct (win_asan _ _ _ mm snum tmp res w L Hw) as (AW & AT & AV & AQ & ATA' & AVA' & SHm & OFFm & DG1m & DG2m).
    pose proof (div_step_split sdiv div_n loop num_n d0 d1 i snum tmp res Hdn Hsdl Hnum Hi ltac:(lia) ltac:(lia) ltac:(lia)
                       Hsdiv Hsn Hd0 Hd1 ltac:(change (2 ^ 63)%Z with 9223372036854775808%Z; exact Hnorm) Htop) as DS; cbv zeta in DS; fold w in DS.
    destruct DS as (DS & Lw' & Lt').
    pose proof (div_step_inv sdiv div_n loop num_n d0 d1 Hsdiv Hdn Hsdl Hnum Hd0 Hd1 ltac:(change (2 ^ 63)%Z with 9223372036854775808%Z; exact Hnorm)
                       N0 Ls Lt Lr i (snum, tmp, res) HLs HLt HLr Hi DI) as DI'.
    assert (HVl : Z.of_nat (length V) = dn) by (rewrite firstn_length_le by exact Hsdl; reflexivity).
    assert (EVl : length V = div_n) by (apply firstn_length_le; exact Hsdl).
    eapply evt_eq;
      [ | eapply (db_body sp gp tp F fc POST d0 d1 dn V (SD + 8 * Z.of_nat w)%Z TD VD (RD + 8 * Z.of_nat w)%Z TA VA lo
                          c0 c1 c2 c3 c4 c5 c6 c17 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 loopw ta1 ta2 ta3 ta4 va1 va2 va3 va4 mm
                          d0_lit d1_lit ltac:(lia) ltac:(apply limbs_firstn; exact Hsdiv) HVl
                          ltac:(apply (dl_to_db_bndA SD TD VD RD TA VA lo SP Ls Lt (length sdiv) Lr w div_n DLB); lia)
                          ltac:(apply (dl_to_db_pair SD TD VD RD TA VA Ls Lt (length sdiv) Lr w div_n DLP); lia)
                          (dl_to_db_al SD TD VD RD TA VA w DAL) AW AT AV AQ ATA' AVA' SHm OFFm DG1m DG2m SHLO_LO
                          (dl_to_db_nz SD TD VD RD w DNZ)
                          mm (slice snum w (div_n + 1)) [] [] (Z.of_nat i) x1 x5 x6 x7 x9 _ _ x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 B) ].
    - (* [comment removed for export] *)
      replace (RD + 8 * Z.of_nat (loop - i))%Z with (RD + 8 * Z.of_nat w + 8)%Z by (subst w; lia).
      reflexivity.
    - rewrite slice_length by lia. lia.
    - cbn [length]. lia.
    - cbn [length]. lia.
    - apply slice_limbs. exact Hsn.
    - rewrite EVl, Hd0. eapply div_inv_n0; try eassumption.
    - lia.
    - intros mm' y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y26 y27 y28 y29 y30 y31 B'.
      unfold sc_win, sc_tmp, sc_q in *.
      pose proof (LINV_close _ _ _ mm mm' snum tmp res w _ _ _ R B' Hsnl Html Hrsl Hw Lw' Lt') as L'.
      replace (SD + 8 * Z.of_nat w + 8 * dn + -8)%Z with (WT (S i)) in L' by (subst w; clear - Hnum Hi Hdn; lia).
      replace (SD + 8 * Z.of_nat w)%Z with (WN (S i)) in L' by (subst w; clear - Hnum Hi Hdn; lia).
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) in L' by lia.
      replace (RD + 8 * Z.of_nat w)%Z with (RD + 8 * Z.of_nat (loop - S i))%Z by (subst w; lia).
      eapply K; [symmetry; exact DS | unfold LINV; exact L' | rewrite <- DS; exact DI'].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_loop : forall (cnt i : nat) mm snum tmp res x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
    (i + cnt = loop)%nat ->
    LINV i mm snum tmp res -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr i (snum, tmp, res) ->
    (forall mm' snum' tmp' res' x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x23 x26 x27 x28 x29 x30 x31,
       (snum', tmp', res') = div_loop sdiv div_n loop num_n d0 d1 cnt i (snum, tmp, res) ->
       LINV loop mm' snum' tmp' res' -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr loop (snum', tmp', res') ->
       evt bsegs POST (LST 0x252f54 mm' x1 x5 x6 x7 x9 (Z_to_bv 64 (Z.of_nat loop)) (Z_to_bv 64 (Z.of_nat loop)) x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (dn + 1))
                           x23 x26 x27 x28 x29 x30 x31)) ->
    evt bsegs POST (LST 0x252c24 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - i))) (Z_to_bv 64 (dn + 1))
                        x23 x26 x27 x28 x29 x30 x31).
  Proof.
    induction cnt as [|cnt IH]; intros i mm snum tmp res x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Hcnt L DI K.
    - (* [comment removed for export] *)
      assert (Ei : i = loop) by lia. subst i.
      pose proof L as L0. unfold LINV in L.
      pose proof L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
      step. step. step. clear FR.
      zstep. rewrite lts_signed by (clear - Hsmall Hnum; lia).
      if_cases KX; zify_cond KX. 2:{ exfalso. clear - KX. lia. }
      clear KX.
      eapply K; [reflexivity | exact L0 | exact DI].
    - eapply dl_iter; [lia | exact L | exact DI | ].
      intros mm' snum' tmp' res' y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y26 y27 y28 y29 y30 y31 EDS L' DI'.
      eapply IH; [lia | exact L' | exact DI' | ].
      intros mm2 snum2 tmp2 res2 z1 z5 z6 z7 z9 z12 z13 z14 z15 z16 z17 z19 z23 z26 z27 z28 z29 z30 z31 EDL L2 DI2.
      eapply K; [ | exact L2 | exact DI2 ].
      cbn [div_loop]. rewrite <- EDS. exact EDL.
  Qed.
End Loop.
