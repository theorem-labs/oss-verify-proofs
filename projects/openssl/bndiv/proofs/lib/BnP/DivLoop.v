(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivLoop.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import DivLoopPure DivBody.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition dl_bnd (SD TD VD RD TA VA lo SP : Z) (Ls Lt Lv Lr : nat) : Prop :=
  (0 <= SD /\ 0 <= TD /\ 0 <= VD /\ 0 <= RD /\ 0 <= TA /\ 0 <= VA /\
   SD + 8 * Z.of_nat Ls <= lo /\ TD + 8 * Z.of_nat Lt <= lo /\ VD + 8 * Z.of_nat Lv <= lo /\ RD + 8 * Z.of_nat Lr <= lo /\
   TA + 24 <= lo /\ VA + 24 <= lo /\ lo <= SP - 272 /\ SP < 18446744073709551616)%Z.
Definition dj (A : Z) (n : Z) (B : Z) (k : Z) : Prop := (A + n <= B \/ B + k <= A)%Z.
Definition dl_pair (SD TD VD RD TA VA : Z) (Ls Lt Lv Lr : nat) : Prop :=
  dj SD (8 * Z.of_nat Ls) TD (8 * Z.of_nat Lt) /\ dj SD (8 * Z.of_nat Ls) VD (8 * Z.of_nat Lv) /\ dj SD (8 * Z.of_nat Ls) RD (8 * Z.of_nat Lr) /\
  dj SD (8 * Z.of_nat Ls) TA 24 /\ dj SD (8 * Z.of_nat Ls) VA 24 /\
  dj TD (8 * Z.of_nat Lt) VD (8 * Z.of_nat Lv) /\ dj TD (8 * Z.of_nat Lt) RD (8 * Z.of_nat Lr) /\
  dj TD (8 * Z.of_nat Lt) TA 24 /\ dj TD (8 * Z.of_nat Lt) VA 24 /\
  dj RD (8 * Z.of_nat Lr) VD (8 * Z.of_nat Lv) /\ dj RD (8 * Z.of_nat Lr) TA 24 /\ dj RD (8 * Z.of_nat Lr) VA 24.

Lemma dl_to_db_bnd : forall SD TD VD RD TA VA lo SP Ls Lt Lv Lr (w dnn : nat),
  dl_bnd SD TD VD RD TA VA lo SP Ls Lt Lv Lr -> (w + dnn + 1 <= Ls)%nat -> (dnn + 1 <= Lt)%nat -> (dnn <= Lv)%nat -> (w + 1 <= Lr)%nat ->
  db_bnd (SD + 8 * Z.of_nat w) TD VD (RD + 8 * Z.of_nat w) TA VA lo SP (Z.of_nat dnn).
Proof. intros. unfold dl_bnd, db_bnd in *. lia. Qed.

Lemma dl_to_db_pair : forall SD TD VD RD TA VA Ls Lt Lv Lr (w dnn : nat),
  dl_pair SD TD VD RD TA VA Ls Lt Lv Lr -> (w + dnn + 1 <= Ls)%nat -> (dnn + 1 <= Lt)%nat -> (dnn <= Lv)%nat -> (w + 1 <= Lr)%nat ->
  db_pair (SD + 8 * Z.of_nat w) TD VD (RD + 8 * Z.of_nat w) TA VA (Z.of_nat dnn).
Proof.
  intros SD TD VD RD TA VA Ls Lt Lv Lr w dnn (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) H1 H2 H3 H4.
  unfold dj in *. unfold db_pair.
  split; [clear - P1 H1 H2; lia|]. split; [clear - P2 H1 H3; lia|]. split; [clear - P3 H1 H4; lia|].
  split; [clear - P4 H1; lia|]. split; [clear - P5 H1; lia|]. split; [clear - P6 H2 H3; lia|].
  split; [clear - P7 H2 H4; lia|]. split; [clear - P8 H2; lia|]. split; [clear - P9 H2; lia|].
  split; [clear - P10 H3 H4; lia|]. split; [clear - P11 H4; lia|]. clear - P12 H4; lia.
Qed.

Section Loop.
  Variables (sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (d0 d1 : Z) (sdiv : list Z) (div_n loop num_n : nat).
  Variables (SD TD VD RD TA VA lo : Z) (Ls Lt Lr : nat) (N0 : Z).
  Variables (c0 c4 c5 c7 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 : word).
  Variables (ta1 ta2 ta3 ta4 va1 va2 va3 va4 : word).
  Variable m0 : word -> option byte.
  Notation SP := (bv_unsigned sp).
  Notation dn := (Z.of_nat div_n).
  Notation c8 := (Z_to_bv 64 (Z.of_nat loop)).
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
  Hypothesis DLB : dl_bnd SD TD VD RD TA VA lo SP Ls Lt (length sdiv) Lr.
  Hypothesis DLP : dl_pair SD TD VD RD TA VA Ls Lt (length sdiv) Lr.

  Notation FRAME :=
    [C8 c0; C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32)); C8 c4; C8 c5;
     C8 (Z_to_bv 64 (8 * dn)); C8 c7; C8 c8; C8 (Z_to_bv 64 (dn + 1)); C8 (Z_to_bv 64 (8 * dn)); C8 (Z_to_bv 64 TA); C8 (Z_to_bv 64 VA);
     C8 c13; C8 c14; C8 c15; C8 c16; C8 c17; C8 c18; C8 c19; C8 c20; C8 c21; C8 c22; C8 c23; C8 c24; C8 c25].
  Notation WL := [(SD, SD + 8 * Z.of_nat Ls); (TD, TD + 8 * Z.of_nat Lt); (RD, RD + 8 * Z.of_nat Lr); (bv_unsigned sp - 272, bv_unsigned sp)]%Z.
  Notation V := (firstn div_n sdiv).
  Notation WBST wp rp mb mm WIN TL RL :=
    (BST sp d1 dn V wp TD VD rp TA VA lo c0 c4 c5 c7 c8 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 ta1 ta2 ta3 ta4 va1 va2 va3 va4 mb mm WIN TL RL).

  (* [comment removed for export] *)
  Definition LINV (mm : word -> option byte) (snum tmp res : list Z) : Prop :=
    limbs_at psegs mm SD snum /\ limbs_at psegs mm TD tmp /\ limbs_at psegs mm RD res /\ limbs_at psegs mm VD sdiv /\
    wr_at psegs mm SD (8 * Z.of_nat Ls) /\ wr_at psegs mm TD (8 * Z.of_nat Lt) /\ wr_at psegs mm RD (8 * Z.of_nat Lr) /\
    rw_cells psegs mm TA [C8 (Z_to_bv 64 TD); C4 ta1; C4 ta2; C4 ta3; C4 ta4] /\
    rw_cells psegs mm VA [C8 (Z_to_bv 64 VD); C4 va1; C4 va2; C4 va3; C4 va4] /\
    rw_cells psegs mm (bv_unsigned sp + -208) FRAME /\
    stk psegs mm lo (bv_unsigned sp + -208) /\ mem_inv psegs mm /\
    munch WL m0 mm /\ wmono psegs m0 mm.

  (* [comment removed for export] *)
  Definition LREST (mm : word -> option byte) (w : nat) (snum tmp res : list Z) : Prop :=
    limbs_at psegs mm SD (firstn w snum) /\
    limbs_at psegs mm (SD + 8 * Z.of_nat (w + (div_n + 1))) (skipn (w + (div_n + 1)) snum) /\
    limbs_at psegs mm (TD + 8 * Z.of_nat (div_n + 1)) (skipn (div_n + 1) tmp) /\
    limbs_at psegs mm RD (firstn w res) /\
    limbs_at psegs mm (RD + 8 * Z.of_nat (w + 1)) (skipn (w + 1) res) /\
    limbs_at psegs mm (VD + 8 * dn) (skipn div_n sdiv) /\
    wr_at psegs mm SD (8 * Z.of_nat Ls) /\ wr_at psegs mm TD (8 * Z.of_nat Lt) /\ wr_at psegs mm RD (8 * Z.of_nat Lr) /\
    munch WL m0 mm /\ wmono psegs m0 mm.

  Lemma LINV_open : forall mm snum tmp res w,
    LINV mm snum tmp res -> length snum = Ls -> length tmp = Lt -> length res = Lr -> (w < loop)%nat ->
    WBST (SD + 8 * Z.of_nat w)%Z (RD + 8 * Z.of_nat w)%Z mm mm (slice snum w (div_n + 1)) [] [] /\ LREST mm w snum tmp res.
  Proof using Hsdl Hnum HLs HLt HLr DLB Hdn.
    intros mm snum tmp res w (HS & HT & HR & HVD & WS & WT & WR & CTA & CVA & FR & ST & MI & MU & WM) ELs ELt ELr Hw.
    unfold dl_bnd in DLB.
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
               apply (wr_at_sub psegs mm SD (8 * Z.of_nat Ls)); [exact WS | lia | lia | lia]. }
      split. { apply (wr_at_sub psegs mm TD (8 * Z.of_nat Lt) 0 (8 * (dn + 1))) in WT; [rewrite Z.add_0_r in WT; exact WT | lia | lia | lia]. }
      split. { apply (wr_at_sub psegs mm RD (8 * Z.of_nat Lr)); [exact WR | lia | lia | lia]. }
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

  Lemma LINV_close : forall mm mm' snum tmp res w win' tmp' q',
    LREST mm w snum tmp res ->
    WBST (SD + 8 * Z.of_nat w)%Z (RD + 8 * Z.of_nat w)%Z mm mm' win' tmp' [q'] ->
    length snum = Ls -> length tmp = Lt -> length res = Lr -> (w < loop)%nat ->
    length win' = (div_n + 1)%nat -> length tmp' = (div_n + 1)%nat ->
    LINV mm' (firstn w snum ++ win' ++ skipn (w + (div_n + 1)) snum) (tmp' ++ skipn (div_n + 1) tmp) (firstn w res ++ [q'] ++ skipn (w + 1) res).
  Proof using Hsdl Hnum HLs HLt HLr DLB DLP Hdn.
    intros mm mm' snum tmp res w win' tmp' q' (HS1 & HS3 & HT2 & HR1 & HR3 & HV2 & WS & WT & WR & MU & WM)
           (HWIN & HTL & HRL & HVD & _ & _ & _ & CTA & CVA & FR & ST & MI & MUb & WMb) ELs ELt ELr Hw Lw' Lt'.
    unfold dl_bnd in DLB. destruct DLP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12). unfold dj in *.
    assert (Lf : length (firstn w snum) = w) by (rewrite length_firstn; lia).
    assert (Lfr : length (firstn w res) = w) by (rewrite length_firstn; lia).
    assert (HS1' : limbs_at psegs mm' SD (firstn w snum)).
    { eapply limbs_tr; [exact HS1 | exact MUb | exact (f_equal Z.of_nat Lf) | ]. cbn. clear - DLB P1 P3 Hw HLs HLt HLr Hnum. lia. }
    assert (HS3' : limbs_at psegs mm' (SD + 8 * Z.of_nat (w + (div_n + 1))) (skipn (w + (div_n + 1)) snum)).
    { eapply limbs_tr; [exact HS3 | exact MUb | reflexivity | ]. rewrite length_skipn, ELs. cbn. clear - DLB P1 P3 Hw HLs HLt HLr Hnum. lia. }
    assert (HT2' : limbs_at psegs mm' (TD + 8 * Z.of_nat (div_n + 1)) (skipn (div_n + 1) tmp)).
    { eapply limbs_tr; [exact HT2 | exact MUb | reflexivity | ]. rewrite length_skipn, ELt. cbn. clear - DLB P1 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HR1' : limbs_at psegs mm' RD (firstn w res)).
    { eapply limbs_tr; [exact HR1 | exact MUb | exact (f_equal Z.of_nat Lfr) | ]. cbn. clear - DLB P3 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HR3' : limbs_at psegs mm' (RD + 8 * Z.of_nat (w + 1)) (skipn (w + 1) res)).
    { eapply limbs_tr; [exact HR3 | exact MUb | reflexivity | ]. rewrite length_skipn, ELr. cbn. clear - DLB P3 P7 Hw HLs HLt HLr Hnum. lia. }
    assert (HV2' : limbs_at psegs mm' (VD + 8 * dn) (skipn div_n sdiv)).
    { eapply limbs_tr; [exact HV2 | exact MUb | reflexivity | ]. rewrite length_skipn. cbn. clear - DLB P2 P6 P10 Hw HLs HLt HLr Hnum Hsdl. lia. }
    unfold LINV.
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

  Notation LST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6
             (Z_to_bv 64 dn) (Z_to_bv 64 d1) (Z_to_bv 64 d0) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Lemma d0_lit : (9223372036854775808 <= d0 < 18446744073709551616)%Z.
  Proof using Hd0 Hnorm Hsdiv. split; [exact Hnorm|]. rewrite Hd0, <- BW_lit. apply limbs_nth. exact Hsdiv. Qed.
  Lemma d1_lit : (0 <= d1 < 18446744073709551616)%Z.
  Proof using Hd1 Hsdiv. rewrite Hd1, <- BW_lit. destruct (div_n =? 1)%nat; [exact limb_0 | apply limbs_nth; exact Hsdiv]. Qed.

  (* [comment removed for export] *)
  Lemma dl_iter : forall (i : nat) mm snum tmp res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    (i < loop)%nat ->
    LINV mm snum tmp res -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr i (snum, tmp, res) ->
    (forall mm' snum' tmp' res' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
       (snum', tmp', res') = div_step sdiv div_n loop num_n d0 d1 i (snum, tmp, res) ->
       LINV mm' snum' tmp' res' -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr (S i) (snum', tmp', res') ->
       evt psegs POST (LST 0x10ca10 mm' x1 x5 x6 x7 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - S i))) c8 x11 x12 x13 x14 x15 x16 x17 x18
                           (Z_to_bv 64 (SD + 8 * Z.of_nat (num_n - 1 - S i))) (Z_to_bv 64 (SD + 8 * Z.of_nat (num_n - 1 - S i))) c4
                           (Z_to_bv 64 (Z.of_nat (S i))) (Z_to_bv 64 (SD + 8 * Z.of_nat (loop - S i))) x28 x29 x30 x31)) ->
    evt psegs POST (LST 0x10c88c mm x1 x5 x6 x7 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - i))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                        (Z_to_bv 64 (SD + 8 * Z.of_nat (num_n - 1 - i))) c4 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (SD + 8 * Z.of_nat (loop - i)))
                        x28 x29 x30 x31).
  Proof.
    intros i mm snum tmp res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Hi L DI K.
    pose proof DI as (Hsn & Hsnl & Htm & Html & Hrs & Hrsl & Htop & _).
    set (w := (loop - 1 - i)%nat).
    assert (Hw : (w < loop)%nat) by (subst w; lia).
    destruct (LINV_open mm snum tmp res w L Hsnl Html Hrsl Hw) as [B R].
    pose proof (div_step_split sdiv div_n loop num_n d0 d1 i snum tmp res Hdn Hsdl Hnum Hi ltac:(lia) ltac:(lia) ltac:(lia)
                       Hsdiv Hsn Hd0 Hd1 ltac:(change (2 ^ 63)%Z with 9223372036854775808%Z; exact Hnorm) Htop) as DS; cbv zeta in DS; fold w in DS.
    destruct DS as (DS & Lw' & Lt').
    pose proof (div_step_inv sdiv div_n loop num_n d0 d1 Hsdiv Hdn Hsdl Hnum Hd0 Hd1 ltac:(change (2 ^ 63)%Z with 9223372036854775808%Z; exact Hnorm)
                       N0 Ls Lt Lr i (snum, tmp, res) HLs HLt HLr Hi DI) as DI'.
    assert (HVl : Z.of_nat (length V) = dn) by (rewrite firstn_length_le by exact Hsdl; reflexivity).
    assert (EVl : length V = div_n) by (apply firstn_length_le; exact Hsdl).
    eapply evt_eq;
      [ | eapply (db_body sp gp tp s6 F fc POST d0 d1 dn V (SD + 8 * Z.of_nat w)%Z TD VD (RD + 8 * Z.of_nat w)%Z TA VA lo
                          c0 c4 c5 c7 c8 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 ta1 ta2 ta3 ta4 va1 va2 va3 va4 mm
                          d0_lit d1_lit ltac:(lia) ltac:(apply limbs_firstn; exact Hsdiv) HVl
                          ltac:(apply (dl_to_db_bnd SD TD VD RD TA VA lo SP Ls Lt (length sdiv) Lr w div_n DLB); lia)
                          ltac:(apply (dl_to_db_pair SD TD VD RD TA VA Ls Lt (length sdiv) Lr w div_n DLP); lia)
                          mm (slice snum w (div_n + 1)) [] [] (Z.of_nat i) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 B) ].
    - (* [comment removed for export] *)
      replace (RD + 8 * Z.of_nat (loop - i))%Z with (RD + 8 * Z.of_nat w + 8)%Z by (subst w; lia).
      replace (SD + 8 * Z.of_nat (num_n - 1 - i))%Z with (SD + 8 * Z.of_nat w + 8 * dn)%Z by (subst w; lia).
      replace (SD + 8 * Z.of_nat (loop - i))%Z with (SD + 8 * Z.of_nat w + 8)%Z by (subst w; lia).
      reflexivity.
    - rewrite slice_length by lia. lia.
    - cbn [length]. lia.
    - cbn [length]. lia.
    - apply slice_limbs. exact Hsn.
    - rewrite EVl, Hd0. eapply div_inv_n0; try eassumption. 
    - lia.
    - intros mm' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 B'.
      unfold sc_win, sc_tmp, sc_q in *.
      pose proof (LINV_close mm mm' snum tmp res w _ _ _ R B' Hsnl Html Hrsl Hw Lw' Lt') as L'.
      replace (RD + 8 * Z.of_nat w)%Z with (RD + 8 * Z.of_nat (loop - S i))%Z by (subst w; lia).
      replace (SD + 8 * Z.of_nat w + 8 * dn + -8)%Z with (SD + 8 * Z.of_nat (num_n - 1 - S i))%Z by (subst w; lia).
      replace (SD + 8 * Z.of_nat w)%Z with (SD + 8 * Z.of_nat (loop - S i))%Z by (subst w; lia).
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
      eapply K; [symmetry; exact DS | exact L' | rewrite <- DS; exact DI'].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_loop : forall (cnt i : nat) mm snum tmp res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    (i + S cnt = loop)%nat ->
    LINV mm snum tmp res -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr i (snum, tmp, res) ->
    (forall mm' snum' tmp' res' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x26 x27 x28 x29 x30 x31,
       (snum', tmp', res') = div_loop sdiv div_n loop num_n d0 d1 (S cnt) i (snum, tmp, res) ->
       LINV mm' snum' tmp' res' -> div_inv sdiv div_n loop num_n N0 Ls Lt Lr loop (snum', tmp', res') ->
       evt psegs POST (LST 0x10ca14 mm' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 c4 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (LST 0x10c88c mm x1 x5 x6 x7 (Z_to_bv 64 (RD + 8 * Z.of_nat (loop - i))) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                        (Z_to_bv 64 (SD + 8 * Z.of_nat (num_n - 1 - i))) c4 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (SD + 8 * Z.of_nat (loop - i)))
                        x28 x29 x30 x31).
  Proof.
    induction cnt as [|cnt IH]; intros i mm snum tmp res x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Hcnt L DI K.
    - (* [comment removed for export] *)
      eapply dl_iter; [lia | exact L | exact DI | ].
      intros mm' snum' tmp' res' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 EDS L' DI'.
      assert (RL : (0 <= Z.of_nat loop < 2147483647)%Z) by lia.
      zstep. if_cases KB; zify_cond KB.
      { exfalso. lia. }
      eapply K; [ | exact L' | replace loop with (S i) at 2 by lia; exact DI' ].
      cbn [div_loop]. exact EDS.
    - eapply dl_iter; [lia | exact L | exact DI | ].
      intros mm' snum' tmp' res' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 EDS L' DI'.
      assert (RL : (0 <= Z.of_nat loop < 2147483647)%Z) by lia.
      zstep. if_cases KB; zify_cond KB.
      2:{ exfalso. lia. }
      eapply IH; [lia | exact L' | exact DI' | ].
      intros mm2 snum2 tmp2 res2 z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z26 z27 z28 z29 z30 z31 EDL L2 DI2.
      eapply K; [ | exact L2 | exact DI2 ].
      cbn [div_loop]. rewrite <- EDS. exact EDL.
  Qed.
End Loop.
