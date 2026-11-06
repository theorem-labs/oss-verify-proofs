(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_sqr_words W_sqr_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import AW_mul_words AW_mul_add_words AW_add_words.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AW_sqr_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_normal_aentry := 0x230748%Z.

Notation vl_post2 := W_sqr_normal.vl_post2.
Notation splice_app := W_sqr_normal.splice_app.
Notation upd_splice_snoc := W_sqr_normal.upd_splice_snoc.
Notation upd_length2 := W_sqr_normal.upd_length2.
Notation add_words_fst := W_sqr_normal.add_words_fst.
Notation lts_words_small := W_mul_normal.lts_words_small.
Notation sqr_words_limbs := W_sqr_words.sqr_words_limbs.
Ltac djtac := cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; try exact I; lia.

Lemma upd0_cons : forall x (l : list Z) v, upd (x :: l) 0 v = v :: l.
Proof. intros. reflexivity. Qed.
Lemma upd_cons_S : forall x (l : list Z) i v, upd (x :: l) (S i) v = x :: upd l i v.
Proof. intros. unfold upd, splice. cbn [firstn length Nat.add app skipn]. reflexivity. Qed.
Lemma upd_swap0 : forall (l : list Z) i, (0 < i < length l)%nat -> upd (upd l i 0) 0 0 = upd (upd l 0 0) i 0.
Proof.
  intros l i Hi. destruct l as [|x l]; [cbn in Hi; lia|]. destruct i as [|i]; [lia|].
  rewrite upd_cons_S, !upd0_cons, upd_cons_S. reflexivity.
Qed.

Definition sqn_ptrs (rp ap tq nn lo : Z) : Prop :=
  (rp mod 8 = 0 /\ ap mod 8 = 0 /\ tq mod 8 = 0 /\ (rp + 8 * nn <= SHLO \/ SHHI <= rp) /\ (tq + 8 * nn <= SHLO \/ SHHI <= tq) /\ SHHI <= lo /\
   (rp + 8 * nn <= 65536 \/ 12345344 <= rp) /\ (tq + 8 * nn <= 65536 \/ 12345344 <= tq))%Z.

Section Core.
  Variables (sp a0 : word) (m : word -> option byte) (lo : Z) (A : list Z) (PA PT : Z).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation NA := (Z.of_nat (length A)).
  Notation NN := (2 * Z.of_nat (length A))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (2 * Z.of_nat (length A))); (PT, PT + 8 * (2 * Z.of_nat (length A))); (bv_unsigned sp - 208, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRT : (rp + 8 * NN <= PT \/ PT + 8 * NN <= rp)%Z.
  Hypothesis DAT : (PA + 8 * NA <= PT \/ PT + 8 * NN <= PA)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 208 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 208 \/ SP <= PA)%Z.
  Hypothesis SEPT : (PT + 8 * NN <= SP - 208 \/ SP <= PT)%Z.

  Definition SNB (cells : list cell) (m1 : word -> option byte) : Prop :=
    limbs_at bgasegs m1 PA A /\ wr_at bgasegs m1 rp (8 * NN) /\ wr_at bgasegs m1 PT (8 * NN) /\
    rw_cells bgasegs m1 (SP + -128) cells /\ stk bgasegs m1 lo (SP + -128) /\
    mem_inv bgasegs m1 /\ munch Wfin m m1 /\ wmono bgasegs m m1.

  Definition SNI (cells : list cell) (m1 : word -> option byte) (R : list Z) : Prop :=
    limbs R /\ length R = (2 * length A)%nat /\ limbs_at bgasegs m1 rp R /\ SNB cells m1.

  Lemma sn_upd : forall cells m1 R k v ad,
    Z.of_nat (cells_size cells) = 128%Z ->
    SNI cells m1 R -> (k < 2 * length A)%nat -> (0 <= v < 18446744073709551616)%Z -> ad = (rp + 8 * Z.of_nat k)%Z ->
    store_ok bgasegs m1 (Z_to_bv 64 ad) 8 = true /\
    SNI cells (write_to_mem m1 (Z_to_bv 64 ad) (le8 (Z_to_bv 64 v))) (upd R k v).
  Proof using LA DRA DRT DAT SEPR SEPA SEPT.
    intros cells m1 R k v ad CS (LR & LenR & HR & HA & WR & WT & FR & ST & MI & MU & WM) Hk Hv ->.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    destruct WT as (T0 & T1 & WT'). pose proof (conj T0 (conj T1 WT')) as WT.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgasegs m1 (Z_to_bv 64 (rp + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)). apply (wr_at_store_ok bgasegs m1 rp (8 * NN)); [exact WR | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)).
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
    assert (ER : R = firstn k R ++ [nth k R 0%Z] ++ skipn (S k) R).
    { rewrite app_assoc, <- W_sqr_words.firstn_S_snoc by lia. symmetry. apply firstn_skipn. }
    assert (EU : upd R k v = firstn k R ++ [v] ++ skipn (S k) R).
    { unfold upd, splice. cbn [length app]. rewrite Nat.add_1_r. reflexivity. }
    unfold SNI, SNB.
    split. { apply upd_limbs; [exact LR | unfold limb, BW; exact Hv]. }
    split. { rewrite upd_length by lia. exact LenR. }
    split.
    { rewrite EU. rewrite ER in HR. apply limbs_at_app in HR. destruct HR as [H1 H23]. apply limbs_at_app in H23. destruct H23 as [H2 H3].
      rewrite length_firstn in H2, H3. cbn [length] in H3. replace (Nat.min k (length R)) with k in H2, H3 by lia.
      rewrite app_assoc. apply limbs_at_app. split.
      - replace (rp + 8 * Z.of_nat k)%Z with (rp + 8 * Z.of_nat (length (firstn k R)))%Z by (rewrite length_firstn; f_equal; lia).
        apply limbs_at_snoc_write; [exact H1 | rewrite length_firstn; lia].
      - rewrite length_app, length_firstn. cbn [length]. replace (Nat.min k (length R) + 1)%nat with (S k) by lia.
        replace (rp + 8 * Z.of_nat k + 8 * Z.of_nat 1)%Z with (rp + 8 * Z.of_nat (S k))%Z in H3 by lia.
        apply limbs_at_write_other; [exact H3 | lia | rewrite L8; lia | rewrite L8, length_skipn; lia]. }
    split. { apply limbs_at_write_other; [exact HA | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { apply wr_at_write. exact WR. }
    split. { apply wr_at_write. exact WT. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8, CS; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Lemma sn_call : forall cells m1 m2 R (st : nat) seg fsz,
    Z.of_nat (cells_size cells) = 128%Z ->
    SNI cells m1 R -> (st + length seg <= 2 * length A)%nat -> (0 <= fsz <= 80)%Z ->
    munch [(rp + 8 * Z.of_nat st, rp + 8 * Z.of_nat st + 8 * Z.of_nat (length seg)); (SP + -128 - fsz, SP + -128)]%Z m1 m2 ->
    wmono bgasegs m1 m2 -> mem_inv bgasegs m2 -> limbs_at bgasegs m2 (rp + 8 * Z.of_nat st) seg -> stk bgasegs m2 lo (SP + -128) ->
    limbs seg ->
    SNI cells m2 (splice R st seg).
  Proof using LA DRA DRT DAT SEPR SEPA SEPT.
    intros cells m1 m2 R st seg fsz CS (LR & LenR & HR & HA & WR & WT & FR & ST & MI & MU & WM) Hst Hf MUc WMc MIc HS STc LS.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
    unfold SNI, SNB.
    split. { apply splice_limbs; [exact LR | exact LS]. }
    split. { rewrite splice_length by lia. exact LenR. }
    split.
    { unfold splice. rewrite <- (firstn_skipn st R) in HR. apply limbs_at_app in HR. destruct HR as [H1 H23].
      rewrite <- (firstn_skipn (length seg) (skipn st R)) in H23. apply limbs_at_app in H23. destruct H23 as [_ H3].
      rewrite !length_firstn, length_skipn, skipn_skipn in H3.
      replace (Nat.min st (length R)) with st in H3 by lia. replace (Nat.min (length seg) (length R - st)) with (length seg) in H3 by lia.
      replace (length seg + st)%nat with (st + length seg)%nat in H3 by lia.
      apply limbs_at_app. split.
      - eapply limbs_at_transport; [exact H1 | exact MUc | cbn [disjoint_from]; rewrite length_firstn; lia].
      - rewrite length_firstn. replace (Nat.min st (length R)) with st by lia. apply limbs_at_app. split; [exact HS|].
        eapply limbs_at_transport; [exact H3 | exact MUc | cbn [disjoint_from]; rewrite length_skipn; lia]. }
    split. { eapply limbs_at_transport; [exact HA | exact MUc | cbn [disjoint_from]; lia]. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split. { eapply wr_at_transport; [exact WT | exact WMc]. }
    split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn [disjoint_from]; rewrite CS; lia]. }
    split; [exact STc|]. split; [exact MIc|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  Lemma sn_refrm : forall cells cells' m1 m2 R,
    SNI cells m1 R ->
    munch [(SP + -128, SP)]%Z m1 m2 -> wmono bgasegs m1 m2 -> mem_inv bgasegs m2 ->
    rw_cells bgasegs m2 (SP + -128) cells' -> stk bgasegs m2 lo (SP + -128) ->
    SNI cells' m2 R.
  Proof using SEPR SEPA SEPT.
    intros cells cells' m1 m2 R (LR & LenR & HR & HA & HW & HT & FR & ST & MI & MU & WM) MUs WMs MI2 FR2 ST2.
    split; [exact LR|]. split; [exact LenR|].
    split. { eapply limbs_at_transport; [exact HR | exact MUs | cbn [disjoint_from]; rewrite LenR; clear - SEPR; lia]. }
    split. { eapply limbs_at_transport; [exact HA | exact MUs | cbn [disjoint_from]; clear - SEPA; lia]. }
    split. { eapply wr_at_transport; [exact HW | exact WMs]. }
    split. { eapply wr_at_transport; [exact HT | exact WMs]. }
    split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUs].
             unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply wmono_trans; [exact WM | exact WMs].
  Qed.

  Lemma sn_recell : forall cells cells' m1 R,
    SNI cells m1 R -> (rw_cells bgasegs m1 (SP + -128) cells -> rw_cells bgasegs m1 (SP + -128) cells') -> SNI cells' m1 R.
  Proof using.
    intros cells cells' m1 R (LR & LenR & HR & HA & HW & HT & FR & REST) H.
    split; [exact LR|]. split; [exact LenR|]. split; [exact HR|]. split; [exact HA|]. split; [exact HW|]. split; [exact HT|].
    split; [exact (H FR) | exact REST].
  Qed.
End Core.

Section Mach.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A r0 : list Z).
  Notation rp := (bv_unsigned a0).
  Notation PA := (bv_unsigned a1).
  Notation PT := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Notation NA := (Z.of_nat (length A)).
  Notation NN := (2 * Z.of_nat (length A))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (2 * Z.of_nat (length A))); (bv_unsigned a3, bv_unsigned a3 + 8 * (2 * Z.of_nat (length A))); (bv_unsigned sp - 208, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LR0 : limbs r0.
  Hypothesis LenR0 : length r0 = (2 * length A)%nat.
  Hypothesis NA1 : (1 <= NA)%Z.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = NA.
  Hypothesis RA : limbs_at bgasegs m PA A.
  Hypothesis RR : limbs_at bgasegs m rp r0.
  Hypothesis WR : wr_at bgasegs m rp (8 * NN).
  Hypothesis WT : wr_at bgasegs m PT (8 * NN).
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRT : (rp + 8 * NN <= PT \/ PT + 8 * NN <= rp)%Z.
  Hypothesis DAT : (PA + 8 * NA <= PT \/ PT + 8 * NN <= PA)%Z.
  Hypothesis STK : stk bgasegs m lo SP.
  Hypothesis LO : (lo <= SP - 208)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 208 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 208 \/ SP <= PA)%Z.
  Hypothesis SEPT : (PT + 8 * NN <= SP - 208 \/ SP <= PT)%Z.
  Hypothesis MI0 : mem_inv bgasegs m.

  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgasegs m rp (8 * NN).
  Hypothesis ACA : acc bgasegs m PA (8 * NA).
  Hypothesis ACT : acc bgasegs m PT (8 * NN).
  Hypothesis APT : sqn_ptrs rp PA PT NN lo.

  Notation RES := (fst (sqr_normal A r0)).
  Notation POST := (vl_post2 bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a3) NN 208%Z RES (sqr_words A) lo m).
  Notation REST := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation T0 j0 j1 j2 := (CB 8 j0 :: CB 8 j1 :: CB 8 j2 :: REST).
  Notation T1 j0 j1 := (CB 8 j0 :: CB 8 j1 :: C8 a3 :: REST).
  Notation T2 j0 := (CB 8 j0 :: C8 (Z_to_bv 64 (Z.of_nat (length A))) :: C8 a3 :: REST).
  Notation KSNB cells := (SNB sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) cells).
  Notation KSNI cells := (SNI sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) cells).
  Notation UPD := (sn_upd sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) LA DRA DRT DAT SEPR SEPA SEPT).
  Notation CALL := (sn_call sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) LA DRA DRT DAT SEPR SEPA SEPT).
  Notation REFRM := (sn_refrm sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) SEPR SEPA SEPT).
  Notation RECELL := (sn_recell sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3)).

  Notation TF jj := (CB 16 jj :: C8 a3 :: REST).

  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 sp a0 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (2 * Z.of_nat (length A))) a2 x21
             x22 x23 x24 (Z_to_bv 64 SHB) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Lemma ESP128 : (128 <= SP)%Z -> bv_unsigned (Z_to_bv 64 (SP + -128)) = (SP + -128)%Z.
  Proof.
    intros H. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia.
  Qed.

  Lemma OFFfin : offshW Wfin.
  Proof using APT LO.
    destruct APT as (_ & _ & _ & A4' & A5' & A6' & _). cbn [offshW]. unfold SHHI in *.
    split; [exact A4'|]. split; [exact A5'|]. split; [right; clear - A6' LO; lia | exact I].
  Qed.
  Lemma shb_at : forall m1, munch Wfin m m1 -> shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1.
  Proof using SHBC APT LO.
    intros m1 MU. eapply shb_cells_munch; [exact SHBC | exact MU | | ];
      unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address; cbn [disjoint_from];
      destruct APT as (_ & _ & _ & _ & _ & A6' & O1 & O2); unfold SHHI in A6'; clear - A6' LO O1 O2; lia.
  Qed.

  Lemma run_bounds : forall cells m1, KSNB cells m1 ->
    (0 <= PA /\ PA + 8 * NA <= 140737488355328)%Z /\ (0 <= rp /\ rp + 8 * NN <= 140737488355328)%Z /\ (0 <= PT /\ PT + 8 * NN <= 140737488355328)%Z.
  Proof using NA1.
    intros cells m1 (HA & HW & HT & FR & ST & MI & MU & WM).
    split; [exact (limbs_at_b47 bgasegs m1 PA A HA MI ltac:(clear - NA1; lia))|].
    split; [exact (wr_at_b47 bgasegs m1 rp (8 * NN) HW MI ltac:(clear - NA1; lia)) | exact (wr_at_b47 bgasegs m1 PT (8 * NN) HT MI ltac:(clear - NA1; lia))].
  Qed.

  Lemma callee_asan : forall cells m1 (st sa j : nat), KSNB cells m1 -> (st + j <= 2 * length A)%nat -> (sa + j <= length A)%nat ->
    shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1 /\
    acc bgasegs m1 (rp + 8 * Z.of_nat st) (8 * Z.of_nat j) /\ acc bgasegs m1 (PA + 8 * Z.of_nat sa) (8 * Z.of_nat j) /\
    aptrs3 (rp + 8 * Z.of_nat st) (PA + 8 * Z.of_nat sa) (rp + 8 * Z.of_nat st) (Z.of_nat j) lo /\
    aptrs3 (rp + 8 * Z.of_nat st) (PA + 8 * Z.of_nat sa) (PA + 8 * Z.of_nat sa) (Z.of_nat j) lo.
  Proof using SHBC ACR ACA APT LO NA1.
    intros cells m1 st sa j IB Hst Hsa. pose proof (run_bounds _ _ IB) as (BA & BR & BT).
    pose proof IB as (HA & HW & HT & FR & ST & MI & MU & WM).
    split; [exact (shb_at m1 MU)|].
    split. { apply (acc_tr bgasegs _ m m1 rp (8 * NN) (8 * Z.of_nat st) (8 * Z.of_nat j) ACR MU OFFfin); clear - BR Hst; lia. }
    split. { apply (acc_tr bgasegs _ m m1 PA (8 * NA) (8 * Z.of_nat sa) (8 * Z.of_nat j) ACA MU OFFfin); clear - BA Hsa; lia. }
    destruct APT as (A1 & A2' & A3' & A4' & A5' & A6' & _). unfold aptrs3.
    assert (E8 : ((rp + 8 * Z.of_nat st) mod 8 = 0)%Z) by (clear - A1; Z.div_mod_to_equations; lia).
    assert (E8a : ((PA + 8 * Z.of_nat sa) mod 8 = 0)%Z) by (clear - A2'; Z.div_mod_to_equations; lia).
    split; (split; [exact E8|]; split; [exact E8a|]; split; [first [exact E8 | exact E8a]|]; split; [clear - A4' Hst; unfold SHLO, SHHI in *; lia | exact A6']).
  Qed.

  Lemma shA_rd : forall cells m1 (k : nat) ad, KSNB cells m1 -> (k < length A)%nat -> ad = wa (shad (PA + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACA APT LO NA1.
    intros cells m1 k ad IB Hk ->. pose proof (run_bounds _ _ IB) as (BA & BR & BT).
    pose proof IB as (HA & HW & HT & FR & ST & MI & MU & WM).
    destruct APT as (_ & A2' & _).
    apply (acc_rd_limb bgasegs _ m m1 PA NA 0 (Z.of_nat k) _ ACA MU OFFfin A2' BA);
      [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shR_rd : forall cells m1 (k : nat) ad, KSNB cells m1 -> (k < 2 * length A)%nat -> ad = wa (shad (rp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACR APT LO NA1.
    intros cells m1 k ad IB Hk ->. pose proof (run_bounds _ _ IB) as (BA & BR & BT).
    pose proof IB as (HA & HW & HT & FR & ST & MI & MU & WM).
    destruct APT as (A1' & _).
    apply (acc_rd_limb bgasegs _ m m1 rp NN 0 (Z.of_nat k) _ ACR MU OFFfin A1' BR);
      [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Ltac chkA I k := let IB := fresh "IB" in let RD := fresh "RD" in pose proof I as (_ & _ & _ & IB);
    let ad := cur_mem_addr in
    lazymatch type of IB with SNB _ _ _ _ _ _ _ ?cells ?mc =>
       pose proof (shA_rd cells mc k ad IB ltac:(lia) ltac:(sh_addr)) as RD end; zstep; clear RD IB.
  Ltac chkR I k := let IB := fresh "IB" in let RD := fresh "RD" in pose proof I as (_ & _ & _ & IB);
    let ad := cur_mem_addr in
    lazymatch type of IB with SNB _ _ _ _ _ _ _ ?cells ?mc =>
       pose proof (shR_rd cells mc k ad IB ltac:(lia) ltac:(sh_addr)) as RD end; zstep; clear RD IB.

  Ltac frame_ld I := let FR := fresh "FR" in pose proof I as (_ & _ & _ & _ & _ & _ & FR & _); zstep; clear FR.

  Ltac frame_st I I5 :=
    let FR := fresh "FR" in let ST := fresh "ST" in let MI := fresh "MI" in let MUs := fresh "MUs" in let WMs := fresh "WMs" in
    pose proof I as (_ & _ & _ & _ & _ & _ & FR & ST & MI & _ & _);
    lazymatch type of MI with mem_inv _ ?mm =>
      pose proof (munch_refl [(SP + -128, SP)]%Z mm) as MUs; pose proof (wmono_refl bgasegs mm) as WMs end;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (REFRM _ _ _ mm _ I MUs WMs MI FR ST) as I5 end;
    clear I FR ST MI MUs WMs.

  Ltac sn_st I k v Hv :=
    let ad := cur_mem_addr in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    lazymatch type of I with SNI _ _ _ _ _ _ _ ?cells ?mc ?R =>
      destruct (UPD cells mc R k v E eq_refl I ltac:(lia) Hv ltac:(lia)) as [SOK I2] end;
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.

  Ltac sn_st0 I k :=
    let ad := cur_mem_addr in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    lazymatch type of I with SNI _ _ _ _ _ _ _ ?cells ?mc ?R =>
      destruct (UPD cells mc R k 0%Z E eq_refl I ltac:(lia) ltac:(lia) ltac:(lia)) as [SOK I2] end;
    change (le8 (Z_to_bv 64 0)) with (Z_to_le_bytes 8 0) in I2;
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.

  Lemma sn_finish : forall jj m1 R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x27 x28 x29 x30 x31,
    KSNI (TF jj) m1 R -> fst (add_words (fst (add_words R R)) (sqr_words A)) = RES ->
    evt bgasegs POST (ST 0x2308ac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 a1 x22 x23 x24 x26 x27 x28 x29 x30 x31).
  Proof using LA LR0 LenR0 NA1 N31 A2 DRA DRT DAT LO SEPR SEPA SEPT SHBC ACR ACA ACT APT.
    intros until x31. intros I ERES.
    assert (CS : Z.of_nat (cells_size (TF jj)) = 128%Z) by reflexivity.
    pose proof I as (LRl & LenR & HR & IB). pose proof IB as (HA & HW & HT & FR & STf & MI & MU & WM).
    pose proof (run_bounds _ _ IB) as (BA & BR & BT).
    pose proof (proj1 STf) as LO0.
    assert (SP128 : (208 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESP128 ltac:(lia)) as ESP.
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (ENN : bv_unsigned (Z_to_bv 64 NN) = NN) by (apply unsigned_lit; lia).
    destruct (callee_asan _ m1 0%nat 0%nat 0%nat IB ltac:(lia) ltac:(lia)) as (SH1 & _).
    assert (AC1 : acc bgasegs m1 rp (8 * NN)).
    { pose proof (acc_tr bgasegs _ m m1 rp (8 * NN) 0 (8 * NN) ACR MU OFFfin) as X. rewrite Z.add_0_r in X. apply X; clear - BR; lia. }
    assert (APR : aptrs3 rp rp rp NN lo).
    { destruct APT as (A1' & _ & _ & A4' & _ & A6' & _). unfold aptrs3. tauto. }
    do 4 zstep. zstep.

    eapply evt_cut.
    { eapply bn_add_words_aspec with (a := R) (b := R) (lo := lo) (m := m1).
      - exact LRl.
      - exact LRl.
      - reflexivity.
      - rewrite LenR. lia.
      - rewrite ENN, LenR. lia.
      - exact HR.
      - exact HR.
      - rewrite LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact HW.
      - unfold alias_ok. left. reflexivity.
      - unfold alias_ok. left. reflexivity.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite ESP, LenR. lia.
      - rewrite ESP, LenR. lia.
      - rewrite ESP, LenR. lia.
      - exact MI.
      - exact SH1.
      - rewrite LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact AC1.
      - rewrite LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact AC1.
      - rewrite LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact AC1.
      - rewrite LenR. replace (Z.of_nat (2 * length A))%Z with NN by lia. exact APR. }
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite ESP, LenR in *.
    rewrite (ret_pc_even 0x2308c0) by lia.
    pose proof (add_words_fst R R LRl LRl eq_refl) as (Lres & Lad).
    assert (I2 : KSNI (TF jj) m2 (fst (add_words R R))).
    { replace (fst (add_words R R)) with (splice R 0 (fst (add_words R R))).
      2:{ unfold splice. cbn [firstn app Nat.add]. rewrite Lad, skipn_all, app_nil_r. reflexivity. }
      eapply (CALL _ m1 m2 R 0%nat (fst (add_words R R)) 48%Z CS I); [rewrite Lad; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lres].
      - rewrite Lad, LenR. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - rewrite Z.mul_0_r, Z.add_0_r. exact HS. }
    clear I IB HR HA HW HT FR STf MI MU WM MUc WMc MIc HS STc SH1 AC1. rename I2 into I.
    pose proof I as (LRl2 & LenR2 & HR & IB). pose proof IB as (HA & HW & HT & FR & STf & MI & MU & WM).
    destruct (callee_asan _ m2 0%nat 0%nat 0%nat IB ltac:(lia) ltac:(lia)) as (SH2 & _).
    assert (ACT2 : acc bgasegs m2 PT (16 * NA)).
    { pose proof (acc_tr bgasegs _ m m2 PT (8 * NN) 0 (16 * NA) ACT MU OFFfin) as X. rewrite Z.add_0_r in X. apply X; clear - BT; lia. }
    assert (ACA2 : acc bgasegs m2 PA (8 * NA)).
    { pose proof (acc_tr bgasegs _ m m2 PA (8 * NA) 0 (8 * NA) ACA MU OFFfin) as X. rewrite Z.add_0_r in X. apply X; clear - BA; lia. }
    assert (APS : aptrs2 PT PA (2 * NA) lo).
    { destruct APT as (_ & A2' & A3' & _ & A5' & A6' & _). unfold aptrs2. tauto. }
    frame_ld I.
    do 3 zstep. zstep.

    eapply evt_cut.
    { eapply bn_sqr_words_aspec with (a := A) (lo := lo) (m := m2).
      - exact LA.
      - lia.
      - exact A2.
      - exact HA.
      - replace (16 * NA)%Z with (8 * NN)%Z by lia. exact HT.
      - lia.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite ESP. lia.
      - rewrite ESP. lia.
      - exact MI.
      - exact SH2.
      - exact ACT2.
      - exact ACA2.
      - exact APS. }
    intros ms' PO. unfold sqw_apost in PO.
    destruct PO as (u0' & u1' & u2' & w0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m3 & E & MUs & WMs & MIs & HTS & STs).
    subst ms'. rewrite ESP in *.
    rewrite (ret_pc_even 0x2308d4) by lia.
    assert (HR3 : limbs_at bgasegs m3 rp (fst (add_words R R))).
    { eapply limbs_at_transport; [exact HR | exact MUs | rewrite Lad, LenR; djtac]. }
    eapply (rw_cells_transport bgasegs _ m2 m3) in FR; [| exact MUs | exact WMs | cbn [disjoint_from]; rewrite CS; clear - SEPT; lia].
    assert (HW3 : wr_at bgasegs m3 rp (8 * NN)) by (eapply wr_at_transport; [exact HW | exact WMs]).
    assert (MU3 : munch Wfin m m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUs]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM3 : wmono bgasegs m m3) by (eapply wmono_trans; [exact WM | exact WMs]).
    assert (SH3 : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m3) by exact (shb_at m3 MU3).
    assert (ACR3 : acc bgasegs m3 rp (8 * NN)).
    { pose proof (acc_tr bgasegs _ m m3 rp (8 * NN) 0 (8 * NN) ACR MU3 OFFfin) as X. rewrite Z.add_0_r in X. apply X; clear - BR; lia. }
    assert (ACT3 : acc bgasegs m3 PT (8 * NN)).
    { pose proof (acc_tr bgasegs _ m m3 PT (8 * NN) 0 (8 * NN) ACT MU3 OFFfin) as X. rewrite Z.add_0_r in X. apply X; clear - BT; lia. }
    assert (APF : aptrs3 rp rp PT NN lo).
    { destruct APT as (A1' & _ & A3' & A4' & _ & A6' & _). unfold aptrs3. tauto. }
    clear HR HA HW HT STf MI MU WM MUs WMs I IB.
    apply (rw_cells_merge_prefix bgasegs _ _ [CB 16 jj; C8 a3]) in FR. cbn [cells_size csize Nat.add] in FR.
    do 4 zstep.
    do 14 zstep.
    release_frame FR STs (bv_unsigned sp).
    zstep.

    pose proof (sqr_words_limbs A LA) as LT. pose proof (W_sqr_words.sqr_words_length A) as LTn.
    eapply evt_cut.
    { eapply bn_add_words_aspec with (a := fst (add_words R R)) (b := sqr_words A) (lo := lo) (m := m3).
      - exact Lres.
      - exact LT.
      - rewrite LTn, Lad, LenR. reflexivity.
      - rewrite Lad, LenR. lia.
      - rewrite ENN, Lad, LenR. lia.
      - exact HR3.
      - exact HTS.
      - rewrite Lad, LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact HW3.
      - unfold alias_ok. left. reflexivity.
      - rewrite Lad, LenR. unfold alias_ok. right. lia.
      - exact STs.
      - lia.
      - rewrite Lad, LenR. lia.
      - rewrite Lad, LenR. lia.
      - rewrite Lad, LenR. lia.
      - exact MIs.
      - exact SH3.
      - rewrite Lad, LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact ACR3.
      - rewrite Lad, LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact ACR3.
      - rewrite Lad, LenR. replace (8 * Z.of_nat (2 * length A))%Z with (8 * NN)%Z by lia. exact ACT3.
      - rewrite Lad, LenR. replace (Z.of_nat (2 * length A))%Z with NN by lia. exact APF. }
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m4 & E & MUf & WMf & MIf & HSf & STff).
    subst ms'. rewrite Lad, LenR in *.
    apply evt_done. unfold W_sqr_normal.vl_post2.
    do 15 eexists. exists m4. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU3|]. eapply munch_weaken; [|exact MUf]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split. { eapply wmono_trans; [exact WM3 | exact WMf]. }
    split; [exact MIf|].
    split. { rewrite <- ERES. exact HSf. }
    split. { eapply limbs_at_transport; [exact HTS | exact MUf | rewrite LTn; djtac]. }
    exact STff.
  Qed.

  Lemma slice_tail : forall k, slice A (1 + k) (length A - 1 - k) = skipn (1 + k) A.
  Proof. intros k. unfold slice. apply firstn_all2. rewrite length_skipn. lia. Qed.
  Lemma slice_tail0 : slice A 1 (length A - 1) = skipn 1 A.
  Proof. unfold slice. apply firstn_all2. rewrite length_skipn. lia. Qed.

  Lemma sn_loop : forall (cnt k : nat) R jj m1 x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
    (k + cnt + 1 = length A)%nat -> (1 <= cnt)%nat -> (1 <= k)%nat -> KSNI (TF jj) m1 R ->
    (forall m' R' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x27 x28 x29 x30 x31,
       KSNI (TF jj) m' R' -> R' = sqr_normal_loop A cnt k R ->
       evt bgasegs POST (ST 0x2308ac m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 a1 x22 x23 x24 x26 x27 x28 x29 x30 x31)) ->
    evt bgasegs POST (ST 0x230860 m1 x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (NA - 1 - Z.of_nat k)) x13 x14 x15 x16 x17 (Z_to_bv 64 1) a1
                         (Z_to_bv 64 (rp + 8 * (1 + 2 * Z.of_nat k))) x23 (Z_to_bv 64 (8 * (Z.of_nat k - 1)))
                         (Z_to_bv 64 (rp + 8 * (NA + 1))) (Z_to_bv 64 (shad (PA + 8 * Z.of_nat k))) x28 x29 x30 x31).
  Proof using LA LR0 LenR0 NA1 N31 A2 DRA DRT DAT LO SEPR SEPA SEPT SHBC ACR ACA ACT APT.
    induction cnt as [|cnt IH]; intros k R jj m1 x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 Hk Hc K1 I K; [lia|].
    assert (CS : Z.of_nat (cells_size (TF jj)) = 128%Z) by reflexivity.
    pose proof I as (LRl & LenR & HR & IB). pose proof IB as (HA & HW & HT & FR & STf & MI & MU & WM).
    pose proof (run_bounds _ _ IB) as (BA & BR & BT).
    pose proof (proj1 STf) as LO0.
    pose proof (ESP128 ltac:(clear - LO LO0; lia)) as ESP.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word a3) as R3. unfold inr64 in R0, R1, R3.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    set (j := (length A - 1 - k)%nat).
    assert (Ej : (NA - 1 - Z.of_nat k = Z.of_nat j)%Z) by (subst j; lia).
    rewrite Ej.

    chkA I k. zstep. chk0.
    zstep.

    assert (NK : nth_error A k = Some (nth k A 0%Z)) by (apply nth_error_nth'; lia).
    assert (Rw : (0 <= nth k A 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA).
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgasegs m1 PA A k _ ad HA NK ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    do 2 zstep. zstep.
    replace (PA + 8 * (Z.of_nat k - 1) + 16)%Z with (PA + 8 * (1 + Z.of_nat k))%Z by lia.

    assert (Erk : bv_unsigned (Z_to_bv 64 (rp + 8 * (1 + 2 * Z.of_nat k))) = (rp + 8 * (1 + 2 * Z.of_nat k))%Z) by (apply unsigned_lit; lia).
    assert (Eak : bv_unsigned (Z_to_bv 64 (PA + 8 * (1 + Z.of_nat k))) = (PA + 8 * (1 + Z.of_nat k))%Z) by (apply unsigned_lit; lia).
    assert (Ejw : bv_unsigned (Z_to_bv 64 (Z.of_nat j)) = Z.of_nat j) by (apply unsigned_lit; lia).
    assert (Eww : bv_unsigned (Z_to_bv 64 (nth k A 0%Z)) = nth k A 0%Z) by (apply unsigned_lit; lia).
    assert (LS : length (slice R (1 + 2 * k) j) = length (skipn (1 + k) A)) by (rewrite slice_length, length_skipn by lia; lia).
    pose proof (mul_add_words_spec (slice R (1 + 2 * k) j) (skipn (1 + k) A) (nth k A 0%Z) (slice_limbs _ _ _ LRl) (limbs_skipn _ _ LA) LS Rw) as MSP.
    assert (HAk : limbs_at bgasegs m1 (PA + 8 * (1 + Z.of_nat k)) (skipn (1 + k) A)).
    { rewrite <- (firstn_skipn (1 + k) A) in HA. apply limbs_at_app in HA. destruct HA as [_ HA2].
      rewrite length_firstn in HA2. replace (Nat.min (1 + k) (length A)) with (1 + k)%nat in HA2 by lia.
      replace (PA + 8 * Z.of_nat (1 + k))%Z with (PA + 8 * (1 + Z.of_nat k))%Z in HA2 by lia. exact HA2. }
    assert (HRk : limbs_at bgasegs m1 (rp + 8 * (1 + 2 * Z.of_nat k)) (slice R (1 + 2 * k) j)).
    { unfold slice. rewrite <- (firstn_skipn (1 + 2 * k) R) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
      rewrite <- (firstn_skipn j (skipn (1 + 2 * k) R)) in HR2. apply limbs_at_app in HR2. destruct HR2 as [HR2 _].
      rewrite length_firstn in HR2. replace (Nat.min (1 + 2 * k) (length R)) with (1 + 2 * k)%nat in HR2 by lia.
      replace (rp + 8 * Z.of_nat (1 + 2 * k))%Z with (rp + 8 * (1 + 2 * Z.of_nat k))%Z in HR2 by lia. exact HR2. }
    destruct (callee_asan _ m1 (1 + 2 * k)%nat (1 + k)%nat j IB ltac:(subst j; lia) ltac:(subst j; lia)) as (SH1 & ACR1 & ACA1 & APT1 & _).
    replace (rp + 8 * Z.of_nat (1 + 2 * k))%Z with (rp + 8 * (1 + 2 * Z.of_nat k))%Z in ACR1, APT1 by lia.
    replace (PA + 8 * Z.of_nat (1 + k))%Z with (PA + 8 * (1 + Z.of_nat k))%Z in ACA1, APT1 by lia.
    assert (Elj : length (skipn (1 + k) A) = j) by (rewrite length_skipn; subst j; lia).
    eapply evt_cut.
    { eapply bn_mul_add_words_aspec with (a := skipn (1 + k) A) (r := slice R (1 + 2 * k) j) (lo := lo) (m := m1).
      - apply limbs_skipn. exact LA.
      - apply slice_limbs. exact LRl.
      - exact LS.
      - rewrite length_skipn. lia.
      - rewrite Ejw, length_skipn. lia.
      - rewrite Eak. exact HAk.
      - rewrite Erk. exact HRk.
      - rewrite Erk, length_skipn. apply (wr_at_sub bgasegs m1 rp (8 * NN) (8 * (1 + 2 * Z.of_nat k)) (8 * Z.of_nat (length A - (1 + k))) HW); lia.
      - rewrite Erk, Eak, length_skipn. unfold alias_ok. right. lia.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite Erk, ESP, length_skipn. lia.
      - rewrite Eak, ESP, length_skipn. lia.
      - exact MI.
      - exact SH1.
      - rewrite Erk, Elj. exact ACR1.
      - rewrite Eak, Elj. exact ACA1.
      - rewrite Erk, Eak, Elj. exact APT1. }
    intros ms' PO. unfold maw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite Erk, ESP, Eww, length_skipn in *.
    rewrite (ret_pc_even 0x230880) by lia.
    destruct (mul_add_words (slice R (1 + 2 * k) j) (skipn (1 + k) A) (nth k A 0%Z)) as [seg c] eqn:EMA. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc. try rewrite length_skipn in Eseg.
    assert (I2 : KSNI (TF jj) m2 (splice R (1 + 2 * k) seg)).
    { eapply (CALL _ m1 m2 R (1 + 2 * k)%nat seg 80%Z CS I); [rewrite Eseg; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lseg].
      - rewrite Eseg. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - replace (rp + 8 * Z.of_nat (1 + 2 * k))%Z with (rp + 8 * (1 + 2 * Z.of_nat k))%Z by lia. exact HS. }
    clear I IB HR HA HW HT FR STf MI MU WM MUc WMc MIc HS STc HAk HRk SH1 ACR1 ACA1 APT1. rename I2 into I.

    do 3 zstep.
    chkR I (length A + k)%nat. chk0.
    sn_st I (1 + 2 * k + length seg)%nat c Lc.
    rewrite (upd_splice_snoc R (1 + 2 * k) seg c) in I by (rewrite Eseg, LenR; lia).
    do 2 zstep.
    rewrite (bn_swrap32_small (Z.of_nat j + -1)) by lia.
    do 2 zstep.
    assert (STEP : forall c', sqr_normal_loop A (S c') k R = sqr_normal_loop A c' (S k) (splice R (1 + 2 * k) (seg ++ [c]))).
    { intros c'. cbn [sqr_normal_loop]. fold j. rewrite slice_tail, EMA. reflexivity. }
    zstep. if_cases KB; zify_cond KB.
    -
      rewrite ?unsigned_lit in KB by lia.
      replace (rp + 8 * (1 + 2 * Z.of_nat k) + 16)%Z with (rp + 8 * (1 + 2 * Z.of_nat (S k)))%Z by lia.
      replace (8 * (Z.of_nat k - 1) + 8)%Z with (8 * (Z.of_nat (S k) - 1))%Z by lia.
      replace (Z.of_nat j + -1)%Z with (NA - 1 - Z.of_nat (S k))%Z by lia.
      setreg 27%Z (Z_to_bv 64 (shad (PA + 8 * Z.of_nat (S k)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply IH; [lia | lia | lia | exact I |].
      intros m' R' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y26 y27 y28 y29 y30 y31 I' ER'.
      eapply K; [exact I' |]. rewrite STEP. exact ER'.
    -
      assert (Ec : cnt = 0%nat) by (rewrite ?unsigned_lit in KB by lia; lia). subst cnt.
      eapply K; [exact I |]. rewrite STEP. reflexivity.
  Qed.

  Lemma bn_sqr_normal_aspec :
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x230748) fc None m (seg_rom bgasegs)).
  Proof.
    pose proof (munch_refl Wfin m) as MU. pose proof (munch_refl [(SP + -128, SP)]%Z m) as MUF. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word a3) as R3. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, R3, RSP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RR) as BR.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    pose proof (proj1 STK) as LO0.
    assert (SP128 : (208 <= SP)%Z) by (clear - LO LO0; lia).
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold sqn_ptrs, SHHI in APT; tauto).
    pose proof (wr_at_b47 bgasegs m rp (8 * NN) WR MI0 ltac:(clear - NA1; lia)) as BR47.
    pose proof (limbs_at_b47 bgasegs m PA A RA MI0 ltac:(clear - NA1; lia)) as BA47.
    pose proof SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 128%nat STK.
    apply (rw_cells_split_CB bgasegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 14 zstep. zstep. do 4 zstep.
    zstep. setreg 19%Z (Z_to_bv 64 NN) ltac:(rewrite <- A2; f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite bn_swrap32_small by lia; lia).
    zstep. zstep. zstep. zstep.
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * length A - 1))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -128)) = (SP + -128)%Z) by (apply ESP128; clear - SP128; lia).
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j0 :: CB 8 ?j1 :: CB 8 ?j2 :: _) =>
      assert (I : KSNI (T0 j0 j1 j2) m1 r0);
      [ unfold SNI, SNB; split; [exact LR0|]; split; [exact LenR0|];
        split; [ eapply limbs_at_transport; [exact RR | exact MUF | rewrite LenR0; djtac] |];
        split; [ eapply limbs_at_transport; [exact RA | exact MUF | djtac] |];
        split; [exact WR|]; split; [exact WT|]; split; [exact FR|]; split; [exact STK|]; split; [exact MI0|]; split; [exact MU | exact WM] | ]
    end.
    clear MUF FR STK RA RR WR WT MI0 MU WM G1 G2.

    do 2 zstep.
    chkR I (2 * length A - 1)%nat. chk0.
    sn_st0 I (2 * length A - 1)%nat.

    do 2 zstep.
    chkR I 0%nat. chk0.
    zstep.
    frame_st I I5. rename I5 into I.
    zstep.
    lazymatch type of I with SNI _ _ _ _ _ _ _ ?cells ?mc ?R =>
      destruct (UPD cells mc R 0%nat 0%Z rp eq_refl I ltac:(lia) ltac:(lia) ltac:(lia)) as [SOK I2] end.
    rewrite Z_to_bv_bv_unsigned in SOK. rewrite Z_to_bv_bv_unsigned in I2. change (le8 (Z_to_bv 64 0)) with (Z_to_le_bytes 8 0) in I2.
    zstep. clear SOK I.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end. rename I2 into I.
    rewrite (upd_swap0 r0 (2 * length A - 1)) in I by (rewrite LenR0; lia).
    assert (TOF : forall j0 c1 mx Rx, csize c1 = 8%nat -> KSNI (CB 8 j0 :: c1 :: C8 a3 :: REST) mx Rx -> exists jj, KSNI (TF jj) mx Rx).
    { intros j0 c1 mx Rx C1 J. exists (cells_bytes [CB 8 j0; c1]).
      eapply (RECELL _ _ _ _ J). intros FR. apply (rw_cells_merge_prefix bgasegs _ _ [CB 8 j0; c1]) in FR.
      cbn [cells_size csize] in FR. rewrite C1 in FR. exact FR. }

    zstep. rewrite lts_words_small by (rewrite ?A2, ?unsigned_lit; lia). rewrite A2, (unsigned_lit 2) by lia.
    if_cases KR; zify_cond KR.
    { assert (E1 : length A = 1%nat) by (rewrite ?A2 in KR; lia).
      destruct ((fun C => TOF _ _ _ _ C I) eq_refl) as (jj & I').
      eapply sn_finish; [exact I' |].
      unfold sqr_normal. rewrite E1. cbn [Nat.ltb Nat.leb Nat.sub Nat.mul Nat.add sqr_normal_loop]. reflexivity. }
    assert (N2 : (2 <= length A)%nat) by (rewrite ?A2 in KR; lia).
    clear KR.

    do 2 zstep.
    chkA I 0%nat. chk0.
    pose proof I as (LRl & LenR & HR & IB). pose proof IB as (HA & HW & HT & FR & STf & MI & MU2 & WM2).
    assert (N0 : nth_error A 0 = Some (nth 0 A 0%Z)) by (apply nth_error_nth'; lia).
    assert (Rw : (0 <= nth 0 A 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA).
    pose proof (limbs_at_read_nth bgasegs _ PA A 0 _ a1 HA N0 ltac:(symmetry; unfold wa; rewrite Z.mul_0_r, Z.add_0_r; apply Z_to_bv_bv_unsigned)) as RD.
    zstep. clear RD.
    zstep. zstep. rewrite (bn_swrap32_small (bv_unsigned a2 + -1)) by lia. rewrite A2.
    do 4 zstep. zstep.
    assert (Er1 : bv_unsigned (Z_to_bv 64 (rp + 8)) = (rp + 8)%Z) by (apply unsigned_lit; lia).
    assert (Ea1 : bv_unsigned (Z_to_bv 64 (PA + 8)) = (PA + 8)%Z) by (apply unsigned_lit; lia).
    assert (En1 : bv_unsigned (Z_to_bv 64 (NA + -1)) = (NA + -1)%Z) by (apply unsigned_lit; lia).
    assert (Eww : bv_unsigned (Z_to_bv 64 (nth 0 A 0%Z)) = nth 0 A 0%Z) by (apply unsigned_lit; lia).
    lazymatch type of HA with limbs_at _ ?mc _ _ =>
      assert (HA1 : limbs_at bgasegs mc (PA + 8) (skipn 1 A));
      [ rewrite <- (firstn_skipn 1 A) in HA; apply limbs_at_app in HA; destruct HA as [_ HA2];
        rewrite length_firstn in HA2; replace (Nat.min 1 (length A)) with 1%nat in HA2 by lia; exact HA2 | ]
    end.
    pose proof (mul_words_spec (skipn 1 A) (nth 0 A 0%Z) (limbs_skipn _ _ LA) ltac:(unfold limb; rewrite BW_lit; exact Rw)) as MS0.
    destruct (callee_asan _ _ 1%nat 1%nat (length A - 1)%nat IB ltac:(lia) ltac:(lia)) as (SH1 & ACR1 & ACA1 & _ & APT1).
    replace (rp + 8 * Z.of_nat 1)%Z with (rp + 8)%Z in ACR1, APT1 by lia.
    replace (PA + 8 * Z.of_nat 1)%Z with (PA + 8)%Z in ACA1, APT1 by lia.
    eapply evt_cut.
    { eapply bn_mul_words_aspec with (a := skipn 1 A) (lo := lo).
      - apply limbs_skipn. exact LA.
      - rewrite length_skipn. lia.
      - rewrite En1, length_skipn. lia.
      - rewrite Ea1. exact HA1.
      - rewrite Er1, length_skipn. apply (wr_at_sub bgasegs _ rp (8 * NN) 8 (8 * Z.of_nat (length A - 1)) HW); lia.
      - rewrite Er1, Ea1, length_skipn. unfold alias_ok. right. lia.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite Er1, ESP, length_skipn. lia.
      - rewrite Ea1, ESP, length_skipn. lia.
      - exact MI.
      - exact SH1.
      - rewrite Er1, length_skipn. exact ACR1.
      - rewrite Ea1, length_skipn. exact ACA1.
      - rewrite Er1, Ea1, length_skipn. exact APT1. }
    intros ms' PO. unfold mw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite Er1, ESP, Eww, length_skipn in *.
    rewrite (ret_pc_even 0x230810) by lia.
    destruct (mul_words (skipn 1 A) (nth 0 A 0%Z)) as [seg0 c0] eqn:EMW. cbn [fst snd] in *.
    destruct MS0 as (Lseg0 & Eseg0 & Lc0 & _). unfold limb, BW in Lc0. try rewrite length_skipn in Eseg0.
    lazymatch type of I with SNI _ _ _ _ _ _ _ ?cells ?mc ?R =>
      assert (I2 : KSNI cells m4 (splice R 1 seg0));
      [ eapply (CALL cells mc m4 _ 1%nat seg0 80%Z eq_refl I); [rewrite Eseg0; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lseg0];
        [ rewrite Eseg0; eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia
        | replace (rp + 8 * Z.of_nat 1)%Z with (rp + 8)%Z by lia; exact HS ] | ]
    end.
    clear I IB HR HA HW HT FR STf MI MU2 WM2 MUc WMc MIc HS STc HA1 SH1 ACR1 ACA1 APT1. rename I2 into I.
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    zstep. do 2 zstep.
    chkR I (length A). chk0.
    zstep. rewrite (bn_swrap32_small (bv_unsigned a2 + -2)) by lia. rewrite A2.
    sn_st I (1 + length seg0)%nat c0 Lc0.
    rewrite (upd_splice_snoc _ 1 seg0 c0) in I by (rewrite Eseg0, upd_length2 by lia; lia).
    assert (EM : forall R', R' = sqr_normal_loop A (length A - 2) 1 (splice (upd (upd r0 0 0) (2 * length A - 1) 0) 1 (seg0 ++ [c0])) ->
                 fst (add_words (fst (add_words R' R')) (sqr_words A)) = RES).
    { intros R' ->. unfold sqr_normal. rewrite (proj2 (Nat.ltb_lt 1 (length A))) by lia. rewrite slice_tail0, EMW. reflexivity. }
    zstep. if_cases KZ; zify_cond KZ.
    -
      assert (E2 : length A = 2%nat) by lia.
      destruct ((fun C => TOF _ _ _ _ C I) eq_refl) as (jj & I').
      eapply sn_finish; [exact I' |]. apply EM. rewrite E2. reflexivity.
    -
      do 5 zstep.
      frame_st I I5. rename I5 into I.
      do 5 zstep.
      rewrite shl32_shr29 by (rewrite A2; lia). rewrite A2.
      destruct ((fun C => TOF _ _ _ _ C I) eq_refl) as (jj & I').
      replace (rp + 24)%Z with (rp + 8 * (1 + 2 * Z.of_nat 1))%Z by lia.
      replace (rp + 8 * NA + 8)%Z with (rp + 8 * (NA + 1))%Z by lia.
      replace (NA + -2)%Z with (NA - 1 - Z.of_nat 1)%Z by lia.
      setreg 24%Z (Z_to_bv 64 (8 * (Z.of_nat 1 - 1))) ltac:(reflexivity).
      setreg 27%Z (Z_to_bv 64 (shad (PA + 8 * Z.of_nat 1))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
      eapply (sn_loop (length A - 2)%nat 1%nat); [lia | lia | lia | exact I' |].
      intros m' R' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y26 y27 y28 y29 y30 y31 I'' ER'.
      eapply sn_finish; [exact I'' | apply EM; exact ER'].
  Qed.
End Mach.
