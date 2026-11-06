(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_words W_mul_add_words W_add_words W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require Import W_sqr_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_normal_entry := 0xfcf4c%Z.

Ltac djtac := cbn [disjoint_from cells_size csize Nat.add]; repeat match goal with |- _ /\ _ => split end; try exact I; lia.

Definition vl_post2 (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp tp_ n fs : Z) (res rest : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(rp, rp + 8 * n); (tp_, tp_ + 8 * n); (bv_unsigned sp - fs, bv_unsigned sp)]%Z m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ limbs_at segs m' rp res /\ limbs_at segs m' tp_ rest
    /\ stk segs m' lo (bv_unsigned sp).

Lemma firstn_len_app : forall (l1 l2 : list Z), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all. Qed.
Lemma skipn_len_app : forall (l1 l2 : list Z), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. Qed.
Lemma splice_app : forall (R : list Z) st s1 s2,
  (st + length s1 + length s2 <= length R)%nat ->
  splice (splice R st s1) (st + length s1) s2 = splice R st (s1 ++ s2).
Proof.
  intros R st s1 s2 H. unfold splice.
  set (P := firstn st R). assert (LP : length P = st) by (subst P; rewrite length_firstn; lia).
  set (Q := skipn (st + length s1) R).
  assert (E1 : firstn (st + length s1) (P ++ s1 ++ Q) = P ++ s1).
  { rewrite app_assoc. replace (st + length s1)%nat with (length (P ++ s1)) by (rewrite length_app, LP; lia). apply firstn_len_app. }
  assert (E2 : skipn (st + length s1 + length s2) (P ++ s1 ++ Q) = skipn (length s2) Q).
  { rewrite app_assoc. replace (st + length s1 + length s2)%nat with (length s2 + length (P ++ s1))%nat by (rewrite length_app, LP; lia).
    rewrite <- skipn_skipn. rewrite skipn_len_app. reflexivity. }
  rewrite E1, E2. subst Q. rewrite skipn_skipn, length_app, <- !app_assoc. do 3 f_equal. f_equal. lia.
Qed.
Lemma upd_splice_snoc : forall (R : list Z) st seg c,
  (st + length seg + 1 <= length R)%nat -> upd (splice R st seg) (st + length seg) c = splice R st (seg ++ [c]).
Proof. intros R st seg c H. unfold upd. apply splice_app. cbn [length]. lia. Qed.

Lemma upd_length2 : forall (l : list Z) i j v w, (i < length l)%nat -> (j < length l)%nat -> length (upd (upd l i v) j w) = length l.
Proof. intros. rewrite upd_length; rewrite upd_length; lia. Qed.

Lemma add_words_fst : forall a b, limbs a -> limbs b -> length a = length b ->
  limbs (fst (add_words a b)) /\ length (fst (add_words a b)) = length a.
Proof.
  intros a b Ha Hb L. pose proof (add_words_spec a b Ha Hb L) as H. destruct (add_words a b) as [r c]. cbn [fst]. tauto.
Qed.

Section Core.
  Variables (sp a0 : word) (m : word -> option byte) (lo : Z) (A : list Z) (PA PT : Z).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation NA := (Z.of_nat (length A)).
  Notation NN := (2 * Z.of_nat (length A))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (2 * Z.of_nat (length A))); (PT, PT + 8 * (2 * Z.of_nat (length A))); (bv_unsigned sp - 128, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRT : (rp + 8 * NN <= PT \/ PT + 8 * NN <= rp)%Z.
  Hypothesis DAT : (PA + 8 * NA <= PT \/ PT + 8 * NN <= PA)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 128 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 128 \/ SP <= PA)%Z.
  Hypothesis SEPT : (PT + 8 * NN <= SP - 128 \/ SP <= PT)%Z.

  Definition SNB (cells : list cell) (m1 : word -> option byte) : Prop :=
    limbs_at bgpsegs m1 PA A /\ wr_at bgpsegs m1 rp (8 * NN) /\ wr_at bgpsegs m1 PT (8 * NN) /\
    rw_cells bgpsegs m1 (SP + -96) cells /\ stk bgpsegs m1 lo (SP + -96) /\
    mem_inv bgpsegs m1 /\ munch Wfin m m1 /\ wmono bgpsegs m m1.

  Definition SNI (cells : list cell) (m1 : word -> option byte) (R : list Z) : Prop :=
    limbs R /\ length R = (2 * length A)%nat /\ limbs_at bgpsegs m1 rp R /\ SNB cells m1.

  Lemma sn_upd : forall cells m1 R k v ad,
    Z.of_nat (cells_size cells) = 96%Z ->
    SNI cells m1 R -> (k < 2 * length A)%nat -> (0 <= v < 18446744073709551616)%Z -> ad = (rp + 8 * Z.of_nat k)%Z ->
    store_ok bgpsegs m1 (Z_to_bv 64 ad) 8 = true /\
    SNI cells (write_to_mem m1 (Z_to_bv 64 ad) (le8 (Z_to_bv 64 v))) (upd R k v).
  Proof using LA DRA DRT DAT SEPR SEPA SEPT.
    intros cells m1 R k v ad CS (LR & LenR & HR & HA & WR & WT & FR & ST & MI & MU & WM) Hk Hv ->.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    destruct WT as (T0 & T1 & WT'). pose proof (conj T0 (conj T1 WT')) as WT.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgpsegs m1 (Z_to_bv 64 (rp + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)). apply (wr_at_store_ok bgpsegs m1 rp (8 * NN)); [exact WR | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)).
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
    assert (ER : R = firstn k R ++ [nth k R 0%Z] ++ skipn (S k) R).
    { rewrite app_assoc, <- firstn_S_snoc by lia. symmetry. apply firstn_skipn. }
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
    Z.of_nat (cells_size cells) = 96%Z ->
    SNI cells m1 R -> (st + length seg <= 2 * length A)%nat -> (0 <= fsz <= 32)%Z ->
    munch [(rp + 8 * Z.of_nat st, rp + 8 * Z.of_nat st + 8 * Z.of_nat (length seg)); (SP + -96 - fsz, SP + -96)]%Z m1 m2 ->
    wmono bgpsegs m1 m2 -> mem_inv bgpsegs m2 -> limbs_at bgpsegs m2 (rp + 8 * Z.of_nat st) seg -> stk bgpsegs m2 lo (SP + -96) ->
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
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (2 * Z.of_nat (length A))); (bv_unsigned a3, bv_unsigned a3 + 8 * (2 * Z.of_nat (length A))); (bv_unsigned sp - 128, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LR0 : limbs r0.
  Hypothesis LenR0 : length r0 = (2 * length A)%nat.
  Hypothesis NA1 : (1 <= NA)%Z.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = NA.
  Hypothesis RA : limbs_at bgpsegs m PA A.
  Hypothesis RR : limbs_at bgpsegs m rp r0.
  Hypothesis WR : wr_at bgpsegs m rp (8 * NN).
  Hypothesis WT : wr_at bgpsegs m PT (8 * NN).
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRT : (rp + 8 * NN <= PT \/ PT + 8 * NN <= rp)%Z.
  Hypothesis DAT : (PA + 8 * NA <= PT \/ PT + 8 * NN <= PA)%Z.
  Hypothesis STK : stk bgpsegs m lo SP.
  Hypothesis LO : (lo <= SP - 128)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 128 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 128 \/ SP <= PA)%Z.
  Hypothesis SEPT : (PT + 8 * NN <= SP - 128 \/ SP <= PT)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.

  Notation RES := (fst (sqr_normal A r0)).
  Notation POST := (vl_post2 bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a3) NN 128%Z RES (sqr_words A) lo m).
  Notation FCELLS := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation KSNI := (SNI sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) FCELLS).
  Notation UPD := (sn_upd sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) LA DRA DRT DAT SEPR SEPA SEPT FCELLS).
  Notation CALL := (sn_call sp a0 m lo A (bv_unsigned a1) (bv_unsigned a3) LA DRA DRT DAT SEPR SEPA SEPT FCELLS).

  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp a3 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (2 * Z.of_nat (length A))) a0 a2 a1
             x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Lemma ESP96 : (96 <= SP)%Z -> bv_unsigned (Z_to_bv 64 (SP + -96)) = (SP + -96)%Z.
  Proof.
    intros H. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia.
  Qed.

  Ltac sn_st I k v Hv :=
    let ad := cur_mem_addr in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    destruct (UPD _ _ k v E eq_refl I ltac:(lia) Hv ltac:(lia)) as [SOK I2];
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.

  Lemma sn_finish : forall m1 R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    KSNI m1 R -> fst (add_words (fst (add_words R R)) (sqr_words A)) = RES ->
    evt bgpsegs POST (ST 0xfd02c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ERES.
    pose proof I as (LRl & LenR & HR & HA & HW & HT & FR & STf & MI & MU & WM).
    pose proof (proj1 STf) as LO0.
    assert (SP96 : (128 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESP96 ltac:(lia)) as ESP.
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (ENN : bv_unsigned (Z_to_bv 64 NN) = NN) by (apply unsigned_lit; lia).
    do 4 zstep. zstep.

    eapply evt_cut.
    { eapply bn_add_words_spec with (a := R) (b := R) (lo := lo) (m := m1).
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
      - exact MI. }
    intros ms' PO. unfold aw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite ESP, LenR in *.
    rewrite (ret_pc_even 0xfd040) by lia.
    pose proof (add_words_fst R R LRl LRl eq_refl) as (Lres & Lad).
    assert (I2 : KSNI m2 (fst (add_words R R))).
    { replace (fst (add_words R R)) with (splice R 0 (fst (add_words R R))).
      2:{ unfold splice. cbn [firstn app Nat.add]. rewrite Lad, skipn_all, app_nil_r. reflexivity. }
      eapply (CALL m1 m2 R 0%nat (fst (add_words R R)) 16%Z eq_refl I); [rewrite Lad; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lres].
      - rewrite Lad, LenR. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - rewrite Z.mul_0_r, Z.add_0_r. exact HS. }
    clear I HR HA HW HT FR STf MI MU WM MUc WMc MIc HS STc. rename I2 into I.
    pose proof I as (LRl2 & LenR2 & HR & HA & HW & HT & FR & STf & MI & MU & WM).
    do 3 zstep. zstep.

    eapply evt_cut.
    { eapply bn_sqr_words_spec with (a := A) (lo := lo) (m := m2).
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
      - exact MI. }
    intros ms' PO. unfold sqw_post in PO.
    destruct PO as (u0' & u1' & u2' & w0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m3 & E & MUs & WMs & MIs & HTS & STs).
    subst ms'. rewrite ESP in *.
    rewrite (ret_pc_even 0xfd050) by lia.
    assert (HR3 : limbs_at bgpsegs m3 rp (fst (add_words R R))).
    { eapply limbs_at_transport; [exact HR | exact MUs | rewrite Lad, LenR; djtac]. }
    eapply (rw_cells_transport bgpsegs _ m2 m3) in FR; [| exact MUs | exact WMs | djtac].
    assert (HW3 : wr_at bgpsegs m3 rp (8 * NN)) by (eapply wr_at_transport; [exact HW | exact WMs]).
    assert (MU3 : munch Wfin m m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUs]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM3 : wmono bgpsegs m m3) by (eapply wmono_trans; [exact WM | exact WMs]).
    clear HR HA HW HT STf MI MU WM MUs WMs I.
    do 4 zstep.
    do 13 zstep.
    release_frame FR STs (bv_unsigned sp).
    zstep.

    pose proof (sqr_words_limbs A LA) as LT. pose proof (sqr_words_length A) as LTn.
    eapply evt_cut.
    { eapply bn_add_words_spec with (a := fst (add_words R R)) (b := sqr_words A) (lo := lo) (m := m3).
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
      - exact MIs. }
    intros ms' PO. unfold aw_post, wl_post in PO.
    destruct PO as (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m4 & E & MUf & WMf & MIf & HSf & STff).
    subst ms'. rewrite Lad, LenR in *.
    apply evt_done. unfold vl_post2.
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

  Lemma sn_loop : forall (cnt k : nat) R m1 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
    (k + cnt + 1 = length A)%nat -> (1 <= cnt)%nat -> (1 <= k)%nat -> KSNI m1 R ->
    (forall m' R' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31,
       KSNI m' R' -> R' = sqr_normal_loop A cnt k R ->
       evt bgpsegs POST (ST 0xfd02c m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31)) ->
    evt bgpsegs POST (ST 0xfcffc m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (NA - 1 - Z.of_nat k)) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (rp + 8 * (1 + 2 * Z.of_nat k))) (Z_to_bv 64 (PA + 8 * (1 + Z.of_nat k))) x24
                         (Z_to_bv 64 (rp + 8 * (NA + Z.of_nat k))) (Z_to_bv 64 1) x28 x29 x30 x31).
  Proof.
    induction cnt as [|cnt IH]; intros k R m1 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 Hk Hc K1 I K; [lia|].
    pose proof I as (LRl & LenR & HR & HA & HW & HT & FR & STf & MI & MU & WM).
    pose proof (proj1 STf) as LO0.
    pose proof (ESP96 ltac:(clear - LO LO0; lia)) as ESP.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word a3) as R3. unfold inr64 in R0, R1, R3.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    set (j := (length A - 1 - k)%nat).
    assert (Ej : (NA - 1 - Z.of_nat k = Z.of_nat j)%Z) by (subst j; lia).
    rewrite Ej.

    assert (NK : nth_error A k = Some (nth k A 0%Z)) by (apply nth_error_nth'; lia).
    assert (Rw : (0 <= nth k A 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA).
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgpsegs m1 PA A k _ ad HA NK ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    zstep. do 3 zstep. zstep.

    assert (Erk : bv_unsigned (Z_to_bv 64 (rp + 8 * (1 + 2 * Z.of_nat k))) = (rp + 8 * (1 + 2 * Z.of_nat k))%Z) by (apply unsigned_lit; destruct HW as (W0 & W1 & _); lia).
    assert (Eak : bv_unsigned (Z_to_bv 64 (PA + 8 * (1 + Z.of_nat k))) = (PA + 8 * (1 + Z.of_nat k))%Z) by (apply unsigned_lit; lia).
    assert (Ejw : bv_unsigned (Z_to_bv 64 (Z.of_nat j)) = Z.of_nat j) by (apply unsigned_lit; lia).
    assert (Eww : bv_unsigned (Z_to_bv 64 (nth k A 0%Z)) = nth k A 0%Z) by (apply unsigned_lit; lia).
    assert (LS : length (slice R (1 + 2 * k) j) = length (skipn (1 + k) A)) by (rewrite slice_length, length_skipn by lia; lia).
    pose proof (mul_add_words_spec (slice R (1 + 2 * k) j) (skipn (1 + k) A) (nth k A 0%Z) (slice_limbs _ _ _ LRl) (limbs_skipn _ _ LA) LS Rw) as MSP.
    assert (HAk : limbs_at bgpsegs m1 (PA + 8 * (1 + Z.of_nat k)) (skipn (1 + k) A)).
    { rewrite <- (firstn_skipn (1 + k) A) in HA. apply limbs_at_app in HA. destruct HA as [_ HA2].
      rewrite length_firstn in HA2. replace (Nat.min (1 + k) (length A)) with (1 + k)%nat in HA2 by lia.
      replace (PA + 8 * Z.of_nat (1 + k))%Z with (PA + 8 * (1 + Z.of_nat k))%Z in HA2 by lia. exact HA2. }
    assert (HRk : limbs_at bgpsegs m1 (rp + 8 * (1 + 2 * Z.of_nat k)) (slice R (1 + 2 * k) j)).
    { unfold slice. rewrite <- (firstn_skipn (1 + 2 * k) R) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
      rewrite <- (firstn_skipn j (skipn (1 + 2 * k) R)) in HR2. apply limbs_at_app in HR2. destruct HR2 as [HR2 _].
      rewrite length_firstn in HR2. replace (Nat.min (1 + 2 * k) (length R)) with (1 + 2 * k)%nat in HR2 by lia.
      replace (rp + 8 * Z.of_nat (1 + 2 * k))%Z with (rp + 8 * (1 + 2 * Z.of_nat k))%Z in HR2 by lia. exact HR2. }
    eapply evt_cut.
    { eapply bn_mul_add_words_spec with (a := skipn (1 + k) A) (r := slice R (1 + 2 * k) j) (lo := lo) (m := m1).
      - apply limbs_skipn. exact LA.
      - apply slice_limbs. exact LRl.
      - exact LS.
      - rewrite length_skipn. lia.
      - rewrite Ejw, length_skipn. lia.
      - rewrite Eak. exact HAk.
      - rewrite Erk. exact HRk.
      - rewrite Erk, length_skipn. apply (wr_at_sub bgpsegs m1 rp (8 * NN) (8 * (1 + 2 * Z.of_nat k)) (8 * Z.of_nat (length A - (1 + k))) HW); lia.
      - rewrite Erk, Eak, length_skipn. unfold alias_ok. right. lia.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite Erk, ESP, length_skipn. lia.
      - rewrite Eak, ESP, length_skipn. lia.
      - exact MI. }
    intros ms' PO. unfold maw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite Erk, ESP, Eww, length_skipn in *.
    rewrite (ret_pc_even 0xfd014) by lia.
    destruct (mul_add_words (slice R (1 + 2 * k) j) (skipn (1 + k) A) (nth k A 0%Z)) as [seg c] eqn:EMA. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc. try rewrite length_skipn in Eseg.
    assert (I2 : KSNI m2 (splice R (1 + 2 * k) seg)).
    { eapply (CALL m1 m2 R (1 + 2 * k)%nat seg 32%Z eq_refl I); [rewrite Eseg; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lseg].
      - rewrite Eseg. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - replace (rp + 8 * Z.of_nat (1 + 2 * k))%Z with (rp + 8 * (1 + 2 * Z.of_nat k))%Z by lia. exact HS. }
    clear I HR HA HW HT FR STf MI MU WM MUc WMc MIc HS STc HAk HRk. rename I2 into I.

    sn_st I (1 + 2 * k + length seg)%nat c Lc.
    rewrite (upd_splice_snoc R (1 + 2 * k) seg c) in I by (rewrite Eseg, LenR; lia).
    do 4 zstep.
    rewrite (bn_swrap32_small (Z.of_nat j + -1)) by lia.
    assert (STEP : forall c', sqr_normal_loop A (S c') k R = sqr_normal_loop A c' (S k) (splice R (1 + 2 * k) (seg ++ [c]))).
    { intros c'. cbn [sqr_normal_loop]. fold j. rewrite slice_tail, EMA. reflexivity. }
    zstep. if_cases KB; zify_cond KB.
    -
      rewrite ?unsigned_lit in KB by lia.
      replace (rp + 8 * (1 + 2 * Z.of_nat k) + 16)%Z with (rp + 8 * (1 + 2 * Z.of_nat (S k)))%Z by lia.
      replace (PA + 8 * (1 + Z.of_nat k) + 8)%Z with (PA + 8 * (1 + Z.of_nat (S k)))%Z by lia.
      replace (rp + 8 * (NA + Z.of_nat k) + 8)%Z with (rp + 8 * (NA + Z.of_nat (S k)))%Z by lia.
      replace (Z.of_nat j + -1)%Z with (NA - 1 - Z.of_nat (S k))%Z by lia.
      eapply IH; [lia | lia | lia | exact I |].
      intros m' R' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y25 y26 y28 y29 y30 y31 I' ER'.
      eapply K; [exact I' |]. rewrite STEP. exact ER'.
    -
      assert (Ec : cnt = 0%nat) by (rewrite ?unsigned_lit in KB by lia; lia). subst cnt.
      eapply K; [exact I |]. rewrite STEP. reflexivity.
  Qed.

  Ltac sn_st0 I k :=
    let ad := cur_mem_addr in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    destruct (UPD _ _ k 0%Z E eq_refl I ltac:(lia) ltac:(lia) ltac:(lia)) as [SOK I2];
    change (le8 (Z_to_bv 64 0)) with (Z_to_le_bytes 8 0) in I2;
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.

  Lemma slice_tail0 : slice A 1 (length A - 1) = skipn 1 A.
  Proof. unfold slice. apply firstn_all2. rewrite length_skipn. lia. Qed.

  Lemma bn_sqr_normal_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xfcf4c) fc None m (seg_rom bgpsegs)).
  Proof.
    pose proof (munch_refl Wfin m) as MU. pose proof (munch_refl [(SP + -96, SP)]%Z m) as MUF. pose proof (wmono_refl bgpsegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word a3) as R3. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, R3, RSP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RR) as BR.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    pose proof (proj1 STK) as LO0.
    assert (SP96 : (128 <= SP)%Z) by (clear - LO LO0; lia).
    carve_frame 96%nat STK.
    do 13 zstep. zstep. do 4 zstep.
    zstep. setreg 18%Z (Z_to_bv 64 NN) ltac:(rewrite <- A2; f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite bn_swrap32_small by lia; lia).
    zstep. zstep. zstep. setreg 11%Z (Z_to_bv 64 (rp + 8 * NN)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -96)) = (SP + -96)%Z) by (apply ESP96; clear - SP96; lia).
    assert (I : KSNI m1 r0).
    { unfold SNI, SNB. split; [exact LR0|]. split; [exact LenR0|].
      split. { eapply limbs_at_transport; [exact RR | exact MUF | rewrite LenR0; djtac]. }
      split. { eapply limbs_at_transport; [exact RA | exact MUF | djtac]. }
      split; [exact WR|]. split; [exact WT|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear MUF FR STK.

    destruct (UPD _ _ 0%nat 0%Z rp eq_refl I ltac:(lia) ltac:(lia) ltac:(lia)) as [SOK I2].
    rewrite Z_to_bv_bv_unsigned in SOK. rewrite Z_to_bv_bv_unsigned in I2. change (le8 (Z_to_bv 64 0)) with (Z_to_le_bytes 8 0) in I2.
    zstep. clear SOK I.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end. rename I2 into I.

    sn_st0 I (2 * length A - 1)%nat.

    zstep. rewrite lts_words_small by (rewrite ?A2, ?unsigned_lit; lia). rewrite A2, (unsigned_lit 2) by lia.
    if_cases KR; zify_cond KR.
    { assert (E1 : length A = 1%nat) by (rewrite ?A2 in KR; lia).
      eapply sn_finish; [exact I |].
      unfold sqr_normal. rewrite E1. cbn [Nat.ltb Nat.leb Nat.sub Nat.mul Nat.add sqr_normal_loop]. reflexivity. }
    assert (N2 : (2 <= length A)%nat) by (rewrite ?A2 in KR; lia).
    clear KR.

    pose proof I as (LRl & LenR & HR & HA & HW & HT & FR & STf & MI & MU2 & WM2).
    assert (N0 : nth_error A 0 = Some (nth 0 A 0%Z)) by (apply nth_error_nth'; lia).
    assert (Rw : (0 <= nth 0 A 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA).
    pose proof (limbs_at_read_nth bgpsegs _ PA A 0 _ a1 HA N0 ltac:(symmetry; unfold wa; rewrite Z.mul_0_r, Z.add_0_r; apply Z_to_bv_bv_unsigned)) as RD.
    zstep. clear RD.
    zstep. zstep. rewrite (bn_swrap32_small (bv_unsigned a2 + -1)) by lia. rewrite A2.
    do 3 zstep. zstep.
    assert (Er1 : bv_unsigned (Z_to_bv 64 (rp + 8)) = (rp + 8)%Z) by (apply unsigned_lit; destruct HW as (W0 & W1 & _); lia).
    assert (Ea1 : bv_unsigned (Z_to_bv 64 (PA + 8)) = (PA + 8)%Z) by (apply unsigned_lit; lia).
    assert (En1 : bv_unsigned (Z_to_bv 64 (NA + -1)) = (NA + -1)%Z) by (apply unsigned_lit; lia).
    assert (Eww : bv_unsigned (Z_to_bv 64 (nth 0 A 0%Z)) = nth 0 A 0%Z) by (apply unsigned_lit; lia).
    assert (HA1 : limbs_at bgpsegs m0 (PA + 8) (skipn 1 A)).
    { rewrite <- (firstn_skipn 1 A) in HA. apply limbs_at_app in HA. destruct HA as [_ HA2].
      rewrite length_firstn in HA2. replace (Nat.min 1 (length A)) with 1%nat in HA2 by lia. exact HA2. }
    pose proof (mul_words_spec (skipn 1 A) (nth 0 A 0%Z) (limbs_skipn _ _ LA) ltac:(unfold limb; rewrite BW_lit; exact Rw)) as MS0.
    eapply evt_cut.
    { eapply bn_mul_words_spec with (a := skipn 1 A) (lo := lo) (m := m0).
      - apply limbs_skipn. exact LA.
      - rewrite length_skipn. lia.
      - rewrite En1, length_skipn. lia.
      - rewrite Ea1. exact HA1.
      - rewrite Er1, length_skipn. apply (wr_at_sub bgpsegs m0 rp (8 * NN) 8 (8 * Z.of_nat (length A - 1)) HW); lia.
      - rewrite Er1, Ea1, length_skipn. unfold alias_ok. right. lia.
      - rewrite ESP. exact STf.
      - rewrite ESP. lia.
      - rewrite Er1, ESP, length_skipn. lia.
      - rewrite Ea1, ESP, length_skipn. lia.
      - exact MI. }
    intros ms' PO. unfold mw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite Er1, ESP, Eww, length_skipn in *.
    rewrite (ret_pc_even 0xfcfcc) by lia.
    destruct (mul_words (skipn 1 A) (nth 0 A 0%Z)) as [seg0 c0] eqn:EMW. cbn [fst snd] in *.
    destruct MS0 as (Lseg0 & Eseg0 & Lc0 & _). unfold limb, BW in Lc0. try rewrite length_skipn in Eseg0.
    assert (I2 : KSNI m4 (splice (upd (upd r0 0 0) (2 * length A - 1) 0) 1 seg0)).
    { eapply (CALL m0 m4 _ 1%nat seg0 16%Z eq_refl I); [rewrite Eseg0; lia | lia | | exact WMc | exact MIc | | exact STc | exact Lseg0].
      - rewrite Eseg0. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - replace (rp + 8 * Z.of_nat 1)%Z with (rp + 8)%Z by lia. exact HS. }
    clear I HR HA HW HT FR STf MI MU2 WM2 MUc WMc MIc HS STc HA1. rename I2 into I.
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    zstep. zstep. rewrite (bn_swrap32_small (bv_unsigned a2 + -2)) by lia. rewrite A2.
    sn_st I (1 + length seg0)%nat c0 Lc0.
    rewrite (upd_splice_snoc _ 1 seg0 c0) in I by (rewrite Eseg0, upd_length2 by lia; lia).
    assert (EM : forall R', R' = sqr_normal_loop A (length A - 2) 1 (splice (upd (upd r0 0 0) (2 * length A - 1) 0) 1 (seg0 ++ [c0])) ->
                 fst (add_words (fst (add_words R' R')) (sqr_words A)) = RES).
    { intros R' ->. unfold sqr_normal. rewrite (proj2 (Nat.ltb_lt 1 (length A))) by lia. rewrite slice_tail0, EMW. reflexivity. }
    zstep. if_cases KZ; zify_cond KZ.
    -
      assert (E2 : length A = 2%nat) by lia.
      eapply sn_finish; [exact I |]. apply EM. rewrite E2. reflexivity.
    -
      do 7 zstep.
      rewrite shl32_shr29 by (rewrite A2; lia). rewrite A2.
      replace (rp + 24)%Z with (rp + 8 * (1 + 2 * Z.of_nat 1))%Z by lia.
      replace (PA + 16)%Z with (PA + 8 * (1 + Z.of_nat 1))%Z by lia.
      replace (8 * NA + rp + 8)%Z with (rp + 8 * (NA + Z.of_nat 1))%Z by lia.
      replace (NA + -2)%Z with (NA - 1 - Z.of_nat 1)%Z by lia.
      eapply (sn_loop (length A - 2)%nat 1%nat); [lia | lia | lia | exact I |].
      intros m' R' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y25 y26 y28 y29 y30 y31 I' ER'.
      eapply sn_finish; [exact I' | apply EM; exact ER'].
  Qed.
End Mach.
