(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import TacX StoreDj.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope bv_scope.
Definition strspn_entry := 0x56a638%Z.           (* [comment removed for export] *)
Definition AGOT_SSP_CELL : Z := 0x5e9798.      (* [comment removed for export] *)
Definition ACANARY_CELL : Z := 0xc01cd0.       (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inset (acc : list byte) (x : byte) : bool := existsb (fun a => Z.eqb (bv_unsigned a) (bv_unsigned x)) acc.

Fixpoint spn (s acc : list byte) : nat :=
  match s with
  | [] => 0
  | x :: s' => if inset acc x then S (spn s' acc) else 0
  end.

Lemma spn_le : forall s acc, (spn s acc <= length s)%nat.
Proof. induction s as [|x s IH]; intros acc; cbn; [lia|]. destruct (inset acc x); [specialize (IH acc); lia| lia]. Qed.

Lemma spn_prefix : forall s acc i, (i <= length s)%nat ->
  (forall j x, (j < i)%nat -> nth_error s j = Some x -> inset acc x = true) ->
  (forall x, nth_error s i = Some x -> inset acc x = false) ->
  spn s acc = i.
Proof.
  induction s as [|y s IH]; intros acc i Hi IN OUT; cbn in Hi |- *.
  - lia.
  - destruct i as [|i].
    + rewrite (OUT y eq_refl). reflexivity.
    + rewrite (IN 0%nat y ltac:(lia) eq_refl). f_equal. apply IH; [lia| |].
      * intros j x Hj Hx. exact (IN (S j) x ltac:(lia) Hx).
      * intros x Hx. exact (OUT x Hx).
Qed.

(* [comment removed for export] *)
Definition setw (l : list byte) (k : Z) : Z :=
  fold_left (fun w (b : byte) => if (bv_unsigned b / 64 =? k)%Z then Z.lor w (Z.shiftl 1 (bv_unsigned b mod 64)) else w) l 0%Z.

Lemma setw_nil : forall k, setw [] k = 0%Z. Proof. reflexivity. Qed.
Lemma setw_snoc : forall l b k,
  setw (l ++ [b]) k = (if (bv_unsigned b / 64 =? k)%Z then Z.lor (setw l k) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l k).
Proof. intros. unfold setw. rewrite fold_left_app. reflexivity. Qed.

Lemma lor_range64 : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> (0 <= Z.lor a b < 2^64)%Z.
Proof. intros. apply lor_lt_pow2; assumption. Qed.

Lemma setw_range : forall l k, (0 <= setw l k < 2^64)%Z.
Proof.
  intros l k. induction l as [|b l IH] using rev_ind; [rewrite setw_nil; lia|].
  rewrite setw_snoc. destruct (bv_unsigned b / 64 =? k)%Z; [| exact IH].
  pose proof (byte_range b). apply lor_range64; [exact IH|].
  rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; Z.div_mod_to_equations; lia].
Qed.

Lemma setw_testbit : forall l k j, (0 <= j < 64)%Z ->
  Z.testbit (setw l k) j = existsb (fun a => (bv_unsigned a / 64 =? k)%Z && (bv_unsigned a mod 64 =? j)%Z) l.
Proof.
  intros l k j Hj. induction l as [|b l IH] using rev_ind; [rewrite setw_nil; apply Z.bits_0|].
  rewrite setw_snoc, existsb_app. cbn [existsb]. rewrite orb_false_r.
  pose proof (byte_range b).
  destruct (Z.eqb_spec (bv_unsigned b / 64) k) as [E|NE].
  - rewrite Z.lor_spec, IH, Z.shiftl_1_l, Z.pow2_bits_eqb by (Z.div_mod_to_equations; lia). cbn [andb]. reflexivity.
  - rewrite IH. cbn [andb]. rewrite orb_false_r. reflexivity.
Qed.

Lemma inset_testbit : forall l x, inset l x = Z.testbit (setw l (bv_unsigned x / 64)) (bv_unsigned x mod 64).
Proof.
  intros l x. pose proof (byte_range x). rewrite setw_testbit by (Z.div_mod_to_equations; lia). unfold inset.
  induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. f_equal. pose proof (byte_range a).
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned x)) as [E|NE].
  - rewrite E, !Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned a / 64) (bv_unsigned x / 64)); destruct (Z.eqb_spec (bv_unsigned a mod 64) (bv_unsigned x mod 64)); cbn; try reflexivity.
    exfalso. apply NE. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma bidx : forall b, (0 <= b < 256)%Z -> Z.land (Z.shiftr b 3) 18446744073709551608 = (8 * (b / 64))%Z.
Proof.
  intros b Hb. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
  assert (R : (0 <= b / 8 < 32)%Z) by (Z.div_mod_to_equations; lia).
  replace (b / 64)%Z with (b / 8 / 8)%Z by (rewrite Z.div_div by lia; reflexivity).
  set (q := (b / 8)%Z) in *. clearbody q.
  assert (E : exists n, (n < 32)%nat /\ q = Z.of_nat n) by (exists (Z.to_nat q); split; lia).
  destruct E as (n & Hn & ->).
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition astrspn_real_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (str acc : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (spn str acc))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Section W.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str sslack acc aslack : list byte) (lo can : Z).
  Notation Sa := (bv_unsigned a0).
  Notation Ca := (bv_unsigned a1).
  Notation L := (Z.of_nat (length str)).
  Notation sfull := (str ++ Z_to_bv 8 0 :: sslack).
  Notation afull := (acc ++ Z_to_bv 8 0 :: aslack).
  Hypothesis STR : bytes_at asegs m Sa sfull.
  Hypothesis SNONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis ACC : bytes_at asegs m Ca afull.
  Hypothesis ANONUL : ~ In (Z_to_bv 8 0) acc.
  Hypothesis ALEN : (2 <= length acc)%nat.
  Hypothesis GOTC : rw_cells asegs m AGOT_SSP_CELL [C8 (wz ACANARY_CELL)].
  Hypothesis CAN : rw_cells asegs m ACANARY_CELL [C8 (wz can)].
  Hypothesis CANR : (0 <= can < 2^64)%Z.
  Hypothesis HS : (Sa + Z.of_nat (length sfull) <= bv_unsigned sp - 48)%Z.
  Hypothesis HC : (Ca + Z.of_nat (length afull) <= bv_unsigned sp - 48)%Z.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (0xc04000 <= lo)%Z.
  Hypothesis LOS : (lo <= bv_unsigned sp - 48)%Z.
  Hypothesis SPH : (bv_unsigned sp + 8 <= 2^64)%Z.
  Hypothesis MI : mem_inv asegs m.

  Notation POST := (astrspn_real_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str acc lo m).

  Lemma str_nth_lt : forall i, (0 <= i < L)%Z -> exists b, nth_error sfull (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split; [rewrite nth_error_app1 by lia; exact E|]. split; [reflexivity|].
      intros Hb. apply SNONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.
  Lemma str_nth_len : nth_error sfull (Z.to_nat L) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.
  Lemma acc_nth_lt : forall i, (0 <= i < Z.of_nat (length acc))%Z -> exists b, nth_error afull (Z.to_nat i) = Some b /\ nth_error acc (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error acc (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split; [rewrite nth_error_app1 by lia; exact E|]. split; [reflexivity|].
      intros Hb. apply ANONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.
  Lemma acc_nth_len : nth_error afull (Z.to_nat (Z.of_nat (length acc))) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition frame (l : list byte) : list cell :=
    [C8 (Z_to_bv 64 (setw l 0)); C8 (Z_to_bv 64 (setw l 1)); C8 (Z_to_bv 64 (setw l 2)); C8 (Z_to_bv 64 (setw l 3)); C8 (Z_to_bv 64 can); C8 ra].

  (* [comment removed for export] *)
  Notation ST pc mm x5 x11 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 t1 t2 s0 s1 a0 x11 (Z_to_bv 64 ACANARY_CELL) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition MEMS (m1 : word -> option byte) : Prop :=
    mem_inv asegs m1 /\ bytes_at asegs m1 Sa sfull /\ bytes_at asegs m1 Ca afull
    /\ rw_cells asegs m1 AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] /\ rw_cells asegs m1 ACANARY_CELL [C8 (Z_to_bv 64 can)]
    /\ stk asegs m1 lo (bv_unsigned sp + -48) /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1.

  (* [comment removed for export] *)
  Lemma afin_694 : forall m1 (r : Z) x5 x11 x13 x14 (w : word) x16 x17,
    MEMS m1 -> rw_cells asegs m1 (bv_unsigned sp + -48) (frame acc) -> r = Z.of_nat (spn str acc) -> w = Z_to_bv 64 (Sa + r) ->
    evt asegs POST (ST 0x56a710 m1 x5 x11 x13 x14 w x16 x17).
  Proof.
    intros m1 r x5 x11 x13 x14 w x16 x17 (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1) FR -> ->.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (spn_le str acc) as SL. pose proof (bytes_at_bound _ _ _ _ STR1) as SB. rewrite length_app in SB. cbn [length] in SB.
    unfold AGOT_SSP_CELL, ACANARY_CELL in *. unfold frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    release_frame FR ST1 (bv_unsigned sp).
    try replace (Sa + Z.of_nat (spn str acc) - Sa)%Z with (Z.of_nat (spn str acc)) by lia. try replace (Sa + Z.of_nat (spn str acc) + - Sa)%Z with (Z.of_nat (spn str acc)) by lia. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma bit_of : forall w j, (0 <= w)%Z -> (0 <= j)%Z -> Z.land (Z.shiftr w j) 1 = (if Z.testbit w j then 1 else 0)%Z.
  Proof.
    intros w j Hw Hj. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    pose proof (Z.testbit_spec' w j Hj) as E. destruct (Z.testbit w j); cbn [Z.b2z] in E; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ascan_loop : forall (k : nat) (i : Z) m1 (b : byte) x5 (w : word) x15 x16 x17,
    Z.to_nat (L - i) = k -> (0 <= i < L)%Z -> nth_error str (Z.to_nat i) = Some b ->
    (forall j x, (j < Z.to_nat i)%nat -> nth_error str j = Some x -> inset acc x = true) ->
    MEMS m1 -> rw_cells asegs m1 (bv_unsigned sp + -48) (frame acc) -> w = Z_to_bv 64 (Sa + i) ->
    evt asegs POST (ST 0x56a6b8 m1 x5 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned b)) w x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i m1 b x5 w x15 x16 x17 Hk Hi HB IN MM FR Hw; [lia|]. subst w.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bytes_at_bound _ _ _ _ STR1) as SB. rewrite length_app in SB. cbn [length] in SB.
    pose proof (byte_range b) as BR. pose proof (setw_range acc (bv_unsigned b / 64)) as WR.
    unfold frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    (* [comment removed for export] *)
    assert (K : evt asegs POST (ST 0x56a6c8 m1 x5 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (Sa + i)) (Z_to_bv 64 (setw acc q)) x16 x17)).
    { zstep. zstep.
      replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
      try rewrite (Z.land_ones_low _ 64) by (first [apply Z.shiftr_nonneg; lia | idtac]; try lia;
        (destruct (Z.eq_dec (Z.shiftr (setw acc q) (bv_unsigned b mod 64)) 0) as [->|NZ]; [cbn; lia|]; apply Z.log2_lt_pow2; [pose proof (Z.shiftr_nonneg (setw acc q) (bv_unsigned b mod 64)); lia|];
         rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]; eapply Z.lt_le_trans; [apply (proj2 WR)|];
         rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia)).
      rewrite bit_of by lia. replace (Z.testbit (setw acc q) (bv_unsigned b mod 64)%Z) with (inset acc b) by (subst q; first [apply inset_testbit | symmetry; apply inset_testbit]).
      (* [comment removed for export] *)
      zstep. destruct (inset acc b) eqn:INB.
      - if_false.
        (* [comment removed for export] *)
        destruct (Z.eq_dec (i + 1) L) as [EQ|NE].
        + pose proof str_nth_len as HN. rewrite <- EQ in HN.
          pose proof (u8ro_read asegs m1 Sa sfull (i + 1) _ (Z_to_bv 64 (Sa + i + 1)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
          zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep. zstep. if_false. zstep.
          replace (Sa + i + 1)%Z with (Sa + (i + 1))%Z by lia.
          apply (afin_694 m1 (i + 1)); [exact MM| exact FR| | reflexivity].
          rewrite (spn_prefix str acc (length str)); [lia| lia| |].
          * intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|]. apply (IN j x); [lia| exact Hx].
          * intros x Hx. exfalso. pose proof (proj2 (nth_error_None str (length str)) ltac:(lia)) as X. rewrite X in Hx. discriminate.
        + destruct (str_nth_lt (i + 1) ltac:(lia)) as (b' & HN & HB' & NZ'). pose proof (byte_range b') as BR'.
          pose proof (u8ro_read asegs m1 Sa sfull (i + 1) _ (Z_to_bv 64 (Sa + i + 1)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
          zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
          zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. exact (NZ' K1). }
          replace (Sa + i + 1)%Z with (Sa + (i + 1))%Z by lia.
          apply (IH (i + 1)%Z m1 b'); [lia| lia| rewrite <- HB'; f_equal; lia| | exact MM| unfold frame; exact FR| reflexivity].
          intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|]. apply (IN j x); [lia| exact Hx].
      - if_true.
        (* [comment removed for export] *)
        zstep.
        apply (afin_694 m1 i); [exact MM| exact FR| | reflexivity].
        rewrite (spn_prefix str acc (Z.to_nat i)); [lia| lia| exact IN|].
        intros x Hx. rewrite HB in Hx. inversion Hx. subst. exact INB. }
    (* [comment removed for export] *)
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    clearbody q.
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in K |- *.
    - replace (bv_unsigned sp + -48 + 8 * 0)%Z with (bv_unsigned sp + -48)%Z by lia. zstep. exact K.
    - replace (bv_unsigned sp + -48 + 8 * 1)%Z with (bv_unsigned sp + -40)%Z by lia. zstep. exact K.
    - replace (bv_unsigned sp + -48 + 8 * 2)%Z with (bv_unsigned sp + -32)%Z by lia. zstep. exact K.
    - replace (bv_unsigned sp + -48 + 8 * 3)%Z with (bv_unsigned sp + -24)%Z by lia. zstep. exact K.
  Qed.

  Lemma firstn_snoc : forall (l : list byte) i b, nth_error l i = Some b -> firstn (S i) l = firstn i l ++ [b].
  Proof.
    induction l as [|x l IHl]; intros [|i] b H; cbn in H |- *; try discriminate.
    - inversion H. reflexivity.
    - rewrite (IHl i b H). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ascan_entry : forall m1 x5 x11 x13 x14 x15 x16 x17,
    MEMS m1 -> rw_cells asegs m1 (bv_unsigned sp + -48) (frame acc) ->
    evt asegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 t1 t2 s0 s1 a0 x11 (Z_to_bv 64 ACANARY_CELL) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x56a6a4) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 x5 x11 x13 x14 x15 x16 x17 MM FR. pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (bytes_at_bound _ _ _ _ STR1) as SB. rewrite length_app in SB. cbn [length] in SB.
    destruct (Z.eq_dec 0 L) as [EQ|NE].
    - (* [comment removed for export] *)
      pose proof str_nth_len as HN. rewrite <- EQ in HN.
      pose proof (u8ro_read asegs m1 Sa sfull 0 _ a0 STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
      change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      zstep. zstep. if_true.
      apply (afin_694 m1 0); [exact MM| exact FR| destruct str; [reflexivity| cbn in EQ; lia]| rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned].
    - destruct (str_nth_lt 0 ltac:(lia)) as (b & HN & HB & NZ). pose proof (byte_range b) as BR.
      pose proof (u8ro_read asegs m1 Sa sfull 0 _ a0 STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. exact (NZ K0). }
      (* [comment removed for export] *)
      zstep. zstep.
      apply (ascan_loop (Z.to_nat (L - 0)) 0 m1 b); [lia| lia| exact HB| intros j x Hj; lia| exact MM| exact FR| rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned].
  Qed.

  Lemma aframe_snoc : forall l (b : byte) (q : Z), q = (bv_unsigned b / 64)%Z ->
    frame (l ++ [b]) =
      [C8 (Z_to_bv 64 (if (q =? 0)%Z then Z.lor (setw l 0) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 0));
       C8 (Z_to_bv 64 (if (q =? 1)%Z then Z.lor (setw l 1) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 1));
       C8 (Z_to_bv 64 (if (q =? 2)%Z then Z.lor (setw l 2) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 2));
       C8 (Z_to_bv 64 (if (q =? 3)%Z then Z.lor (setw l 3) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 3));
       C8 (Z_to_bv 64 can); C8 ra].
  Proof. intros l b q ->. unfold frame. rewrite !setw_snoc. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma abuild_loop : forall (k : nat) (i : Z) m1 (b : byte) x5 x16 x17,
    Z.to_nat (Z.of_nat (length acc) - i) = k -> (0 <= i < Z.of_nat (length acc))%Z -> nth_error acc (Z.to_nat i) = Some b ->
    MEMS m1 -> rw_cells asegs m1 (bv_unsigned sp + -48) (frame (firstn (Z.to_nat i) acc)) ->
    evt asegs POST (ST 0x56a67c m1 x5 (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -48)) x16 x17).
  Proof.
    induction k as [|k IH]; intros i m1 b x5 x16 x17 Hk Hi HB MM FR; [lia|].
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1). clear MM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bytes_at_bound _ _ _ _ ACC1) as CB0. rewrite length_app in CB0. cbn [length] in CB0.
    pose proof (byte_range b) as BR.
    pose proof HS as HS'. pose proof HC as HC'. rewrite length_app in HS', HC'. cbn [length] in HS', HC'.
    pose proof (bytes_at_bound _ _ _ _ STR1) as SB. rewrite length_app in SB. cbn [length] in SB.
    unfold AGOT_SSP_CELL, ACANARY_CELL in GOT1, CAN1. unfold frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    (* [comment removed for export] *)
    assert (NX : exists b', nth_error afull (Z.to_nat (i + 1)) = Some b' /\ (bv_unsigned b' = 0%Z <-> i + 1 = Z.of_nat (length acc))%Z).
    { destruct (Z.eq_dec (i + 1) (Z.of_nat (length acc))) as [E|NE].
      - exists (Z_to_bv 8 0). rewrite E. split; [exact acc_nth_len|]. split; [intros _; reflexivity| intros _; reflexivity].
      - destruct (acc_nth_lt (i + 1) ltac:(lia)) as (b' & H1 & _ & NZ'). exists b'. split; [exact H1|]. split; [intros X; exfalso; exact (NZ' X)| intros X; lia]. }
    destruct NX as (b' & HN' & NZ'). pose proof (byte_range b') as BR'.
    (* [comment removed for export] *)
    assert (K : forall m2 x5' x16' x17', MEMS m2 -> rw_cells asegs m2 (bv_unsigned sp + -48) (frame (firstn (Z.to_nat (i + 1)) acc)) ->
              evt asegs POST (ST 0x56a69c m2 x5' (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b')) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -48)) x16' x17')).
    { intros m2 x5' x16' x17' MM2 FR2.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ.
      - replace (Ca + i + 2)%Z with (Ca + (i + 1) + 1)%Z by lia.
        apply (IH (i + 1)%Z m2 b'); [lia| lia| | exact MM2| exact FR2].
        rewrite nth_error_app1 in HN' by lia. exact HN'.
      - apply (proj1 NZ') in KZ. replace (Z.to_nat (i + 1)) with (length acc) in FR2 by lia. rewrite firstn_all in FR2.
        apply ascan_entry; [exact MM2| exact FR2]. }
    (* [comment removed for export] *)
    pose proof (u8ro_read asegs m1 Ca afull (i + 1) _ (Z_to_bv 64 (Ca + i + 1)) ACC1 HN' ltac:(lia) ltac:(addr_tac)) as RD.
    assert (EF : firstn (Z.to_nat (i + 1)) acc = firstn (Z.to_nat i) acc ++ [b]).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_snoc. exact HB. }
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    pose proof (aframe_snoc (firstn (Z.to_nat i) acc) b q eq_refl) as FS. rewrite <- EF in FS.
    pose proof (setw_range (firstn (Z.to_nat i) acc) q) as WR.
    clearbody q.
    assert (SR : (0 <= Z.shiftl 1 (bv_unsigned b mod 64) < 2^64)%Z).
    { rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; Z.div_mod_to_equations; lia]. }
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in FS, WR |- *; cbn [Z.eqb Pos.eqb] in FS; pose proof (lor_range64 _ _ WR SR) as LR;
    [ replace (bv_unsigned sp + -48 + 8 * 0)%Z with (bv_unsigned sp + -48)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 1)%Z with (bv_unsigned sp + -40)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 2)%Z with (bv_unsigned sp + -32)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 3)%Z with (bv_unsigned sp + -24)%Z by lia ].
    all: zstep; zstep; zstep; clear RD; lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
    all: replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    all: zstep; rewrite ?unsigned_lit by lia; zstep.
    all: lazymatch goal with H : rw_cells asegs ?mc (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z in H by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity);
        rewrite <- FS in H; apply (K mc); [unfold MEMS, AGOT_SSP_CELL, ACANARY_CELL; repeat (lazymatch goal with |- _ /\ _ => split end); assumption| exact H] end.
  Qed.

  Lemma astrspn_real_walk : forall m0,
    mem_inv asegs m0 -> bytes_at asegs m0 Sa sfull -> bytes_at asegs m0 Ca afull ->
    rw_cells asegs m0 AGOT_SSP_CELL [C8 (wz ACANARY_CELL)] -> rw_cells asegs m0 ACANARY_CELL [C8 (wz can)] ->
    stk asegs m0 lo (bv_unsigned sp) -> munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m0 -> wmono asegs m m0 ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x56a638) fc None m0 (seg_rom asegs)).
  Proof.
    intros m0 MI1 STR1 ACC1 GOTC' CAN' ST1 MU WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bytes_at_bound _ _ _ _ STR1) as SB. pose proof (bytes_at_bound _ _ _ _ ACC1) as CB0.
    pose proof HS as HS'. pose proof HC as HC'.
    rewrite length_app in SB, HS'. rewrite length_app in CB0, HC'. cbn [length] in SB, HS', CB0, HC'.
    unfold AGOT_SSP_CELL, ACANARY_CELL in GOTC', CAN'. unfold wz in GOTC', CAN'.
    (* [comment removed for export] *)
    zstep. carve_frame 48%nat ST1. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (acc_nth_lt 0 ltac:(lia)) as (c0 & HC0 & HC0' & NZ0). pose proof (byte_range c0) as C0R.
    pose proof (u8ro_read asegs _ Ca afull 0 c0 a1 ACC1 HC0 ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. zstep. if_cases K0; zify_cond K0. { exfalso. exact (NZ0 K0). }
    (* [comment removed for export] *)
    destruct (acc_nth_lt 1 ltac:(lia)) as (c1 & HC1 & HC1' & NZ1). pose proof (byte_range c1) as C1R.
    pose proof (u8ro_read asegs _ Ca afull 1 c1 (Z_to_bv 64 (Ca + 1)) ACC1 HC1 ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. clear RD. lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
    zstep. if_cases K1; zify_cond K1. { exfalso. exact (NZ1 K1). }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Ca + 1)%Z with (Ca + 0 + 1)%Z by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      apply (abuild_loop (Z.to_nat (Z.of_nat (length acc) - 0)) 0 mc c0); [lia| lia| exact HC0'| |] end.
    - unfold MEMS, AGOT_SSP_CELL, ACANARY_CELL. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| eapply munch_weaken; [| exact MU]; intros x Hx; exact Hx].
    - cbn [Z.to_nat firstn]. unfold frame. rewrite !setw_nil. exact FR.
  Qed.
End W.

(* [comment removed for export] *)
Lemma astrspn_real_body : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str sslack acc aslack : list byte) (lo can : Z),
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: sslack) -> ~ In (Z_to_bv 8 0) str ->
  bytes_at asegs m (bv_unsigned a1) (acc ++ Z_to_bv 8 0 :: aslack) -> ~ In (Z_to_bv 8 0) acc -> (2 <= length acc)%nat ->
  rw_cells asegs m AGOT_SSP_CELL [C8 (wz ACANARY_CELL)] -> rw_cells asegs m ACANARY_CELL [C8 (wz can)] -> (0 <= can < 2^64)%Z ->
  (bv_unsigned a0 + Z.of_nat (length (str ++ Z_to_bv 8 0 :: sslack)) <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned a1 + Z.of_nat (length (acc ++ Z_to_bv 8 0 :: aslack)) <= bv_unsigned sp - 48)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (0xc04000 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp + 8 <= 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (astrspn_real_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str acc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56a638) fc None m (seg_rom asegs)).
Proof. intros. eapply astrspn_real_walk; try eassumption; [apply munch_refl| apply wmono_refl]. Qed.
