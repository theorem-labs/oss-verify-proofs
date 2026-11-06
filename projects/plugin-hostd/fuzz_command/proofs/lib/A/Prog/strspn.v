(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Ref/F_strspn.v, with its module paths, module names and addresses changed; 221 of its 374 lines of code are new or changed and 188 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import strspn_c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac addr_tac := first [ symmetry; apply wa_of_var; lia | unfold wa; f_equal; lia ].
Ltac weq := first [ reflexivity | f_equal; lia | rewrite ?unsigned_lit by lia; f_equal; lia
                   | symmetry; apply wa_of_var; rewrite ?unsigned_lit by lia; lia ].
Ltac beta_goal := lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.

Lemma spn_le : forall set s, (spn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn; [lia|]. destruct (in_set set x); lia. Qed.

Lemma spn_prefix : forall set s i, (i <= length s)%nat ->
  (forall j x, (j < i)%nat -> nth_error s j = Some x -> in_set set x = true) ->
  (forall x, nth_error s i = Some x -> in_set set x = false) ->
  spn_len set s = i.
Proof.
  intros set s. induction s as [|y s IH]; intros i Hi IN OUT; cbn in Hi |- *.
  - lia.
  - destruct i as [|i].
    + rewrite (OUT y eq_refl). reflexivity.
    + rewrite (IN 0%nat y ltac:(lia) eq_refl). f_equal. apply IH; [lia| |].
      * intros j x Hj Hx. exact (IN (S j) x ltac:(lia) Hx).
      * intros x Hx. exact (OUT x Hx).
Qed.

Lemma spn_nil : forall s, spn_len [] s = 0%nat.
Proof. intros [|x s]; reflexivity. Qed.

Lemma in_set1 : forall c x, in_set [c] x = Z.eqb (bv_unsigned c) (bv_unsigned x).
Proof. intros c x. unfold in_set. cbn [existsb]. apply orb_false_r. Qed.

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

Lemma in_set_testbit : forall l x, in_set l x = Z.testbit (setw l (bv_unsigned x / 64)) (bv_unsigned x mod 64).
Proof.
  intros l x. pose proof (byte_range x). rewrite setw_testbit by (Z.div_mod_to_equations; lia). unfold in_set.
  induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. f_equal. pose proof (byte_range a).
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned x)) as [E|NE].
  - rewrite E, !Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned a / 64) (bv_unsigned x / 64)); destruct (Z.eqb_spec (bv_unsigned a mod 64) (bv_unsigned x mod 64)); cbn; try reflexivity.
    exfalso. apply NE. Z.div_mod_to_equations. lia.
Qed.

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

Lemma bit_of : forall w j, (0 <= w)%Z -> (0 <= j)%Z -> Z.land (Z.shiftr w j) 1 = (if Z.testbit w j then 1 else 0)%Z.
Proof.
  intros w j Hw Hj. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  pose proof (Z.testbit_spec' w j Hj) as E. destruct (Z.testbit w j); cbn [Z.b2z] in E; lia.
Qed.

Lemma firstn_snoc : forall (l : list byte) i b, nth_error l i = Some b -> firstn (S i) l = firstn i l ++ [b].
Proof.
  induction l as [|x l IHl]; intros [|i] b H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IHl i b H). reflexivity.
Qed.

Lemma ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. unfold ro_cells, cells_at. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma cstr_nth_lt : forall (l : list byte) i, ~ In (Z_to_bv 8 0) l -> (0 <= i < Z.of_nat (length l))%Z ->
  exists b, nth_error (l ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b /\ nth_error l (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
Proof.
  intros l i NZ Hi. destruct (nth_error l (Z.to_nat i)) as [b|] eqn:E.
  - exists b. split; [rewrite nth_error_app1 by lia; exact E|]. split; [reflexivity|].
    intros Hb. apply NZ. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hb. reflexivity.
  - apply nth_error_None in E. lia.
Qed.

Lemma cstr_nth_len : forall (l : list byte), nth_error (l ++ [Z_to_bv 8 0]) (Z.to_nat (Z.of_nat (length l))) = Some (Z_to_bv 8 0).
Proof. intros l. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

Lemma len1 : forall (l : list byte) c, length l = 1%nat -> nth_error l 0 = Some c -> l = [c].
Proof. intros [|x [|y r]] c H1 H2; cbn in *; try discriminate. inversion H2. reflexivity. Qed.

Lemma nth_none_len : forall (l : list byte), nth_error l (length l) = None.
Proof. intros l. apply nth_error_None. lia. Qed.

Section W.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str set : list byte) (lo : Z) (can : word).
  Notation Sa := (bv_unsigned a0).
  Notation Ca := (bv_unsigned a1).
  Notation SP := (bv_unsigned sp).
  Notation L := (Z.of_nat (length str)).
  Notation K := (Z.of_nat (length set)).
  Notation sfull := (str ++ [Z_to_bv 8 0]).
  Notation afull := (set ++ [Z_to_bv 8 0]).
  Hypothesis SNONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis ANONUL : ~ In (Z_to_bv 8 0) set.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis LOS : lo + 48 <= SP.
  Hypothesis DS : Sa + L + 1 <= lo \/ SP <= Sa.
  Hypothesis DC : Ca + K + 1 <= lo \/ SP <= Ca.
  Hypothesis DG : 0xa7098 + 8 <= lo \/ SP <= 0xa7098.
  Hypothesis DK : 0x6045d8 + 8 <= lo \/ SP <= 0x6045d8.
  Hypothesis SB : Sa + L + 1 <= 2^64.
  Hypothesis CB0 : Ca + K + 1 <= 2^64.

  Notation POST := (strspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str set lo m).

  Definition MEMS (m1 : word -> option byte) : Prop :=
    mem_inv rsegs m1 /\ bytes_at rsegs m1 Sa sfull /\ bytes_at rsegs m1 Ca afull
    /\ ro_cells rsegs m1 0xa7098 [C8 (Z_to_bv 64 0x6045d8)] /\ ro_cells rsegs m1 0x6045d8 [C8 can]
    /\ stk rsegs m1 lo (SP + -48) /\ munch [(SP - 48, SP)] m m1 /\ wmono rsegs m m1.

  Definition frame (l : list byte) : list cell :=
    [C8 (Z_to_bv 64 (setw l 0)); C8 (Z_to_bv 64 (setw l 1)); C8 (Z_to_bv 64 (setw l 2)); C8 (Z_to_bv 64 (setw l 3)); C8 can; C8 ra].

  Notation ST pc mm x5 x10 x11 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 0x6045d8) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Lemma fin : forall m1 x5 (w : word) x11 x13 x14 x15 x16 x17 (w0 w1 w2 w3 : word),
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) [C8 w0; C8 w1; C8 w2; C8 w3; C8 can; C8 ra] ->
    w = Z_to_bv 64 (Z.of_nat (spn_len set str)) ->
    evt rsegs POST (ST 0x9f7e8 m1 x5 w x11 x13 x14 x15 x16 x17).
  Proof using All.
    intros m1 x5 w x11 x13 x14 x15 x16 x17 w0 w1 w2 w3 (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1) FR ->.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    zstep. zstep. zstep. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
    zstep. zstep. zstep.
    release_frame FR ST1 (bv_unsigned sp).
    finish.
  Qed.

  Lemma fin_sub : forall m1 x5 x11 x13 x14 (w : word) x16 x17 (w0 w1 w2 w3 : word),
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) [C8 w0; C8 w1; C8 w2; C8 w3; C8 can; C8 ra] ->
    w = Z_to_bv 64 (Sa + Z.of_nat (spn_len set str)) ->
    evt rsegs POST (ST 0x9f7e4 m1 x5 a0 x11 x13 x14 w x16 x17).
  Proof using All.
    intros m1 x5 x11 x13 x14 w x16 x17 w0 w1 w2 w3 MM FR ->.
    pose proof (spn_le set str) as SL.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    zstep.
    eapply fin; [exact MM| exact FR| weq].
  Qed.

  Lemma scan_loop : forall (k : nat) (i : Z) m1 (b : byte) x5 (w : word) x15 x16 x17,
    Z.to_nat (L - i) = k -> (0 <= i < L)%Z -> nth_error str (Z.to_nat i) = Some b ->
    (forall j x, (j < Z.to_nat i)%nat -> nth_error str j = Some x -> in_set set x = true) ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) (frame set) -> w = Z_to_bv 64 (Sa + i) ->
    evt rsegs POST (ST 0x9f78c m1 x5 a0 (Z_to_bv 64 (SP + -48)) (Z_to_bv 64 (bv_unsigned b)) w x15 x16 x17).
  Proof using All.
    induction k as [|k IH]; intros i m1 b x5 w x15 x16 x17 Hk Hi HB IN MM FR Hw; [lia|]. subst w.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (byte_range b) as BR. pose proof (setw_range set (bv_unsigned b / 64)) as WR.
    unfold frame in FR.
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    assert (KQ : evt rsegs POST (ST 0x9f79c m1 x5 a0 (Z_to_bv 64 (SP + -48)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (Sa + i)) (Z_to_bv 64 (setw set q)) x16 x17)).
    { zstep. zstep.
      replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
      rewrite bit_of by lia. unfold q. rewrite <- in_set_testbit.
      zstep. destruct (in_set set b) eqn:INB.
      - if_false.
        destruct (Z.eq_dec (i + 1) L) as [EQ|NE].
        + pose proof (cstr_nth_len str) as HN. rewrite <- EQ in HN.
          pose proof (u8ro_read rsegs m1 Sa sfull (i + 1) _ (Z_to_bv 64 (Sa + i + 1)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
          zstep. clear RD. beta_goal.
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep. zstep. if_false. zstep.
          eapply fin_sub; [exact MM| exact FR|].
          rewrite (spn_prefix set str (length str)); [weq| lia| |].
          * intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|]. apply (IN j x); [lia| exact Hx].
          * intros x Hx. rewrite nth_none_len in Hx. discriminate.
        + destruct (cstr_nth_lt str (i + 1) SNONUL ltac:(lia)) as (b' & HN & HB' & NZ'). pose proof (byte_range b') as BR'.
          pose proof (u8ro_read rsegs m1 Sa sfull (i + 1) _ (Z_to_bv 64 (Sa + i + 1)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
          zstep. clear RD. beta_goal.
          zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. exact (NZ' K1). }
          replace (Sa + i + 1)%Z with (Sa + (i + 1))%Z by lia.
          apply (IH (i + 1)%Z m1 b'); [lia| lia| rewrite <- HB'; f_equal; lia| | exact MM| unfold frame; exact FR| reflexivity].
          intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|]. apply (IN j x); [lia| exact Hx].
      - if_true.
        zstep.
        eapply fin_sub; [exact MM| exact FR|].
        rewrite (spn_prefix set str (Z.to_nat i)); [weq| lia| exact IN|].
        intros x Hx. rewrite HB in Hx. inversion Hx. subst. exact INB. }
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    clearbody q.
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in KQ |- *.
    - replace (bv_unsigned sp + -48 + 8 * 0)%Z with (bv_unsigned sp + -48)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -48 + 8 * 1)%Z with (bv_unsigned sp + -40)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -48 + 8 * 2)%Z with (bv_unsigned sp + -32)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -48 + 8 * 3)%Z with (bv_unsigned sp + -24)%Z by lia. zstep. exact KQ.
  Qed.

  Lemma scan_entry : forall m1 x5 x11 x13 x14 x15 x16 x17,
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) (frame set) ->
    evt rsegs POST (ST 0x9f778 m1 x5 a0 x11 x13 x14 x15 x16 x17).
  Proof using All.
    intros m1 x5 x11 x13 x14 x15 x16 x17 MM FR. pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    destruct (Z.eq_dec 0 L) as [EQ|NE].
    - pose proof (cstr_nth_len str) as HN. rewrite <- EQ in HN.
      pose proof (u8ro_read rsegs m1 Sa sfull 0 _ a0 STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. beta_goal.
      change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      zstep. zstep. if_true.
      eapply fin_sub; [exact MM| unfold frame in FR; exact FR|].
      pose proof (spn_le set str). weq.
    - destruct (cstr_nth_lt str 0 SNONUL ltac:(lia)) as (b & HN & HB & NZ). pose proof (byte_range b) as BR.
      pose proof (u8ro_read rsegs m1 Sa sfull 0 _ a0 STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. beta_goal.
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. exact (NZ K0). }
      zstep. zstep.
      apply (scan_loop (Z.to_nat (L - 0)) 0 m1 b); [lia| lia| exact HB| intros j x Hj; lia| exact MM| exact FR| weq].
  Qed.

  Lemma frame_snoc : forall l (b : byte) (q : Z), q = (bv_unsigned b / 64)%Z ->
    frame (l ++ [b]) =
      [C8 (Z_to_bv 64 (if (q =? 0)%Z then Z.lor (setw l 0) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 0));
       C8 (Z_to_bv 64 (if (q =? 1)%Z then Z.lor (setw l 1) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 1));
       C8 (Z_to_bv 64 (if (q =? 2)%Z then Z.lor (setw l 2) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 2));
       C8 (Z_to_bv 64 (if (q =? 3)%Z then Z.lor (setw l 3) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 3));
       C8 can; C8 ra].
  Proof using All. intros l b q ->. unfold frame. rewrite !setw_snoc. reflexivity. Qed.

  Lemma build_loop : forall (k : nat) (i : Z) m1 (b : byte) x5 x16 x17,
    Z.to_nat (K - i) = k -> (0 <= i < K)%Z -> nth_error set (Z.to_nat i) = Some b ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) (frame (firstn (Z.to_nat i) set)) ->
    evt rsegs POST (ST 0x9f750 m1 x5 a0 (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 1) (Z_to_bv 64 (SP + -48)) x16 x17).
  Proof using All.
    induction k as [|k IH]; intros i m1 b x5 x16 x17 Hk Hi HB MM FR; [lia|].
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1). clear MM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (byte_range b) as BR.
    unfold frame in FR.
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    assert (NX : exists b', nth_error afull (Z.to_nat (i + 1)) = Some b' /\ (bv_unsigned b' = 0%Z <-> i + 1 = K)%Z).
    { destruct (Z.eq_dec (i + 1) K) as [E|NE].
      - exists (Z_to_bv 8 0). rewrite E. split; [exact (cstr_nth_len set)|]. split; [intros _; reflexivity| intros _; reflexivity].
      - destruct (cstr_nth_lt set (i + 1) ANONUL ltac:(lia)) as (b' & H1 & _ & NZ'). exists b'. split; [exact H1|]. split; [intros X; exfalso; exact (NZ' X)| intros X; lia]. }
    destruct NX as (b' & HN' & NZ'). pose proof (byte_range b') as BR'.
    assert (KQ : forall m2 x5' x16' x17', MEMS m2 -> rw_cells rsegs m2 (SP + -48) (frame (firstn (Z.to_nat (i + 1)) set)) ->
              evt rsegs POST (ST 0x9f770 m2 x5' a0 (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b')) (Z_to_bv 64 1) (Z_to_bv 64 (SP + -48)) x16' x17')).
    { intros m2 x5' x16' x17' MM2 FR2.
      zstep. zstep. if_cases KZ; zify_cond KZ.
      - replace (Ca + i + 2)%Z with (Ca + (i + 1) + 1)%Z by lia.
        apply (IH (i + 1)%Z m2 b'); [lia| lia| | exact MM2| exact FR2].
        rewrite nth_error_app1 in HN' by lia. exact HN'.
      - apply (proj1 NZ') in KZ. replace (Z.to_nat (i + 1)) with (length set) in FR2 by lia. rewrite firstn_all in FR2.
        apply scan_entry; [exact MM2| exact FR2]. }
    pose proof (u8ro_read rsegs m1 Ca afull (i + 1) _ (Z_to_bv 64 (Ca + i + 1)) ACC1 HN' ltac:(lia) ltac:(addr_tac)) as RD.
    assert (EF : firstn (Z.to_nat (i + 1)) set = firstn (Z.to_nat i) set ++ [b]).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_snoc. exact HB. }
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    pose proof (frame_snoc (firstn (Z.to_nat i) set) b q eq_refl) as FS. rewrite <- EF in FS.
    pose proof (setw_range (firstn (Z.to_nat i) set) q) as WR.
    clearbody q.
    assert (SR : (0 <= Z.shiftl 1 (bv_unsigned b mod 64) < 2^64)%Z).
    { rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; Z.div_mod_to_equations; lia]. }
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in FS, WR |- *; cbn [Z.eqb Pos.eqb] in FS; pose proof (lor_range64 _ _ WR SR) as LR;
    [ replace (bv_unsigned sp + -48 + 8 * 0)%Z with (bv_unsigned sp + -48)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 1)%Z with (bv_unsigned sp + -40)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 2)%Z with (bv_unsigned sp + -32)%Z by lia
    | replace (bv_unsigned sp + -48 + 8 * 3)%Z with (bv_unsigned sp + -24)%Z by lia ].
    all: zstep; zstep; zstep; clear RD; beta_goal.
    all: replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    all: zstep; rewrite ?unsigned_lit by lia; zstep.
    all: lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z in H by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity);
        rewrite <- FS in H; apply (KQ mc); [unfold MEMS; repeat (lazymatch goal with |- _ /\ _ => split end); assumption| exact H] end.
  Qed.

  Lemma one_loop : forall (k : nat) (i : Z) (c0 : byte) m1 x5 x14 x15 x16 x17 (w0 w1 w2 w3 : word),
    set = [c0] -> Z.to_nat (L + 1 - i) = k -> (0 <= i <= L)%Z ->
    (forall j x, (j < Z.to_nat i)%nat -> nth_error str j = Some x -> in_set set x = true) ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -48) [C8 w0; C8 w1; C8 w2; C8 w3; C8 can; C8 ra] ->
    evt rsegs POST (ST 0x9f7c8 m1 x5 a0 (Z_to_bv 64 i) (Z_to_bv 64 (bv_unsigned c0)) x14 x15 x16 x17).
  Proof using All.
    induction k as [|k IH]; intros i c0 m1 x5 x14 x15 x16 x17 w0 w1 w2 w3 E1 Hk Hi IN MM FR; [lia|].
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1).
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    assert (C0 : bv_unsigned c0 <> 0).
    { intros X. apply ANONUL. rewrite E1. left. apply bv_eq. rewrite X. reflexivity. }
    assert (NX : exists b, nth_error sfull (Z.to_nat i) = Some b /\ (i < L -> nth_error str (Z.to_nat i) = Some b) /\ (bv_unsigned b = 0 <-> i = L)).
    { destruct (Z.eq_dec i L) as [EQ|NE].
      - exists (Z_to_bv 8 0). rewrite EQ. split; [exact (cstr_nth_len str)|]. split; [lia|]. split; [intros _; reflexivity| intros _; reflexivity].
      - destruct (cstr_nth_lt str i SNONUL ltac:(lia)) as (b & H1 & H2 & NZ). exists b. split; [exact H1|]. split; [intros _; exact H2|]. split; [intros X; exfalso; exact (NZ X)| intros X; lia]. }
    destruct NX as (b & HN & HB & NZ). pose proof (byte_range b) as BR.
    zstep. rewrite ?unsigned_lit by lia.
    pose proof (u8ro_read rsegs m1 Sa sfull i _ (Z_to_bv 64 (Sa + i)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. clear RD. beta_goal.
    zstep. rewrite ?unsigned_lit by lia.
    zstep. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
    - assert (HiL : i < L) by (destruct (Z.eq_dec i L) as [EQ|NE]; [pose proof (proj2 NZ EQ); lia| lia]).
      apply (IH (i + 1) c0 m1 x5 _ x15 x16 x17 w0 w1 w2 w3 E1); [lia| lia| | exact MM| exact FR].
      intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj].
      + rewrite (HB HiL) in Hx. inversion Hx. subst x. rewrite E1, in_set1. apply Z.eqb_eq. lia.
      + apply (IN j x); [lia| exact Hx].
    - zstep. zstep.
      eapply fin; [exact MM| exact FR|].
      rewrite (spn_prefix set str (Z.to_nat i)); [weq| lia| exact IN|].
      intros x Hx. destruct (Z.eq_dec i L) as [EQ|NE].
      + rewrite EQ, Nat2Z.id, nth_none_len in Hx. discriminate.
      + rewrite (HB ltac:(lia)) in Hx. inversion Hx. subst x. rewrite E1, in_set1. apply Z.eqb_neq. lia.
  Qed.

  Lemma walk : forall m0,
    mem_inv rsegs m0 -> bytes_at rsegs m0 Sa sfull -> bytes_at rsegs m0 Ca afull ->
    ro_cells rsegs m0 0xa7098 [C8 (Z_to_bv 64 0x6045d8)] -> ro_cells rsegs m0 0x6045d8 [C8 can] ->
    stk rsegs m0 lo SP -> munch [(SP - 48, SP)] m m0 -> wmono rsegs m m0 ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9f70c) fc None m0 (seg_rom rsegs)).
  Proof using All.
    intros m0 MI1 STR1 ACC1 GOT1 CAN1 ST1 MU WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64)%Z in A1R.
    zstep. carve_frame 48%nat ST1. zstep. zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec K 0) as [K0|K0].
    - pose proof (cstr_nth_len set) as HC0. rewrite K0 in HC0.
      pose proof (u8ro_read rsegs _ Ca afull 0 _ a1 ACC1 HC0 ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. beta_goal.
      change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      zstep. zstep. zstep. zstep. zstep. if_true.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply (fin mc) end.
      + unfold MEMS. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| eapply munch_weaken; [| exact MU]; intros x Hx; exact Hx].
      + exact FR.
      + assert (E : set = []) by (apply length_zero_iff_nil; lia). rewrite E, spn_nil. reflexivity.
    - destruct (cstr_nth_lt set 0 ANONUL ltac:(lia)) as (c0 & HC0 & HC0' & NZ0). pose proof (byte_range c0) as C0R.
      pose proof (u8ro_read rsegs _ Ca afull 0 c0 a1 ACC1 HC0 ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. beta_goal.
      zstep. zstep. zstep. zstep. zstep. if_cases KZ0; zify_cond KZ0. { exfalso. exact (NZ0 KZ0). }
      destruct (Z.eq_dec K 1) as [K1|K1].
      + pose proof (cstr_nth_len set) as HC1. rewrite K1 in HC1.
        pose proof (u8ro_read rsegs _ Ca afull 1 _ (Z_to_bv 64 (Ca + 1)) ACC1 HC1 ltac:(lia) ltac:(addr_tac)) as RD.
        zstep. clear RD. beta_goal.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zstep. if_true. zstep.
        assert (E1 : set = [c0]) by (apply len1; [lia| exact HC0']).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply (one_loop (Z.to_nat (L + 1 - 0)) 0 c0 mc); [exact E1| lia| lia| intros j x Hj; lia| |exact FR] end.
        unfold MEMS. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| eapply munch_weaken; [| exact MU]; intros x Hx; exact Hx].
      + destruct (cstr_nth_lt set 1 ANONUL ltac:(lia)) as (c1 & HC1 & HC1' & NZ1). pose proof (byte_range c1) as C1R.
        pose proof (u8ro_read rsegs _ Ca afull 1 c1 (Z_to_bv 64 (Ca + 1)) ACC1 HC1 ltac:(lia) ltac:(addr_tac)) as RD.
        zstep. clear RD. beta_goal.
        zstep. if_cases KZ1; zify_cond KZ1. { exfalso. exact (NZ1 KZ1). }
        zstep. zstep. zstep.
        replace (Ca + 1)%Z with (Ca + 0 + 1)%Z by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          apply (build_loop (Z.to_nat (K - 0)) 0 mc c0); [lia| lia| exact HC0'| |] end.
        * unfold MEMS. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| eapply munch_weaken; [| exact MU]; intros x Hx; exact Hx].
        * cbn [Z.to_nat firstn]. unfold frame. rewrite !setw_nil. exact FR.
  Qed.
End W.

Theorem strspn_holds : strspn_contract.
Proof.
  unfold strspn_contract, STRSPN, SSP_GOT, SSP_GUARD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str set lo can
    STR SNZ ACC ANZ GOT CAN ST LOS DS DC DG DK MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. pose proof (bytes_at_bound _ _ _ _ ACC) as CB.
  rewrite length_app in SB, CB. cbn [length] in SB, CB.
  pose proof ST as (LO0 & _ & _).
  eapply walk; try eassumption; try lia; [apply ro8; exact GOT| apply ro8; exact CAN| apply munch_refl| apply wmono_refl].
Qed.
