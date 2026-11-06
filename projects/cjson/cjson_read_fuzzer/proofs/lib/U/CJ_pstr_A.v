(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition esc_extra (c : Z) : Z :=
  if (c =? 34) || (c =? 92) || (c =? 8) || (c =? 12) || (c =? 10) || (c =? 13) || (c =? 9) then 1
  else if c <? 32 then 5 else 0.

Fixpoint esc_count (s : list byte) : Z :=
  match s with [] => 0 | b :: s' => esc_extra (bv_unsigned b) + esc_count s' end.

Lemma esc_extra_range : forall c, 0 <= esc_extra c <= 5.
Proof. intros c. unfold esc_extra. destruct (_ || _); [lia|]. destruct (c <? 32); lia. Qed.

Lemma esc_count_app : forall a b, esc_count (a ++ b) = esc_count a + esc_count b.
Proof. induction a as [|x a IH]; intros b; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma esc_count_range : forall s, 0 <= esc_count s <= 5 * Z.of_nat (length s).
Proof. induction s as [|b s IH]; cbn; [lia|]. pose proof (esc_extra_range (bv_unsigned b)). lia. Qed.

Lemma esc_count_firstn_le : forall s i, esc_count (firstn i s) <= esc_count s.
Proof.
  intros s i. rewrite <- (firstn_skipn i s) at 2. rewrite esc_count_app. pose proof (esc_count_range (skipn i s)). lia.
Qed.

Lemma firstn_S_snoc : forall {A} (pre post : list A) (b : A), firstn (S (length pre)) (pre ++ b :: post) = pre ++ [b].
Proof. intros A pre post b. induction pre as [|x pre IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_len_app : forall {A} (pre post : list A), firstn (length pre) (pre ++ post) = pre.
Proof. intros A pre post. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma esc_count_firstn_S : forall s i b, nth_error s i = Some b ->
  esc_count (firstn (S i) s) = esc_count (firstn i s) + esc_extra (bv_unsigned b).
Proof.
  intros s i b H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen). subst i.
  rewrite firstn_S_snoc, firstn_len_app, esc_count_app. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition RMASK : Z := 0x400003700.
Definition resc1b (c : Z) : bool := (c =? 8) || (c =? 9) || (c =? 10) || (c =? 12) || (c =? 13) || (c =? 34).

Lemma rmask_bit : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK (Z.land c 63)) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.land (Z.of_nat n) 63)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma rmask_bit' : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK c) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.of_nat n)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma resc1b_extra : forall c, 0 < c <= 34 -> esc_extra c = if resc1b c then 1 else if c <? 32 then 5 else 0.
Proof.
  intros c Hc. unfold esc_extra, resc1b.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
Qed.

Lemma esc_extra_gt34 : forall c, 34 < c -> esc_extra c = if c =? 92 then 1 else 0.
Proof.
  intros c Hc. unfold esc_extra.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
  destruct (Z.ltb_spec c 32); [lia| reflexivity].
Qed.

Lemma unsigned_lit8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Hc. Qed.

Lemma neg_flag5 : forall b, Z.land (bv_swrap 32 (0 - Z.b2z b) mod 18446744073709551616) 5 = if b then 5 else 0.
Proof. intros [|]; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Str.
  Variables (S : Z) (str tail : list byte).
  Hypothesis NONUL : ~ In (wb 0) str.

  Notation full := (str ++ wb 0 :: tail).
  Notation L := (Z.of_nat (length str)).
  Notation E := (esc_count str).

  Lemma full_nth_lt : forall i, 0 <= i < L ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ 0 < bv_unsigned b < 256.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:EQ.
    - exists b. split. { rewrite nth_error_app1 by lia. exact EQ. } split; [reflexivity|].
      pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
      enough (bv_unsigned b <> 0) by lia.
      intros Hb. apply NONUL. replace (wb 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in EQ. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat L) = Some (wb 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition chb (i : Z) : byte := nth (Z.to_nat i) full (wb 0).
  Notation ch i := (bv_unsigned (chb i)).

  Lemma chb_nth : forall i, 0 <= i <= L -> nth_error full (Z.to_nat i) = Some (chb i).
  Proof.
    intros i Hi. unfold chb. destruct (nth_error full (Z.to_nat i)) as [b|] eqn:EQ.
    - f_equal. symmetry. apply nth_error_nth. exact EQ.
    - apply nth_error_None in EQ. rewrite length_app in EQ. cbn [length] in EQ. lia.
  Qed.

  Lemma ch_L : ch L = 0.
  Proof. pose proof (chb_nth L ltac:(lia)) as H. rewrite full_nth_len in H. injection H as <-. reflexivity. Qed.

  Lemma ch_lt : forall i, 0 <= i < L -> nth_error str (Z.to_nat i) = Some (chb i) /\ 0 < ch i < 256.
  Proof.
    intros i Hi. destruct (full_nth_lt i Hi) as (b & H1 & H2 & H3).
    rewrite (chb_nth i ltac:(lia)) in H1. injection H1 as ->. auto.
  Qed.

  Lemma ch_range : forall i, 0 <= i <= L -> 0 <= ch i < 256 /\ (ch i = 0 <-> i = L).
  Proof.
    intros i Hi. destruct (Z.eq_dec i L) as [->|NE].
    - rewrite ch_L. lia.
    - destruct (ch_lt i ltac:(lia)) as [_ H]. lia.
  Qed.

  Lemma ch_read : forall m i, bytes_at usegs m S full -> 0 <= i <= L -> ov_read_bytes usegs m (wa (S + i)) 1 = Some [chb i].
  Proof. intros m i STR Hi. eapply u8ro_read; [exact STR| apply chb_nth; exact Hi| lia| reflexivity]. Qed.

  Lemma esc_step : forall i, 0 <= i < L -> esc_count (firstn (Z.to_nat (i + 1)) str) = esc_count (firstn (Z.to_nat i) str) + esc_extra (ch i).
  Proof.
    intros i Hi. destruct (ch_lt i Hi) as [H2 _].
    replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. apply esc_count_firstn_S. exact H2.
  Qed.

  (* [comment removed for export] *)
  Definition pos (i : Z) : Z := i + esc_count (firstn (Z.to_nat i) str).

  Lemma pos_0 : pos 0 = 0.
  Proof. reflexivity. Qed.

  Lemma pos_step : forall i, 0 <= i < L -> pos (i + 1) = pos i + 1 + esc_extra (ch i).
  Proof. intros i Hi. unfold pos. rewrite esc_step by exact Hi. lia. Qed.

  Lemma pos_bound : forall i, 0 <= i <= L -> i <= pos i /\ pos i + (L - i) <= L + E.
  Proof.
    intros i Hi. unfold pos. pose proof (esc_count_range (firstn (Z.to_nat i) str)) as R1.
    pose proof (esc_count_firstn_le str (Z.to_nat i)) as R2. lia.
  Qed.

  Lemma pos_next_bound : forall i, 0 <= i < L -> pos i + 1 + esc_extra (ch i) + (L - i - 1) <= L + E.
  Proof. intros i Hi. rewrite <- pos_step by exact Hi. pose proof (pos_bound (i + 1) ltac:(lia)). lia. Qed.

  Lemma pos_L : pos L = L + E.
  Proof. unfold pos. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

 Ltac killK K := first [exfalso; lia | exfalso; apply K; reflexivity].

 Section Count.
  Variables (m : word -> option byte).
  Hypothesis STR : bytes_at usegs m S full.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis SHI : S + L + 1 + Z.of_nat (length tail) <= alloc_ceiling.

  Lemma S_bound : 0 <= S /\ S + L + 1 + Z.of_nat (length tail) <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B. lia. Qed.

  (* [comment removed for export] *)
  Variables (x1 x2 x3 x4 x5 x6 x7 x9 x12 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation CST pc j e c a5v x17 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 34) (Z_to_bv 64 92) x12 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17179883264) (Z_to_bv 64 a5v) (Z_to_bv 64 c) x17
             x18 x19 (Z_to_bv 64 e) (Z_to_bv 64 j) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Definition count_end : machine_state -> Prop :=
    fun ms' => exists c a5v x17, ms' = CST 0x1576c (L + 1) E c a5v x17.

  (* [comment removed for export] *)
  Definition PEC (i : Z) : Prop := forall x17, ch i <= 34 ->
    evt usegs count_end (CST 0x1571c (i + 1) (esc_count (firstn (Z.to_nat i) str)) (ch i) (S + i + 1) x17).
  Definition P1C (i : Z) : Prop := forall x17, (34 < ch i \/ (ch i <> 0 /\ resc1b (ch i) = false)) ->
    evt usegs count_end (CST 0x1574c (i + 1) (esc_count (firstn (Z.to_nat i) str)) (ch i) (S + i + 1) x17).

  Lemma count_both : forall (k : nat) (i : Z), Z.of_nat k = L - i -> 0 <= i <= L -> PEC i /\ P1C i.
  Proof.
    induction k as [|k IH]; intros i Hk Hi; unfold PEC, P1C.
    - assert (Ei : i = L) by lia. subst i. rewrite !ch_L. split; intros x17 Hc.
      + pose proof S_bound as SB.
        zstep. zstep. change (Z.land (Z.shiftr 17179883264 0) 1) with 0.
        step. if_cases K; zify_cond K; first [killK K | idtac]. clear K.
        step. if_cases K; zify_cond K; first [killK K | idtac]. clear K.
        apply evt_done. unfold count_end. rewrite firstn_all2 by lia. do 3 eexists. reflexivity.
      + exfalso. lia.
    - assert (Hi' : 0 <= i < L) by lia.
      destruct (IH (i+1) ltac:(lia) ltac:(lia)) as [IHEC IH1C]. unfold PEC, P1C in IHEC, IH1C.
      pose proof (ch_read m (i+1) STR ltac:(lia)) as RD1. destruct (ch_range (i+1) ltac:(lia)) as [CR1 CZ1].
      destruct (ch_lt i Hi') as [_ CR].
      pose proof (esc_step i Hi') as ES.
      pose proof S_bound as SB. pose proof SHI as SHI'. try rewrite alloc_ceiling_eq in SHI'.
      (* [comment removed for export] *)
      assert (D04 : forall x16 x17, evt usegs count_end
                (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 34) (Z_to_bv 64 92) x12 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17179883264) (Z_to_bv 64 (S + i)) x16 x17
                         x18 x19 (Z_to_bv 64 (esc_count (firstn (Z.to_nat (i + 1)) str))) (Z_to_bv 64 (i + 1)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x15734) fc None m (seg_rom usegs))).
      { intros x16 x17. zstep. zstep. replace (S + (i + 2) + -1) with (S + (i + 1)) by lia. zstep. cbv beta.
        step. if_cases K; zify_cond K; [| step];
          try (replace (S + (i + 2)) with (S + (i + 1) + 1) by lia); try (replace (i + 2) with (i + 1 + 1) by lia);
          [apply IHEC; lia | apply IH1C; lia]. }
      (* [comment removed for export] *)
      assert (BF8 : forall x17, esc_extra (ch i) = 1 ->
                evt usegs count_end (CST 0x15728 (i + 1) (esc_count (firstn (Z.to_nat i) str)) (ch i) (S + i + 1) x17)).
      { intros x17 HE. zstep. zstep. replace (S + i + 1 + -1) with (S + i) by lia.
        step. if_cases K; zify_cond K; first [killK K | idtac]. clear K.
        replace (esc_count (firstn (Z.to_nat i) str) + 1) with (esc_count (firstn (Z.to_nat (i + 1)) str)) by lia.
        apply D04. }
      (* [comment removed for export] *)
      assert (B20 : forall x17, esc_extra (ch i) = (if ch i <? 32 then 5 else 0) ->
                evt usegs count_end (CST 0x15750 (i + 1) (esc_count (firstn (Z.to_nat i) str)) (ch i) (S + i + 1) x17)).
      { intros x17 HE. zstep. zstep. zstep. rewrite neg_flag5. rewrite <- HE.
        zstep. rewrite <- ES. zstep. replace (S + i + 1 + -1) with (S + i) by lia.
        step. if_cases K; zify_cond K; first [killK K | idtac]; clear K; apply D04. }
      assert (H1C : forall x17, (34 < ch i \/ (ch i <> 0 /\ resc1b (ch i) = false)) ->
                evt usegs count_end (CST 0x1574c (i + 1) (esc_count (firstn (Z.to_nat i) str)) (ch i) (S + i + 1) x17)).
      { intros x17 Hc. step. if_cases K; zify_cond K.
        - apply BF8. rewrite esc_extra_gt34, K by lia. reflexivity.
        - apply B20. destruct (Z_lt_le_dec 34 (ch i)) as [Hgt|Hle].
          + rewrite esc_extra_gt34 by lia. replace (ch i =? 92) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (ch i <? 32) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
          + destruct Hc as [Hc|[Hz RB]]; [exfalso; lia|]. rewrite resc1b_extra, RB by lia. reflexivity. }
      split; [| exact H1C]. intros x17 Hc.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (Z.mod_small (ch i) 64) by lia. rewrite rmask_bit' by lia.
      destruct (resc1b (ch i)) eqn:RB.
      + step. if_cases K; zify_cond K; first [killK K | idtac]. clear K. apply BF8. rewrite resc1b_extra, RB by lia. reflexivity.
      + step. if_cases K; zify_cond K; first [killK K | idtac]. clear K.
        step. if_cases K; zify_cond K; first [killK K | idtac]. clear K.
        apply H1C. right. split; [lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma count_loop : forall (a5 a6 : word) x17, evt usegs count_end (CST 0x15710 1 0 (bv_unsigned a6) (bv_unsigned a5) x17).
  Proof.
    intros a5 a6 x17. pose proof S_bound as SB.
    pose proof (ch_read m 0 STR ltac:(lia)) as RD0. destruct (ch_range 0 ltac:(lia)) as [CR0 CZ0]. rewrite Z.add_0_r in RD0.
    destruct (count_both (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as [HEC H1C]. unfold PEC, P1C in HEC, H1C. cbn [Z.to_nat firstn esc_count] in HEC, H1C.
    rewrite !Z.add_0_l, !Z.add_0_r in HEC, H1C.
    zstep. replace (S + 1 + -1) with S by lia. zstep. cbv beta.
    step. if_cases K; zify_cond K.
    - apply H1C. lia.
    - apply HEC. lia.
  Qed.

 End Count.
End Str.


End CeilWrap.
