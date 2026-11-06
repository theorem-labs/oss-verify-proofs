(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import OblsLib InitClf OblsClf DrvEdges.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP PlanS OL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module OblsStart.
Import DrvEdges.DrvEdges.

Definition SIZE8 : sv := VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63.
Definition SIZE9 : sv := VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63.
Definition WORD64 : sv := VBlob false 2%uint63 (VP 64%uint63 (wp 0%uint63)) 8%uint63.
Definition BYTE64 : sv := VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63).
Definition V64 (i : int) : sv := VP 64%uint63 (wp i).

Definition chk_start_obl (o : obligation) : bool :=
  let fs := fst o in
  match fs with
  | [] => false
  | h :: _ =>
    (fact_eqb (snd o) (FULt (V64 15%uint63) SIZE8) && fact_eqb h (FNe WORD64 (VL (wp 0%uint63)))
       && has_fact (FAlign 64%uint63 3%uint63) fs && has_fact (FULt (V64 7%uint63) SIZE8) fs)
    || (fact_eqb (snd o) (FEq (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (V64 8%uint63)) (VP 3%uint63 (wp 0%uint63)))
       && fact_eqb h (FEq WORD64 (VL (wp 0%uint63)))
       && has_fact (FAlign 64%uint63 3%uint63) fs && has_fact (FULt (V64 7%uint63) SIZE8) fs
       && has_fact (FEq (VP 3%uint63 (wp 0%uint63)) (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) SIZE8)) fs)
    || (fact_eqb (snd o) (FULt (V64 1%uint63) SIZE9)
       && (fact_eqb h (FNe BYTE64 (VL (wp 0%uint63))) || fact_eqb h (FEq BYTE64 (VL (wp 47%uint63))))
       && has_fact (FULt (V64 0%uint63) SIZE9) fs)
  end.

Section WithE.
Variable E : env.
Hypothesis HPB : InitClf.PB_CLF (eb E).
Hypothesis Hz : ev E 0%uint63 = Z_to_bv 64 0.

Let K : Z := bv_unsigned (ev E 64%uint63).

Lemma den_V64 : forall i, bv_unsigned (den E (V64 i)) = (K + to_Z i) mod 2 ^ 64.
Proof. intros i. unfold V64. rewrite den_VP. reflexivity. Qed.

Lemma le_forms : forall fs, facts_hold E fs ->
  has_fact (FAlign 64%uint63 3%uint63) fs = true -> has_fact (FULt (V64 7%uint63) SIZE8) fs = true ->
  exists (a0 : list byte) (eptrs : list word) (q : Z),
    eb E 2%uint63 = flat_map word_le8 eptrs ++ word_le8 (Z_to_bv 64 0) /\ Forall (fun p => 0 < bv_unsigned p) eptrs /\
    bv_unsigned (den E SIZE8) = 8 * Z.of_nat (length eptrs) + 8 /\ Z.of_nat (length eptrs) <= 256 /\
    K = 8 * q /\ 0 <= q <= Z.of_nat (length eptrs) /\
    den E WORD64 = nth (Z.to_nat q) (eptrs ++ [Z_to_bv 64 0]) (Z_to_bv 64 0).
Proof.
  intros fs Hfs HA H7.
  pose proof HPB as (a0 & eptrs & Hb1 & Hnz & Hlen & Hb2 & Hle & Hptr & Hb8 & Hb9).
  pose proof (has_fact_sound E _ fs Hfs HA) as XA. cbn [fact_holds] in XA. change (2 ^ to_Z 3%uint63) with 8 in XA.
  pose proof (has_fact_sound E _ fs Hfs H7) as X7. cbn [fact_holds] in X7. fold (V64 7%uint63) in X7. rewrite den_V64 in X7.
  change (to_Z 7%uint63) with 7 in X7.
  pose proof (den_param8_u E 8%uint63 _ Hb8 ltac:(lia)) as S8. fold SIZE8 in S8. rewrite S8 in X7.
  pose proof (u64_range (ev E 64%uint63)) as HK. fold K in HK.
  apply Z.mod_divide in XA; [|lia]. destruct XA as [q Hq]. fold K in Hq.
  assert (Hq2 : 0 <= q <= Z.of_nat (length eptrs)).
  { destruct (Z_lt_ge_dec (K + 7) (2 ^ 64)); [rewrite Z.mod_small in X7 by lia; lia|].
    exfalso. rewrite <- (Z.mod_add _ (-1)) in X7 by lia. rewrite Z.mod_small in X7 by lia. lia. }
  exists a0, eptrs, q. split; [exact Hb2|]. split; [exact Hptr|]. split; [exact S8|]. split; [exact Hle|]. split; [lia|]. split; [exact Hq2|].
  unfold WORD64. apply (OblsClf.envp_word E eptrs q Hb2); lia.
Qed.

Lemma obl_le0 : forall fs, facts_hold E fs ->
  has_fact (FAlign 64%uint63 3%uint63) fs = true -> has_fact (FULt (V64 7%uint63) SIZE8) fs = true ->
  fact_holds E (FNe WORD64 (VL (wp 0%uint63))) -> fact_holds E (FULt (V64 15%uint63) SIZE8).
Proof.
  intros fs Hfs HA H7 Hne. destruct (le_forms fs Hfs HA H7) as (a0 & eptrs & q & Hb2 & Hptr & S8 & Hle & HKq & Hq & HW).
  cbn [fact_holds] in Hne |- *. rewrite den_V64, S8. change (to_Z 15%uint63) with 15.
  assert (Hqn : q <> Z.of_nat (length eptrs)).
  { intros Heq. apply Hne. rewrite HW, Heq, Nat2Z.id, OblsClf.nth_last_word. apply bv_eq. rewrite den_lit. reflexivity. }
  pose proof (u64_range (ev E 64%uint63)) as HK. fold K in HK. rewrite Z.mod_small; lia.
Qed.

Lemma obl_le1 : forall fs, facts_hold E fs ->
  has_fact (FAlign 64%uint63 3%uint63) fs = true -> has_fact (FULt (V64 7%uint63) SIZE8) fs = true ->
  has_fact (FEq (VP 3%uint63 (wp 0%uint63)) (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) SIZE8)) fs = true ->
  fact_holds E (FEq WORD64 (VL (wp 0%uint63))) ->
  fact_holds E (FEq (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (V64 8%uint63)) (VP 3%uint63 (wp 0%uint63))).
Proof.
  intros fs Hfs HA H7 H3 Heq0. destruct (le_forms fs Hfs HA H7) as (a0 & eptrs & q & Hb2 & Hptr & S8 & Hle & HKq & Hq & HW).
  pose proof (has_fact_sound E _ fs Hfs H3) as X3. cbn [fact_holds] in X3, Heq0 |- *.
  assert (Hqe : q = Z.of_nat (length eptrs)).
  { destruct (Z.eq_dec q (Z.of_nat (length eptrs))) as [|Hne]; [assumption|exfalso].
    rewrite HW in Heq0. assert (Hlt : (Z.to_nat q < length eptrs)%nat) by lia. rewrite app_nth1 in Heq0 by exact Hlt.
    pose proof (proj1 (Forall_nth _ _) Hptr (Z.to_nat q) (Z_to_bv 64 0) Hlt) as Hp. cbn beta in Hp.
    rewrite Heq0, den_lit in Hp. change (to_Z 0%uint63) with 0 in Hp. lia. }
  apply (f_equal bv_unsigned) in X3. rewrite den_add, !den_VP, S8 in X3. change (to_Z 0%uint63) with 0 in X3.
  apply bv_eq. rewrite den_add, !den_VP, den_V64. change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
  pose proof (u64_range (ev E 2%uint63)). pose proof (u64_range (ev E 3%uint63)). pose proof (u64_range (ev E 64%uint63)) as HK. fold K in HK.
  rewrite X3. rewrite (Z.mod_small (bv_unsigned (ev E 2%uint63) + 0)) by lia. rewrite (Z.mod_small (K + 8)) by lia.
  f_equal. lia.
Qed.

Lemma obl_lp : forall fs, facts_hold E fs -> has_fact (FULt (V64 0%uint63) SIZE9) fs = true ->
  fact_holds E (FNe BYTE64 (VL (wp 0%uint63))) -> fact_holds E (FULt (V64 1%uint63) SIZE9).
Proof.
  intros fs Hfs H0 Hne. pose proof HPB as (a0 & eptrs & Hb1 & Hnz & Hlen & Hb2 & Hle & Hptr & Hb8 & Hb9).
  pose proof (has_fact_sound E _ fs Hfs H0) as X0. cbn [fact_holds] in X0, Hne |- *.
  pose proof (den_param8_u E 9%uint63 _ Hb9 ltac:(lia)) as S9. fold SIZE9 in S9. rewrite S9 in X0 |- *.
  rewrite den_V64 in X0 |- *. change (to_Z 0%uint63) with 0 in X0. change (to_Z 1%uint63) with 1.
  pose proof (u64_range (ev E 64%uint63)) as HK. fold K in HK. rewrite Z.add_0_r, Z.mod_small in X0 by lia.
  pose proof (OblsClf.lp_core E a0 Hb1 ltac:(fold K; lia) Hne) as C. fold K in C. rewrite Z.mod_small; lia.
Qed.

Lemma chk_start_obl_sound : forall o, chk_start_obl o = true -> facts_hold E (fst o) -> fact_holds E (snd o).
Proof.
  intros [fs f] H Hfs. unfold chk_start_obl in H. cbn [fst snd] in *.
  destruct fs as [|h t]; [discriminate H|].
  pose proof (proj1 (Forall_forall _ _) Hfs h (or_introl eq_refl)) as Hh.
  apply orb_prop in H. destruct H as [H|H]; [apply orb_prop in H; destruct H as [H|H]|].
  - apply andb_prop in H as [H H7]. apply andb_prop in H as [H HA]. apply andb_prop in H as [Hc Hd].
    apply fact_eqb_eq in Hc. apply fact_eqb_eq in Hd. subst f h. exact (obl_le0 _ Hfs HA H7 Hh).
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H HA]. apply andb_prop in H as [Hc Hd].
    apply fact_eqb_eq in Hc. apply fact_eqb_eq in Hd. subst f h. exact (obl_le1 _ Hfs HA H7 H3 Hh).
  - apply andb_prop in H as [H H0]. apply andb_prop in H as [Hc Hd]. apply fact_eqb_eq in Hc. subst f.
    apply (obl_lp _ Hfs H0). apply orb_prop in Hd. destruct Hd as [Hd|Hd]; apply fact_eqb_eq in Hd; subst h; [exact Hh|].
    cbn [fact_holds] in Hh |- *. rewrite Hh. intros X. apply (f_equal bv_unsigned) in X. rewrite !den_lit in X. discriminate X.
Qed.
End WithE.

Theorem obls_start_sound : forall (PB : (int -> list byte) -> Prop) (l : list obligation),
  (forall b, PB b -> InitClf.PB_CLF b) -> forallb chk_start_obl l = true -> obls_hold PB l.
Proof.
  intros PB l HPB H. unfold obls_hold. apply Forall_forall. intros o Ho E HPBE Hz Hfs.
  exact (chk_start_obl_sound E (HPB _ HPBE) o (proj1 (forallb_forall _ _) H o Ho) Hfs).
Qed.

End OblsStart.
