(** * Gap7Bridge — THE CHARACTERIZATION BRIDGE, proven (r4 respell).

    OWNER: an earlier development run (lane fork; ladder item (d), assembly file 2 of 2).

    LANDED IN THE r4 WINDOW alongside the Gap7Strict REPLACE: the
    theorem is typed at the tree's own (repaired) name.  Provenance:
    proven first in the g1 bridge bed against a verbatim restatement
    of the r4 draft (Gap7Bridge.v , bridge_r4_holds); this
    landing copy deletes that restatement and retypes the theorem —
    the proof body is byte-unchanged from the bed green.

    PROOF SHAPE: [it_pre_accepts] characterizes the driver positively —
    under the band, [it_pre] lands in PreEmpty or PreGo (never
    PreErr/PreOver): the kraft premises discharge the counter via the
    landed [it_kraft_15_spec] + [counts_of_it_count]; the incomplete
    check dies at lft = 0 (complete arm) or mx = 1 (the one-code arm);
    the it_enough charge dies by the regime bound
    [kraft_min_pow_bound] (completeness + population cap force
    findmin <= root0, CODES has no it_enough disjunct at all).
    [accepts_to_true] then mirrors [GtItTotal.it_model_total]'s fuel
    discharge, with the residue INSTANCE premise killing ItOverflow.

    PA-EXPORTS: build_accepts_of_kraft_holds.
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff Inftrees InftreesBridge DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblSortWin GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7BridgeParts.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The driver accepts: never PreErr, never PreOver.                    *)

Lemma it_pre_accepts :
  forall ty (l : list nat) (lens : zarr) (codes root0 : Z) (t0 : ztbl),
    codes = Z.of_nat (length l) ->
    CountsOf (it_cnt0 lens codes) l 15%nat ->
    (forall len, In len l -> (len <= 15)%nat) ->
    ((kraft_sum l 15 = 2 ^ 15)%nat
       \/ ((forall len, In len l -> (len <= 1)%nat)
           /\ (count_len l 1 <= 1)%nat
           /\ (ty = CT_LENS \/ ty = CT_DISTS))) ->
    1 <= root0 ->
    (forall m : nat, (2 ^ m <= length l)%nat -> Z.of_nat m <= root0) ->
    (forall u, 1 <= u <= 2 ^ root0 -> it_enough ty u = false) ->
    (exists t, it_pre ty lens codes root0 t0 = PreEmpty t)
    \/ (exists c st, it_pre ty lens codes root0 t0 = PreGo c st).
Proof.
  intros ty l lens codes root0 t0 Hcodes HC Hcap15 HKC Hr1 HN Hen.
  unfold it_pre. cbv zeta.
  change (it_count (Z.to_nat codes) 0 lens zzero) with (it_cnt0 lens codes).
  set (cnt := it_cnt0 lens codes) in *.
  set (mx := it_findmax 15%nat MAXBITS cnt) in *.
  destruct (Z.eqb mx 0) eqn:Emx.
  { left. eexists. reflexivity. }
  apply Z.eqb_neq in Emx.
  set (mn := it_findmin 16%nat 1 mx cnt).
  pose proof (sw_findmax_15 cnt) as [Hzhi Hdisj].
  fold mx in Hzhi, Hdisj.
  destruct Hdisj as [H0|[HmxR Hmxnz]]; [exact (False_ind _ (Emx H0))|].
  assert (HmxR' : 1 <= mx <= 15) by (unfold MAXBITS in HmxR; lia).
  pose proof (sw_findmin_16 mx cnt ltac:(lia)) as [Hzlo Hmnle].
  fold mn in Hzlo, Hmnle.
  assert (HmnR : 1 <= mn <= 15).
  { destruct (findmin_result 16%nat 1 mx cnt) as [Heq|[HRg _]];
      [fold mn in Heq | fold mn in HRg]; lia. }
  (* Normalize the incomplete arm: mx = 1 and the sum is small. *)
  assert (HKC2 : (kraft_sum l 15 = 2 ^ 15)%nat
                 \/ (mx = 1 /\ (kraft_sum l 15 <= 2 ^ 14)%nat
                     /\ (ty = CT_LENS \/ ty = CT_DISTS))).
  { destruct HKC as [HCk | (Hle1 & Hc1 & Hty2)]; [now left|right].
    assert (Hmx1 : mx = 1).
    { destruct (Z.eq_dec mx 1) as [->|Hne]; [reflexivity|]. exfalso.
      assert (Hb15 : (1 <= Z.to_nat mx <= 15)%nat) by lia.
      pose proof (HC (Z.to_nat mx) Hb15) as Hcc.
      rewrite Z2Nat.id in Hcc by lia.
      assert (Hcl : count_len l (Z.to_nat mx) = 0%nat).
      { unfold count_len. apply count_occ_not_In.
        intro Hin. pose proof (Hle1 _ Hin). lia. }
      rewrite Hcl in Hcc. apply Hmxnz. rewrite Hcc. reflexivity. }
    split; [exact Hmx1|]. split; [|exact Hty2].
    rewrite (ksum_le1 l Hle1). nia. }
  clear HKC.
  assert (Hle32768 : (kraft_sum l 15 <= 32768)%nat).
  { assert (H15 : (2 ^ 15)%nat = 32768%nat) by reflexivity.
    assert (H1415 : (2 ^ 14 <= 2 ^ 15)%nat)
      by (apply Nat.pow_le_mono_r; lia).
    destruct HKC2 as [HCk | (_ & Hsm & _)]; lia. }
  assert (Hkeq : it_kraft 15%nat 1 1 cnt
                 = Some (32768 - Z.of_nat (kraft_sum l 15))).
  { rewrite (it_kraft_15_spec l cnt Hcap15 HC).
    now rewrite (proj2 (Nat.leb_le _ _) Hle32768). }
  rewrite Hkeq. cbv beta iota.
  assert (Hinc : it_incomplete ty (32768 - Z.of_nat (kraft_sum l 15)) mx
                 = false).
  { destruct HKC2 as [HCk | (Hmx1 & _ & Hty2)].
    - replace (32768 - Z.of_nat (kraft_sum l 15)) with 0
        by (rewrite HCk; vm_compute; reflexivity).
      apply it_incomplete_complete.
    - rewrite Hmx1. destruct Hty2 as [->| ->];
        [apply it_incomplete_lens_one | apply it_incomplete_dists_one]. }
  rewrite Hinc. cbv beta iota.
  set (r1 := if Z.ltb mx root0 then mx else root0) in *.
  set (rr := if Z.ltb r1 mn then mn else r1) in *.
  assert (Hmnroot : mn <= root0).
  { destruct HKC2 as [HCk | (Hmx1 & _ & _)].
    - assert (Hzn : forall b : nat,
                 (1 <= b < Z.to_nat mn)%nat -> count_len l b = 0%nat).
      { intros b Hb.
        assert (Hcb : cnt (Z.of_nat b) = 0) by (apply Hzlo; lia).
        assert (Hb15 : (1 <= b <= 15)%nat) by lia.
        pose proof (HC b Hb15) as Hcc.
        rewrite Hcb in Hcc. lia. }
      pose proof (kraft_min_pow_bound l (Z.to_nat mn) Hcap15 HCk
                    ltac:(lia) Hzn) as Hpow.
      pose proof (HN (Z.to_nat mn) Hpow) as HNn.
      rewrite Z2Nat.id in HNn by lia. exact HNn.
    - lia. }
  assert (Hrr : 1 <= rr <= root0).
  { assert (Hr1b : 1 <= r1 <= root0).
    { unfold r1. destruct (Z.ltb_spec mx root0); lia. }
    unfold rr. destruct (Z.ltb_spec r1 mn); lia. }
  destruct (it_enough ty (Z.shiftl 1 rr)) eqn:Een.
  - exfalso.
    rewrite Z.shiftl_mul_pow2 in Een by lia.
    rewrite Z.mul_1_l in Een.
    rewrite Hen in Een; [discriminate|].
    split.
    + assert (0 < 2 ^ rr) by (apply Z.pow_pos_nonneg; lia). lia.
    + apply Z.pow_le_mono_r; lia.
  - right. eexists. eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* From an accepted pre-state to the guard, via the fuel discharge.    *)

Lemma accepts_to_true :
  forall ty (l : list nat) root0,
    0 <= Z.of_nat (length l) ->
    LensBounded (Gap7Strict.lens_of_list l) (Z.of_nat (length l)) ->
    (forall c st,
        it_pre ty (Gap7Strict.lens_of_list l) (Z.of_nat (length l)) root0 tnone
          = PreGo c st ->
        forall n t, it_loop n c st <> Some (ItOverflow t)) ->
    ((exists t, it_pre ty (Gap7Strict.lens_of_list l) (Z.of_nat (length l))
                  root0 tnone = PreEmpty t)
     \/ (exists c st, it_pre ty (Gap7Strict.lens_of_list l)
                        (Z.of_nat (length l)) root0 tnone = PreGo c st)) ->
    Gap7Strict.build_accepts_b ty l root0 = true.
Proof.
  intros ty l root0 Hc0 Hb INST HACC.
  unfold Gap7Strict.build_accepts_b, it_model.
  destruct HACC as [[t Ht]|(c & st & Hgo)].
  - rewrite Ht. reflexivity.
  - rewrite Hgo.
    pose proof (pre_tot_ok ty (Gap7Strict.lens_of_list l)
                  (Z.of_nat (length l)) root0 tnone Hc0 Hb) as HP.
    rewrite Hgo in HP. cbn [PreTotOk] in HP.
    assert (Hfuel : sw_N (Gap7Strict.lens_of_list l) (Z.of_nat (length l))
                    - s_sym st
                    <= Z.of_nat (S (Z.to_nat (Z.of_nat (length l))))).
    { pose proof (sw_N_le_codes (Gap7Strict.lens_of_list l)
                    (Z.of_nat (length l)) Hc0 Hb).
      pose proof (ti_sym _ _ _ _ HP).
      rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
    destruct (tot_loop (S (Z.to_nat (Z.of_nat (length l))))
                (Gap7Strict.lens_of_list l) (Z.of_nat (length l))
                c st Hc0 Hb HP Hfuel) as (r & Hr & Hnc).
    rewrite Hr.
    destruct r as [st'|st'|tv]; [case Hnc | reflexivity |].
    exfalso.
    exact (INST c st Hgo (S (Z.to_nat (Z.of_nat (length l)))) tv Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* THE THEOREM.                                                        *)

Theorem build_accepts_of_kraft_holds : build_accepts_of_kraft_STMT.
Proof.
  intros ty l root0 BAND INST.
  assert (Hc0 : 0 <= Z.of_nat (length l)) by apply Nat2Z.is_nonneg.
  destruct BAND as [ (Hty & Hlen & Hr0 & HKs & Hcap)
                   | [ (Hty & Hlen & Hr0 & HKd & Hcap)
                     | (Hty & Hlen & Hr0 & HKd & Hcap) ] ]; subst ty root0.
  - (* CODES: complete at scale 7, no it_enough disjunct at all *)
    assert (Hcap15 : forall len, In len l -> (len <= 15)%nat)
      by (intros len Hin; pose proof (Hcap len Hin); lia).
    assert (HK15 : (kraft_sum l 15 = 2 ^ 15)%nat).
    { rewrite (kraft_sum_scale l 7 15 Hcap ltac:(lia)), HKs. reflexivity. }
    apply (accepts_to_true CT_CODES l 7 Hc0 (zlens_bounded l Hcap15) INST).
    apply (it_pre_accepts CT_CODES l (Gap7Strict.lens_of_list l)
             (Z.of_nat (length l)) 7 tnone eq_refl
             (counts_of_it_count l 15%nat) Hcap15 (or_introl HK15)
             ltac:(lia)).
    + intros m Hm.
      destruct (Nat.le_gt_cases m 4) as [Hm4|Hm4]; [lia|].
      exfalso.
      assert (H5 : (2 ^ 5 <= 2 ^ m)%nat) by (apply Nat.pow_le_mono_r; lia).
      assert (H32 : (2 ^ 5 = 32)%nat) by reflexivity. lia.
    + intros u _. reflexivity.
  - (* LENS *)
    assert (HKC : (kraft_sum l 15 = 2 ^ 15)%nat
                  \/ ((forall len, In len l -> (len <= 1)%nat)
                      /\ (count_len l 1 <= 1)%nat
                      /\ (CT_LENS = CT_LENS \/ CT_LENS = CT_DISTS))).
    { destruct HKd as [HK|[Hle1 Hf]]; [now left|right].
      refine (conj Hle1 (conj _ (or_introl eq_refl))).
      rewrite count_len_filter1. exact Hf. }
    apply (accepts_to_true CT_LENS l 9 Hc0 (zlens_bounded l Hcap) INST).
    apply (it_pre_accepts CT_LENS l (Gap7Strict.lens_of_list l)
             (Z.of_nat (length l)) 9 tnone eq_refl
             (counts_of_it_count l 15%nat) Hcap HKC ltac:(lia)).
    + intros m Hm.
      destruct (Nat.le_gt_cases m 8) as [Hm8|Hm8]; [lia|].
      exfalso.
      assert (H9 : (2 ^ 9 <= 2 ^ m)%nat) by (apply Nat.pow_le_mono_r; lia).
      assert (H512 : (2 ^ 9 = 512)%nat) by reflexivity. lia.
    + intros u Hu.
      unfold it_enough, ENOUGH_LENS, ENOUGH_DISTS.
      change (2 ^ 9) with 512 in Hu.
      replace (852 <? u) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
  - (* DISTS *)
    assert (HKC : (kraft_sum l 15 = 2 ^ 15)%nat
                  \/ ((forall len, In len l -> (len <= 1)%nat)
                      /\ (count_len l 1 <= 1)%nat
                      /\ (CT_DISTS = CT_LENS \/ CT_DISTS = CT_DISTS))).
    { destruct HKd as [HK|[Hle1 Hf]]; [now left|right].
      refine (conj Hle1 (conj _ (or_intror eq_refl))).
      rewrite count_len_filter1. exact Hf. }
    apply (accepts_to_true CT_DISTS l 6 Hc0 (zlens_bounded l Hcap) INST).
    apply (it_pre_accepts CT_DISTS l (Gap7Strict.lens_of_list l)
             (Z.of_nat (length l)) 6 tnone eq_refl
             (counts_of_it_count l 15%nat) Hcap HKC ltac:(lia)).
    + intros m Hm.
      destruct (Nat.le_gt_cases m 4) as [Hm4|Hm4]; [lia|].
      exfalso.
      assert (H5 : (2 ^ 5 <= 2 ^ m)%nat) by (apply Nat.pow_le_mono_r; lia).
      assert (H32 : (2 ^ 5 = 32)%nat) by reflexivity. lia.
    + intros u Hu.
      unfold it_enough, ENOUGH_LENS, ENOUGH_DISTS.
      change (2 ^ 6) with 64 in Hu.
      replace (592 <? u) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
Qed.

Set Printing Width 2000.
Print Assumptions build_accepts_of_kraft_holds.
