(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section P12.
  Variables (norm : list Z) (maxSV tl : Z).
  Hypothesis TL : 5 <= tl <= 9.
  Hypothesis MSV : 0 <= maxSV <= 52.
  Hypothesis LEN : maxSV + 1 <= Zlength norm.
  Hypothesis GE : forall i, 0 <= i <= maxSV -> -1 <= Znth i norm.
  Hypothesis SUM : pws norm (maxSV + 1) = 2^tl.
  Variables (cells0 : list seqsym) (symNext0 spread0 : list Z) (cells1 : list seqsym) (symNext1 : list Z) (high fast : Z).
  Hypothesis HC : Zlength cells0 = 2^tl.
  Hypothesis HN : maxSV + 1 <= Zlength symNext0.
  Hypothesis HSP : 2^tl + 8 <= Zlength spread0.
  Hypothesis LP : lowprob (Z.to_nat (maxSV + 1)) norm (2^(tl - 1)) 0 cells0 symNext0 (2^tl - 1) 1 = (cells1, symNext1, high, fast).

  Let size := 2^tl.

  Lemma p12_after1 :
    high + 1 = nsum norm (maxSV + 1) /\ -1 <= high <= 2^tl - 1 /\ Zlength cells1 = 2^tl /\ Zlength symNext1 = Zlength symNext0
    /\ (forall i, 0 <= i <= maxSV -> Znth i symNext1 = snext0 norm i)
    /\ above_good norm maxSV tl high cells1.
  Proof.
    pose proof (lowprob_inv norm maxSV tl TL MSV LEN GE SUM (2^(tl - 1)) (Z.to_nat (maxSV + 1)) 0 cells0 symNext0 (2^tl - 1) 1
                  ltac:(lia) ltac:(lia) HC HN) as P1.
    rewrite LP in P1. destruct P1 as (C1 & N1 & H1 & G1 & _ & S1).
    { change (pws norm 0 - nsum norm 0) with 0. lia. }
    { intros u Hu. lia. }
    { intros i Hi. lia. }
    pose proof (nsum_nonneg norm maxSV tl TL LEN (maxSV + 1) ltac:(lia)) as NN.
    assert (TOT : nsum norm (maxSV + 1) <= 2^tl).
    { pose proof (low_mono norm maxSV tl TL LEN GE 0 (maxSV + 1) ltac:(lia) ltac:(lia)) as LM. change (pws norm 0 - nsum norm 0) with 0 in LM.
      rewrite SUM in LM. lia. }
    split; [lia|]. split; [lia|]. split; [exact C1|]. split; [exact N1|]. split; [exact S1|].
    intros u Hu Hh. apply G1. lia.
  Qed.

  Lemma p12_fast : high = 2^tl - 1 -> forall spread1 pos1 cells2 p2,
    lay_symbols (Z.to_nat (maxSV + 1)) norm 0 0 spread0 = (spread1, pos1) ->
    place_fast (Z.to_nat (2^tl / 2)) (2^tl) (fse_tablestep (2^tl)) spread1 0 0 cells1 = (cells2, p2) ->
    Zlength cells2 = 2^tl /\ forall v, 0 <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells2 v)).
  Proof.
    intros EH spread1 pos1 cells2 p2 LSY PF0.
    destruct p12_after1 as (HH & HR & C1 & N1 & S1 & AG1).
    pose proof (size_range tl TL) as SR.
    assert (NOLOW : forall i, 0 <= i <= maxSV -> 0 <= Znth i norm).
    { intros i Hi. pose proof (GE i Hi). destruct (Z.eq_dec (Znth i norm) (-1)) as [E|E]; [|lia]. exfalso.
      pose proof (low_step norm maxSV tl TL LEN GE i Hi) as LS. rewrite E in LS. change (-1 =? -1) with true in LS. cbv iota in LS.
      pose proof (low_mono norm maxSV tl TL LEN GE 0 i ltac:(lia) ltac:(lia)) as L0. change (pws norm 0 - nsum norm 0) with 0 in L0.
      pose proof (low_mono norm maxSV tl TL LEN GE (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as L1. rewrite SUM in L1. lia. }
    pose proof (lay_symbols_inv norm maxSV tl TL MSV LEN GE SUM (Z.to_nat (maxSV + 1)) 0 0 spread0 ltac:(lia) ltac:(lia) NOLOW eq_refl HSP ltac:(intros; lia)) as LS.
    rewrite LSY in LS. destruct LS as (_ & PE & SG). rewrite PE in SG. replace (nsum norm (maxSV + 1)) with (2^tl) in SG by lia.
    assert (EVEN : 2 * (2^tl / 2) = 2^tl).
    { assert (E2 : 2^tl = 2^(tl - 1) * 2).
      { replace tl with (Z.succ (tl - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. lia. }
      rewrite E2, Z.div_mul by lia. lia. }
    pose proof (place_fast_inv norm maxSV tl TL MSV (fse_tablestep (2^tl)) spread1 SG (Z.to_nat (2^tl / 2)) 0 0 cells1 [] ltac:(lia) ltac:(lia) ltac:(lia) C1) as PF.
    change (2 * 0) with 0 in PF. rewrite PF0 in PF.
    destruct PF as (C2 & W2); [rewrite <- EH; exact AG1|intros u []|].
    split; [exact C2|].
    intros v Hv. apply W2; [|exact Hv]. rewrite app_nil_r.
    replace (2 * Z.to_nat (2^tl / 2))%nat with (Z.to_nat (2^tl - 1 + 1)) by lia.
    apply (cover_all tl (2^tl - 1) v); lia.
  Qed.

  Lemma p12_slow : high <> 2^tl - 1 -> forall cells2 p2,
    spread_slow (Z.to_nat (maxSV + 1)) norm (2^tl) (fse_tablestep (2^tl)) high 0 0 cells1 = (cells2, p2) ->
    Zlength cells2 = 2^tl /\ forall v, 0 <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells2 v)).
  Proof.
    intros NH cells2 p2 SS0.
    destruct p12_after1 as (HH & HR & C1 & N1 & S1 & AG1).
    pose proof (spread_slow_inv norm maxSV tl TL MSV LEN (fse_tablestep (2^tl)) high (Z.to_nat (maxSV + 1)) 0 0 cells1 [] ltac:(lia) ltac:(lia) C1 AG1 ltac:(intros u [])) as SS.
    rewrite SS0 in SS. destruct SS as (C2 & A2 & W2). split; [exact C2|].
    intros v Hv. destruct (Z.le_gt_cases v high) as [LE|GT]; [|apply A2; lia].
    apply W2; [|exact Hv]. rewrite app_nil_r. change (nsum norm 0) with 0. rewrite Z.sub_0_r.
    replace (nsum norm (maxSV + 1)) with (high + 1) by lia.
    apply (cover_all tl high v); lia.
  Qed.
End P12.
