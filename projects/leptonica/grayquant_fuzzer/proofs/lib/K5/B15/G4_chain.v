(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Arr Walk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout R_unwind_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint chain_okW (W : list (Z * Z)) (pc : Z) (m : mem) (lo f : Z) (ras : list Z) : Prop :=
  match ras with
  | [] => f <= lo \/ f mod 8 <> 0 \/ 2^63 <= f
  | ra1 :: ras' =>
      lo < f /\ f mod 8 = 0 /\ 16 <= f < 2^64 /\ 4096 <= ra1 < 2^64 /\ ra1 <> pc
      /\ disjoint_from W (f + -16) 16
      /\ exists fp1 : Z, 0 <= fp1 < 2^64 /\ rw_cells asegs m (f + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 ra1)]
                         /\ chain_okW W pc m f fp1 ras'
  end.

Lemma uw_loop_chain : forall W pc hi (m : mem) ras lo f ra acc,
  chain_okW W pc m lo f ras -> hi <= 2^63 -> 4096 <= ra -> ra <> pc ->
  (Z.of_nat (length acc) + Z.of_nat (length ras) + 1 <= 30) ->
  exists ch tr k, chain_cells W m f ch /\ uw_loop pc 4096 hi 30 ((ra, f) :: ch) lo acc = Some tr
                  /\ (k <= length ras)%nat /\ tr = acc ++ ra :: firstn k ras.
Proof.
  intros W pc hi m ras. induction ras as [|ra1 ras IH]; intros lo f ra acc HC Hhi Hra Hne Hlen.
  - exists [], (acc ++ [ra]), 0%nat. split; [exact I|]. split; [| split; [cbn; lia | reflexivity]].
    cbn [uw_loop]. cbn [length] in Hlen.
    rewrite (proj2 (Z.leb_gt 30 (Z.of_nat (length acc)))) by lia.
    rewrite (proj2 (Z.ltb_ge ra 4096)) by lia. rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne.
    assert (FS : fr_ok lo hi f = false).
    { unfold fr_ok. cbn [chain_okW] in HC. destruct HC as [H|[H|H]].
      - rewrite (proj2 (Z.ltb_ge lo f)) by lia. reflexivity.
      - rewrite (proj2 (Z.eqb_neq (f mod 8) 0)) by exact H. rewrite !andb_false_r. reflexivity.
      - rewrite (proj2 (Z.ltb_ge f hi)) by lia. rewrite andb_false_r. reflexivity. }
    rewrite FS. reflexivity.
  - cbn [chain_okW] in HC. destruct HC as (H1 & H2 & H3 & H4 & H5 & H6 & fp1 & H7 & H8 & H9).
    cbn [length] in Hlen.
    destruct (IH f fp1 ra1 (acc ++ [ra]) H9 Hhi ltac:(lia) H5 ltac:(rewrite length_app; cbn [length]; lia)) as (ch & tr & k & C1 & C2 & C3 & C4).
    destruct (fr_ok lo hi f) eqn:FS.
    + exists ((ra1, fp1) :: ch), tr, (S k). split; [| split; [| split; [cbn [length]; lia |]]].
      * cbn [chain_cells]. split; [exact H8|]. split; [lia|]. split; [exact H6 | exact C1].
      * cbn [uw_loop]. rewrite (proj2 (Z.leb_gt 30 (Z.of_nat (length acc)))) by lia.
        rewrite (proj2 (Z.ltb_ge ra 4096)) by lia. rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne. rewrite FS.
        cbn [uw_loop] in C2. exact C2.
      * rewrite C4. rewrite <- app_assoc. reflexivity.
    + exists ((ra1, fp1) :: ch), (acc ++ [ra]), 0%nat. split; [| split; [| split; [lia | reflexivity]]].
      * cbn [chain_cells]. split; [exact H8|]. split; [lia|]. split; [exact H6 | exact C1].
      * cbn [uw_loop]. rewrite (proj2 (Z.leb_gt 30 (Z.of_nat (length acc)))) by lia.
        rewrite (proj2 (Z.ltb_ge ra 4096)) by lia. rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne. rewrite FS. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem unwind_trace_chain : forall W pc bot top (m : mem) usp ra s0 ras,
  chain_okW W pc m usp s0 ras -> 4096 <= top -> top <= 2^63 -> 4096 <= ra -> ra <> pc -> (length ras <= 20)%nat ->
  exists ch tr j, chain_cells W m s0 ch /\ unwind_trace pc 4096 bot top 30 usp ((ra, s0) :: ch) = Some tr
                  /\ (1 <= j <= S (S (length ras)))%nat /\ tr = firstn j (pc :: ra :: ras).
Proof.
  intros W pc bot top m usp ra s0 ras HC Ht1 Ht2 Hra Hne Hl.
  destruct (uw_loop_chain W pc (top - 16) m ras usp s0 ra [pc] HC ltac:(lia) Hra Hne ltac:(cbn [length]; lia))
    as (ch & tr & k & C1 & C2 & C3 & C4).
  unfold unwind_trace. rewrite (proj2 (Z.eqb_neq (top / 4096) 0)) by (Z.div_mod_to_equations; lia).
  destruct (fr_ok bot (top - 16) usp).
  - exists ch, tr, (S (S k)). split; [exact C1|]. split; [exact C2|]. split; [lia|]. rewrite C4. reflexivity.
  - exists ch, [pc], 1%nat. split; [exact C1|]. split; [reflexivity|]. split; [lia | reflexivity].
Qed.

(* [comment removed for export] *)
Definition prefixes (l : list Z) : list (list Z) := map (fun k => firstn (S k) l) (seq 0 (length l)).

Lemma prefixes_in : forall l j, (1 <= j <= length l)%nat -> In (firstn j l) (prefixes l).
Proof.
  intros l j Hj. unfold prefixes. apply in_map_iff. exists (j - 1)%nat. split; [f_equal; lia|]. apply in_seq. lia.
Qed.

Lemma prefixes_length : forall l t, In t (prefixes l) -> (1 <= length t <= length l)%nat.
Proof.
  intros l t H. unfold prefixes in H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. rewrite length_firstn. lia.
Qed.

Lemma firstn_length_le : forall (l : list Z) j, (length (firstn j l) <= j)%nat.
Proof. intros l j. rewrite length_firstn. lia. Qed.
