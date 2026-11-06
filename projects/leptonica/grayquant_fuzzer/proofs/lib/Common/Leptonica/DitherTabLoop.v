(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib DitherLib DitherTab.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition apart2 (r1 r2 : Z * Z) : Prop := fst r1 + snd r1 <= fst r2 \/ fst r2 + snd r2 <= fst r1.
Fixpoint pairwise (l : list (Z * Z)) : Prop :=
  match l with [] => True | r :: tl => (forall r', In r' tl -> apart2 r r') /\ pairwise tl end.
Lemma apart2_sym : forall r1 r2, apart2 r1 r2 -> apart2 r2 r1.
Proof. intros r1 r2 [H|H]; [right | left]; exact H. Qed.
Lemma pairwise_nth : forall l (i j : nat) d, pairwise l -> (i < j < length l)%nat -> apart2 (nth i l d) (nth j l d).
Proof.
  induction l as [|r tl IH]; intros i j d P Hij; [cbn in Hij; lia|].
  destruct P as [P1 P2]. destruct j as [|j]; [lia|]. destruct i as [|i].
  - cbn [nth]. apply P1. apply nth_In. cbn in Hij. lia.
  - cbn [nth]. apply IH; [exact P2 | cbn in Hij; lia].
Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

Definition tab_ok (sx : bool) (P : Z -> Prop) (m : word -> option byte) (tab : Z) : Prop :=
  0 <= tab /\ tab + 1024 <= 2 ^ 64 /\
  forall k, 0 <= k <= 255 -> exists bs, rdn segs m (Z_to_bv 64 (tab + 4 * k)) 4 = Some bs /\ P (rdv sx 4 bs).

(* [comment removed for export] *)
Lemma tab_ok_sok : forall sx (M0 Mi : word -> option byte) (tab : Z), wr_readable segs -> mem_grows M0 Mi ->
  store_ok segs M0 (Z_to_bv 64 tab) 1024 = true -> 0 <= tab -> tab + 1024 <= 2 ^ 64 -> tab_ok sx (fun _ => True) Mi tab.
Proof.
  intros sx M0 Mi tab WR G S H0 H1. split; [exact H0|]. split; [exact H1|]. intros k Hk.
  destruct (reg_read segs M0 Mi tab 1024 (tab + 4 * k) 4 WR G S H0 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [bs R].
  exists bs. split; [exact R | exact I].
Qed.

(* [comment removed for export] *)
Lemma tab_rd_of : forall sx P (R cells : list (Z * Z)) (M0 m : word -> option byte) (tab : Z),
  tab_ok sx P M0 tab -> rinv R M0 m -> cells_in R cells ->
  (forall r, In r R -> tab + 1024 <= fst r \/ fst r + snd r <= tab) ->
  tab_rd segs sx P cells m tab.
Proof.
  intros sx P R cells M0 m tab (T0 & T1 & TK) RI CI AP m' k FR Hk.
  destruct (TK k Hk) as (bs & Rd & Pb). exists bs. split; [|exact Pb]. rewrite <- Rd.
  apply (rinv_rdn segs R M0 m' (tab + 4 * k) 4 (rinv_cells R cells M0 m m' RI FR CI)); [lia | cbn; lia |].
  intros r Hr. specialize (AP r Hr). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

(* [comment removed for export] *)
Lemma tab_ok_rinv : forall sx P (R : list (Z * Z)) (M0 m : word -> option byte) (tab : Z),
  tab_ok sx P M0 tab -> rinv R M0 m -> (forall r, In r R -> tab + 1024 <= fst r \/ fst r + snd r <= tab) -> tab_ok sx P m tab.
Proof.
  intros sx P R M0 m tab (T0 & T1 & TK) RI AP. split; [exact T0|]. split; [exact T1|]. intros k Hk.
  destruct (TK k Hk) as (bs & Rd & Pb). exists bs. split; [|exact Pb]. rewrite <- Rd.
  apply (rinv_rdn segs R M0 m (tab + 4 * k) 4 RI); [lia | cbn; lia |].
  intros r Hr. specialize (AP r Hr). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
End WithSegs.

(* [comment removed for export] *)
Ltac pw GD i j D :=
  pose proof (pairwise_nth _ i j (0, 0) GD ltac:(cbn; lia)) as D; cbn in D; unfold apart2 in D; cbn [fst snd] in D.
