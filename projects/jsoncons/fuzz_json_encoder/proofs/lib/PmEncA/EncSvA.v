(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ESVA.
Import PMES.
Section S.
Variable L : asan_layout.
Abbreviation mem := (word -> option byte).

Lemma sv_argA_agree : forall (LBo : list (Z * Z)) (FF : list fframe) (sp V S2 : Z) (M1 M2 : mem) (sv : Z) (bs : list Z),
  0 <= sv -> sv + 16 <= 2 ^ 64 ->
  (forall a, sv <= a < sv + 16 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall j, 0 <= j < 2 -> M2 (Z_to_bv 64 (S sv + j)) = M1 (Z_to_bv 64 (S sv + j))) ->
  (forall b0, In b0 LBo -> (0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 64) /\ (forall a, fst b0 <= a < fst b0 + snd b0 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\
                          (forall j, 0 <= j < snd b0 / 8 -> M2 (Z_to_bv 64 (S (fst b0) + j)) = M1 (Z_to_bv 64 (S (fst b0) + j)))) ->
  PMESA.sv_argA L LBo FF sp V S2 M1 sv bs -> PMESA.sv_argA L LBo FF sp V S2 M2 sv bs.
Proof.
  intros LBo FF sp V S2 M1 M2 sv bs HS0 HS1 KSV KSH KB (q & U1 & U2 & BY & DF & (bq & nq & Hin & N8 & Q1 & Q2 & SZ) & AP1 & AP2 & (FI & F8 & FZ)).
  destruct (KB _ Hin) as ((B0 & B1) & KQ & KQS). cbn [fst snd] in B0, B1, KQ, KQS.
  assert (LQ : 0 <= len bs) by (unfold len; lia).
  exists q. split; [apply (L5C.u64_at_agree _ M1 M2); [intros i Hi; apply KSV; lia | lia | lia | exact U1]|].
  split; [apply (L5C.u64_at_agree _ M1 M2); [intros i Hi; apply KSV; lia | lia | lia | exact U2]|].
  split; [apply (L5C.bytes_at_agree _ M1 M2); [intros i Hi; apply KQ; unfold len in *; lia | lia | unfold len in *; lia | exact BY]|].
  split; [apply (L5C.defined_agree M1 M2); [intros i Hi; apply KQ; lia | exact DF]|].
  split; [exists bq, nq; split; [exact Hin|]; split; [exact N8|]; split; [exact Q1|]; split; [exact Q2|]; apply (CL5A.shadow_zero_same M1 M2); [exact KQS | exact SZ]|].
  split; [exact AP1|]. split; [exact AP2|].
  split; [exact FI|]. split; [exact F8|]. apply (CL5A.shadow_zero_same M1 M2); [|exact FZ]. change (16 / 8) with 2. exact KSH.
Qed.
End S.
End ESVA.
