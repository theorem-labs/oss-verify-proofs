(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMemSound VCert VContract VContractSound VContractSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zkey (z : Z) : positive := Z.to_pos z.

Definition contract_eqb (a b : contract) : bool :=
  match a, b with
  | C_memcpy, C_memcpy | C_memset, C_memset | C_memcmp, C_memcmp | C_bcmp, C_bcmp
  | C_strlen, C_strlen | C_strcmp, C_strcmp | C_strncpy, C_strncpy | C_tolower, C_tolower
  | C_strtoul, C_strtoul => true
  | _, _ => false
  end.

Lemma contract_eqb_eq a b : contract_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intros; congruence. Qed.

(* [comment removed for export] *)
Definition ctab_check (expected : list (Z * contract)) (ctab : pmap contract) : bool :=
  forallb (fun kv : positive * contract =>
             existsb (fun e : Z * contract =>
                        Z.ltb 0 (fst e) && Pos.eqb (fst kv) (Z.to_pos (fst e)) && contract_eqb (snd kv) (snd e))
                     expected)
          (pm_elements ctab).

Section Tab.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable CI : cimg.

  (* [comment removed for export] *)
  Definition ctab_sound (ctab : pmap contract) : Prop :=
    forall tgt c, 0 < tgt -> pm_get (zkey tgt) ctab = Some c ->
      contract_post SEGS P E mem0 rom CI c tgt /\ contract_dead SEGS P E mem0 CI c.

  Definition entry_ok (e : Z * contract) : Prop :=
    contract_post SEGS P E mem0 rom CI (snd e) (fst e) /\ contract_dead SEGS P E mem0 CI (snd e).

  Lemma ctab_sound_of_check expected ctab :
    ctab_check expected ctab = true -> Forall entry_ok expected -> ctab_sound ctab.
  Proof.
    intros Hc HF tgt c Ht Hg. unfold ctab_check in Hc.
    apply pm_elements_complete in Hg.
    pose proof (proj1 (forallb_forall _ _) Hc _ Hg) as X. cbn beta in X.
    apply existsb_exists in X as [[t' c'] [Hin Hb]]. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb Hcc]. apply andb_prop in Hb as [Ht' Hk].
    apply Z.ltb_lt in Ht'. apply Pos.eqb_eq in Hk. apply contract_eqb_eq in Hcc. subst c'.
    assert (tgt = t') by (unfold zkey in Hk; rewrite <- (Z2Pos.id tgt Ht), <- (Z2Pos.id t' Ht'), Hk; reflexivity). subst t'.
    exact (proj1 (Forall_forall _ _) HF _ Hin).
  Qed.
End Tab.
