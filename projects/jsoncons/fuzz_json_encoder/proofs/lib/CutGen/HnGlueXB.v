(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import HnKitXB2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HGX.
Section G.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.

Lemma enc_agree_ns_ok : HK2.enc_agree_nsP (PMESA.enc_invA L IC EC).
Proof.
  intros M M' V S2 g HI HA. pose proof HI as (I1 & _ & _ & _ & _ & _ & (R1 & R2 & R3 & R4 & RB)).
  assert (AV : EKA.agree M M' V PMES.ENC_SIZE) by (intros i Hi; apply HA; left; exact Hi).
  apply (EKA.enc_invA_agree L IC EC M M' V S2 g); [apply (EKA.agree_sub _ _ _ _ _ _ AV); unfold PMES.O_COLUMN, PMES.ENC_SIZE; lia | apply (EKA.agree_sub _ _ _ _ _ _ AV); unfold PMES.O_COLON, PMES.ENC_SIZE; lia | | | | exact HI].
  - unfold PMESA.enc_objA in I1. repeat (destruct I1 as [_ I1]). apply (L5C.defined_agree M M'); [apply (EKA.agree_sub _ _ _ _ _ _ AV); unfold PMES.O_COLUMN, PMES.ENC_SIZE; lia|].
    intros i Hi. replace (V + PMES.O_COLUMN + i) with (V + (PMES.O_COLUMN + i)) by lia. apply I1. unfold PMES.O_COLUMN, PMES.ENC_SIZE in *. lia.
  - intros i Hi. apply HA. right. left. exact Hi.
  - intros b Hb. destruct (RB b Hb) as (B0 & B16 & Bn & B1). split.
    + intros i Hi. apply HA. right. right. left. exists b. exact (conj Hb Hi).
    + apply (EKA.shagree_of_shadow M M' (fst b) (snd b) (snd b / 8)); [| exact Bn | apply Z.div_pos; lia | pose proof (Z.mul_div_le (snd b) 8 ltac:(lia)); lia |].
      * exact (CHA.mod8_of_16 _ B16).
      * intros a Ha. apply HA. right. right. right. exists b. exact (conj Hb Ha).
Qed.

Lemma enc_vis_ok : forall (M : PMSA.mem) V S2 g, PMESA.enc_invA L IC EC M V S2 g -> PMSA.vis_at L IC M V.
Proof. intros M V S2 g ((H & _) & _). exact H. Qed.
End G.
End HGX.
