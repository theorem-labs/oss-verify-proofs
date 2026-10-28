(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma wf_ps_init sb bptr : wf_ps (PMS.ps_init sb bptr).
Proof.
  unfold wf_ps, PMS.ps_init. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [lia|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; tauto|].
  exists [], []. split; [reflexivity|]. split; [constructor|]. intros _.
  split; [reflexivity|]. split; [lia|].
  split; [left; unfold ST_START; lia|].
  split; [left; split; [reflexivity| unfold comment_or_cr, ST_START, ST_CR; lia]|].
  split; [intros [H|[]]; discriminate H | intros H; discriminate H].      (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma kleft_init sb bptr : kleft (PMS.ps_init sb bptr) = 22.
Proof. reflexivity. Qed.
Lemma bleft_init sb bptr : bleft (PMS.ps_init sb bptr) = 2 ^ 28 + 1452.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Example num_final_ex1 : num_final [49; 46; 53; 101; 43; 49; 48].      (* [comment removed for export] *)
Proof. exists 7. split; [reflexivity | cbn; tauto]. Qed.
Example num_final_quirk : num_final [45; 48; 49; 50].                 (* [comment removed for export] *)
Proof. exists 2. split; [reflexivity | cbn; tauto]. Qed.
Example num_not_final : ~ num_final [49; 46].                          (* [comment removed for export] *)
Proof. intros (k & H & Hin). cbn in H. injection H as <-. cbn in Hin. lia. Qed.

(* [comment removed for export] *)
Example ls_next_ex : ls_next LS0 LS1 /\ ls_next LS0 LS2 /\ ls_next LS1 LS1 /\ ls_next LS1 LS2 /\ ls_next LS2 LS2 /\ ~ ls_next LS2 LS1 /\ ~ ls_next LS1 LS0.
Proof. cbn. tauto. Qed.

(* [comment removed for export] *)
Lemma ls1_mid M : ls_ok LS1 M -> PMS.statics_mid M.
Proof. intros (Hro & Hq & (G1 & G2 & G3) & Hg & Ha). split; [exact Hro|]. split; [exact Hq|]. split; [split; [exact G1 | exact G2]|]. split; [right; exact G3|]. left; split; assumption. Qed.   (* [comment removed for export] *)
Lemma ls2_mid M : ls_ok LS2 M -> PMS.statics_mid M.
Proof. intros (Hro & Hq & (G1 & G2 & G3) & Hg & Ha). split; [exact Hro|]. split; [exact Hq|]. split; [split; [exact G1 | exact G2]|]. split; [right; exact G3|]. right; split; assumption. Qed.   (* [comment removed for export] *)
