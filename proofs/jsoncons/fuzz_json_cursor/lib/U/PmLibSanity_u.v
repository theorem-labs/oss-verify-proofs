(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma wf_ps_init sb bptr : wf_ps (PMS.ps_init sb bptr).
Proof.
  unfold wf_ps, PMS.ps_init. cbn [ps_sst ps_nst ps_stack ps_scap ps_more ps_level ps_st ps_buf].
  split; [lia|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; tauto|].
  exists [], []. split; [reflexivity|]. split; [constructor|]. intros _.
  split; [reflexivity|]. split; [lia|].
  split; [left; unfold ST_START; lia|].
  split; [left; split; [reflexivity| unfold comment_or_cr, ST_START, ST_CR; lia]|].
  split; [intros [H|[]]; discriminate H | intros H; discriminate H].
Qed.

Lemma kleft_init sb bptr : kleft (PMS.ps_init sb bptr) = 22.
Proof. reflexivity. Qed.
Lemma bleft_init sb bptr : bleft (PMS.ps_init sb bptr) = 2 ^ 28 + 1452.
Proof. reflexivity. Qed.

Example num_final_ex1 : num_final [49; 46; 53; 101; 43; 49; 48].
Proof. exists 7. split; [reflexivity | cbn; tauto]. Qed.
Example num_final_quirk : num_final [45; 48; 49; 50].
Proof. exists 2. split; [reflexivity | cbn; tauto]. Qed.
Example num_not_final : ~ num_final [49; 46].
Proof. intros (k & H & Hin). cbn in H. injection H as <-. cbn in Hin. lia. Qed.

Example ls_next_ex : ls_next LS0 LS1 /\ ls_next LS0 J /\ ls_next LS1 LS1 /\ ls_next LS1 J /\ ls_next J J /\ ~ ls_next J LS1 /\ ~ ls_next LS1 LS0 /\
                    ls_next J JC /\ ls_next C CJ /\ ls_next LS1 C /\ ~ ls_next JC CJ.
Proof.
  unfold ls_next, ls_le. repeat split; cbn; try discriminate; try exact I; try (left; reflexivity); try (right; reflexivity); try reflexivity;
  try (intros (_ & [Hx|Hx]); discriminate Hx); try (intros (Hx & _); apply Hx; reflexivity); try (intros (_ & Hx); discriminate Hx).
Qed.

Lemma ls_mid : forall g M, g <> LS0 -> ls_ok g M -> PMS.statics_mid M.
Proof.
  intros g M Hg (Hro & Hq & H).
  assert (H' : loc_done M /\ errcat_guard M (jbit g) /\ convcat_guard M (cbit g) /\ atexit_cells M (ls_atexit g))
    by (destruct g; [exfalso; apply Hg; reflexivity | exact H ..]).
  destruct H' as ((G1 & G2 & G3) & Hj & Hc & Ha).
  split; [exact Hro|]. split; [exact Hq|]. split; [split; [exact G1 | exact G2]|]. split; [right; exact G3|].
  exists g. split; [exact Hg|]. split; [exact Hj|]. split; [exact Hc | exact Ha].
Qed.
Lemma ls1_mid M : ls_ok LS1 M -> PMS.statics_mid M.
Proof. apply ls_mid. discriminate. Qed.
