(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzTac BzTac2 BzContracts DecCut DecTac DecTacM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac dj_slim AOK Y slim :=
  slim; pose proof Y; pose proof alloc_ceiling_range; pose proof (alin_core _ _ AOK);
  cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_plain.

Ltac revive_fs H MUL WML AOK slim :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML | dj_slim AOK (act_img_s _ _ AOK) slim ]
  | u32arr ?segs me ?A ?ws =>
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML | dj_slim AOK (act_img_s _ _ AOK) slim ]
  | u8arr ?segs me ?A ?bs =>
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML | dj_slim AOK (act_img_s _ _ AOK) slim ]
  | bytes_at ?segs me ?A ?bs =>
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL | dj_slim AOK (act_sep_s_src _ _ AOK) slim ]
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H;
      [ | exact MUL | exact WML | dj_slim AOK I slim | dj_slim AOK I slim | dj_slim AOK I slim ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | slim;
          let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
          pose proof alloc_ceiling_range; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; dj_plain ]
  end end.

(* [comment removed for export] *)
Ltac revive_all_fs MUL WML AOK slim :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive_fs H MUL WML AOK slim | fail 100 "cannot revive" H ] end.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzDState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecCutF DecTacF DecTacFR.
Ltac dpureF_solve DP ::=
  eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); dmodel_cbn;
  [ (* [comment removed for export] *) first [ exact (dpureF_jwf _ _ _ _ _ _ DP)
                      | pose proof (dpureF_jwf _ _ _ _ _ _ DP) as X__; unfold jk_wf in *;
                        cbn [jk_set_t jk_set_s j_p1 j_p2 j_p3 j_s1 j_s2 j_q1 j_q2] in *; decompose [and] X__; clear X__;
                        repeat split; try assumption;
                        cbn [cells_bytes cbytes app]; rewrite ?length_app, ?length_le4, ?length_le8; first [reflexivity | ulia] ]
  | (* [comment removed for export] *) first [ exact (dpureF_static _ _ _ _ _ _ DP)
                          | pose proof (dpureF_static _ _ _ _ _ _ DP) as X__; unfold jk_static in *;
                            cbn [jk_set_t jk_set_s j_q1 j_q2 j_tol j_toh j_bzalloc j_bzfree j_opaque] in *; exact X__ ]
  | first [reflexivity | ulia] | first [reflexivity | ulia] | first [reflexivity | ulia]
  | first [reflexivity | ulia]
  | (* [comment removed for export] *) first [ exact (dpureF_in _ _ _ _ _ _ DP) | assumption | eapply (in_rel_tail _ _ _ _ _ (dpureF_in _ _ _ _ _ _ DP)); reflexivity | idtac ]
  | (* [comment removed for export] *) first [ cbn [length s_in]; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | apply u32_range | apply u32_range' | let X := fresh "X_" in pose proof (dpureF_bb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_bl _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "CR_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; cbn [length s_in] in *; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_snb _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_snb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_nbu _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_nbu _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "RP_" in pose proof (dpureF_rep _ _ _ _ _ _ DP) as X;
            unfold drep in X |- *; dmodel_cbn_in X; hyp_chk X; dmodel_cbn;
            first [ exact X
                  | (* [comment removed for export] *)
                    decompose [and] X; repeat match goal with |- _ /\ _ => split end; try assumption;
                    first [ apply u32_range | apply u32_range' | ulia
                          | (* [comment removed for export] *)
                            let i := fresh "i" in
                            intros i; rewrite ?zget_zset; repeat (destruct (Z.eqb i _));
                            first [ ulia | match goal with Hb : (forall j : Z, _) |- _ => solve [ apply Hb ] end ] ] ]
          | idtac ] ].
