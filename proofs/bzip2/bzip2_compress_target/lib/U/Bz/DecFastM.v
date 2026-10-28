(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut DecTacM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac revive_f_old H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; dj_plain ]; clear Y
  | u32arr ?segs me ?A ?ws =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_plain ]; clear Y
  | u8arr ?segs me ?A ?bs =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_plain ]; clear Y
  | bytes_at ?segs me ?A ?bs =>
      let Y := fresh "SEPsrc" in pose proof (act_sep_s_src _ _ AOK) as Y;
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL | cbn [disjoint_from]; simpl_sizes; dj_plain ]; clear Y
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; dj_plain | cbn [disjoint_from]; dj_plain | cbn [disjoint_from]; dj_plain ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
          cbn [disjoint_from]; dj_plain ]
  end end.

Ltac revive_f_fast H MUL WML AOK := first [ revive_new H MUL WML AOK | revive_f_old H MUL WML AOK ].
