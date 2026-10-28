(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut DecTac DecTacS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac revive_sm_old H AOK SM0 MUL WML :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?Ad ?cs =>
      apply (rw_cells_transport segs W me m' Ad cs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; dj_all AOK SM0 ]
  | u32arr ?segs me ?Ad ?ws =>
      apply (u32arr_transport segs W me m' Ad ws) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_all AOK SM0 ]
  | u8arr ?segs me ?Ad ?bs =>
      apply (u8arr_transport segs W me m' Ad bs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_all AOK SM0 ]
  | bytes_at ?segs me ?Ad ?bs =>
      apply (bytes_at_transport segs W me m' Ad bs) in H; [ | exact MUL | cbn [disjoint_from]; simpl_sizes; dj_all AOK SM0 ]
  | drest_at ?segs me ?Sd ?r =>
      apply (drest_transport segs W me m' Sd r) in H;
      [ | exact MUL | exact WML | cbn [disjoint_from]; dj_all AOK SM0 | cbn [disjoint_from]; dj_all AOK SM0 | cbn [disjoint_from]; dj_all AOK SM0 ]
  | blk_at ?segs me ?cxx ?k =>
      apply (blk_at_transport segs W me m' cxx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          first [ exfalso; clear -E SM0; congruence | cbn [disjoint_from]; dj_all AOK SM0 ]; try clear E ]
  end end.

(* [comment removed for export] *)
Ltac dj_all_fast_c AOK SM0 :=
  lazymatch goal with
  | |- _ /\ _ => split; [ first [ dj_sb_conj | dj_conj AOK SM0 ] | dj_all_fast_c AOK SM0 ]
  | |- True => exact I
  | |- _ => first [ dj_sb_conj | dj_conj AOK SM0 ]
  end.
(* [comment removed for export] *)
Ltac dj_sm_facts AOK SM0 :=
  pose proof (act_img_s _ _ AOK); pose proof (act_sep_s_src _ _ AOK); pose proof (act_sep_s_dst _ _ AOK);
  first [ (let X := fresh "DJX" in pose proof (act_ll _ _ AOK SM0) as X;
           cps_destruct X as (_ & ? & ? & ? & ? & ? & ? & ?);
           let Y := fresh "DJY" in pose proof (act_img_ll _ _ AOK SM0) as Y; destruct Y as (? & ?))
        | (let X := fresh "DJX" in pose proof (act_tt _ _ AOK SM0) as X; cps_destruct X as (_ & ? & ? & ?);
           pose proof (act_img_tt _ _ AOK SM0))
        | idtac ].
Ltac dj_seplin_sm AOK SM0 :=
  lazymatch goal with |- context [@length _ _] => DecFast.dj_len_norm; DecFast.dj_len_db | _ => idtac end;
  DecFast.dj_blk_unbox;
  dj_sm_facts AOK SM0;
  SepLinT.sl_tslia ltac:(idtac; lia).
Ltac dj_all_fast AOK SM0 := first [ solve [ dj_seplin_sm AOK SM0 ] | dj_all_fast_c AOK SM0 ].
Ltac revive_sm_new H AOK SM0 MUL WML :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?Ad ?cs =>
      let n := dj_cells_n cs in
      dj_get (disjoint_from W Ad n) ltac:(cbn [disjoint_from]; first [ solve [ dj_seplin_sm AOK SM0 ] | simpl_sizes; dj_all_fast_c AOK SM0 ])
        ltac:(fun D => apply (rw_cells_transport segs W me m' Ad cs) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | u32arr ?segs me ?Ad ?ws =>
      dj_get (disjoint_from W Ad (4 * Z.of_nat (length ws))) ltac:(cbn [disjoint_from]; first [ solve [ dj_seplin_sm AOK SM0 ] | simpl_sizes; simpl_arr_sizes_occ; dj_all_fast_c AOK SM0 ])
        ltac:(fun D => apply (u32arr_transport segs W me m' Ad ws) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | u8arr ?segs me ?Ad ?bs =>
      dj_get (disjoint_from W Ad (Z.of_nat (length bs))) ltac:(cbn [disjoint_from]; first [ solve [ dj_seplin_sm AOK SM0 ] | simpl_sizes; simpl_arr_sizes_occ; dj_all_fast_c AOK SM0 ])
        ltac:(fun D => apply (u8arr_transport segs W me m' Ad bs) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | bytes_at ?segs me ?Ad ?bs =>
      dj_get (disjoint_from W Ad (Z.of_nat (length bs))) ltac:(cbn [disjoint_from]; first [ solve [ dj_seplin_sm AOK SM0 ] | simpl_sizes; dj_all_fast_c AOK SM0 ])
        ltac:(fun D => apply (bytes_at_transport segs W me m' Ad bs) in H; [ | exact MUL | exact (dj_cache_elim _ D) ])
  | drest_at ?segs me ?Sd ?r =>
      dj_get (disjoint_from W (Sd + 68) (4 * 256)) ltac:(cbn [disjoint_from]; dj_all_fast AOK SM0) ltac:(fun D1 =>
      dj_get (disjoint_from W (Sd + 2124) 1028) ltac:(cbn [disjoint_from]; dj_all_fast AOK SM0) ltac:(fun D2 =>
      dj_get (disjoint_from W (Sd + 3196) 60840) ltac:(cbn [disjoint_from]; dj_all_fast AOK SM0) ltac:(fun D3 =>
        apply (drest_transport segs W me m' Sd r) in H;
        [ | exact MUL | exact WML | exact (dj_cache_elim _ D1) | exact (dj_cache_elim _ D2) | exact (dj_cache_elim _ D3) ])))
  end end.
Ltac revive_sm_cached H AOK SM0 MUL WML :=
  first [ first [ DecFast.dj_blk_prefill MUL AOK | idtac ]; revive_sm_new H AOK SM0 MUL WML | revive_sm_old H AOK SM0 MUL WML ].

(* [comment removed for export] *)
Ltac revive_all_smL_split AOK SM0 MUL WML LIN DP :=
  lazymatch type of LIN with
  | lin_box _ =>
      clear LIN; lin_clear_atoms;
      let L := fresh "LINs" in let L2 := fresh "LINm" in
      pose proof (act_lin_core _ _ AOK) as L; lin_split_generic L;
      first [ pose proof (act_lin_ll _ _ AOK SM0) as L2 | pose proof (act_lin_tt _ _ AOK SM0) as L2 ]; lin_split_generic L2;
      revive_all_sm AOK SM0 MUL WML;
      lin_clear_atoms; pose proof (act_lin _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split_core LIN
  | _ =>
      clear LIN;
      let L := fresh "LINs" in let L2 := fresh "LINm" in
      pose proof (act_lin_core _ _ AOK) as L;
      first [ pose proof (act_lin_ll _ _ AOK SM0) as L2 | pose proof (act_lin_tt _ _ AOK SM0) as L2 ];
      revive_all_sm AOK SM0 MUL WML;
      clear L L2; pose proof (act_lin _ _ _ AOK DP) as LIN; cbv zeta in LIN
  end.
