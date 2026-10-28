(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import GbKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpMem BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section GbKitF.
  Variables (fr : Z) (A : act14).
  Hypothesis AOK : act_ok fr A.
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Section Close.
    Variable I : dimg.
    Hypothesis IOK : di_in_img I.
    Let segs := di_segs I.

    (* [comment removed for export] *)
    Lemma gbF_dmem_close : forall m m' J d s J' d' s',
      dmem I cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      munch [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z m m' -> wmono segs m m' ->
      rw_cells segs m' S (HEAD_CELLS (hd_of cx J' d')) ->
      rw_cells segs m' (b_strm cx) (STRM_CELLS (bs_of cx J' s')) ->
      d_nused d' = d_nused d -> d_cftab d' = d_cftab d -> mid_of cx d' = mid_of cx d ->
      j_s1 J' = j_s1 J -> sv_nblock (d_sv d') = sv_nblock (d_sv d) -> j_s2 J' = j_s2 J ->
      r_of d' = r_of d -> blk_of cx d' = blk_of cx d ->
      dmem I cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J' d' s').
    Proof.
      intros m m' J d s J' d' s' DM DP MUL WML HD' STRM' E1 E2 E3 E4 E5 E6 E7 E8.
      pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
      pose proof (act_img_s _ _ AOK) as IMGs. pose proof (act_sep_s_src _ _ AOK) as SEPsrc.
      unfold di_in_img in IOK.
      unfold dmem, dvF in DM |- *. cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in *.
      rewrite E1, E2, E3, E4, E5, E6, E7, E8.
      cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).
      pose proof rnums_words_length as RNL.
      split; [exact HD'|].
      split. { eapply rw_cells_transport; [exact NBU|exact MUL|exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply u32arr_transport; [exact CF|exact MUL|exact WML|]. cbn [disjoint_from]. rewrite zw32_length by lia. lia. }
      split. { eapply rw_cells_transport; [exact MIDc|exact MUL|exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply rw_cells_transport; [exact SAV|exact MUL|exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply drest_transport; [exact DR|exact MUL|exact WML| | | ]; cbn [disjoint_from]; lia. }
      split; [exact STRM'|].
      split. { eapply blk_at_transport; [exact BLK|exact MUL|exact WML|].
               intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
               [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
               | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
               | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
               pose proof (alin_core _ _ AOK);
               try (pose proof (alin_tt _ _ AOK E)); try (pose proof (alin_ll _ _ AOK E));
               cbn [disjoint_from]; lia. }
      split. { eapply bytes_at_transport; [exact PAY|exact MUL|]. cbn [disjoint_from]. lia. }
      split. { eapply rw_cells_transport; [exact GOT|exact MUL|exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply rw_cells_transport; [exact SEV|exact MUL|exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      eapply u32arr_transport; [exact RN|exact MUL|exact WML|]. cbn [disjoint_from]. lia.
    Qed.
  End Close.
End GbKitF.
End ACeilS1.
