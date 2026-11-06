(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpMem BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition di_in_imgA (ihi : Z) (I : dimg) : Prop :=
  (65536 <= di_got I /\ di_got I + 40 <= ihi /\ 65536 <= di_stderrp I /\ di_stderrp I + 8 <= ihi /\
   65536 <= di_rnums I /\ di_rnums I + 2048 <= ihi)%Z.
Definition di_in_imgA_b (ihi : Z) (I : dimg) : bool :=
  ((65536 <=? di_got I) && (di_got I + 40 <=? ihi) && (65536 <=? di_stderrp I) && (di_stderrp I + 8 <=? ihi) &&
   (65536 <=? di_rnums I) && (di_rnums I + 2048 <=? ihi))%bool%Z.
Lemma di_in_imgA_ok : forall ihi I, di_in_imgA_b ihi I = true -> di_in_imgA ihi I.
Proof.
  intros ihi I H. unfold di_in_imgA_b in H. rewrite !Bool.andb_true_iff in H. rewrite !Z.leb_le in H. unfold di_in_imgA. tauto.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section GbKitB.
  Variables (ihi : Z) (A : act14).
  Hypothesis AOK : act_ok ihi A.
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Section Close.
    Variable I : dimg.
    Hypothesis IOK : di_in_imgA ihi I.
    Let segs := di_segs I.

    (* [comment removed for export] *)
    Lemma gbF_dmem_close : forall m m' J d s J' d' s',
      dmem I cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      munch [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z m m' -> wmono segs m m' ->
      rw_cells segs m' S (HEAD_CELLS (hd_of cx J' d')) ->
      rw_cells segs m' (b_strm cx) (STRM_CELLS (bs_of cx J' s')) ->
      d_nused d' = d_nused d -> d_cftab d' = d_cftab d -> mid_of cx d' = mid_of cx d ->
      j_s1 J' = j_s1 J -> sv_nblock (d_sv d') = sv_nblock (d_sv d) -> j_s2 J' = j_s2 J ->
      r_of d' = r_of d -> blk_of cx d' = blk_of cx d ->
      dmem I cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J' d' s').
    Proof.
      intros m m' J d s J' d' s' DM DP MUL WML HD' STRM' E1 E2 E3 E4 E5 E6 E7 E8.
      pose proof (alin_core _ _ AOK) as LIN.
      pose proof (act_img_sb _ _ AOK) as (IMGs & IMGt & SEPst & IHR). pose proof (act_sep_src _ _ AOK) as (SEPsrc & SEPtsrc).
      unfold di_in_imgA in IOK.
      unfold dmem, dvF in DM |- *. cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in *.
      rewrite E1, E2, E3, E4, E5, E6, E7, E8.
      cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).
      pose proof rnums_words_length as RNL.
      split; [exact HD'|].
      split. { eapply rw_cells_transport; [exact NBU|exact MUL|exact WML|]. clear IMGs IMGt SEPsrc SEPtsrc. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply u32arr_transport; [exact CF|exact MUL|exact WML|]. clear IMGs IMGt SEPsrc SEPtsrc. cbn [disjoint_from]. rewrite zw32_length by lia. lia. }
      split. { eapply rw_cells_transport; [exact MIDc|exact MUL|exact WML|]. clear IMGs IMGt SEPsrc SEPtsrc. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply rw_cells_transport; [exact SAV|exact MUL|exact WML|]. clear IMGs IMGt SEPsrc SEPtsrc. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply drest_transport; [exact DR|exact MUL|exact WML| | | ]; clear IMGs IMGt SEPsrc SEPtsrc; cbn [disjoint_from]; lia. }
      split; [exact STRM'|].
      split. { eapply blk_at_transport; [exact BLK|exact MUL|exact WML|]. clear IMGs IMGt SEPsrc SEPtsrc SEPst.
               intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
               [ cps_pose (act_tt_s _ _ AOK E) as (? & ? & ?)
               | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ? & ? & ?)
               | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ? & ? & ?) ];
               cbn [disjoint_from]; lia. }
      split. { eapply bytes_at_transport; [exact PAY|exact MUL|]. clear IMGs IMGt SEPst. cbn [disjoint_from]. lia. }
      split. { eapply ro_cells_transport; [exact GOT|exact MUL|]. clear SEPsrc SEPtsrc SEPst. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      split. { eapply ro_cells_transport; [exact SEV|exact MUL|]. clear SEPsrc SEPtsrc SEPst. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      eapply u32arr_transport; [exact RN|exact MUL|exact WML|]. clear SEPsrc SEPtsrc SEPst. cbn [disjoint_from]. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma gbF_payload_tr : forall m m' J d s,
      dmem I cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      munch [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z m m' ->
      bytes_at segs m' (b_src cx) (a_payload A).
    Proof.
      intros m m' J d s DM MUL.
      pose proof (alin_core _ _ AOK) as LIN.
      pose proof (act_sep_src _ _ AOK) as (SEPsrc & SEPtsrc).
      cps_destruct DM as (_ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
      eapply bytes_at_transport; [exact PAY|exact MUL|]. cbn [disjoint_from]. lia.
    Qed.
  End Close.
End GbKitB.
End ACeilS1.
