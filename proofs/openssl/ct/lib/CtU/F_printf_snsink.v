(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Printf_lib F_memset F_memcpy F_fwritex F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_func : forall m a (bs1 bs2 : list byte), bytes_at ctusegs m a bs1 -> bytes_at ctusegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- H1 by exact Hi. rewrite <- H2 by lia. reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
Lemma C8_func : forall m a (v w : word), rw_cells ctusegs m a [C8 v] -> rw_cells ctusegs m a [C8 w] -> v = w.
Proof.
  intros m a v w [[_ H1] _] [[_ H2] _]. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  pose proof (bytes_at_func _ _ _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Section SnProofs.
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

  Lemma sn_sink_frame : sink_frame_stmt Fp B 80 SINK.
  Proof.
    unfold sink_frame_stmt. intros W m m' o (junk & WF & FR & FRL & LEN & SEPB & T1 & T2) MU WM D1 D2.
    exists junk. split; [|split; [|split; [exact FRL | split; [exact LEN | split; [exact SEPB | split; assumption]]]]].
    - destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
      pose proof (zb_length o) as LZ. unfold zlength, SN_CAP in LEN.
      split; [|split; [|repeat split; assumption]].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size FILE_cells csize Nat.add]; lia | cbn [cells_size FILE_cells csize Nat.add]; lia].
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; rewrite LZ; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | lia | lia].
  Qed.

  Lemma sn_sink_flags : sink_flags_stmt Fp SINK.
  Proof.
    unfold sink_flags_stmt. intros m o (junk & (FC & BUF & FL & _) & _).
    exists fl0. split; [|exact FL].
    apply (proj1 (rw_cells_app ctusegs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma sn_topok : topok_stmt (TOPOK_sn TOP).
  Proof. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Lemma sn_out : out_stmt Fp B 80 SINK (TOPOK_sn TOP) OUT_sn.
  Proof.
    unfold out_stmt. intros until canary. intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 D5. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold OUT_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZb. rewrite LZo in *. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LZb in SB.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
    unfold OUT_sn. apply implM_get_l. unfold zlength, SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length o) + Z.of_nat (length bs)) 80) as [FIT|NOFIT]; [|apply implM_unr].
    apply implM_put.
    destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono.
    { eapply (fwritex_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 j2 lbfw B (zb o) junk (zb bs));
        rewrite ?EFp, ?LZo, ?LZb.
      - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST2. - exact MI.
      - lia. - lia. - lia. - lia. - lia. - lia. }
    cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp, ?LZo, ?LZb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
    unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length bs) junk). split; [rewrite zb_app; exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_app, length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
    split. { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
             - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
             - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    exact SRC'.
  Qed.

End SnProofs.
