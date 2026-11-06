(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Printf_mlib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3 Require Import Printf_sn2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import FX_lib F_memset F_memcpy F_fwritex F_printf_iface.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import R_m2s I_consts F_achk F_fwritex_fit F_fwritex_sn F_pkit F_printf_snsink.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import F_sn_write2 F_fwritex_sn2.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Open Scope Z_scope.
Open Scope mspec_scope.

Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_recast2 : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_CB_len : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

Lemma rw_CB_split : forall m A n (x y : list byte), rw_cells asegs m A [CB n (x ++ y)] ->
  rw_cells asegs m A [CB (length x) x] /\ rw_cells asegs m (A + Z.of_nat (length x)) [CB (length y) y].
Proof.
  intros m A n x y H.
  assert (H' : rw_cells asegs m A ([CB (length x) x] ++ [CB (length y) y])).
  { eapply rw_cells_recast2; [exact H | cbn; repeat split | cbn [app cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]. }
  apply (proj1 (rw_cells_app asegs _ _ _ _)) in H'. cbn [cells_size csize] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.

Lemma rw_CB_join : forall m A (x y : list byte) n, rw_cells asegs m A [CB (length x) x] -> rw_cells asegs m (A + Z.of_nat (length x)) [CB (length y) y] ->
  n = (length x + length y)%nat -> rw_cells asegs m A [CB n (x ++ y)].
Proof.
  intros m A x y n H1 H2 ->.
  assert (H' : rw_cells asegs m A ([CB (length x) x] ++ [CB (length y) y])).
  { apply (proj2 (rw_cells_app asegs _ _ _ _)). cbn [cells_size csize]. rewrite Nat.add_0_r. split; assumption. }
  eapply rw_cells_recast2; [exact H' | cbn; rewrite length_app; repeat split | cbn [app cells_bytes cbytes]; rewrite !app_nil_r; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_nth1 : forall m A pre c post, rw_cells asegs m A (pre ++ c :: post) -> rw_cells asegs m (A + Z.of_nat (cells_size pre)) [c].
Proof.
  intros m A pre c post H. apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. destruct H as [_ H].
  change (c :: post) with ([c] ++ post) in H. apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Lemma rw_cells_replace2 : forall W m m' A p1 c1 c1' p2 c2 c2' p3,
  rw_cells asegs m A (p1 ++ c1 :: p2 ++ c2 :: p3) -> munch W m m' -> wmono asegs m m' ->
  csize c1' = csize c1 -> csize c2' = csize c2 ->
  disjoint_from W A (Z.of_nat (cells_size p1)) ->
  disjoint_from W (A + Z.of_nat (cells_size p1) + Z.of_nat (csize c1)) (Z.of_nat (cells_size p2)) ->
  disjoint_from W (A + Z.of_nat (cells_size p1) + Z.of_nat (csize c1) + Z.of_nat (cells_size p2) + Z.of_nat (csize c2)) (Z.of_nat (cells_size p3)) ->
  rw_cells asegs m' (A + Z.of_nat (cells_size p1)) [c1'] ->
  rw_cells asegs m' (A + Z.of_nat (cells_size p1) + Z.of_nat (csize c1) + Z.of_nat (cells_size p2)) [c2'] ->
  rw_cells asegs m' A (p1 ++ c1' :: p2 ++ c2' :: p3).
Proof.
  intros W m m' A p1 c1 c1' p2 c2 c2' p3 H MU WM E1 E2 D1 D2 D3 N1 N2.
  apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. destruct H as [H1 H].
  change (c1 :: p2 ++ c2 :: p3) with ([c1] ++ p2 ++ c2 :: p3) in H.
  apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. destruct H as [_ H]. cbn [cells_size csize] in H. rewrite Nat.add_0_r in H.
  apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. destruct H as [H2 H].
  change (c2 :: p3) with ([c2] ++ p3) in H.
  apply (proj1 (rw_cells_app asegs _ _ _ _)) in H. destruct H as [_ H3]. cbn [cells_size csize] in H3. rewrite Nat.add_0_r in H3.
  apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact (rw_cells_transport asegs W m m' _ _ H1 MU WM D1)|].
  change (c1' :: p2 ++ c2' :: p3) with ([c1'] ++ p2 ++ c2' :: p3).
  apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact N1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, E1.
  apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact (rw_cells_transport asegs W m m' _ _ H2 MU WM D2)|].
  change (c2' :: p3) with ([c2'] ++ p3).
  apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact N2|]. cbn [cells_size csize]. rewrite Nat.add_0_r, E2.
  exact (rw_cells_transport asegs W m m' _ _ H3 MU WM D3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sn_mid (B : Z) (mode : word) : list cell :=
  [C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 0xc2f8c); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
   C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 4294967295)].
Definition sn_j2 (B : Z) (mode : word) : list byte := cells_bytes (sn_mid B mode).
(* [comment removed for export] *)
Definition sn_rest (CK : Z) : list cell :=
  [C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Lemma sn_mid_wf : forall B mode, cells_wf (sn_mid B mode).
Proof. intros. cbn. repeat split. Qed.

(* [comment removed for export] *)
Lemma snfile_open : forall m Fp fl0 j1 WEND WPOS B mode lbfw,
  rw_cells asegs m Fp (FILE_cells fl0 j1 WEND WPOS (sn_j2 B mode) lbfw) ->
  rw_cells asegs m Fp ([CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS)] ++ sn_mid B mode ++ [C4 lbfw]).
Proof.
  intros m Fp fl0 j1 WEND WPOS B mode lbfw H.
  exact (rw_cells_unmerge m Fp [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS)] (sn_mid B mode) [C4 lbfw] H (sn_mid_wf B mode)).
Qed.
Lemma snfile_close : forall m Fp fl0 j1 WEND WPOS B mode lbfw,
  rw_cells asegs m Fp ([CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS)] ++ sn_mid B mode ++ [C4 lbfw]) ->
  rw_cells asegs m Fp (FILE_cells fl0 j1 WEND WPOS (sn_j2 B mode) lbfw).
Proof.
  intros m Fp fl0 j1 WEND WPOS B mode lbfw H.
  exact (rw_cells_merge asegs m Fp [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS)] (sn_mid B mode) [C4 lbfw] H).
Qed.

Section Sn2Sink.
  (* [comment removed for export] *)
  Variables (Fp : Z) (fl0 : byte) (j1 : list byte) (mode lbfw : word) (B TOP CK D n : Z) (dn : nat) (cap : Z).

  Definition SINK_sn2 (m : mem) (st : sn2) : Prop :=
    exists (junk jd : list byte),
      wfile m Fp fl0 j1 (sn_j2 B mode) lbfw B (zb (snd st)) junk
      /\ rw_cells asegs m (Fp + 148) (sn_rest CK)
      /\ zlength (snd st) + zlength junk = SN_CAP
      /\ rw_cells asegs m CK [C8 (Z_to_bv 64 (D + zlength (fst st))); C8 (Z_to_bv 64 (n - zlength (fst st)))]
      /\ rw_cells asegs m D [CB dn (zb (fst st) ++ jd)]
      /\ zlength (fst st) + zlength (snd st) <= cap
      /\ (cap <= n /\ n < 2^63 /\ cap < Z.of_nat dn)
      (* [comment removed for export] *)
      /\ (TOP <= B /\ B + SN_CAP <= Fp /\ Fp + 232 <= CK /\ CK + 16 < 2^63)
      /\ (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D) /\ GLOBALS_TOP <= D.

  Definition sn2_SR : list (Z * Z) := SR Fp B 80 CK 16 D (Z.of_nat dn).
End Sn2Sink.

(* [comment removed for export] *)
Ltac cell_of FO k off H :=
  lazymatch type of FO with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some ?c =>
      assert (H : rw_cells asegs m (A + off) [c])
        by (replace (A + off) with (A + Z.of_nat (cells_size pre)) by (cbn [cells_size csize Nat.add]; lia); exact (rw_cells_nth1 m A pre c post FO))
    end end.

Section Sn2Proofs.
  Variables (Fp : Z) (fl0 : byte) (j1 : list byte) (mode lbfw : word) (B TOP CK D n : Z) (dn : nat) (cap : Z).
  Let SINK := SINK_sn2 Fp fl0 j1 mode lbfw B TOP CK D n dn cap.
  Hypothesis RIP : rip_stmt.

  Lemma sn2_sink_frame : sink_frame_stmt Fp B 80 CK 16 D (Z.of_nat dn) SINK.
  Proof.
    unfold sink_frame_stmt. intros W m m' [d o] (junk & jd & WF & FR & LEN & CKC & DST & CAP & CAPS & LAY & DSH & DGL) MU WM D1 D2.
    cbn [fst snd] in *. exists junk, jd. cbn [fst snd].
    pose proof (Forall_impl _ (fun _ H => proj1 H) D2) as D2b.
    pose proof (Forall_impl _ (fun _ H => proj1 (proj2 H)) D2) as D2c.
    pose proof (Forall_impl _ (fun _ H => proj2 (proj2 H)) D2) as D2d. cbv beta in D2b, D2c, D2d.
    pose proof (rw_CB_len _ _ _ _ DST) as LD.
    split; [|split; [|split; [exact LEN | split; [|split; [|split; [exact CAP | split; [exact CAPS | split; [exact LAY | split; assumption]]]]]]]].
    - destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
      pose proof (zb_length o) as LZ. unfold zlength, SN_CAP in LEN.
      split; [|split; [|repeat split; assumption]].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size FILE_cells csize Nat.add]; lia | cbn [cells_size FILE_cells csize Nat.add]; lia].
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D2b | lia | cbn [cells_size csize Nat.add]; rewrite LZ; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size sn_rest csize Nat.add]; lia | cbn [cells_size sn_rest csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact CKC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2c | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact DST | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2d | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma sn2_sink_flags : sink_flags_stmt Fp SINK.
  Proof.
    unfold sink_flags_stmt. intros m st (junk & jd & (FC & BUF & FL & _) & _).
    exists fl0. split; [|exact FL].
    apply (proj1 (rw_cells_app asegs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  (* [comment removed for export] *)
  Lemma sn2_out : out_stmt Fp B 80 CK 16 D (Z.of_nat dn) SINK (TOPOK_sn TOP) (OUT_sn2b cap).
  Proof using RIP.
    unfold out_stmt. intros until canary. intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 D5 HSH IC CHS [CHB CHD].
    destruct st as [d o].
    destruct HS as (junk & jd & WF & FR & LEN & CKC & DST & CAP & (CAPn & N63 & CAPd) & (L1 & L2 & L3 & L4) & DSH & DGL).
    cbn [fst snd] in *.
    destruct D2 as (D2b & D2c & D2d). destruct D5 as (D5b & D5c & D5d).
    unfold TOPOK_sn in TQ. unfold OUT_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZb. pose proof (zb_length d) as LZd. rewrite LZo in *. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LZb in SB.
    pose proof (rw_CB_len _ _ _ _ DST) as LD. rewrite length_app, LZd in LD.
    pose proof (chkr_bound _ _ _ CHS) as (CS0 & CS1). unfold kHighMemEnd in CS1.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
    unfold OUT_sn2b. apply implM_get_l. cbv beta iota. unfold zlength, PG.F_printf_iface.SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length d) + Z.of_nat (length o) + Z.of_nat (length bs)) cap) as [INCAP|NOCAP]; [|apply implM_unr].
    destruct (Z.leb_spec0 (Z.of_nat (length o) + Z.of_nat (length bs)) 80) as [FIT|NOFIT].
    - (* [comment removed for export] *)
      apply implM_put.
      eapply evt_mono.
      { eapply (fwritex_spec_A RIP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 (sn_j2 B mode) lbfw B (zb o) junk (zb bs) lo);
          rewrite ?EFp, ?LZo, ?LZb.
        - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST. - lia. - exact HSH. - lia.
        - exact MI.
        - lia. - lia. - lia. - lia. - lia. - lia.
        - exact CHS. - apply (chkr_sub m B 80 _ _ CHB); lia. - exact IC. }
      cbv beta. intros ms' P. unfold fwritex_postA in P. rewrite ?EFp, ?LZo, ?LZb in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
      unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
      split; [reflexivity|].
      split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
      split; [exact WM|]. split; [exact MI'|].
      split; [exact ST'|].
      split. { exists (skipn (length bs) junk), jd. cbn [fst snd]. split; [rewrite zb_app; exact WF2|].
               split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from cells_size sn_rest csize Nat.add]; lia]. }
               split. { unfold zlength, SN_CAP. rewrite length_app, length_skipn. lia. }
               split. { eapply rw_cells_transport; [exact CKC | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
               split. { eapply rw_cells_transport; [exact DST | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
               split. { unfold zlength. rewrite length_app. lia. }
               unfold SN_CAP, GLOBALS_TOP. repeat split; assumption. }
      split. { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
               - eapply ro_cells_transport; [exact S1 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
               - eapply ro_cells_transport; [exact S2 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      exact SRC'.
    - (* [comment removed for export] *)
      apply implM_put.
      pose proof (snfile_open _ _ _ _ _ _ _ _ _ FC) as FO. cbn [app sn_mid] in FO.
      cell_of FO 2%nat 32 F32. cell_of FO 3%nat 40 F40. cell_of FO 5%nat 56 F56. cell_of FO 7%nat 72 F72. cell_of FO 9%nat 88 F88.
      pose proof FR as FR'. unfold sn_rest in FR'. cell_of FR' 1%nat 4 F152. replace (Fp + 148 + 4) with (Fp + 152) in F152 by lia. clear FR'.
      destruct (rw_CB_split _ _ _ _ _ DST) as [DSTa DSTb]. rewrite LZd in DSTa, DSTb.
      pose proof (rw_cells_bytes_at' _ _ _ _ BUF) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
      apply bytes_at_app in SRCB. destruct SRCB as [SRCB _].
      try rewrite LZo in F32, F40.
      eapply evt_mono.
      { eapply (fwritex_over_spec RIP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  Fp CK (D + Z.of_nat (length d)) (n - Z.of_nat (length d)) B B (bv_unsigned a0) (Z.of_nat (length junk)) o bs (length jd) jd lo);
          unfold zlength.
        - symmetry. apply Z_to_bv_bv_unsigned. - exact Ha1. - exact Ha2.
        - exact F32. - exact F40. - exact F56. - exact F72. - exact F88. - exact F152. - exact CKC.
        - exact SRCB. - exact SRC. - exact DSTb. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia.
        - exact ST. - lia. - exact HSH. - lia. - exact MI.
        - apply (chkr_sub m B 80 _ _ CHB); lia. - exact CHS. - apply (chkr_sub m D (Z.of_nat dn) _ _ (CHD ltac:(lia))); lia. - exact IC.
        - lia. - unfold GLOBALS_TOP. lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. }
      cbv beta. intros ms' P. unfold sn_write_gen_post in P. unfold zlength in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & CK' & DST' & F40' & F56' & SRCB' & SRC').
      unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
      split; [reflexivity|].
      split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
      split; [exact WM|]. split; [exact MI'|].
      split; [exact ST'|].
      split.
      { exists (zb o ++ junk), (Z_to_bv 8 0 :: skipn (S (length o + length bs)) jd). cbn [fst snd].
        split.
        { (* [comment removed for export] *)
          unfold wfile. cbn [zb map length Z.of_nat]. rewrite length_app, LZo, Nat2Z.inj_add, !Z.add_0_r.
          split.
          { apply snfile_close. cbn [app sn_mid].
            replace (B + (Z.of_nat (length o) + Z.of_nat (length junk))) with (B + Z.of_nat (length o) + Z.of_nat (length junk)) by lia.
            refine (rw_cells_replace2 _ m m' Fp [CB 1 [fl0]; CB 31 j1; C8 _] (C8 _) (C8 (Z_to_bv 64 B)) [C8 z64] (C8 (Z_to_bv 64 B)) (C8 (Z_to_bv 64 B)) _ FO MU WM eq_refl eq_refl _ _ _ _ _);
              cbn [disjoint_from cells_size csize Nat.add]; first [ lia | idtac ].
            - replace (Fp + Z.of_nat 40) with (Fp + 40) by lia. exact F40'.
            - replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8) with (Fp + 56) by lia. exact F56'. }
          split.
          { pose proof (rw_cells_transport asegs _ m m' _ _ BUF MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as BUF'.
            eapply rw_cells_recast2; [exact BUF' | cbn; rewrite length_app; repeat split; lia | cbn [app cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]. }
          repeat split; first [assumption | lia]. }
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from cells_size sn_rest csize Nat.add]; lia]. }
        split. { unfold zlength, SN_CAP. cbn [length Z.of_nat]. rewrite length_app, LZo. lia. }
        split. { unfold zlength. rewrite !length_app.
                 replace (D + Z.of_nat (length d + (length o + length bs))) with (D + Z.of_nat (length d) + Z.of_nat (length o) + Z.of_nat (length bs)) by lia.
                 replace (n - Z.of_nat (length d + (length o + length bs))) with (n - Z.of_nat (length d) - Z.of_nat (length o) - Z.of_nat (length bs)) by lia.
                 exact CK'. }
        split. { pose proof (rw_cells_transport asegs _ m m' _ _ DSTa MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as DSTa'.
                 rewrite <- LZd in DSTa'.
                 pose proof (rw_cells_bound _ _ _ _ DST') as DB'.
                 rewrite !zb_app, <- !app_assoc.
                 eapply (rw_CB_join m' D (zb d) _ dn DSTa'); [rewrite LZd | rewrite LZd].
                 - match type of DST' with rw_cells _ _ _ [CB _ ?l] => replace (length jd) with (length l) in DST' by (exact (rw_CB_len _ _ _ _ DST')) end. exact DST'.
                 - pose proof (rw_CB_len _ _ _ _ DST') as LJ'. lia. }
        split. { unfold zlength. cbn [length Z.of_nat]. rewrite !length_app. lia. }
        unfold SN_CAP, GLOBALS_TOP. repeat split; assumption. }
      split. { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
               - eapply ro_cells_transport; [exact S1 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia].
               - eapply ro_cells_transport; [exact S2 | exact MU | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      exact SRC'.
  Qed.

End Sn2Proofs.
