(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_printf_snsink.v, with its module paths changed; 444 of its 486 lines of code are new or changed and 129 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require Import G_memcpy G_fwritex G_pad G_fmt_fp_lib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require Import CopyCall G_sn_write G_fwritex_w G_fwritex_room G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.LiaClosure.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.


Lemma zb_len : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app2 : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.

Lemma Forall_disj : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma implM_get_k : forall segs {S B} (k : S -> M S B) s Q ms, implM segs (k s) s Q ms -> implM segs (mbind mget k) s Q ms.
Proof. intros. exact H. Qed.

Lemma rw_cells_unmerge : forall segs m A pre mid post n,
  rw_cells segs m A (pre ++ CB n (cells_bytes mid) :: post) -> cells_wf mid -> n = cells_size mid ->
  rw_cells segs m A (pre ++ mid ++ post).
Proof.
  intros segs m A pre mid post n [[Hwf Hb] Hw] Hm Hn. subst n.
  split; [split|].
  - apply cells_wf_app in Hwf. destruct Hwf as [H1 H23]. cbn [cells_wf] in H23. destruct H23 as [_ H3].
    apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. tauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. exact Hw.
Qed.

Lemma rw_cells_sub : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) -> rw_cells segs m (A + Z.of_nat (cells_size pre)) mid.
Proof.
  intros segs m A pre mid post H. apply (proj1 (rw_cells_app segs m A pre (mid ++ post))) in H.
  destruct H as [_ H]. apply (proj1 (rw_cells_app segs m _ mid post)) in H. tauto.
Qed.

Lemma rw_cells_join : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros. apply (proj2 (rw_cells_app segs m A cs1 cs2)). tauto. Qed.

Lemma rw_cells_hd_bytes : forall segs m A n (l : list byte) cs, rw_cells segs m A (CB n l :: cs) -> bytes_at segs m A l.
Proof.
  intros segs m A n l cs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  apply (proj1 (bytes_at_app _ _ _ _ _)) in Hb. tauto.
Qed.

Lemma split_prefix : forall (a b : list byte) n, length a = n -> firstn n (a ++ b) = a /\ skipn n (a ++ b) = b.
Proof.
  intros a b n <-. split.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
  - rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma snf_dbytes : forall (o1 o2 bs : list Z) (junkd : list byte) (Nn w1n kn : nat) (z : byte),
  w1n = Nat.min (length o1) Nn -> kn = Nat.min (Nn - w1n) (length o2 + length bs) ->
  zb (firstn Nn o1) ++ firstn (Nn - w1n) (zb o2 ++ zb bs) ++ z :: skipn (S kn) (z :: skipn (S w1n) junkd)
  = zb (firstn Nn (o1 ++ o2 ++ bs)) ++ z :: skipn (S (w1n + kn)) junkd.
Proof.
  intros o1 o2 bs junkd Nn w1n kn z E1 E2.
  rewrite (firstn_app Nn o1 (o2 ++ bs)), zb_app2, (zb_firstn (Nn - length o1) (o2 ++ bs)), zb_app2, <- app_assoc. f_equal.
  replace (Nn - length o1)%nat with (Nn - w1n)%nat by lia. f_equal. f_equal.
  cbn [skipn]. rewrite skipn_skipn. f_equal. lia.
Qed.

Section Img.
  Context {IMG : RImg}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
  Context {SPEC_fwritex_room : fwritex_room_stmt copy_ready}.
  Context {SPEC_fwritex_w : fwritex_w_stmt copy_ready}.
  Context {SPEC_sn_write : sn_write_contract copy_ready}.

Definition snf_out_ready (Fp B CK D : Z) (dn : nat) (m : mem) (sp S L : Z) : Prop :=
  forall m' Dst P N,
    munch ((B, B + SNF_CAP) :: sn_write_footprint sp Fp CK D (Z.of_nat dn)) m m' -> wmono img_segs m m' ->
    (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ B <= Dst /\ Dst + N <= B + SNF_CAP) -> 0 <= N ->
    (P = B /\ N <= SNF_CAP \/ P = S /\ N <= L) ->
    copy_ready m' (sp - 64) Dst P N.

Lemma sn_write_ready_weaken : forall m sp f CK cs dn WB pn S sn cs' dn' pn' S' sn',
  sn_write_ready copy_ready m sp f CK cs dn WB pn S sn ->
  cs <= cs' -> cs' + dn' <= cs + dn -> pn' <= pn -> S' = S -> sn' <= sn ->
  sn_write_ready copy_ready m sp f CK cs' dn' WB pn' S' sn'.
Proof.
  intros m sp f CK cs dn WB pn S sn cs' dn' pn' S' sn' READY H1 H2 H3 -> H5 m' D P N MU WM HD HN HEND HS.
  refine (READY m' D P N _ WM _ _ _ _).
  - eapply munch_weaken; [|exact MU]. unfold sub_fp, sn_write_footprint. cbn [outside]. intros x Hx. lia.
  - lia.
  - lia.
  - lia.
  - destruct HS as [[-> HP]|[-> HP]]; [left|right]; (split; [reflexivity|lia]).
Qed.

Lemma snf_ready_room : forall Fp B CK D dn m sp S L nc lb,
  snf_out_ready Fp B CK D dn m sp S L -> 0 <= nc -> 0 <= lb -> nc + lb <= SNF_CAP -> lb <= L ->
  fwritex_room_ready copy_ready m sp Fp (B + nc) S lb.
Proof.
  intros Fp B CK D dn m sp S L nc lb R H1 H2 H3 H4 m' MU WM.
  refine (R m' (B + nc) S lb _ WM _ _ _).
  - eapply munch_weaken; [|exact MU].
    unfold sub_fp, fwritex_room_footprint, sn_write_footprint, SNF_CAP, SN_WRITE_DEPTH, COPY_DEPTH in *.
    cbn [outside]. intros x Hx. lia.
  - right. unfold SNF_CAP in *. lia.
  - lia.
  - right. split; [reflexivity|lia].
Qed.

Lemma snf_ready_snw : forall Fp B CK D dn m sp S L cs dn' pn sn,
  snf_out_ready Fp B CK D dn m sp S L -> D <= cs -> cs + dn' <= D + Z.of_nat dn -> pn <= SNF_CAP -> sn <= L ->
  sn_write_ready copy_ready m sp Fp CK cs dn' B pn S sn.
Proof.
  intros Fp B CK D dn m sp S L cs dn' pn sn R H1 H2 H3 H4 m' D' P N MU WM HD HN HEND HS.
  refine (R m' D' P N _ WM _ _ _).
  - eapply munch_weaken; [|exact MU]. unfold sub_fp, sn_write_footprint. cbn [outside]. intros x Hx. lia.
  - left. lia.
  - lia.
  - destruct HS as [[-> HP]|[-> HP]]; [left|right]; (split; [reflexivity|lia]).
Qed.

Lemma snf_j2_cells : forall jm jr js jt B,
  cells_bytes [CB 8 jm; C8 (Z_to_bv 64 B); CB 8 jr; C8 (Z_to_bv 64 (sym K_SN_WRITE)); CB 8 js; C8 (Z_to_bv 64 B); CB 48 jt]
  = snf_j2 jm jr js jt B.
Proof. intros. cbn [cells_bytes cbytes]. unfold snf_j2. rewrite app_nil_r. reflexivity. Qed.

Lemma snf_file_split : forall m Fp fl0 j1 jm jr js jt lbfw B WE WP,
  length jm = 8%nat -> length jr = 8%nat -> length js = 8%nat -> length jt = 48%nat ->
  rw_cells img_segs m Fp (FILE_cells fl0 j1 WE WP (snf_j2 jm jr js jt B) lbfw) ->
  rw_cells img_segs m Fp [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WE)]
  /\ rw_cells img_segs m (Fp + 40) [C8 (Z_to_bv 64 WP)]
  /\ rw_cells img_segs m (Fp + 48) [CB 8 jm]
  /\ rw_cells img_segs m (Fp + 56) [C8 (Z_to_bv 64 B)]
  /\ rw_cells img_segs m (Fp + 64) [CB 8 jr; C8 (Z_to_bv 64 (sym K_SN_WRITE)); CB 8 js; C8 (Z_to_bv 64 B); CB 48 jt; C4 lbfw]
  /\ rw_cells img_segs m (Fp + 32) [C8 (Z_to_bv 64 WE)]
  /\ rw_cells img_segs m (Fp + 72) [C8 (Z_to_bv 64 (sym K_SN_WRITE))]
  /\ rw_cells img_segs m (Fp + 88) [C8 (Z_to_bv 64 B)].
Proof.
  intros m Fp fl0 j1 jm jr js jt lbfw B WE WP Ljm Ljr Ljs Ljt FC.
  unfold FILE_cells in FC. rewrite <- snf_j2_cells in FC.
  apply (rw_cells_unmerge _ _ _ [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WE); C8 (Z_to_bv 64 WP)] _ [C4 lbfw] 96) in FC;
    [ | cbn; tauto | reflexivity ].
  cbn [app] in FC.
  apply (proj1 (rw_cells_app _ _ _ [_; _; _] _)) in FC. destruct FC as [P1 FC]. cbn [cells_size csize Nat.add] in FC.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in FC. destruct FC as [P2 FC]. cbn [cells_size csize Nat.add] in FC.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in FC. destruct FC as [P3 FC]. cbn [cells_size csize Nat.add] in FC.
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in FC. destruct FC as [P4 P5]. cbn [cells_size csize Nat.add] in P5.
  pose proof (rw_cells_sub _ _ _ [CB 1 [fl0]; CB 31 j1] [C8 (Z_to_bv 64 WE)] [] P1) as Q1.
  pose proof (rw_cells_sub _ _ _ [CB 8 jr] [C8 (Z_to_bv 64 (sym K_SN_WRITE))] [CB 8 js; C8 (Z_to_bv 64 B); CB 48 jt; C4 lbfw] P5) as Q2.
  pose proof (rw_cells_sub _ _ _ [CB 8 jr; C8 (Z_to_bv 64 (sym K_SN_WRITE)); CB 8 js] [C8 (Z_to_bv 64 B)] [CB 48 jt; C4 lbfw] P5) as Q3.
  cbn [cells_size csize Nat.add] in Q1, Q2, Q3.
  replace (Fp + Z.of_nat 40) with (Fp + 40) in P2 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8) with (Fp + 48) in P3 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8) with (Fp + 56) in P4 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (Fp + 64) in P5, Q2, Q3 by lia.
  replace (Fp + Z.of_nat 32) with (Fp + 32) in Q1 by lia.
  replace (Fp + 64 + Z.of_nat 8) with (Fp + 72) in Q2 by lia.
  replace (Fp + 64 + Z.of_nat 24) with (Fp + 88) in Q3 by lia.
  tauto.
Qed.

Lemma snf_file_join : forall m Fp fl0 j1 jm jr js jt lbfw B WE WP,
  length jm = 8%nat -> length jr = 8%nat -> length js = 8%nat -> length jt = 48%nat ->
  rw_cells img_segs m Fp [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WE)] ->
  rw_cells img_segs m (Fp + 40) [C8 (Z_to_bv 64 WP)] ->
  rw_cells img_segs m (Fp + 48) [CB 8 jm] ->
  rw_cells img_segs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells img_segs m (Fp + 64) [CB 8 jr; C8 (Z_to_bv 64 (sym K_SN_WRITE)); CB 8 js; C8 (Z_to_bv 64 B); CB 48 jt; C4 lbfw] ->
  rw_cells img_segs m Fp (FILE_cells fl0 j1 WE WP (snf_j2 jm jr js jt B) lbfw).
Proof.
  intros m Fp fl0 j1 jm jr js jt lbfw B WE WP Ljm Ljr Ljs Ljt P1 P2 P3 P4 P5.
  assert (J : rw_cells img_segs m Fp ([CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WE); C8 (Z_to_bv 64 WP)]
            ++ [CB 8 jm; C8 (Z_to_bv 64 B); CB 8 jr; C8 (Z_to_bv 64 (sym K_SN_WRITE)); CB 8 js; C8 (Z_to_bv 64 B); CB 48 jt]
            ++ [C4 lbfw])).
  { cbn [app].
    apply (rw_cells_join _ _ _ [_; _; _] _); [exact P1|]. cbn [cells_size csize Nat.add].
    replace (Fp + Z.of_nat 40) with (Fp + 40) by lia.
    apply (rw_cells_join _ _ _ [_] _); [exact P2|]. cbn [cells_size csize Nat.add].
    replace (Fp + 40 + Z.of_nat 8) with (Fp + 48) by lia.
    apply (rw_cells_join _ _ _ [_] _); [exact P3|]. cbn [cells_size csize Nat.add].
    replace (Fp + 48 + Z.of_nat 8) with (Fp + 56) by lia.
    apply (rw_cells_join _ _ _ [_] _); [exact P4|]. cbn [cells_size csize Nat.add].
    replace (Fp + 56 + Z.of_nat 8) with (Fp + 64) by lia. exact P5. }
  apply rw_cells_merge in J. rewrite snf_j2_cells in J.
  cbn [cells_size csize Nat.add] in J. unfold FILE_cells. exact J.
Qed.

Section SnfProofs.
  Variables (Fp : Z) (fl0 : byte) (j1 jm jr js jt jx jy : list byte) (lbfw : word)
            (B CK D : Z) (dn : nat) (junkd : list byte) (N TOP OM : Z).

  Ltac dest_snf H :=
    let o1 := fresh "o1" in let o2 := fresh "o2" in let bj := fresh "bj" in
    destruct H as (o1 & o2 & bj & H); cbv zeta in H;
    destruct H as (Eo & Lc & Ljm & Ljr & Ljs & Ljt & Ljx & Ljy & WF & FX & CKC & DC & Ljd & HN & HOM & Ho
                   & SFB & SFC & SBC & SDF & SDB & SDC & SDG1 & SDG2 & T1 & T2 & T3 & P1 & P2 & P3 & P4 & P5 & P6).

  Ltac tr_by MU WM DFL := first
    [ eapply rw_cells_transport; [ eassumption | exact MU | exact WM | ];
      eapply Forall_disj; [ exact DFL | | | ]; cbn [cells_size csize Nat.add FILE_cells length]; rewrite ?zb_len; unfold zlength, SNF_CAP in *; lia ].

  Ltac plia := try unfold SN_WRITE_DEPTH, COPY_DEPTH, SNF_CAP in *; lia0_prune_s; lia.
  Ltac dsolve := first [ plia | match goal with H : _ \/ _ |- _ => destruct H as [H|H]; plia end ].
  Ltac dj := repeat (match goal with |- _ /\ _ => split end); try exact I; dsolve.
  Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
  Ltac mk_tr MU TR :=
    lazymatch type of MU with munch ?W ?m0 ?m1 =>
      assert (TR : forall A cs, rw_cells img_segs m0 A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells img_segs m1 A cs)
        by (intros; eapply rw_cells_transport; eauto)
    end.

  Lemma snf_sink_frame : sink_frame_stmt Fp B SNF_CAP CK 16 D (Z.of_nat dn)
                           (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM).
  Proof.
    unfold sink_frame_stmt. intros W m m' o HS MU WM DF DBB DCK DD.
    dest_snf HS.
    pose proof WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    assert (FC' : rw_cells img_segs m' Fp (FILE_cells fl0 j1 (B + Z.of_nat (length (zb o2)) + Z.of_nat (length bj))
                                            (B + Z.of_nat (length (zb o2))) (snf_j2 jm jr js jt B) lbfw)) by (tr_by MU WM DF).
    assert (BUF' : rw_cells img_segs m' B [CB (length (zb o2)) (zb o2); CB (length bj) bj]) by (tr_by MU WM DBB).
    assert (FX' : rw_cells img_segs m' (Fp + 148) [CB 4 jx; C8 (Z_to_bv 64 CK); CB 72 jy]) by (tr_by MU WM DF).
    assert (CKC' : rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (zlength o1) N)); C8 (Z_to_bv 64 (N - Z.min (zlength o1) N))])
      by (tr_by MU WM DCK).
    assert (DC' : rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o1) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength o1) N))) junkd)])
      by (tr_by MU WM DD).
    exists o1, o2, bj. cbv zeta.
    repeat (match goal with |- _ /\ _ => split end); try first [ assumption | lia ].
    unfold wfile. repeat (match goal with |- _ /\ _ => split end); assumption.
  Qed.

  Lemma snf_sink_flags : sink_flags_stmt Fp (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM).
  Proof.
    unfold sink_flags_stmt. intros m o HS. dest_snf HS.
    destruct WF as (FC & _ & FL & _). exists fl0. split; [|exact FL].
    unfold FILE_cells in FC. apply (proj1 (rw_cells_app img_segs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma snf_flush_a_ok : snf_flush_a_stmt copy_ready Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM.
  Proof.
    unfold snf_flush_a_stmt. intros until o. intros HS -> -> -> ST SPLO STOP SD MI RDY.
    dest_snf HS. subst o.
    pose proof WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    apply snf_file_split in FC; [ | assumption.. ].
    destruct FC as (FA & FWP & FB2 & FWB & FHI & FWE & FWR & FBF).
    pose proof FX as FX1.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FX1. destruct FX1 as [_ FX1]. cbn [cells_size csize Nat.add] in FX1.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FX1. destruct FX1 as [FCK _].
    replace (Fp + 148 + Z.of_nat 4) with (Fp + 152) in FCK by plia.
    pose proof (rw_cells_hd_bytes _ _ _ _ _ _ BUF) as PEND.
    pose proof (zb_len o2) as LZo.
    unfold zlength, SNF_CAP in *.
    rewrite length_app in Ho.
    remember (Z.to_nat (Z.min (Z.of_nat (length o1)) N)) as w1n eqn:Ew1n.
    assert (Hw1n : Z.of_nat w1n = Z.min (Z.of_nat (length o1)) N) by plia.
    assert (Hw1d : (w1n < dn)%nat) by plia.
    assert (LF : length (zb (firstn (Z.to_nat N) o1)) = w1n) by (rewrite zb_len, length_firstn; plia).
    replace dn with (w1n + (dn - w1n))%nat in DC at 1 by plia.
    apply rw_CB_split in DC. destruct DC as [DCa DCb].
    destruct (split_prefix _ (Z_to_bv 8 0 :: skipn (S w1n) junkd) _ LF) as [EF ES].
    rewrite EF in DCa. rewrite ES in DCb.
    assert (Ldst : length (Z_to_bv 8 0 :: skipn (S w1n) junkd) = (dn - w1n)%nat) by (cbn [length]; rewrite length_skipn; plia).
    rewrite <- Ldst in DCb. rewrite Hw1n in DCb.
    eapply evt_mono.
    { eapply (SPEC_sn_write ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                Fp B B CK (D + Z.min (Z.of_nat (length o1)) N) (N - Z.min (Z.of_nat (length o1)) N) (zb o2) []
                (Z_to_bv 8 0 :: skipn (S w1n) junkd));
        [ reflexivity
        | rewrite unsigned_lit by plia; apply bytes_at_nil; plia
        | rewrite unsigned_lit by plia; reflexivity
        | exact FWP | exact FWB | exact FBF | exact FCK | exact CKC | exact PEND
        | plia
        | exact DCb
        | plia
        | unfold sn_k; cbn [length]; rewrite length_skipn, Nat.add_0_r; plia
        | exact ST | plia | exact MI
        | eapply sn_write_ready_weaken; [ exact RDY | plia | plia | plia | rewrite unsigned_lit by plia; reflexivity | cbn [length]; plia ]
        | right; plia | right; plia | destruct SD; [left|right]; plia | right; plia
        | left; rewrite unsigned_lit by plia; cbn [length]; plia
        | destruct SFC; [left|right]; plia | destruct SDF; [left|right]; plia | destruct SDC; [left|right]; plia
        | destruct SDB; [right|left]; plia
        | left; rewrite unsigned_lit by plia; cbn [length]; plia | left; rewrite unsigned_lit by plia; cbn [length]; plia ]. }
    intros ms' P. unfold sn_write_post, snf_flush_a_post, SN_WRITE_DEPTH, COPY_DEPTH in *.
    destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & E & MU & WM & MI' & ST' & WP' & WB' & CK' & DST').
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m', (zb o2 ++ bj).
    unfold zlength.
    rewrite Ldst in MU.
    mk_tr MU TR.
    split; [exact E|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. clear_disj. lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [rewrite length_app, zb_len; plia|].
    split.
    { unfold wfile. split; [|split; [|split; [exact FL|split; [exact LBF|split; [plia|split; rewrite ?length_app, ?zb_len; cbn [length]; dj]]]]].
      - replace (B + Z.of_nat (length (@nil byte)) + Z.of_nat (length (zb o2 ++ bj)))
          with (B + Z.of_nat (length (zb o2)) + Z.of_nat (length bj)) by (rewrite length_app; cbn [length]; plia).
        replace (B + Z.of_nat (length (@nil byte))) with B by (cbn [length]; plia).
        apply snf_file_join; try assumption.
        + apply TR; [exact FA|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
        + apply TR; [exact FB2|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
        + apply TR; [exact FHI|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
      - assert (BUF' : rw_cells img_segs m' B [CB (length (zb o2)) (zb o2); CB (length bj) bj]).
        { apply TR; [exact BUF|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
        assert (J : rw_cells img_segs m' B ([] ++ [CB (length (zb o2)) (zb o2); CB (length bj) bj] ++ [])) by (cbn [app]; exact BUF').
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite Nat.add_0_r, app_nil_r in J.
        apply (rw_cells_join _ _ _ [CB (length (@nil byte)) []] _); [ apply rw_CB_nil; plia | ].
        cbn [cells_size csize length Nat.add Z.of_nat]. rewrite Z.add_0_r, length_app. exact J. }
    split.
    { apply TR; [exact FX|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
    split.
    { replace (D + Z.min (Z.of_nat (length (o1 ++ o2))) N)
        with (D + Z.min (Z.of_nat (length o1)) N + sn_k (N - Z.min (Z.of_nat (length o1)) N) (zb o2) [])
        by (unfold sn_k; rewrite length_app, zb_len; cbn [length]; plia).
      replace (N - Z.min (Z.of_nat (length (o1 ++ o2))) N)
        with (N - Z.min (Z.of_nat (length o1)) N - sn_k (N - Z.min (Z.of_nat (length o1)) N) (zb o2) [])
        by (unfold sn_k; rewrite length_app, zb_len; cbn [length]; plia).
      exact CK'. }
    assert (DCa' : rw_cells img_segs m' D [CB w1n (zb (firstn (Z.to_nat N) o1))]).
    { apply TR; [exact DCa|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
    rewrite <- Hw1n in DST'.
    pose proof (rw_CB_join _ _ _ _ _ _ _ DCa' DST') as J.
    replace dn with (w1n + length (Z_to_bv 8 0 :: skipn (S w1n) junkd))%nat by plia.
    match type of J with rw_cells _ _ _ [CB _ ?L] =>
      replace (zb (firstn (Z.to_nat N) (o1 ++ o2)) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (Z.of_nat (length (o1 ++ o2))) N))) junkd)
        with L; [exact J|] end.
    replace (Z.to_nat (N - Z.of_nat w1n)) with (Z.to_nat N - w1n)%nat by plia.
    change (zb o2 ++ []) with (zb o2 ++ zb []).
    rewrite (snf_dbytes o1 o2 [] junkd (Z.to_nat N) w1n (Z.to_nat (sn_k (N - Z.of_nat w1n) (zb o2) [])) (Z_to_bv 8 0));
      [ | plia | unfold sn_k; rewrite zb_len; cbn [length]; plia ].
    rewrite app_nil_r. f_equal. f_equal. f_equal. unfold sn_k. rewrite length_app, zb_len. cbn [length]. plia.
  Qed.


  Lemma snf_out_a : out_a_stmt Fp B SNF_CAP CK 16 D (Z.of_nat dn)
                      (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM) (TOPOK_snf TOP) (OUT_snf OM)
                      (snf_out_ready Fp B CK D dn).
  Proof.
    unfold out_a_stmt. intros until canary.
    intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 E1 E2 E3 E4 E5 RDY. rename st into o.
    unfold OUT_snf. apply implM_get_k.
    destruct (Z.leb_spec0 (zlength o + zlength bs) OM) as [FIT|NOFIT]; [ | apply implM_unr ].
    apply implM_put.
    dest_snf HS. subst o.
    unfold TOPOK_snf in TQ. unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_len bs) as LZb. pose proof (zb_len o2) as LZo.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; plia).
    destruct SSP as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    destruct (stk_split _ _ _ (bv_unsigned sp - SN_WRITE_DEPTH) _ ST ltac:(plia)) as [ST1 ST2].
    unfold SN_WRITE_DEPTH, COPY_DEPTH in ST1, ST2.
    unfold zlength, SNF_CAP in *. rewrite length_app in Ho, FIT.
    destruct (Z.le_gt_cases (Z.of_nat (length bs)) (80 - Z.of_nat (length o2))) as [ROOM|NOROOM].
    - eapply evt_mono.
      { eapply (SPEC_fwritex_room ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m fl0 j1 (snf_j2 jm jr js jt B) lbfw B (zb o2) bj (zb bs));
          rewrite ?EFp, ?LZo, ?LZb.
        - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by plia. reflexivity. - plia. - exact ST2. - exact MI.
        - plia. - eapply snf_ready_room; [ exact RDY | plia | plia | plia | plia ].
        - right; plia. - right; plia. - destruct E1; [left|right]; plia. - destruct E3; [left|right]; plia.
        - destruct E2; [left|right]; plia. }
      cbv beta. intros ms' P. unfold fwritex_room_post, fwritex_room_footprint, SN_WRITE_DEPTH, COPY_DEPTH in P.
      rewrite ?EFp, ?LZo, ?LZb in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
      mk_tr MU TR.
      unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
      split; [reflexivity|].
      split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear_disj. lia. }
      split; [exact WM|]. split; [exact MI'|].
      split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; dj] | exact ST' | plia ]. }
      split.
      { assert (FX' : rw_cells img_segs m' (Fp + 148) [CB 4 jx; C8 (Z_to_bv 64 CK); CB 72 jy])
          by (apply TR; [exact FX|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
        assert (CKC' : rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (Z.of_nat (length o1)) N)); C8 (Z_to_bv 64 (N - Z.min (Z.of_nat (length o1)) N))])
          by (apply TR; [exact CKC|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
        assert (DC' : rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o1) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (Z.of_nat (length o1)) N))) junkd)])
          by (apply TR; [exact DC|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
        rewrite <- zb_app2 in WF2.
        exists o1, (o2 ++ bs), (skipn (length bs) bj). cbv zeta. unfold zlength, SNF_CAP.
        repeat (match goal with |- _ /\ _ => split end);
          first [ assumption | (symmetry; apply app_assoc) | (rewrite ?length_app, ?length_skipn; plia) ]. }
      split.
      { unfold ssp_cells, got_ssp, ssp_guard. split.
        - apply TR; [exact SS1|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
        - apply TR; [exact SS2|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
      exact SRC'.
    - apply snf_file_split in FC; [ | assumption.. ].
      destruct FC as (FA & FWP & FB2 & FWB & FHI & FWE & FWR & FBF).
      pose proof FX as FX1.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FX1. destruct FX1 as [_ FX1]. cbn [cells_size csize Nat.add] in FX1.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FX1. destruct FX1 as [FCK _].
      replace (Fp + 148 + Z.of_nat 4) with (Fp + 152) in FCK by plia.
      pose proof (rw_cells_hd_bytes _ _ _ _ _ _ BUF) as PEND.
      remember (Z.to_nat (Z.min (Z.of_nat (length o1)) N)) as w1n eqn:Ew1n.
      assert (Hw1n : Z.of_nat w1n = Z.min (Z.of_nat (length o1)) N) by plia.
      assert (Hw1d : (w1n < dn)%nat) by plia.
      assert (LF : length (zb (firstn (Z.to_nat N) o1)) = w1n) by (rewrite zb_len, length_firstn; plia).
      replace dn with (w1n + (dn - w1n))%nat in DC at 1 by plia.
      apply rw_CB_split in DC. destruct DC as [DCa DCb].
      destruct (split_prefix _ (Z_to_bv 8 0 :: skipn (S w1n) junkd) _ LF) as [EF ES].
      rewrite EF in DCa. rewrite ES in DCb.
      assert (Ldst : length (Z_to_bv 8 0 :: skipn (S w1n) junkd) = (dn - w1n)%nat) by (cbn [length]; rewrite length_skipn; plia).
      rewrite <- Ldst in DCb. rewrite Hw1n in DCb.
      eapply evt_mono.
      { eapply (SPEC_fwritex_w ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  Fp (B + Z.of_nat (length (zb o2)) + Z.of_nat (length bj)) B B CK
                  (D + Z.min (Z.of_nat (length o1)) N) (N - Z.min (Z.of_nat (length o1)) N) (zb o2) (zb bs)
                  (Z_to_bv 8 0 :: skipn (S w1n) junkd));
          [ exact Ha2 | exact SRC | subst a1; rewrite unsigned_lit by plia; rewrite LZb; reflexivity
          | exact FWE | exact FWP | exact FWB | exact FWR | exact FBF | exact FCK | exact CKC | exact PEND
          | plia | plia | plia
          | exact DCb | plia
          | unfold sn_k; cbn [length]; rewrite length_skipn; plia
          | exact ST2 | plia | exact MI
          | eapply snf_ready_snw; [ exact RDY | plia | plia | plia | plia ]
          | right; plia | right; plia | destruct D4; [left|right]; plia | right; plia
          | destruct E1; [left|right]; plia
          | destruct SFC; [left|right]; plia | destruct SDF; [left|right]; plia | destruct SDC; [left|right]; plia
          | destruct SDB; [right|left]; plia
          | destruct E5; [left|right]; plia | destruct E4; [left|right]; plia ]. }
      cbv beta. intros ms' P. unfold sn_write_post, SN_WRITE_DEPTH, COPY_DEPTH in P.
      destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & E & MU & WM & MI' & ST' & WP' & WB' & CK' & DST').
      rewrite Ldst in MU.
      mk_tr MU TR.
      unfold out_post, SR. exists y0, y1, y2, (Z_to_bv 64 (Z.of_nat (length (zb bs)))), y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m'.
      split; [exact E|].
      split. { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. clear_disj. lia. }
      split; [exact WM|]. split; [exact MI'|].
      split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; dj] | exact ST' | plia ]. }
      split.
      { assert (FX' : rw_cells img_segs m' (Fp + 148) [CB 4 jx; C8 (Z_to_bv 64 CK); CB 72 jy])
          by (apply TR; [exact FX|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
        assert (WF' : wfile m' Fp fl0 j1 (snf_j2 jm jr js jt B) lbfw B (zb []) (zb o2 ++ bj)).
        { change (zb []) with (@nil byte).
          unfold wfile. split; [|split; [|split; [exact FL|split; [exact LBF|split; [plia|split; rewrite ?length_app, ?zb_len; cbn [length]; dj]]]]].
          - replace (B + Z.of_nat (length (@nil byte)) + Z.of_nat (length (zb o2 ++ bj)))
              with (B + Z.of_nat (length (zb o2)) + Z.of_nat (length bj)) by (rewrite length_app; cbn [length]; plia).
            replace (B + Z.of_nat (length (@nil byte))) with B by (cbn [length]; plia).
            apply snf_file_join; try assumption.
            + apply TR; [exact FA|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
            + apply TR; [exact FB2|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
            + apply TR; [exact FHI|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
          - assert (BUF' : rw_cells img_segs m' B [CB (length (zb o2)) (zb o2); CB (length bj) bj]).
            { apply TR; [exact BUF|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
            assert (J : rw_cells img_segs m' B ([] ++ [CB (length (zb o2)) (zb o2); CB (length bj) bj] ++ [])) by (cbn [app]; exact BUF').
            apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite Nat.add_0_r, app_nil_r in J.
            apply (rw_cells_join _ _ _ [CB (length (@nil byte)) []] _); [ apply rw_CB_nil; plia | ].
            cbn [cells_size csize length Nat.add Z.of_nat]. rewrite Z.add_0_r, length_app. exact J. }
        assert (CKC' : rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N));
                                                C8 (Z_to_bv 64 (N - Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N))]).
        { replace (D + Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N)
            with (D + Z.min (Z.of_nat (length o1)) N + sn_k (N - Z.min (Z.of_nat (length o1)) N) (zb o2) (zb bs))
            by (unfold sn_k; rewrite !length_app, !zb_len; plia).
          replace (N - Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N)
            with (N - Z.min (Z.of_nat (length o1)) N - sn_k (N - Z.min (Z.of_nat (length o1)) N) (zb o2) (zb bs))
            by (unfold sn_k; rewrite !length_app, !zb_len; plia).
          exact CK'. }
        assert (DC' : rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) (o1 ++ o2 ++ bs)) ++ Z_to_bv 8 0
                                                  :: skipn (S (Z.to_nat (Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N))) junkd)]).
        { assert (DCa' : rw_cells img_segs m' D [CB w1n (zb (firstn (Z.to_nat N) o1))]).
          { apply TR; [exact DCa|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
          rewrite <- Hw1n in DST'.
          pose proof (rw_CB_join _ _ _ _ _ _ _ DCa' DST') as J.
          replace dn with (w1n + length (Z_to_bv 8 0 :: skipn (S w1n) junkd))%nat by plia.
          match type of J with rw_cells _ _ _ [CB _ ?L] =>
            replace (zb (firstn (Z.to_nat N) (o1 ++ o2 ++ bs)) ++ Z_to_bv 8 0
                       :: skipn (S (Z.to_nat (Z.min (Z.of_nat (length (o1 ++ o2 ++ bs))) N))) junkd)
              with L; [exact J|] end.
          replace (Z.to_nat (N - Z.of_nat w1n)) with (Z.to_nat N - w1n)%nat by plia.
          rewrite (snf_dbytes o1 o2 bs junkd (Z.to_nat N) w1n (Z.to_nat (sn_k (N - Z.of_nat w1n) (zb o2) (zb bs))) (Z_to_bv 8 0));
            [ | plia | unfold sn_k; rewrite !zb_len; plia ].
          f_equal. f_equal. f_equal. unfold sn_k. rewrite !length_app, !zb_len. plia. }
        exists (o1 ++ o2 ++ bs), [], (zb o2 ++ bj). cbv zeta. unfold zlength, SNF_CAP.
        repeat (match goal with |- _ /\ _ => split end);
          first [ assumption | (rewrite app_nil_r; symmetry; apply app_assoc) | (cbn [length]; rewrite ?length_app, ?zb_len; plia) ]. }
      split.
      { unfold ssp_cells, got_ssp, ssp_guard. split.
        - apply TR; [exact SS1|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
        - apply TR; [exact SS2|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
      eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. rewrite LZb. dj.
  Qed.

End SnfProofs.

End Img.
