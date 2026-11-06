(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Eg3i DA_Cells DA_Entry.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Agree.
  Variable segs : list Segment.
  Variables (m m' : word -> option byte).

  Lemma mrd_agree : forall x, m' x = m x -> mrd segs m' x = mrd segs m x.
  Proof. intros x H. unfold mrd. rewrite H. reflexivity. Qed.
  Lemma wview_agree : forall x, m' x = m x -> wview segs m' x = wview segs m x.
  Proof. intros x H. unfold wview. rewrite H. reflexivity. Qed.

  Lemma bytes_at_agree : forall a bs,
    (forall i, 0 <= i < Z.of_nat (length bs) -> m' (wz (a + i)) = m (wz (a + i))) ->
    bytes_at segs m a bs -> bytes_at segs m' a bs.
  Proof.
    intros a bs AG (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold wa. rewrite (mrd_agree _ (AG (Z.of_nat i) ltac:(lia))). apply H. exact Hi.
  Qed.
  Lemma wr_at_agree : forall a n,
    (forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i))) ->
    wr_at segs m a n -> wr_at segs m' a n.
  Proof.
    intros a n AG (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold wa. rewrite (wview_agree _ (AG i Hi)). apply H. exact Hi.
  Qed.
  Lemma ro_cells_agree : forall a cs,
    (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (a + i)) = m (wz (a + i))) ->
    ro_cells segs m a cs -> ro_cells segs m' a cs.
  Proof.
    intros a cs AG [WF B]. split; [exact WF|]. apply bytes_at_agree; [|exact B].
    rewrite (cells_bytes_length cs WF). exact AG.
  Qed.
  Lemma rw_cells_agree : forall a cs,
    (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (a + i)) = m (wz (a + i))) ->
    rw_cells segs m a cs -> rw_cells segs m' a cs.
  Proof.
    intros a cs AG [C W]. split; [apply ro_cells_agree; assumption| apply wr_at_agree; assumption].
  Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Raw.
  Variable m : word -> option byte.
  Hypothesis WIMG : forall a, 0xa8000 <= a < 0x60a000 -> wview rsegs m (wz a) <> None.

  Lemma wr_at_img : forall a n, 0xa8000 <= a -> a + n <= 0x60a000 -> wr_at rsegs m a n.
  Proof.
    intros a n H1 H2. split; [lia|]. split; [lia|]. intros i Hi. unfold wa. apply WIMG. lia.
  Qed.

  Lemma ro_cells_of_bytes : forall a cs bs,
    bytes_at rsegs m a bs -> cells_wf cs -> cells_bytes cs = bs -> ro_cells rsegs m a cs.
  Proof. intros a cs bs B WF E. split; [exact WF|]. rewrite E. exact B. Qed.

  Lemma rw_cells_of_bytes : forall a cs bs,
    bytes_at rsegs m a bs -> cells_wf cs -> cells_bytes cs = bs ->
    0xa8000 <= a -> a + Z.of_nat (length bs) <= 0x60a000 -> rw_cells rsegs m a cs.
  Proof.
    intros a cs bs B WF E H1 H2. split; [exact (ro_cells_of_bytes a cs bs B WF E)|].
    rewrite <- (cells_bytes_length cs WF), E. apply wr_at_img; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_sub : forall a bs k n,
    bytes_at rsegs m a bs -> (k + n <= length bs)%nat -> bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
  Proof.
    intros a bs k n (H0 & H1 & H) Hkn.
    assert (LEN : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
    split; [lia|]. split; [rewrite LEN; lia|]. intros i Hi. rewrite LEN in Hi.
    replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat ltac:(lia)).
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by lia. rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite LEN; exact Hi).
    f_equal. rewrite nth_firstn, nth_skipn. destruct (Nat.ltb_spec i n); [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma junk_bytes : forall a n, image_bytes rsegs a n <> None -> 0 <= a -> a + Z.of_nat n <= 2^64 ->
    exists junk, length junk = n /\ bytes_at rsegs m a junk.
  Proof.
    intros a n. revert a. induction n as [|n IH]; intros a IMG H0 H1.
    - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
    - cbn [image_bytes] in IMG. destruct (Lib.PropExec.seg_rom rsegs (wa a)) as [b0|] eqn:E0; [|exfalso; apply IMG; reflexivity].
      destruct (image_bytes rsegs (a + 1) n) as [bs|] eqn:E1; [|exfalso; apply IMG; reflexivity].
      destruct (IH (a + 1) ltac:(rewrite E1; discriminate) ltac:(lia) ltac:(lia)) as (junk & LJ & BJ).
      set (b := match m (wa a) with Some b' => b' | None => b0 end).
      exists (b :: junk). split; [cbn; lia|].
      split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi.
      + cbn. rewrite Z.add_0_r. unfold mrd. subst b. destruct (m (wa a)); [reflexivity| exact E0].
      + cbn [nth_error]. destruct BJ as (_ & _ & BJ). rewrite <- (BJ i ltac:(cbn in Hi; lia)). f_equal. unfold wa. f_equal. lia.
  Qed.

  Lemma junk_rw_cells : forall a n, image_bytes rsegs a n <> None -> 0xa8000 <= a -> a + Z.of_nat n <= 0x60a000 ->
    exists junk, rw_cells rsegs m a [CB n junk].
  Proof.
    intros a n IMG H1 H2. destruct (junk_bytes a n IMG ltac:(lia) ltac:(lia)) as (junk & LJ & BJ).
    exists junk. apply (rw_cells_of_bytes a [CB n junk] junk BJ); [cbn; split; [exact LJ| exact I] | cbn; apply app_nil_r | lia | rewrite LJ; lia].
  Qed.
  Lemma junk_ro_cells : forall a n, image_bytes rsegs a n <> None -> 0 <= a -> a + Z.of_nat n <= 2^64 ->
    exists junk, ro_cells rsegs m a [CB n junk].
  Proof.
    intros a n IMG H1 H2. destruct (junk_bytes a n IMG H1 H2) as (junk & LJ & BJ).
    exists junk. apply (ro_cells_of_bytes a [CB n junk] junk BJ); [cbn; split; [exact LJ| exact I] | cbn; apply app_nil_r].
  Qed.
End Raw.

(* [comment removed for export] *)
Lemma img_stdout_buf : image_bytes rsegs STDOUT_BUF 1024 <> None. Proof. vm_compute. discriminate. Qed.
Lemma img_stderr_buf : image_bytes rsegs STDERR_BUFP 8 <> None. Proof. vm_compute. discriminate. Qed.
Lemma img_tr_empty : image_bytes rsegs TR_EMPTY 16 <> None. Proof. vm_compute. discriminate. Qed.
Lemma img_atexit_fin : image_bytes rsegs ATEXIT 1 <> None. Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  #[local] Notation p0a := (e_p0a usp argv envp).
  #[local] Notation p1a := (e_p1a usp argv envp).
  #[local] Notation argc := (e_argc argv).
  #[local] Notation span := (e_span argv envp).

  Record main_view (A0 : AS) (m : word -> option byte) (md : Model) : Prop := {
    mv_ainv  : ainv A0 m md;
    mv_mi    : mem_inv rsegs (aview A0 m);
    mv_fs    : m_fs md = fs;
    mv_fds   : m_fds md = fds_std;
    (* [comment removed for export] *)
    mv_stk   : stk rsegs (aview A0 m) (STK_LO usp) usp;
    mv_stksh : forall a, STKSH_LO <= a < STKSH_HI -> aview A0 m (wz a) = Some (Z_to_bv 8 0);
    mv_usp   : sp_window_lo <= usp /\ usp + span <= 2^47 /\ usp mod 16 = 0 /\ 0 <= span;
    (* [comment removed for export] *)
    mv_cells : exists tid, dcells (aview A0 m) tid SO_pristine 0;
    mv_sspgot : ro_cells rsegs (aview A0 m) SSP_GOT [C8 (wz SSP_GUARD)];
    mv_errno : exists e, rw_cells rsegs (aview A0 m) ERRNO_CELL [C4 e];
    (* [comment removed for export] *)
    mv_argv0p : bytes_at rsegs (aview A0 m) (usp + 8) (le8 (wz p0a));
    mv_argv1p : 2 <= argc -> bytes_at rsegs (aview A0 m) (usp + 16) (le8 (wz p1a));
    mv_argv0 : bytes_at rsegs (aview A0 m) p0a (nth 0 argv [] ++ [Z_to_bv 8 0]);
    mv_argv1 : 2 <= argc -> bytes_at rsegs (aview A0 m) p1a (nth 1 argv [] ++ [Z_to_bv 8 0]);
    mv_str0  : usp + 24 <= p0a /\ p0a + e_L0 argv + 1 + 16 <= usp + span;
    mv_str1  : 2 <= argc -> p1a + e_L1 argv + 1 + 16 <= usp + span;
    (* [comment removed for export] *)
    mv_slack0 : exists sl, length sl = 16%nat /\ bytes_at rsegs (aview A0 m) (p0a + e_L0 argv + 1) sl;
    mv_slack1 : 2 <= argc -> exists sl, length sl = 16%nat /\ bytes_at rsegs (aview A0 m) (p1a + e_L1 argv + 1) sl;
    (* [comment removed for export] *)
    mv_A0    : entry_A0 usp span A0
  }.

  Variables (R : bvmap 5 word) (FULL : word -> option byte) (md : Model) (A0 : AS).
  Hypothesis ER : entry_raw usp argv envp fs R FULL md.
  Hypothesis AINV : ainv A0 FULL md.
  Hypothesis EA : entry_A0 usp span A0.
  #[local] Notation v0 := (aview A0 FULL).

  (* [comment removed for export] *)
  Lemma view_img : forall a, 0x10000 <= a < 0x60a000 -> v0 (wz a) = FULL (wz a).
  Proof.
    intros a Ha. unfold aview, aview_of, mrestrict.
    rewrite (as_image_visible LPA A0 FULL md a AINV); [reflexivity|]. unfold in_image. cbn. lia.
  Qed.
  Lemma view_stack : forall a, STK_LO usp <= a < usp + span -> v0 (wz a) = FULL (wz a).
  Proof.
    intros a Ha. unfold aview, aview_of, mrestrict. rewrite (ea_vis_stack _ _ _ EA a); [reflexivity|]. unfold STK_LO in Ha. lia.
  Qed.
  Lemma view_stksh : forall a, STKSH_LO <= a < STKSH_HI -> v0 (wz a) = FULL (wz a).
  Proof.
    intros a Ha. unfold aview, aview_of, mrestrict. rewrite (ea_vis_stksh _ _ _ EA a); [reflexivity| exact Ha].
  Qed.
  (* [comment removed for export] *)
  Lemma view_some : forall x b, v0 x = Some b -> FULL x = Some b.
  Proof. intros x b H. unfold aview, aview_of, mrestrict in H. destruct (hidc (ahull A0) x); [discriminate| exact H]. Qed.

  Lemma wimg_view : forall a, 0xa8000 <= a < 0x60a000 -> wview rsegs v0 (wz a) <> None.
  Proof. intros a Ha. rewrite (wview_agree rsegs FULL v0 _ (view_img a ltac:(lia))). apply (er_wimg _ _ _ _ _ _ _ ER). exact Ha. Qed.

  (* [comment removed for export] *)
  Lemma main_cell : forall i a bs, nth_error MAIN_CELLS i = Some (a, bs) ->
    0x10000 <= a -> a + Z.of_nat (length bs) <= 0x60a000 -> bytes_at rsegs v0 a bs.
  Proof.
    intros i a bs Hn H1 H2.
    pose proof (proj1 (Forall_forall _ _) (er_cells _ _ _ _ _ _ _ ER) (a, bs) (nth_error_In _ _ Hn)) as B. cbn [fst snd] in B.
    apply (bytes_at_agree rsegs FULL v0); [| exact B]. intros j Hj. apply view_img. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac addr_lia :=
    unfold EXIT_LOCK, ATEXIT, NEED_LOCKS, OFL_HEAD, TID_CELL, STDIN_F, STDOUT_F, STDERR_F, STDERR_CELL, STDERR_BUFP,
           STDOUT_BUF, SSP_GUARD, SSP_GOT, TR_INITIALIZED, TR_INCB, TR_EMPTY, ERRNO_CELL, CALL_TRAMP, AEF_GUARD in *;
    repeat match goal with |- context [length ?l] =>
      lazymatch l with _ :: _ => let n := eval vm_compute in (length l) in change (length l) with n end end;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length]; first [lia | cbn; lia].

  Ltac mcell i :=
    lazymatch goal with
    | |- ro_cells _ _ ?a ?cs =>
        eapply (ro_cells_of_bytes v0 a cs); [eapply (main_cell i); [reflexivity| addr_lia| addr_lia] | cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity
                                            | apply bytes_eq_of_unsigned; vm_compute; reflexivity]
    | |- rw_cells _ _ ?a ?cs =>
        eapply (rw_cells_of_bytes v0 wimg_view a cs); [eapply (main_cell i); [reflexivity| addr_lia| addr_lia] | cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity
                                            | apply bytes_eq_of_unsigned; vm_compute; reflexivity | addr_lia | addr_lia]
    end.

  Lemma main_cells_view : exists tid, dcells v0 tid SO_pristine 0.
  Proof.
    destruct (er_tid _ _ _ _ _ _ _ ER) as (tid & TR & TB).
    exists tid. unfold dcells. split; [| split; [| split]].
    - (* [comment removed for export] *) constructor.
      + (* [comment removed for export] *) eapply (ro_cells_of_bytes v0 TID_CELL [C4 (wz tid)]); [| cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
        apply (bytes_at_agree rsegs FULL v0); [| exact TB]. intros j Hj. apply view_img. unfold TID_CELL. cbn in Hj. lia.
      + lia.
      + (* [comment removed for export] *) mcell 7%nat.
      + (* [comment removed for export] *) mcell 17%nat.
      + mcell 8%nat.
      + (* [comment removed for export] *) mcell 10%nat.
      + mcell 11%nat.
      + mcell 12%nat.
      + mcell 13%nat.
      + mcell 14%nat.
      + mcell 15%nat.
      + mcell 5%nat.
      + mcell 3%nat.
      + mcell 1%nat.
      + (* [comment removed for export] *)
        exists (Z_to_bv 64 0), (Z_to_bv 64 0).
        pose proof (main_cell 4 STDIN_F _ eq_refl ltac:(addr_lia) ltac:(unfold STDIN_F; addr_lia)) as B.
        unfold file_clean.
        assert (FLD : forall k n cs, (k + n <= 152)%nat -> cells_wf cs ->
                  map bv_unsigned (cells_bytes cs) = map bv_unsigned (firstn n (skipn k (snd (nth 4 MAIN_CELLS (0, []))))) ->
                  ro_cells rsegs v0 (STDIN_F + Z.of_nat k) cs).
        { intros k n cs Hkn WF E. eapply (ro_cells_of_bytes v0 _ cs _ (bytes_at_sub v0 STDIN_F _ k n B ltac:(addr_lia)) WF).
          apply bytes_eq_of_unsigned. exact E. }
        split; [| split; [| split; [| split]]].
        * apply (FLD 140%nat 4%nat); [addr_lia| cbn; tauto| vm_compute; reflexivity].
        * apply (FLD 40%nat 8%nat); [addr_lia| cbn; tauto| vm_compute; reflexivity].
        * apply (FLD 56%nat 8%nat); [addr_lia| cbn; tauto| vm_compute; reflexivity].
        * apply (FLD 8%nat 8%nat); [addr_lia| cbn; tauto| vm_compute; reflexivity].
        * apply (FLD 16%nat 8%nat); [addr_lia| cbn; tauto| vm_compute; reflexivity].
      + mcell 6%nat.
      + (* [comment removed for export] *) destruct (rw_C8_any v0 SSP_GUARD ltac:(addr_lia) ltac:(addr_lia)
                                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (g & G).
        exists g. exact (proj1 G).
      + (* [comment removed for export] *)
        apply ro_C8_of_bytes. apply (consts_lookup v0 _ _ (as_consts LPA A0 FULL md AINV)). vm_compute. reflexivity.
      + (* [comment removed for export] *) apply (junk_rw_cells v0 wimg_view STDERR_BUFP 8 img_stderr_buf); addr_lia.
      + (* [comment removed for export] *) apply (junk_ro_cells v0 TR_EMPTY 16 img_tr_empty); addr_lia.
    - (* [comment removed for export] *)
      unfold file_at. pose proof MAIN_CELLS_stderr as E.
      eapply (rw_cells_of_bytes v0 wimg_view STDERR_F (file_cells stderr0) (cells_bytes (file_cells stderr0))).
      + apply (main_cell 0); [| addr_lia| unfold STDERR_F; rewrite cells_bytes_length by (cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity); addr_lia].
        rewrite <- E. reflexivity.
      + cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
      + reflexivity.
      + addr_lia.
      + rewrite cells_bytes_length by (cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity). unfold STDERR_F; addr_lia.
    - (* [comment removed for export] *)
      cbn [stdout_at]. split.
      + unfold file_at. pose proof MAIN_CELLS_stdout as E.
        eapply (rw_cells_of_bytes v0 wimg_view STDOUT_F (file_cells stdout0) (cells_bytes (file_cells stdout0))).
        * apply (main_cell 2); [| addr_lia| unfold STDOUT_F; rewrite cells_bytes_length by (cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity); addr_lia].
          rewrite <- E. reflexivity.
        * cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
        * reflexivity.
        * addr_lia.
        * rewrite cells_bytes_length by (cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity). unfold STDOUT_F; addr_lia.
      + apply (junk_rw_cells v0 wimg_view STDOUT_BUF 1024 img_stdout_buf); addr_lia.
    - (* [comment removed for export] *)
      split; [left; reflexivity|]. split; [mcell 16%nat|]. split; [mcell 20%nat|]. split; [mcell 9%nat|]. split; [mcell 18%nat| mcell 19%nat].
  Qed.

  Ltac eun := unfold STK_LO, e_span, e_p1a in *; unfold e_p0a, e_L0, e_L1, e_argc, e_envc in *.

  Theorem main_view_of_entry : main_view A0 FULL md.
  Proof.
    pose proof (er_usp _ _ _ _ _ _ _ ER) as (U1 & U2 & U3 & U4). pose proof (er_str0 _ _ _ _ _ _ _ ER) as S0.
    pose proof (er_str1 _ _ _ _ _ _ _ ER) as S1.
    unfold sp_window_lo, e_span in *.
    constructor.
    - exact AINV.
    - (* [comment removed for export] *) intros x b Hx. apply view_some in Hx.
      destruct (ro_addr rsegs x) eqn:RO; [|reflexivity]. exfalso.
      apply (as_ro_addr_iff LPA x) in RO. cbn [cl_image_lo cl_rw_lo LPA] in RO.
      pose proof (er_roimg _ _ _ _ _ _ _ ER (bv_unsigned x) RO) as N. rewrite Z_to_bv_bv_unsigned in N. rewrite N in Hx. discriminate.
    - exact (er_fs _ _ _ _ _ _ _ ER).
    - exact (er_fds _ _ _ _ _ _ _ ER).
    - (* [comment removed for export] *) split; [unfold STK_LO; lia|]. split; [lia|]. intros a Ha.
      pose proof (er_stack _ _ _ _ _ _ _ ER a Ha) as P. unfold STK_LO in Ha.
      assert (V : v0 (wz a) = FULL (wz a)) by (apply view_stack; eun; lia).
      assert (NS : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
      { apply (as_find_segment_outside LPA). unfold in_image, wa. rewrite unsigned_lit by lia. cbn. lia. }
      unfold wa in *. split.
      + unfold wview. rewrite V. destruct (FULL (wz a)); [discriminate|]. rewrite NS. exact P.
      + unfold mrd. rewrite V. destruct (FULL (wz a)) as [b|]; [exists b; reflexivity| exfalso; apply P; reflexivity].
    - (* [comment removed for export] *) intros a Ha. rewrite (view_stksh a Ha). apply (er_stkshadow _ _ _ _ _ _ _ ER). exact Ha.
    - unfold sp_window_lo, e_span. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - exact main_cells_view.
    - apply ro_C8_of_bytes. apply (consts_lookup v0 _ _ (as_consts LPA A0 FULL md AINV)). vm_compute. reflexivity.
    - (* [comment removed for export] *) exact (rw_errno_any v0).
    - apply (bytes_at_agree rsegs FULL v0); [| exact (er_argv0p _ _ _ _ _ _ _ ER)]. intros i Hi. apply view_stack.
      rewrite length_le8 in Hi. eun; lia.
    - intros H2. apply (bytes_at_agree rsegs FULL v0); [| exact (er_argv1p _ _ _ _ _ _ _ ER H2)]. intros i Hi. apply view_stack.
      rewrite length_le8 in Hi. eun; lia.
    - apply (bytes_at_agree rsegs FULL v0); [| exact (er_argv0 _ _ _ _ _ _ _ ER)]. intros i Hi. apply view_stack.
      rewrite length_app in Hi. cbn [length] in Hi. eun; lia.
    - intros H2. apply (bytes_at_agree rsegs FULL v0); [| exact (er_argv1 _ _ _ _ _ _ _ ER H2)]. intros i Hi. apply view_stack.
      rewrite length_app in Hi. cbn [length] in Hi. specialize (S1 H2). eun; lia.
    - eun; lia.
    - intros H2. exact (S1 H2).
    - destruct (er_slack0 _ _ _ _ _ _ _ ER) as (sl & L & B). exists sl. split; [exact L|].
      apply (bytes_at_agree rsegs FULL v0); [| exact B]. intros i Hi. apply view_stack. rewrite L in Hi. eun; lia.
    - intros H2. destruct (er_slack1 _ _ _ _ _ _ _ ER H2) as (sl & L & B). exists sl. split; [exact L|].
      apply (bytes_at_agree rsegs FULL v0); [| exact B]. intros i Hi. apply view_stack. rewrite L in Hi. specialize (S1 H2). eun; lia.
    - exact EA.
  Qed.
End S.
