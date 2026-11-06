From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

Definition RT (sp : Z) (m : word -> option byte) (md : Model) : Prop :=
  asan_cells m /\ shadow_rw m /\ asan_opt_cells m /\ asan_cf_cells m /\ asan_uw_cells m /\ asan_real_cells m
  /\ asan_im_cells m /\ asan_exit_cells m /\ asan_fs_cells m.

Definition rt_disjoint (W : list ivl) : Prop :=
  disjoint_from W RT_LO (RT_HI - RT_LO) /\ disjoint_from W RT_GOT_AF 8 /\ disjoint_from W (RT_AF + 60) 1
  /\ disjoint_from W RT_GOT_VERB 8 /\ disjoint_from W RT_VERB 4
  /\ disjoint_from W RT_GOT_CF 8 /\ disjoint_from W RT_CF 288 /\ disjoint_from W (RT_AF + 29) 1
  /\ disjoint_from W RT_TSDI 1 /\ disjoint_from W RT_TSDK 4 /\ disjoint_from W RT_PGSZ 8
  /\ disjoint_from W (RT_TP - 88) 8 /\ disjoint_from W RT_TSDMAIN 8
  /\ disjoint_from W RT_REAL_LO (RT_REAL_HI - RT_REAL_LO) /\ disjoint_from W RT_IMAP 8 /\ disjoint_from W RT_IMEM 8
  /\ disjoint_from W (RT_AF + 24) 4 /\ disjoint_from W RT_MUG 8 /\ disjoint_from W RT_AGLOB RT_AGLOB_LEN
  /\ disjoint_from W (RT_TP - 8) 24 /\ disjoint_from W (RT_TP + 40) 8.

Lemma asan_opt_cells_kept : forall W m m', asan_opt_cells m -> munch W m m' -> rt_disjoint W -> asan_opt_cells m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4) MU (_ & D1 & D2 & D3 & D4 & _). split; [|split; [|split]].
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite length_le8; exact D1].
  - eapply bytes_at_transport; [exact H2 | exact MU | cbn [length]; exact D2].
  - eapply bytes_at_transport; [exact H3 | exact MU | rewrite length_le8; exact D3].
  - eapply bytes_at_transport; [exact H4 | exact MU | rewrite length_le4; exact D4].
Qed.

Lemma asan_cf_cells_kept : forall W m m', asan_cf_cells m -> munch W m m' -> rt_disjoint W -> asan_cf_cells m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) MU (_ & _ & _ & _ & _ & D1 & D2 & D3 & _).
  assert (DS : forall o n, 0 <= o -> o + n <= 288 -> disjoint_from W (RT_CF + o) n).
  { intros o n Ho Hn. eapply disjoint_from_sub; [exact D2 | lia | lia]. }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite length_le8; exact D1].
  - eapply bytes_at_transport; [exact H2 | exact MU | exact (DS 32 8 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H3 | exact MU | exact (DS 64 1 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H4 | exact MU | exact (DS 84 1 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H5 | exact MU | rewrite length_le8; exact (DS 120 8 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H6 | exact MU | exact (DS 137 1 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H7 | exact MU | exact (DS 240 21 ltac:(lia) ltac:(lia))].
  - eapply bytes_at_transport; [exact H8 | exact MU | exact D3].
Qed.

Lemma asan_uw_cells_kept : forall W m m', asan_uw_cells m -> munch W m m' -> rt_disjoint W -> asan_uw_cells m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4 & c & H5) MU (_ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & D5 & _).
  split; [|split; [|split; [|split]]].
  - eapply bytes_at_transport; [exact H1 | exact MU | exact D1].
  - eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le4; exact D2].
  - eapply bytes_at_transport; [exact H3 | exact MU | rewrite length_le8; exact D3].
  - eapply bytes_at_transport; [exact H4 | exact MU | rewrite length_le8; exact D4].
  - exists c. eapply bytes_at_transport; [exact H5 | exact MU | rewrite length_le8; exact D5].
Qed.

Lemma real_cells_kept_gen : forall W m m' (L : list (Z * Z)),
  Forall (fun p => bytes_at rsegs m (fst p) (le8 (wa (snd p)))) L ->
  Forall (fun p => RT_REAL_LO <= fst p /\ fst p + 8 <= RT_REAL_HI) L ->
  munch W m m' -> disjoint_from W RT_REAL_LO (RT_REAL_HI - RT_REAL_LO) ->
  Forall (fun p => bytes_at rsegs m' (fst p) (le8 (wa (snd p)))) L.
Proof.
  intros W m m' L H S MU D. induction L as [|p L IH]; [constructor|].
  rewrite Forall_cons_iff in H, S. destruct H as [Hp Hl]. destruct S as [Sp Sl].
  constructor; [|exact (IH Hl Sl)].
  eapply bytes_at_transport; [exact Hp | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D | lia | lia]].
Qed.

Lemma asan_real_cells_kept : forall W m m', asan_real_cells m -> munch W m m' -> rt_disjoint W -> asan_real_cells m'.
Proof.
  intros W m m' H MU (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D & _).
  exact (real_cells_kept_gen W m m' RT_REALS H RT_REALS_span MU D).
Qed.

Lemma real_cell_of : forall m a f, asan_real_cells m ->
  existsb (fun p => Z.eqb (fst p) a && Z.eqb (snd p) f) RT_REALS = true -> bytes_at rsegs m a (le8 (wa f)).
Proof.
  intros m a f H E. apply existsb_exists in E. destruct E as ([a' f'] & I & E). cbn in E.
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst a' f'.
  unfold asan_real_cells in H. rewrite Forall_forall in H. exact (H (a, f) I).
Qed.

Lemma asan_im_cells_kept : forall W m m', asan_im_cells m -> munch W m m' -> rt_disjoint W -> asan_im_cells m'.
Proof.
  intros W m m' (H1 & t & H2) MU (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _). split.
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite length_le8; exact D1].
  - exists t. eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le8; exact D2].
Qed.

Lemma asan_exit_cells_kept : forall W m m', asan_exit_cells m -> munch W m m' -> rt_disjoint W -> asan_exit_cells m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4) MU
    (_ & _ & _ & _ & _ & _ & DC & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & _).
  split; [|split; [|split]].
  - eapply bytes_at_transport; [exact H1 | exact MU | eapply disjoint_from_sub; [exact DC | cbn; lia | cbn; lia]].
  - eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le4; exact D1].
  - eapply bytes_at_transport; [exact H3 | exact MU | rewrite length_le8; exact D2].
  - eapply bytes_at_transport; [exact H4 | exact MU | rewrite RT_AGLOB_len; exact D3].
Qed.

Lemma asan_fs_cells_kept : forall W m m', asan_fs_cells m -> munch W m m' -> rt_disjoint W -> asan_fs_cells m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4 & (FS & H5 & HF) & (DB & H6 & HD)) MU
    (DL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D3 & D4).
  split; [|split; [|split; [|split; [|split]]]].
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite app_length, !length_le8].
    eapply disjoint_from_sub; [exact DL | unfold RT_LO, RT_TLSIDX; lia | unfold RT_LO, RT_HI, RT_TLSIDX; lia].
  - eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le8].
    eapply disjoint_from_sub; [exact DL | unfold RT_LO, RT_DTPOFF; lia | unfold RT_LO, RT_HI, RT_DTPOFF; lia].
  - eapply bytes_at_transport; [exact H3 | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D3 | lia | lia]].
  - eapply bytes_at_transport; [exact H4 | exact MU | rewrite length_le8; exact D4].
  - exists FS. split; [|exact HF].
    eapply bytes_at_transport; [exact H5 | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D3 | lia | lia]].
  - exists DB. split; [|exact HD].
    eapply bytes_at_transport; [exact H6 | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D3 | lia | lia]].
Qed.

Lemma RT_cells : forall sp m md, RT sp m md -> asan_cells m.
Proof. intros sp m md (H & _ & _ & _ & _ & _ & _ & _ & _). exact H. Qed.

Lemma RT_shadow_rw : forall sp m md, RT sp m md -> shadow_rw m.
Proof. intros sp m md (_ & H & _ & _ & _ & _ & _ & _ & _). exact H. Qed.

Lemma RT_opt_cells : forall sp m md, RT sp m md -> asan_opt_cells m.
Proof. intros sp m md (_ & _ & H & _ & _ & _ & _ & _ & _). exact H. Qed.

Lemma RT_cf_cells : forall sp m md, RT sp m md -> asan_cf_cells m.
Proof. intros sp m md (_ & _ & _ & H & _ & _ & _ & _ & _). exact H. Qed.

Lemma RT_uw_cells : forall sp m md, RT sp m md -> asan_uw_cells m.
Proof. intros sp m md (_ & _ & _ & _ & H & _ & _ & _ & _). exact H. Qed.

Lemma RT_real_cells : forall sp m md, RT sp m md -> asan_real_cells m.
Proof. intros sp m md (_ & _ & _ & _ & _ & H & _ & _ & _). exact H. Qed.

Lemma RT_im_cells : forall sp m md, RT sp m md -> asan_im_cells m.
Proof. intros sp m md (_ & _ & _ & _ & _ & _ & H & _ & _). exact H. Qed.

Lemma RT_exit_cells : forall sp m md, RT sp m md -> asan_exit_cells m.
Proof. intros sp m md (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma RT_fs_cells : forall sp m md, RT sp m md -> asan_fs_cells m.
Proof. intros sp m md (_ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma RT_intro : forall sp m md, asan_cells m -> shadow_rw m -> asan_opt_cells m -> asan_cf_cells m ->
  asan_uw_cells m -> asan_real_cells m -> asan_im_cells m -> asan_exit_cells m -> asan_fs_cells m -> RT sp m md.
Proof.
  intros sp m md H1 H2 H3 H4 H5 H6 H7 H8 H9.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

Lemma RT_any : forall sp sp' m md md', RT sp m md -> RT sp' m md'.
Proof. intros sp sp' m md md' H. exact H. Qed.

Lemma RT_store : forall sp sp' m m' md md' W,
  RT sp m md -> munch W m m' -> wmono rsegs m m' -> all_app W -> rt_disjoint W -> RT sp' m' md'.
Proof.
  intros sp sp' m m' md md' W (HC & HS & HO & HF & HU & HR & HI & HX & HFS) MU WM HA HD.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - exact (asan_cells_kept W m m' HC MU (proj1 HD)).
  - exact (shadow_rw_kept m m' HS (munch_meta W m m' MU HA) WM).
  - exact (asan_opt_cells_kept W m m' HO MU HD).
  - exact (asan_cf_cells_kept W m m' HF MU HD).
  - exact (asan_uw_cells_kept W m m' HU MU HD).
  - exact (asan_real_cells_kept W m m' HR MU HD).
  - exact (asan_im_cells_kept W m m' HI MU HD).
  - exact (asan_exit_cells_kept W m m' HX MU HD).
  - exact (asan_fs_cells_kept W m m' HFS MU HD).
Qed.

Lemma RT_meta_write : forall sp sp' m m' md md' W,
  RT sp m md -> munch W m m' -> wmono rsegs m m' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs m' (wa a) = Some b) ->
  RT sp' m' md'.
Proof.
  intros sp sp' m m' md md' W (HC & HS & HO & HF & HU & HL & HI & HX & HFS) MU WM HD HR.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - exact (asan_cells_kept W m m' HC MU (proj1 HD)).
  - intros a Ha. split; [exact (WM _ (proj1 (HS a Ha))) | exact (HR a Ha)].
  - exact (asan_opt_cells_kept W m m' HO MU HD).
  - exact (asan_cf_cells_kept W m m' HF MU HD).
  - exact (asan_uw_cells_kept W m m' HU MU HD).
  - exact (asan_real_cells_kept W m m' HL MU HD).
  - exact (asan_im_cells_kept W m m' HI MU HD).
  - exact (asan_exit_cells_kept W m m' HX MU HD).
  - exact (asan_fs_cells_kept W m m' HFS MU HD).
Qed.
