(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition IAZ_LO : Z := 0xaabc0.
Definition IAZ_HI : Z := 0x139450.
Definition iaz_ok (iv : Z * Z) : Prop := (IAZ_LO <= fst iv /\ snd iv <= IAZ_HI) \/ CEIL <= fst iv.

Section IAZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
Hypothesis HW : Forall iaz_ok W.

Lemma iaz_disj : forall a sz, (a + sz <= IAZ_LO \/ (IAZ_HI <= a /\ a + sz <= CEIL)) -> disjoint_from W a sz.
Proof.
  intros a sz H. induction W as [|[lo hi] W' IH]; [exact I|].
  inversion HW; subst. cbn. unfold iaz_ok in H2. cbn [fst snd] in H2. unfold IAZ_LO, IAZ_HI, CEIL in *.
  split; [lia| apply IH; assumption].
Qed.

Lemma iaz_Zheap' : forall lo hi, oclr lo hi -> hi <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo) -> framefree st lo hi -> disjoint_from W lo (hi - lo).
Proof. intros lo hi H1 H2 _ _. apply iaz_disj. unfold IAZ_LO, IAZ_HI, CEIL in *. clear - H1 H2. blia. Qed.

Lemma iaz_Zsh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 -> framefree st lo hi ->
  disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2 _ _. apply iaz_disj. right. pose proof (rt_SH_mono hi CEIL H2) as M. rewrite SH_CEIL in M.
  unfold SH, SHADOW_OFFSET, IAZ_HI, CEIL in *. lia.
Qed.

Local Ltac iaz := apply iaz_disj; unfold IAZ_LO, IAZ_HI, CEIL in *; blia.

Lemma IZ_link : WOK_link W.
Proof.
  split; [intros a v Hin; destruct (alink_range a v Hin); iaz| unfold A_GLOBREC_LO, A_GLOBREC_HI; iaz].
Qed.

Lemma IZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; iaz.
Qed.

Lemma IZ_thread : WOK_thread st W.
Proof.
  pose proof (t_page st WF) as (T1 & T2 & T3 & T4). unfold WOK_thread. unfold KHIGHMEM_BEG in T1.
  split; [iaz|]. split; [unfold qcache_t, T_QCACHE; iaz|]. split; [unfold T_UNWINDING; iaz|].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). destruct (loose0_range st WF _ _ CL1) as (R1 & R2 & R3 & R4).
  unfold KHIGHMEM_BEG in R1.
  split; [unfold CTX_TID; iaz|]. split; [unfold CTX_THREAD; iaz|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [iaz|]. split; [iaz|]. split; [iaz|]. split; [iaz|]. split; [iaz|]. split; [iaz|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3). destruct (loose0_range st WF _ _ DL1) as (Q1 & Q2 & Q3 & Q4).
  unfold KHIGHMEM_BEG in Q1. iaz.
Qed.

Lemma IZ_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. iaz.
  - iaz.
  - intros k Hk. iaz.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    destruct (nb_range st WF b Hb) as (R1 & R2 & R3).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    pose proof (ablk_img _ _ R1) as R1i. unfold AIMG_HI in R1i.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE, KHIGHMEM_BEG in *.
    apply iaz_disj. right. unfold IAZ_HI, CEIL. Z.div_mod_to_equations. lia.
  - iaz.
  - intros b Hb. iaz.
Qed.

Lemma IZ_fs : WOK_fs st W.
Proof.
  pose proof (fs_range st WF) as (F1 & F2 & F3). unfold KHIGHMEM_BEG in F1.
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. unfold FS_TOTAL in *. iaz.
  - unfold FS_TOTAL in *. iaz.
  - unfold FS_TOTAL in *. iaz.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. unfold fflag_addr, FS_TOTAL in *. iaz.
  - intros F k Hin. pose proof (frame_range st WF F k Hin) as (Hk & X & Y & _). unfold FS_FRAMES_OFF, FS_TOTAL in *.
    assert (64 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia). iaz.
Qed.

(* [comment removed for export] *)
Theorem iaz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_link m' /\ R_alloc st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_avail st m' /\ R_cache st m' /\ R_thread st m'
  /\ R_live st m' /\ R_quar st m' /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_lowshadow m'.
Proof.
  intros m m' MU WM HR.
  pose proof iaz_Zheap' as ZH. pose proof iaz_Zsh as ZS.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact IZ_link]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| exact IZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| eapply W_rinfo; eauto]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| eapply W_regions; eauto]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| eapply W_avail; eauto]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| eapply W_cache; eauto]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| exact IZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| eapply W_live; eauto]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| eapply W_quar; eauto]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| eapply W_batches; eauto]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| eapply W_ptrarr; eauto]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact IZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact IZ_fs]|].
  tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| eapply W_lowshadow; eauto].
Qed.

Theorem iaz_transport : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_consts st m' -> R_ia m' -> RTREP st m'.
Proof.
  intros m m' MU WM HR HC HI.
  destruct (iaz_others m m' MU WM HR) as (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X16).
  constructor; assumption.
Qed.
End IAZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma st_tls_set_ia : forall st, st_tls (set_ia_inited st) = st_tls st.
Proof. intros st. destruct st; reflexivity. Qed.

Section CONSTS.
Variables (st st' : rtstate) (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis ZW : forall a sz, a + sz <= IAZ_LO \/ (0x12bc21 <= a /\ a + sz <= 0x139448) \/ (0x13944c <= a /\ a + sz <= CEIL) -> disjoint_from W a sz.
Hypothesis WF : RTWF st.                  (* [comment removed for export] *)
Hypothesis HT : st_tls st' = st_tls st.   (* [comment removed for export] *)

Lemma R_consts_iaz :
  R_consts st m ->
  (exists oom : byte, rw_cells bsegs m' A_ALLOC_OOM [C1 oom]) ->
  rw_cells bsegs m' A_IA_INITED [W1 (if st_ia_inited st' then 1 else 0); W1 0; W1 0; W1 0] ->
  R_consts st' m'.
Proof.
  intros H H15' H20'. unfold R_consts in *. unfold R_emb, emb_d, emb_sz in *. rewrite HT.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & _ & H16 & H17 & H18 & H19 & _ & H21 & H22 & H23 & H24 & H25 & H26 & H27 & [(j0 & j1 & H28) H29]).
  Local Ltac trc H := first [ eapply (roT W m m' MU _ _ H) | eapply (rwT W m m' MU WM _ _ H) ]; apply ZW;
    unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
      A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
      A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP, IAZ_LO, CEIL; cbn; lia.
  split; [trc H1|]. split; [trc H2|]. split; [trc H3|]. split; [trc H4|]. split; [trc H5|]. split; [trc H6|].
  split; [trc H7|]. split; [trc H8|]. split; [trc H9|]. split; [trc H10|]. split; [trc H11|]. split; [trc H12|].
  split; [trc H13|]. split; [trc H14|]. split; [exact H15'|]. split; [trc H16|]. split; [trc H17|].
  split; [trc H18|]. split; [trc H19|]. split; [exact H20'|]. split; [trc H21|]. split; [trc H22|]. split; [trc H23|]. split; [trc H24|].
  split; [trc H25|]. split; [trc H26|]. split; [trc H27|].
  split; [exists j0, j1; trc H28|].
  intros Hd. eapply stk_wmono_noseg; [exact (H29 Hd)| exact WM|].
  pose proof (emb_block_range st WF Hd) as (E1 & _). unfold emb_d in E1. unfold AIMG_HI, KHIGHMEM_BEG in *. blia.
Qed.
End CONSTS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma set_ia_inited_true : forall st, st_ia_inited st = true -> set_ia_inited st = st.
Proof. intros st H. destruct st; cbn in *. subst. reflexivity. Qed.
Lemma st_ia_inited_set : forall st, st_ia_inited (set_ia_inited st) = true.
Proof. intros st. destruct st; reflexivity. Qed.
Lemma RTREP_set_ia : forall st m,
  R_link m -> R_consts (set_ia_inited st) m -> R_alloc st m -> R_rinfo st m -> R_regions st m -> R_avail st m ->
  R_cache st m -> R_thread st m -> R_live st m -> R_quar st m -> R_batches st m -> R_ptrarr st m -> R_depot st m ->
  R_fs st m -> R_ia m -> R_lowshadow m -> RTREP (set_ia_inited st) m.
Proof. intros st m. destruct st; cbn. intros; constructor; assumption. Qed.


End CeilWrap.
