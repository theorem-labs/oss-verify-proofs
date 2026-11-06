(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanPlace AsanTotal.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (AsanNodeSem.aok ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

Definition qframe (st st' : astate) : Prop :=
  a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st
  /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st
  /\ a_emb st' = a_emb st
  /\ ucnt_keep st st'.
Lemma qframe_refl : forall st, qframe st st. Proof. intros. unfold qframe. repeat (split; [reflexivity|]). apply ucnt_keep_refl. Qed.
Lemma qframe_trans : forall a b c, qframe a b -> qframe b c -> qframe a c.
Proof. intros a b c (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10) (B1&B2&B3&B4&B5&B6&B7&B8&B9&B10). unfold qframe. repeat (split; [congruence|]). exact (ucnt_keep_trans _ _ _ A10 B10). Qed.
Lemma qframe_same_but : forall c st st', same_but c st st' ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) -> c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) -> qframe st st'.
Proof.
  intros c st st' (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&H13) EA EM. unfold qframe. repeat (split; [assumption|]).
  intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [split; assumption|]. rewrite (H12 c' NE). split; reflexivity.
Qed.
Lemma qframe_put : forall c r st, c_allocated_user r = c_allocated_user (get_cls st c) -> c_mapped_user r = c_mapped_user (get_cls st c) -> qframe st (put_cls c r st).
Proof.
  intros c r st EA EM. unfold qframe. cbn. repeat (split; [reflexivity|]).
  intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite get_put_eq; split; assumption|]. rewrite get_put_ne by congruence. split; reflexivity.
Qed.
Lemma qframe_init_cache : forall st, qframe st (init_cache st).
Proof. intros. unfold qframe. rewrite <- (ucnt_keep_cls_eq st (init_cache st)) || idtac. unfold init_cache. destruct (a_cinit st); (repeat (split; [reflexivity|])); apply ucnt_keep_cls_eq; reflexivity. Qed.
Lemma qframe_lists : forall pc pb st st', qframe st st' ->
  all_chunks pc pb st' = all_chunks pc pb st /\ qbatches pb st' = qbatches pb st /\ CHX pc pb st' = CHX pc pb st.
Proof. intros pc pb st st' (H1&H2&H3&H4&H5&H6&_&_&H9&_). unfold CHX, emb_ent, CH, all_chunks, qbatches, live_chunks. rewrite H1, H3, H5, H9. repeat split; reflexivity. Qed.
Lemma qframe_ucnt : forall st st', qframe st st' -> ucnt_keep st st'.
Proof. intros st st' (_&_&_&_&_&_&_&_&_&U). exact U. Qed.

Lemma cache_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> AM R) mo,
  INV (CPrim c n :: pc) pb st mo -> 1 <= c <= 31 ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (cache_dealloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hc HSB Hk.
  pose proof (INV_init_cache _ _ _ _ HI) as HI1.
  pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  rewrite max_count_init_cache in C9. rewrite all_chunks_cons, cntP_cons in C10. cbn [is_prim_of] in C10. rewrite Z.eqb_refl in C10.
  assert (Hwfpc : Forall chunk_wf pc) by (destruct HA1 as (_ & HW & _); rewrite all_chunks_cons in HW; apply Forall_cons_iff in HW as [_ HW]; unfold all_chunks in HW; apply Forall_app in HW as [X _]; exact X).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb (init_cache st)) /\ 0 <= nbatch c (qbatches pb (init_cache st))).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (F : 32 <= size_of_class c <= 65536 /\ 2 <= max_cached c <= 16).
  { destruct HA1 as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    pose proof (prim_cls_facts c n Hn Hcl) as F. lia. }
  destruct F as [Hsz Hmc'].
  unfold cache_dealloc. cbv zeta. rewrite max_count_init_cache.
  destruct (Z.eqb_spec (c_count (get_cls (init_cache st) c)) (max_cached c)) as [Hfull|Hnf].
  -
    assert (Hhalf : 1 <= max_cached c / 2 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split; [apply Z.div_le_lower_bound; lia| apply Z.mul_div_le; lia]. }
    assert (Hm8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
    set (m := max_cached c / 2) in *. clearbody m.
    assert (Hnf8 : 4 * (c_num_freed (get_cls (init_cache st) c) + m) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (size_of_class c * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (c_allocated_user (get_cls (init_cache st) c)); [|lia]. rewrite C10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (32 * c_num_freed (get_cls (init_cache st) c) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size_of_class c * c_num_freed (get_cls (init_cache st) c)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      assert (m <= 8) by lia.
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    apply (ensure_ok R P (CPrim c n :: pc) pb (init_cache st) c (c_num_freed (get_cls (init_cache st) c) + m) _ mo HI1 Hc ltac:(lia) Hnf8).
    { rewrite CHX_cons. cbn [sec_of app]. rewrite CHX_init_cache. exact HSB. }
    intros st2 mo2 HI2 HSB2 E1 E2 E3 E4 E5. cbn [negb].
    pose proof HI2 as [HA2 HM2].
    destruct (qframe_lists (CPrim c n :: pc) pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2 E2 E1)) as (AC1 & AC2 & AC3).
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *.
        destruct (qframe_lists pc pb (init_cache st) st2 (qframe_same_but _ _ _ HSB2 E2 E1)) as (AC1' & AC2' & AC3').
        rewrite all_chunks_cons, cntP_cons in D10. cbn [is_prim_of] in D10. rewrite Z.eqb_refl in D10.
        rewrite AC1', AC2' in D10 |- *. rewrite E1, E2, E3, E4 in *. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
      * cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. eapply qframe_trans; [exact (qframe_same_but c _ _ HSB2 E2 E1)|]. apply qframe_put; reflexivity.
  -
    apply Hk.
    + apply (INV_repc (CPrim c n :: pc)); auto.
      * intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
      * unfold CLSOK. cproj. rewrite max_count_init_cache. repeat split; try lia.
      * unfold cls_mapped_bytes'. cproj. lia.
      * cproj. lia.
    + eapply qframe_trans; [apply qframe_init_cache|]. apply qframe_put; reflexivity.
Qed.

Lemma large_dealloc_ok : forall R (P : R -> Model -> Prop) pc pb st mb ms n (k : astate -> AM R) mo,
  INV (CSec mb ms n :: pc) pb st mo ->
  zsum2 (CHX (CSec mb ms n :: pc) pb st) <= 2^37 ->
  (forall mo', INV pc pb (set_nsec (a_nsec st - 1) st) mo' -> atot (k (set_nsec (a_nsec st - 1) st)) mo' P) ->
  atot (large_dealloc st mb ms k) mo P.
Proof.
  intros R P pc pb st mb ms n k mo HI HSB Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_dealloc, poison0.

  assert (TAIL : forall mo1, INV (CSec mb (sec_map_size n) n :: pc) pb st mo1 ->
            atot (ev (AMunmap mb (sec_map_size n)) (fun r => if r =? 0 then k (set_nsec (a_nsec st - 1) st)
                     else if is_err r then aundef_ USpin (k (set_nsec (a_nsec st - 1) st)) else aundef_ UBadAnswer (k (set_nsec (a_nsec st - 1) st)))) mo1 P).
  { intros mo1 HI1. unfold ev. apply atotal_vis.
    { apply (INV_munmap_aok _ _ _ _ mb (sec_map_size n) HI1); try lia.
      - rewrite CHX_cons. cbn. left. reflexivity.
      - unfold LS_LO, ACEIL in *. lia. }
    intros z mo2 Hpost. cbn [apost] in Hpost. destruct Hpost as [-> ->]. rewrite Z.eqb_refl.
    apply Hk.
    assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML.
    destruct HI1 as [HA1 HM1]. split.
    - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
      cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
      rewrite all_chunks_set_nsec. change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st).
      change (CH pc pb (set_nsec (a_nsec st - 1) st)) with (CH pc pb st).
      rewrite all_chunks_cons in *. rewrite CH_cons in H6. cbn [sec_of app] in H6. rewrite zlen_cons in H6.
      split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
               rewrite all_chunks_set_nsec. rewrite all_chunks_cons, cntP_cons in X. cbn [is_prim_of] in X.
               change (qbatches pb (set_nsec (a_nsec st - 1) st)) with (qbatches pb st). rewrite Z.add_0_l in X. exact X. }
      split. { apply Forall_cons_iff in H2 as [_ H2]. exact H2. }
      split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [lia|]. split; [exact H7|]. split; [exact H8|].
      unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
    - change (CHX pc pb (set_nsec (a_nsec st - 1) st)) with (CHX pc pb st).
      rewrite CHX_cons in HM1. cbn [sec_of app] in HM1.
      apply (AMI_munmap [] (CHX pc pb st) st); auto; try lia; try (unfold LS_LO, ACEIL in *; lia); try (intros c0 _; apply Z.le_refl).
      unfold commit_bytes, csum, get_cls. cbn. lia. }
  unfold flush_shadow. cbv zeta.
  destruct (Z.ltb_spec (flush_beg mb) (flush_end mb (sec_map_size n))) as [FL|NFL]; [| exact (TAIL mo HI)].
  apply atotal_vis.
  { apply (INV_madvise_aok _ _ _ _ mb (sec_map_size n) HI); first [lia| exact Hrange]. }
  intros z mo1 Hpost. cbn [apost] in Hpost. destruct Hpost as [-> ->]. rewrite Z.eqb_refl. exact (TAIL mo HI).
Qed.

Lemma recycle_chunk_ok : forall R (P : R -> Model -> Prop) pc pb st ch (k : astate -> AM R) mo,
  INV (ch :: pc) pb st mo -> zsum2 (CHX (ch :: pc) pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (recycle_chunk st ch k) mo P.
Proof.
  intros R P pc pb st ch k mo HI HSB Hk. unfold recycle_chunk. destruct ch as [c n|mb ms n].
  - pose proof HI as [HA _]. pose proof HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _]. cbn in Hwf. destruct Hwf as [Hn Hcl].
    pose proof (prim_cls_facts c n Hn Hcl) as F.
    apply (cache_dealloc_ok R P pc pb st c n k mo HI ltac:(lia)).
    + rewrite CHX_cons in HSB. cbn [sec_of app] in HSB. exact HSB.
    + exact Hk.
  - apply (large_dealloc_ok R P pc pb st mb ms n k mo HI HSB).
    intros mo' HI'. apply Hk; [exact HI'|]. unfold qframe. cbn. repeat split; reflexivity.
Qed.

Lemma recycle_chunks_ok : forall R (P : R -> Model -> Prop) l pc pb st (k : astate -> AM R) mo,
  INV (l ++ pc) pb st mo -> zsum2 (CHX (l ++ pc) pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (recycle_chunks st l k) mo P.
Proof.
  intros R P l. induction l as [|ch l IH]; intros pc pb st k mo HI HSB Hk; cbn [recycle_chunks app] in *.
  - apply Hk; [exact HI| apply qframe_refl].
  - apply (recycle_chunk_ok R P (l ++ pc) pb st ch _ mo HI HSB).
    intros st1 mo1 HI1 HQ1. apply (IH pc pb st1 k mo1 HI1).
    + destruct (qframe_lists (l ++ pc) pb st st1 HQ1) as (_ & _ & ->). rewrite CHX_cons in HSB. rewrite zsum2_app in HSB.
      assert (0 <= zsum2 (sec_of ch)).
      { destruct HI as [HA _]. destruct HA as (_ & HW & _). rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf _].
        destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct Hwf as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
      lia.
    + intros st2 mo2 HI2 HQ2. apply Hk; [exact HI2|]. eapply qframe_trans; eassumption.
Qed.

Lemma zsum2_perm : forall l l', Permutation l l' -> zsum2 l = zsum2 l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.

Lemma AINV_requeue : forall pc pb pb' st ql lb qg gb,
  AINV pc pb st ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  AINV pc pb' (set_qglob qg gb (set_qloc ql lb st)).
Proof.
  intros pc pb pb' st ql lb qg gb HA HP HL HB Hlb Hgb. unfold AINV in *.
  destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_qglob set_qloc a_cinit] in *.
  assert (Hq : qbatches pb' (set_qglob qg gb (set_qloc ql lb st)) = pb' ++ ql ++ qg) by reflexivity.
  assert (HPa : Permutation (all_chunks pc pb' (set_qglob qg gb (set_qloc ql lb st))) (all_chunks pc pb st)).
  { unfold all_chunks. rewrite Hq. unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. exact HP. }
  rewrite Hq.
  split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_qglob set_qloc] in *.
           rewrite Hq. rewrite (cntP_perm c _ _ HPa). unfold nbatch in *. rewrite HL. exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
  split; [exact HB|]. split; [exact Hlb|]. split; [exact Hgb|].
  split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  unfold live_budget, live_chunks in *. cbn [a_live set_qglob set_qloc]. exact H13.
Qed.

Lemma INV_requeue : forall pc pb pb' st ql lb qg gb mo,
  INV pc pb st mo ->
  Permutation (qchunks (pb' ++ ql ++ qg)) (qchunks (qbatches pb st)) ->
  zlen (pb' ++ ql ++ qg) = zlen (qbatches pb st) ->
  Forall batch_wf (pb' ++ ql ++ qg) -> lb = bsum ql -> gb = bsum qg ->
  INV pc pb' (set_qglob qg gb (set_qloc ql lb st)) mo.
Proof.
  intros pc pb pb' st ql lb qg gb mo [HA HM] HP HL HB Hlb Hgb. split; [eapply AINV_requeue; eauto|].
  apply (AMI_perm (CHX pc pb st)).
  - unfold CHX; apply Permutation_app; [| apply Permutation_refl]; unfold CH. apply secs_perm. unfold all_chunks. change (qbatches pb' (set_qglob qg gb (set_qloc ql lb st))) with (pb' ++ ql ++ qg).
    unfold live_chunks. cbn [a_live set_qglob set_qloc]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact HP.
  - apply (AMI_mono _ st); auto; [unfold commit_bytes, csum, get_cls; cbn; lia| intros c0 _; apply Z.le_refl].
Qed.

Definition shell : achunk := CPrim K_BATCH_CLASS 7000.
Lemma shell_class : class_id (needed_size 7000) = K_BATCH_CLASS. Proof. vm_compute. reflexivity. Qed.
Lemma shell_wf : chunk_wf shell. Proof. cbn -[class_id needed_size]. split; [lia|]. left. symmetry. exact shell_class. Qed.

Lemma INV_open_batch : forall pc b pb st mo,
  INV pc (b :: pb) st mo -> INV (rev (b_chunks b) ++ shell :: pc) pb st mo.
Proof.
  intros pc b pb st mo [HA HM].
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }

    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons. cbn [is_prim_of shell].
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons in X.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true by reflexivity. lia. }
             replace (K_BATCH_CLASS =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa|]. constructor; [apply shell_wf| exact H2]. }
    split. { apply Forall_cons_iff in H3 as [_ H3]. exact H3. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. symmetry. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CHX pc (b :: pb) st)); [| exact HM]. unfold CHX; apply Permutation_app; [| apply Permutation_refl]; unfold CH. etransitivity; [| apply secs_perm; apply Permutation_sym; exact HPa]. cbn. apply Permutation_refl.
Qed.

Lemma do_recycle_ok : forall R (P : R -> Model -> Prop) bs pc st (k : astate -> AM R) mo,
  INV pc bs st mo -> zsum2 (CHX pc bs st) <= 2^37 ->
  (forall st' mo', INV pc [] st' mo' -> qframe st st' -> atot (k st') mo' P) ->
  atot (do_recycle st bs k) mo P.
Proof.
  intros R P bs. induction bs as [|b bs IH]; intros pc st k mo HI HSB Hk; cbn [do_recycle].
  - apply Hk; [exact HI| apply qframe_refl].
  - pose proof (INV_open_batch _ _ _ _ _ HI) as HI1.
    assert (HPC : Permutation (CH (rev (b_chunks b) ++ shell :: pc) bs st) (CH pc (b :: bs) st)).
    { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite !secs_app, secs_cons. cbn [sec_of shell]. rewrite app_nil_l. rewrite <- !app_assoc.
      eapply Permutation_trans. { apply Permutation_app_tail. apply secs_perm. apply Permutation_sym. apply Permutation_rev. }
      rewrite (app_assoc (secs pc) (secs (live_chunks st))). rewrite (app_assoc (secs pc) (secs (live_chunks st)) (secs (b_chunks b) ++ _)).
      apply Permutation_app_swap_app. }
    apply (recycle_chunks_ok R P (rev (b_chunks b)) (shell :: pc) bs st _ mo HI1).
    + rewrite ?zsum2_CHX in *. rewrite (zsum2_perm _ _ HPC). exact HSB.
    + intros st1 mo1 HI2 HQ1. apply (cache_dealloc_ok R P pc bs st1 K_BATCH_CLASS 7000 _ mo1 HI2 ltac:(unfold K_BATCH_CLASS; lia)).
      * destruct (qframe_lists pc bs st st1 HQ1) as (_ & _ & ->). rewrite ?zsum2_CHX in *.
        pose proof (zsum2_perm _ _ HPC) as E. rewrite CH_cons in E || idtac.
        assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
        { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
          assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
          destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
          apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
          clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
          specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
        lia.
      * intros st2 mo2 HI3 HQ2. apply (IH pc st2 k mo2 HI3).
        -- destruct (qframe_lists pc bs st st2 (qframe_trans _ _ _ HQ1 HQ2)) as (_ & _ & ->). rewrite ?zsum2_CHX in *.
           pose proof (zsum2_perm _ _ HPC).
           assert (E2 : zsum2 (CH pc bs st) <= zsum2 (CH pc (b :: bs) st)).
           { unfold CH, all_chunks. rewrite qbatches_cons, qchunks_cons, !secs_app, !zsum2_app.
             assert (0 <= zsum2 (secs (b_chunks b))); [|lia].
             destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. rewrite qbatches_cons, qchunks_cons in HW.
             apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [_ HW]. apply Forall_app in HW as [HW _].
             clear - HW. induction (b_chunks b) as [|ch l IHl]; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. rewrite secs_cons, zsum2_app.
             specialize (IHl HW). destruct ch as [c n|mb ms n]; cbn in *; [lia|]. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
           lia.
        -- intros st3 mo3 HI4 HQ3. apply Hk; [exact HI4|]. eapply qframe_trans; [exact HQ1|]. eapply qframe_trans; eassumption.
Qed.

Lemma merge_batches_spec : forall rest cur,
  Forall batch_wf (cur :: rest) ->
  let '(l, ex, exb) := merge_batches cur rest in
  Permutation (qchunks (l ++ ex)) (qchunks (cur :: rest)) /\ zlen (l ++ ex) = zlen (cur :: rest)
  /\ bsum l + exb = bsum (cur :: rest) /\ bsum ex = exb /\ Forall batch_wf (l ++ ex) /\ 0 <= exb.
Proof.
  induction rest as [|nx rest IH]; intros cur HB.
  - cbn [merge_batches]. rewrite app_nil_r. cbn [bsum]. rewrite zlen_cons, zlen_nil. repeat split; auto; lia.
  - cbn [merge_batches]. apply Forall_cons_iff in HB as [Hc HB]. pose proof HB as HB0. apply Forall_cons_iff in HB as [Hn HB].
    destruct (Z.leb_spec (b_count cur + b_count nx) Q_BATCH) as [Hle|Hgt].
    + set (cur' := mkABatch (b_count cur + b_count nx) (b_size cur + (b_size nx - Q_BATCH_BYTES)) (b_chunks nx ++ b_chunks cur)).
      assert (Hc' : batch_wf cur').
      { destruct Hc as (C1 & C2 & C3 & C4). destruct Hn as (N1 & N2 & N3 & N4). unfold batch_wf, cur'. cbn [b_count b_size b_chunks].
        rewrite zlen_app, zsumc_app. repeat split; try lia. apply Forall_app; split; assumption. }
      specialize (IH cur' ltac:(constructor; assumption)). destruct (merge_batches cur' rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * rewrite !qchunks_app in *. rewrite qchunks_cons. cbn [b_chunks app]. rewrite !qchunks_cons.
        eapply Permutation_trans. { rewrite app_nil_l || idtac. exact I1. }
        rewrite qchunks_cons. unfold cur'. cbn [b_chunks]. rewrite <- app_assoc. eapply Permutation_trans; [apply Permutation_app_swap_app|]. rewrite app_assoc. apply Permutation_refl.
      * rewrite !zlen_app, !zlen_cons in *. lia.
      * cbn [bsum] in *. unfold cur' in I3. cbn [b_size] in I3. lia.
      * cbn [bsum b_size]. lia.
      * apply Forall_app in I5 as [I5a I5b]. apply Forall_app. split; [exact I5a|]. constructor; [|exact I5b].
        unfold batch_wf. cbn. unfold Q_BATCH, Q_BATCH_BYTES. repeat split; try lia. constructor.
      * unfold Q_BATCH_BYTES. lia.
    + specialize (IH nx HB0). destruct (merge_batches nx rest) as [[l ex] exb]. destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
      split; [|split; [|split; [|split; [|split]]]].
      * cbn [app]. rewrite !qchunks_cons. apply Permutation_app_head. exact I1.
      * cbn [app]. rewrite !zlen_cons in *. lia.
      * cbn [bsum] in *. lia.
      * exact I4.
      * cbn [app]. constructor; assumption.
      * exact I6.
Qed.

Lemma dequeue_while_spec : forall l bytes mn,
  let '(taken, rest, bytes') := dequeue_while l bytes mn in
  taken ++ rest = l /\ bytes' = bytes - bsum taken /\ (bytes' <= mn \/ rest = []).
Proof.
  induction l as [|b l IH]; intros bytes mn; cbn [dequeue_while].
  - repeat split; auto. cbn. lia.
  - destruct (Z.ltb_spec mn bytes).
    + specialize (IH (bytes - b_size b) mn). destruct (dequeue_while l (bytes - b_size b) mn) as [[taken rest] bytes'].
      destruct IH as (I1 & I2 & I3). cbn [app bsum]. rewrite I1. repeat split; auto. lia.
    + repeat split; auto. cbn. lia.
Qed.

Lemma set_qloc_eta : forall st, set_qloc (a_qloc st) (a_qloc_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.
Lemma set_qglob_eta : forall st, set_qglob (a_qglob st) (a_qglob_bytes st) st = st.
Proof. intros st. destruct st; reflexivity. Qed.

Lemma INV_pc_perm : forall pc pc' pb st mo, Permutation pc pc' -> INV pc pb st mo -> INV pc' pb st mo.
Proof.
  intros pc pc' pb st mo HP [HA HM].
  assert (HPa : Permutation (all_chunks pc' pb st) (all_chunks pc pb st)) by (unfold all_chunks; apply Permutation_app_tail; apply Permutation_sym; exact HP).
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa). exact X. }
    split. { eapply Permutation_Forall; [apply Permutation_sym; exact HPa| exact H2]. }
    split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. apply Permutation_sym. exact HPa. }
    exact H7.
  - apply (AMI_perm (CHX pc pb st)); [| exact HM]. unfold CHX; apply Permutation_app; [| apply Permutation_refl]; unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
Qed.

Lemma INV_close_batch : forall pc b pb st mo,
  INV (rev (b_chunks b) ++ shell :: pc) pb st mo -> batch_wf b -> INV pc (b :: pb) st mo.
Proof.
  intros pc b pb st mo [HA HM] Hb.
  assert (HPa : Permutation (all_chunks (rev (b_chunks b) ++ shell :: pc) pb st) (shell :: all_chunks pc (b :: pb) st)).
  { unfold all_chunks. rewrite qbatches_cons, qchunks_cons. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans. { apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    rewrite (app_assoc pc). rewrite (app_assoc pc (live_chunks st)).
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    apply Permutation_app_swap_app. }
  split.
  - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    rewrite qbatches_cons in *.
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. rewrite (cntP_perm c _ _ HPa), cntP_cons in X. cbn [is_prim_of shell] in X.
             unfold nbatch in *. rewrite qbatches_cons, zlen_cons.
             destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|Hne].
             { replace (K_BATCH_CLASS =? K_BATCH_CLASS) with true in X by reflexivity. lia. }
             replace (K_BATCH_CLASS =? c) with false in X by (symmetry; apply Z.eqb_neq; lia). lia. }
    split. { pose proof (Permutation_Forall HPa H2) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
    split. { constructor; assumption. }
    split; [exact H4|]. split; [exact H5|].
    split. { rewrite H6. unfold CH, zlen. f_equal. etransitivity. { apply Permutation_length. apply secs_perm. exact HPa. } reflexivity. }
    exact (conj H7 (conj H8 H9)).
  - apply (AMI_perm (CHX (rev (b_chunks b) ++ shell :: pc) pb st)); [| exact HM]. unfold CHX; apply Permutation_app; [| apply Permutation_refl]; unfold CH. etransitivity; [apply secs_perm; exact HPa|]. cbn. apply Permutation_refl.
Qed.

Lemma recycle_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc st = [] -> a_qloc_bytes st = 0 -> bsum (a_qglob st) <= 2^30 ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MIN -> a_emb st' = a_emb st -> ucnt_keep st st' -> atot (k st') mo' P) ->
  atot (recycle st Q_MIN k) mo P.
Proof.
  intros R P st k mo HI Hql Hqlb HQ Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  assert (Hqb : qbatches [] st = a_qglob st) by (unfold qbatches; rewrite Hql; reflexivity).
  rewrite Hqb in HBW.
  assert (HWq : Forall chunk_wf (qchunks (a_qglob st))).
  { unfold all_chunks in HW. rewrite Hqb in HW. cbn [app] in HW. apply Forall_app in HW as [_ HW]. exact HW. }
  destruct (quarantine_class_bound 1 (a_qglob st) ltac:(lia) HBW HWq) as (_ & Hov & Hpos).
  unfold recycle. cbv zeta. rewrite Hb2.
  destruct (Z.ltb_spec (bsum (a_qglob st)) (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)))) as [X|_]; [unfold Q_BATCH_BYTES, zlen in *; lia|].

  assert (HMB : forall gl ex exb,
    (if (Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) <? bsum (a_qglob st)) && (bsum (a_qglob st) * 100 <? Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) * 200)
     then match a_qglob st with [] => ([], [], 0) | b :: rest => merge_batches b rest end
     else (a_qglob st, [], 0)) = (gl, ex, exb) ->
    Permutation (qchunks (gl ++ ex)) (qchunks (a_qglob st)) /\ zlen (gl ++ ex) = zlen (a_qglob st)
    /\ bsum gl + exb = bsum (a_qglob st) /\ bsum ex = exb /\ Forall batch_wf (gl ++ ex) /\ 0 <= exb).
  { intros gl ex exb E. destruct (_ && _).
    - destruct (a_qglob st) as [|b rest] eqn:Eq.
      + injection E as <- <- <-. cbn. repeat split; auto; try lia; try constructor.
      + pose proof (merge_batches_spec rest b HBW) as MS. rewrite E in MS. exact MS.
    - injection E as <- <- <-. rewrite app_nil_r. cbn [bsum]. repeat split; auto; lia. }
  destruct (if _ && _ then _ else _) as [[gl ex] exb] eqn:E. specialize (HMB gl ex exb eq_refl). destruct HMB as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (dequeue_while_spec gl (bsum (a_qglob st) - exb) Q_MIN) as DS.
  destruct (dequeue_while gl (bsum (a_qglob st) - exb) Q_MIN) as [[taken rest] bytes2]. destruct DS as (D1 & D2 & D3).
  assert (Hb2' : bytes2 = bsum rest) by (subst gl; rewrite bsum_app in M3; lia).
  assert (Hrest0 : 0 <= bsum rest).
  { apply Forall_app in M5 as [M5 _]. subst gl. apply Forall_app in M5 as [_ M5].
    clear - M5. induction rest as [|b rest IH]; [cbn; lia|]. apply Forall_cons_iff in M5 as [(B1&B2&B3&B4) M5]. cbn. specialize (IH M5).
    assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia. }
  destruct (Z.ltb_spec Q_MIN bytes2) as [X|_].
  { exfalso. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN in X. lia. }

  assert (HI1 : INV [] (ex ++ taken) (set_qglob rest bytes2 st) mo).
  { replace (set_qglob rest bytes2 st) with (set_qglob rest bytes2 (set_qloc (a_qloc st) (a_qloc_bytes st) st)) by (rewrite set_qloc_eta; reflexivity).
    rewrite Hql, Hqlb.
    apply (INV_requeue [] [] (ex ++ taken) st [] 0 rest bytes2 mo HI).
    - rewrite Hqb. cbn [app]. rewrite <- app_assoc. eapply Permutation_trans; [|exact M1].
      rewrite <- D1. rewrite !qchunks_app. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_refl.
    - rewrite Hqb, <- M2, <- D1. cbn [app]. rewrite !zlen_app. lia.
    - cbn [app]. rewrite <- D1 in M5. apply Forall_app in M5 as [M5a M5b]. apply Forall_app in M5a as [M5t M5r].
      apply Forall_app; split; [apply Forall_app; split; assumption| exact M5r].
    - reflexivity.
    - exact Hb2'. }
  apply (do_recycle_ok R P (ex ++ taken) [] (set_qglob rest bytes2 st) k mo HI1).
  - destruct HI1 as [HA1 _]. apply (CHX_bounds [] (ex ++ taken) (set_qglob rest bytes2 st) HA1); [| unfold zlen; cbn; lia| cbn; lia].
    unfold qbatches. cbn [a_qloc a_qglob set_qglob]. rewrite Hql. cbn [app]. rewrite !bsum_app. subst gl. rewrite bsum_app in M3. lia.
  - intros st' mo' HI' HQ'. destruct HQ' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _ & _ & Q9 & Q10). cbn in Q1, Q2, Q3, Q4, Q5, Q6, Q9.
    apply Hk; auto; try congruence; try (intros c0; exact (Q10 c0)). rewrite Q6. destruct D3 as [?|Hr]; [lia|]. subst rest. cbn in Hb2'. unfold Q_MIN. lia.
Qed.

Lemma bsum_nonneg : forall bs, Forall batch_wf bs -> 0 <= bsum bs.
Proof.
  induction bs as [|b bs IH]; intros HB; [cbn; lia|]. apply Forall_cons_iff in HB as [(B1&B2&B3&B4) HB]. cbn. specialize (IH HB).
  assert (0 <= zsumc (b_chunks b)) by (apply zsumc_nonneg; eapply Forall_impl; [|exact B4]; cbv beta; intros; lia). unfold Q_BATCH_BYTES in B3. lia.
Qed.

Lemma drain_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
  INV [] [] st mo -> a_qloc_bytes st + a_qglob_bytes st <= 2^30 ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc st' = [] -> a_qloc_bytes st' = 0 ->
     0 <= a_qglob_bytes st' <= Q_MAX -> a_emb st' = a_emb st -> ucnt_keep st st' -> atot (k st') mo' P) ->
  atot (drain st k) mo P.
Proof.
  intros R P st k mo HI HQ Hk. pose proof HI as [HA HM]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
  unfold drain. cbv zeta. cbn [a_qglob a_qglob_bytes a_qloc a_qloc_bytes set_qloc].
  set (st1 := set_qglob (a_qglob st ++ a_qloc st) (a_qglob_bytes st + a_qloc_bytes st) (set_qloc [] 0 st)).
  assert (HI1 : INV [] [] st1 mo).
  { unfold st1. apply (INV_requeue [] [] [] st [] 0 _ _ mo HI).
    - unfold qbatches. cbn [app]. rewrite !qchunks_app. apply Permutation_app_comm.
    - unfold qbatches. cbn [app]. rewrite !zlen_app. lia.
    - unfold qbatches in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app; split; assumption.
    - reflexivity.
    - rewrite bsum_app. lia. }
  assert (HBq : 0 <= bsum (a_qglob st) /\ 0 <= bsum (a_qloc st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  change (a_qglob_bytes st1) with (a_qglob_bytes st + a_qloc_bytes st).
  destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st + a_qloc_bytes st)) as [Hbig|Hsmall].
  - apply (recycle_ok R P st1 k mo HI1); try reflexivity.
    + unfold st1. cbn. rewrite bsum_app. lia.
    + intros st' mo' HI' E1 E2 E3 E4 E5 E6 E7. apply Hk; auto; try (intros c0; exact (E7 c0)). unfold Q_MIN, Q_MAX in *. lia.
  - apply Hk; auto; unfold st1; cbn; try reflexivity; try (intros c0; split; reflexivity). lia.
Qed.

Lemma is_primary_7000 : is_primary 7000 = true. Proof. reflexivity. Qed.

Lemma enqueue_ok : forall R (P : R -> Model -> Prop) st ch n (k : astate -> AM R) mo,
  INV [ch] [] st mo -> chunk_size ch = n -> 0 <= n <= Q_MAX ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  (forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st ->
     a_qglob_bytes st' = a_qglob_bytes st ->
     a_qloc_bytes st <= a_qloc_bytes st' <= a_qloc_bytes st + n + Q_BATCH_BYTES -> a_emb st' = a_emb st ->
     cls_keep K_BATCH_CLASS st st' ->
     atot (k st') mo' P) ->
  atot (enqueue st ch k) mo P.
Proof.
  intros R P st ch n k mo HI Hsz Hn Hql Hqg Hk.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  rewrite all_chunks_cons in HW. apply Forall_cons_iff in HW as [Hwf HW].
  assert (Hchsz : Forall (fun c => 0 <= chunk_size c <= Q_MAX) [ch]) by (constructor; [rewrite Hsz; lia| constructor]).

  assert (NEWB : forall st0, INV [ch] [] st0 mo -> a_live st0 = a_live st -> a_next st0 = a_next st -> a_qloc st0 = a_qloc st -> a_qloc_bytes st0 = a_qloc_bytes st ->
            a_qglob st0 = a_qglob st -> a_qglob_bytes st0 = a_qglob_bytes st -> a_emb st0 = a_emb st -> a_cls st0 = a_cls st ->
            atot (cache_alloc st0 K_BATCH_CLASS (fun st1 ok =>
                     if negb ok then aundef_ USpin (k st1)
                     else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (n + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1))) mo P).
  { intros st0 HI0 E1 E2 E3 E4 E5 E6 E7 E8. pose proof HI0 as [HA0 HM0].
    apply (cache_alloc_ok R P [ch] [] st0 K_BATCH_CLASS 7000 _ mo HI0 ltac:(lia) (or_introl (eq_sym shell_class))).
    - apply (room24_of_AINV (ATOP:=ATOP)); auto.
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + change (size_of_class K_BATCH_CLASS) with 8192. rewrite cntP_cons, cntP_nil. destruct (is_prim_of K_BATCH_CLASS ch); lia.
    - apply (CHX_bounds [ch] [] st0 HA0).
      + unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA0 as (_ & _ & _ & B1 & B2 & _). rewrite <- B1, <- B2, E4, E6. unfold Q_CACHE, Q_MAX in *. lia.
      + destruct ch; cbn; unfold zlen; cbn; lia.
      + destruct ch; cbn in *; lia.
    - intros st1 mo1 HI1 HSB1. cbn [negb].
      assert (F : a_live st1 = a_live st /\ a_next st1 = a_next st /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob st1 = a_qglob st /\ a_qglob_bytes st1 = a_qglob_bytes st /\ a_emb st1 = a_emb st).
      { destruct HSB1 as [X|X]; destruct X as (_&_&_&_&_&L1&L2&L3&L4&L5&L6&_&L7); [| unfold init_cache in *; destruct (a_cinit st0); cbn in *]; repeat split; congruence. }
      destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
      apply Hk; [| cbn [a_live set_qloc]; congruence| cbn [a_next set_qloc]; congruence| cbn [a_qglob_bytes set_qloc]; congruence| cbn [a_qloc_bytes set_qloc]; rewrite F4; unfold Q_BATCH_BYTES; lia| cbn [a_emb set_qloc]; exact F7|
                 intros c0 Hc0; unfold get_cls; cbn [a_cls set_qloc];
                 destruct HSB1 as [X|X]; destruct X as (_&_&_&_&_&_&_&_&_&_&_&G&_); specialize (G c0 Hc0); unfold get_cls in G; rewrite G;
                 [rewrite E8; split; reflexivity| unfold init_cache; destruct (a_cinit st0); cbn [a_cls set_cinit]; rewrite E8; split; reflexivity]].

      set (nb := mkABatch 1 (n + Q_BATCH_BYTES) [ch]).
      assert (Hnb : batch_wf nb).
      { unfold batch_wf, nb. cbn. unfold zlen. cbn. rewrite Hsz. unfold Q_BATCH. repeat split; try lia. exact Hchsz. }
      assert (HI2 : INV [] [nb] st1 mo1).
      { apply INV_close_batch; [|exact Hnb]. unfold nb. cbn [b_chunks rev app]. apply (INV_pc_perm [shell; ch]); [apply perm_swap| exact HI1]. }
      replace (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)
        with (set_qglob (a_qglob st1) (a_qglob_bytes st1) (set_qloc (a_qloc st1 ++ [nb]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)) by (destruct st1; reflexivity).
      apply (INV_requeue [] [nb] [] st1 _ _ _ _ mo1 HI2).
      + unfold qbatches. cbn [app]. rewrite !qchunks_app. cbn. fold (qchunks (a_qloc st1 ++ a_qglob st1)). rewrite qchunks_app.
        eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|]. cbn. apply Permutation_refl.
      + unfold qbatches. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      + destruct HI2 as [(_ & _ & HB2 & _) _]. unfold qbatches in HB2. cbn [app] in *. apply Forall_cons_iff in HB2 as [X Y]. apply Forall_app in Y as [Y1 Y2].
        apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
      + destruct HI2 as [(_ & _ & _ & B1 & _) _]. cbn in B1. rewrite bsum_app, <- B1. cbn. lia.
      + destruct HI2 as [(_ & _ & _ & _ & B2 & _) _]. exact B2. }
  unfold enqueue. rewrite Hsz. cbv zeta.
  destruct (rev (a_qloc st)) as [|b rl] eqn:Hrev.
  - apply NEWB; auto.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [|Hne]; [apply NEWB; auto|].

    assert (Hql' : a_qloc st = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc st)), Hrev; reflexivity).
    assert (Hb : batch_wf b).
    { unfold qbatches in HBW. rewrite Hql' in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X _]. apply Forall_app in X as [_ X]. apply Forall_cons_iff in X as [X _]. exact X. }
    set (b' := mkABatch (b_count b + 1) (b_size b + n) (ch :: b_chunks b)).
    assert (Hb' : batch_wf b').
    { destruct Hb as (B1&B2&B3&B4). unfold batch_wf, b'. cbn. rewrite zlen_cons, Hsz. repeat split; try lia. constructor; [rewrite Hsz; lia| exact B4]. }
    apply Hk; [| reflexivity| reflexivity| reflexivity| cbn [a_qloc_bytes set_qloc]; unfold Q_BATCH_BYTES; lia| reflexivity| apply cls_keep_cls_eq; reflexivity].

    assert (HI1 : INV [ch] [b] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply (INV_requeue [ch] [] [b] st); auto.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !qchunks_app. cbn. rewrite app_nil_r. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
        rewrite <- app_assoc. apply Permutation_app_swap_app.
      - unfold qbatches. rewrite Hql'. cbn [app]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
      - unfold qbatches in *. rewrite Hql' in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app in X as [X1 X2]. apply Forall_cons_iff in X2 as [X2 _].
        constructor; [exact X2|]. apply Forall_app; split; assumption.
      - rewrite Hb1, Hql', bsum_app. cbn. lia. }
    pose proof (INV_open_batch _ _ _ _ _ HI1) as HI2.
    assert (HI3 : INV [] [b'] (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)) mo).
    { apply INV_close_batch; [|exact Hb']. unfold b'. cbn [b_chunks]. cbn [rev]. rewrite <- app_assoc. cbn [app].
      apply (INV_pc_perm (rev (b_chunks b) ++ [shell; ch])); [| exact HI2].
      apply Permutation_app_head. apply perm_swap. }
    replace (set_qloc (rev (b' :: rl)) (a_qloc_bytes st + n) st)
      with (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl ++ [b']) (a_qloc_bytes st - b_size b + b_size b') (set_qglob (a_qglob st) (a_qglob_bytes st) (set_qloc (rev rl) (a_qloc_bytes st - b_size b) st)))).
    2:{ destruct st; cbn. unfold b', set_qloc, set_qglob. cbn. f_equal. lia. }
    apply (INV_requeue [] [b'] [] _ _ _ _ _ mo HI3).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !qchunks_app. cbn. fold (qchunks (rev rl ++ a_qglob st)). rewrite qchunks_app.
      rewrite app_nil_r. rewrite <- app_assoc. rewrite (app_comm_cons). apply (Permutation_app_swap_app (qchunks (rev rl)) (ch :: b_chunks b)).
    + unfold qbatches. cbn [app a_qloc a_qglob set_qglob set_qloc]. rewrite !zlen_app, !zlen_cons, !zlen_nil, ?zlen_app. lia.
    + destruct HI3 as [(_ & _ & HB3 & _) _]. unfold qbatches in HB3 |- *. cbn [app a_qloc a_qglob set_qglob set_qloc] in *. apply Forall_cons_iff in HB3 as [X Y]. apply Forall_app in Y as [Y1 Y2].
      apply Forall_app; split; [apply Forall_app; split; [exact Y1| constructor; [exact X| constructor]]| exact Y2].
    + rewrite Hb1, Hql'. rewrite !bsum_app. unfold b'. cbn [bsum b_size]. lia.
    + exact Hb2.
Qed.

Lemma size_of_class_nonneg : forall c, 1 <= c <= 31 -> 0 <= size_of_class c.
Proof.
  intros c Hc.
  assert (CHK : forallb (fun c => 0 <=? size_of_class c) (zseq 1 31) = true) by (vm_compute; reflexivity).
  apply Z.leb_le. apply (forallb_zseq (fun c => 0 <=? size_of_class c) 1 31 CHK). lia.
Qed.

Lemma INV_live_to_hand : forall st id ch mo,
  INV [] [] st mo -> (a_live st) !! id = Some ch ->
  INV [ch] [] (set_live (delete id (a_live st)) st) mo.
Proof.
  intros st id ch mo [HA HM] Hl. pose proof HA as (_ & HW0 & _).
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  assert (HPa : Permutation (all_chunks [ch] [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) (all_chunks [] [] st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches [] (set_next (a_next st) (set_live (delete id (a_live st)) st))) with (qbatches [] st).
    eapply Permutation_trans. 2:{ apply Permutation_app_tail. apply Permutation_sym. exact HPl. } cbn. apply Permutation_refl. }
  assert (E : set_live (delete id (a_live st)) st = set_next (a_next st) (set_live (delete id (a_live st)) st)) by (destruct st; reflexivity).
  rewrite E. split.
  - apply (AINV_live_perm []); auto.
    + intros id' ch' Hl'. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). apply (Hid id' ch').
      destruct (N.eq_dec id' id) as [->|Hne]; [rewrite lookup_delete_eq in Hl'; discriminate|]. rewrite lookup_delete_ne in Hl' by congruence. exact Hl'.
    + destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB & _). apply live_budget_list_iff in HLB. apply live_budget_list_iff.
      unfold live_chunks in *. cbn [a_live set_next set_live] in *.
      destruct HLB as (B1 & B2 & B3). unfold live_chunks in B1, B2, B3 |- *. cbn [a_live set_next set_live] in B1, B2, B3 |- *. split; [|split].
      * rewrite (cntP_perm K_BATCH_CLASS _ _ HPl), cntP_cons in B1. pose proof (cntP_nonneg K_BATCH_CLASS (map snd (map_to_list (delete id (a_live st))))).
        change (size_of_class K_BATCH_CLASS) with 8192 in *. destruct (is_prim_of K_BATCH_CLASS ch); nia.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)) in B2. rewrite secs_cons, length_app in B2. lia.
      * assert (EB : forall l l', Permutation l l' -> secbytes l = secbytes l') by (intros l l' P0; induction P0; cbn; try lia; [destruct x; lia| destruct x, y; lia]).
        rewrite (EB _ _ HPl) in B3. cbn in B3. destruct ch; cbn in B3; try lia.
        unfold all_chunks, live_chunks in HW0. cbn [app] in HW0. apply Forall_app in HW0 as [HW0 _].
        pose proof (Permutation_Forall HPl HW0) as X. apply Forall_cons_iff in X as [X _]. cbn in X. lia.
  - apply (AMI_perm (CHX [] [] st)).
    + unfold CHX; apply Permutation_app; [| apply Permutation_refl]; unfold CH. apply secs_perm. apply Permutation_sym. exact HPa.
    + apply (AMI_mono _ st); auto; [unfold commit_bytes, csum, get_cls; cbn; lia| intros c0 _; apply Z.le_refl].
Qed.

Definition free_post (st : astate) (id : AsanCtrl.aptr) (st' : astate) (mo' : Model) : Prop :=
  INV [] [] st' mo' /\ a_live st' = delete id (a_live st) /\ a_next st' = a_next st
  /\ a_qloc_bytes st' <= Q_CACHE /\ a_qglob_bytes st' <= Q_MAX
  /\ a_emb st' = a_emb st
  /\ cls_keep K_BATCH_CLASS st st'.

Theorem afree_core : forall st mo id ch,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> (a_live st) !! id = Some ch ->
  atot (afree st (Some id)) mo (free_post st id).
Proof.
  intros st mo id ch HI Hql Hqg Hl.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & HBW & Hb1 & Hb2 & _).
  pose proof (INV_live_to_hand st id ch mo HI Hl) as HI1.
  set (st1 := set_live (delete id (a_live st)) st) in *.
  assert (Hwf : chunk_wf ch).
  { destruct HI1 as [HA1 _]. destruct HA1 as (_ & HW1 & _). rewrite all_chunks_cons in HW1. apply Forall_cons_iff in HW1 as [X _]. exact X. }
  assert (Hszb : 0 <= chunk_size ch <= 2^32 - 2^20) by (destruct ch; cbn in Hwf |- *; lia).
  assert (HQB : 0 <= bsum (a_qloc st) /\ 0 <= bsum (a_qglob st)).
  { unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y]. split; apply bsum_nonneg; assumption. }
  unfold afree. rewrite Hl. fold st1. cbv zeta.

  assert (AFTER : forall st2 mo2, INV [] [] st2 mo2 -> a_live st2 = a_live st1 -> a_next st2 = a_next st1 ->
            0 <= a_qloc_bytes st2 -> a_qloc_bytes st2 + a_qglob_bytes st2 <= 2^30 -> a_qglob_bytes st2 <= Q_MAX -> a_emb st2 = a_emb st ->
            cls_keep K_BATCH_CLASS st st2 ->
            atot (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2) mo2 (free_post st id)).
  { intros st2 mo2 HI2 E1 E2 Hq0 Hq1 Hq2 Eemb CK2. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [Hbig|Hsmall].
    - apply (drain_ok _ _ st2 _ mo2 HI2 Hq1). intros st3 mo3 HI3 F1 F2 F3 F4 F5 F6 F7. apply atotal_ret. unfold free_post.
      rewrite F1, F2, E1, E2, F4, F6, Eemb. unfold st1. cbn -[cls_keep]. unfold Q_CACHE. split; [exact HI3|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      exact (cls_keep_trans _ _ _ _ CK2 (ucnt_cls_keep _ _ _ F7)).
    - apply atotal_ret. unfold free_post. rewrite E1, E2, Eemb. unfold st1. cbn -[cls_keep]. split; [exact HI2|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity| exact CK2]. }
  destruct (Z.leb_spec (chunk_size ch) Q_MAX) as [Hsmall|Hbig].
  -
    apply (enqueue_ok _ _ st1 ch (chunk_size ch) _ mo HI1 eq_refl ltac:(lia)); try (unfold st1; cbn; assumption).
    intros st2 mo2 HI2 E1 E2 E3 E4 E5 CK. unfold st1 in E1, E2, E3, E4, E5. cbn [a_live a_next a_qglob_bytes a_qloc_bytes a_emb set_live] in E1, E2, E3, E4, E5.
    apply AFTER; auto; try (intros c0 Hc0; exact (CK c0 Hc0)); rewrite <- ?Hb1 in E4; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *; lia.
  -
    apply (recycle_chunk_ok _ _ [] [] st1 ch _ mo HI1).
    + destruct HI1 as [HA1 _]. apply (CHX_bounds [ch] [] st1 HA1).
      * unfold qbatches, st1. cbn [app a_qloc a_qglob set_live]. rewrite bsum_app. unfold Q_CACHE, Q_MAX in *. lia.
      * destruct ch; cbn; unfold zlen; cbn; lia.
      * destruct ch; cbn in *; lia.
    + intros st2 mo2 HI2 HQ. destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _ & _ & Q9 & Q10). unfold st1 in Q1, Q2, Q3, Q4, Q5, Q6, Q9. cbn [a_live a_next a_qglob_bytes a_qloc_bytes a_qloc a_qglob a_emb set_live] in Q1, Q2, Q3, Q4, Q5, Q6, Q9.
      apply AFTER; auto; try (intros c0 Hc0; exact (Q10 c0)); rewrite ?Q4, ?Q6; unfold Q_CACHE, Q_MAX in *; lia.
Qed.

End WithResv.
