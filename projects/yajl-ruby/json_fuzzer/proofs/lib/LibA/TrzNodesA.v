(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA NodesA ImplRzA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation trzN := trzA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section TrzNodesA.
Context {St : Type}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma trzA_msys_silent : forall {A} n (dec : resp -> option A) (s : St) mo
    (K : exc (A * St) -> Model -> TSet) (T : TSet),
  minvA mo -> tree_node n ->
  (exists rsp mo' evs, nstep n mo rsp mo' evs) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs ->
     evs = [] /\ t_eq (K (match dec rsp with Some a => Ok (a, s) | None => Unr end) mo') T) ->
  (forall code mo', ~ nexit n mo code mo') ->
  T [] ->
  trzN (msys n dec s) mo K T.
Proof.
  intros A n dec s mo K T Hmi Hsafe Hex Hk Hnx HT.
  rewrite msys_unfold. apply trzA_vis_silent; try assumption.
  intros rsp mo' evs H. destruct (Hk rsp mo' evs H) as [-> Heq]. split; [reflexivity|].
  eapply trzA_conseq; [| exact Heq].
  destruct (dec rsp) as [a|]; apply trzA_ret.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trzA_ioctl : forall fd req (s : St) mo (K : exc (sret * St) -> Model -> TSet),
  minvA mo -> K (Ok (SErr ENOTTY, s)) mo [] ->
  trzN (msys (NIoctl fd req) dec_ioctl s) mo K (K (Ok (SErr ENOTTY, s)) mo).
Proof.
  intros fd req s mo K Hmi HK. apply trzA_msys_silent; try assumption.
  - left; exact I.
  - exists (efferr ENOTTY), mo, []. cbn. auto.
  - intros rsp mo' evs H. destruct (nstep_dec_ioctl _ _ _ _ _ _ H) as (D & -> & ->). rewrite D. split; [reflexivity | apply t_eq_refl].
  - intros code mo' H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trzA_close : forall fd (s : St) mo (K : exc (sret * St) -> Model -> TSet),
  minvA mo -> 3 <= fd < 2^32 ->
  K (Ok (fst (close_out fd mo), s)) (snd (close_out fd mo)) [] ->
  trzN (msys (NClose fd) dec_close s) mo K (K (Ok (fst (close_out fd mo), s)) (snd (close_out fd mo))).
Proof.
  intros fd s mo K Hmi Hfd HK. apply trzA_msys_silent; try assumption.
  - left; exact I.
  - unfold close_out in *. cbn [nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:E.
    + exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo), []. repeat split; auto; lia.
    + exists (efferr EBADF), mo, []. repeat split; auto; lia.
  - intros rsp mo' evs H. destruct (nstep_dec_close _ _ _ _ _ H) as (-> & a & D & Ha). rewrite D.
    split; [reflexivity|]. unfold close_out.
    destruct a as [e|v].
    + destruct Ha as (-> & -> & E). rewrite E. apply t_eq_refl.
    + destruct Ha as (-> & NE & ->). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); [apply t_eq_refl | congruence].
  - intros code mo' H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma trzA_exit : forall c (s : St) mo (K : exc (Empty_set * St) -> Model -> TSet),
  minvA mo ->
  trzN (msys (NExit c) dec_exit s) mo K (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros c s mo K Hmi. rewrite msys_unfold.
  set (code := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)).
  assert (HX : nexit (NExit c) mo code (with_halted code mo)) by (split; reflexivity).
  eapply trzA_conseq.
  - apply (trzA_vis (NExit c) _ mo K (fun _ _ _ => t_nil)
             (inr (exist _ (code, with_halted code mo) HX)) Hmi (or_intror (ex_intro _ c eq_refl))).
    intros rsp mo' evs H. exfalso. exact H.
  - apply t_eq_alt_const.
    + exact (inhabits (inr (exist _ (code, with_halted code mo) HX))).
    + intros [[[[rsp mo'] evs] Hst] | [[code' mo'] Hxt]]; cbn [ansA fst snd].
      * exfalso. exact Hst.
      * pose proof Hxt as [E1 E2]. cbn [fst snd] in E1, E2. subst code' mo'. rewrite m_fs_with_halted. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trzA_read : forall fd buf count (s : St) mo (K : exc (read_ans * St) -> Model -> TSet) a mo',
  minvA mo -> 0 < count < 2^64 ->
  read_out fd buf count mo = Some (a, mo') ->
  K (Ok (a, s)) mo' [] ->
  trzN (msys (NRead fd buf count) (dec_read buf count) s) mo K (K (Ok (a, s)) mo').
Proof.
  intros fd buf count s mo K a mo' Hmi Hc RO HK. apply trzA_msys_silent; try assumption.
  - left; exact I.
  - unfold read_out in RO. cbn [nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
    + destruct (fs_lookup (m_fs mo) p) as [data|] eqn:F; [|discriminate].
      eexists _, _, []. split; [reflexivity|]. split; reflexivity.
    + exists (efferr EISDIR), mo, []. auto.
    + exists (efferr EBADF), mo, []. auto.
  - intros rsp mo1 evs H. assert (Hc' : 0 <= count < 2^64) by lia. destruct (nstep_dec_read _ _ _ _ _ _ _ Hc' H) as (-> & a1 & D & Ha). rewrite D.
    split; [reflexivity|]. unfold read_out in RO.
    destruct a1 as [e|bs].
    + destruct Ha as (-> & [(-> & E) | (-> & E)]); rewrite E in RO; inversion RO; subst; apply t_eq_refl.
    + destruct Ha as (p & off & data & E & F & -> & ->). rewrite E, F in RO. inversion RO; subst. apply t_eq_refl.
  - intros code mo1 H. exact H.
Qed.

(* [comment removed for export] *)
Lemma read_out_totalA : forall fd buf count mo,
  minvA mo -> 3 <= fd < 2^32 -> exists a mo', read_out fd buf count mo = Some (a, mo').
Proof.
  intros fd buf count mo Hmi Hfd. unfold read_out.
  destruct Hmi as (_ & _ & _ & Hch & Hfile & Hkind & _).
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:E; [|eauto].
  pose proof (Hkind _ _ E) as HK. destruct e as [ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]; try contradiction; eauto.
  - pose proof (Hch _ _ E) as H3. rewrite unsigned_lit in H3 by lia. lia.
  - destruct (fs_lookup (m_fs mo) p) eqn:F; [eauto|]. exfalso. exact (Hfile _ _ _ E F).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma trzA_open_errno : forall path e (s : St) mo (K : exc (sret * St) -> Model -> TSet),
  minvA mo -> open_classify path mo = OcErrno e ->
  K (Ok (SErr e, s)) mo [] ->
  trzN (msys (NOpen path) dec_open s) mo K (K (Ok (SErr e, s)) mo).
Proof.
  intros path e s mo K Hmi HC HK.
  assert (He : 1 <= e <= 4095).
  { unfold open_classify in HC. destruct (path_max <=? length path)%nat. { inversion HC. unfold ENAMETOOLONG; lia. }
    destruct path; [inversion HC; unfold ENOENT; lia|]. destruct (path_is_dirref _); [discriminate|].
    destruct (fs_lookup _ _); [discriminate|]. inversion HC. unfold ENOENT; lia. }
  apply trzA_msys_silent; try assumption.
  - left; exact I.
  - exists (efferr e), mo, []. apply nstep_open_iff. rewrite HC. auto.
  - intros rsp mo' evs H. apply nstep_open_iff in H. rewrite HC in H. destruct H as (-> & -> & ->).
    unfold dec_open. rewrite dec_plain_err by exact He. split; [reflexivity | apply t_eq_refl].
  - intros code mo' H. exact H.
Qed.

(* [comment removed for export] *)
Lemma trzA_open_may : forall path ent (s : St) mo (K : exc (sret * St) -> Model -> TSet) (TA TB : TSet),
  minvA mo -> open_classify path mo = OcMay ent ->
  let fd := alloc_fd (m_fds mo) in
  fd_lookup (m_fds mo) fd = None -> 3 <= bv_unsigned fd <= 4096 ->
  (forall e, In e openat_errnos -> t_eq (K (Ok (SErr e, s)) mo) TA) ->
  t_eq (K (Ok (SVal (bv_unsigned fd), s)) (with_fds (fd_insert (m_fds mo) fd ent) mo)) TB ->
  TA [] -> TB [] ->
  trzN (msys (NOpen path) dec_open s) mo K (t_alt2 TA TB).
Proof.
  intros path ent s mo K TA TB Hmi HC fd Hfree Hfd HA HB HA0 HB0.
  rewrite msys_unfold.
  assert (HokB : nstep (NOpen path) mo (eff0 fd) (with_fds (fd_insert (m_fds mo) fd ent) mo) []).
  { apply nstep_open_iff. rewrite HC. split; [reflexivity|]. right. auto. }
  assert (HokA : nstep (NOpen path) mo (efferr ENOMEM) mo []).
  { apply nstep_open_iff. rewrite HC. split; [reflexivity|]. left. exists ENOMEM. split; [cbn; auto| auto]. }
  eapply trzA_conseq.
  - apply (trzA_vis (NOpen path) _ mo K
             (fun rsp mo' evs => K (match (match dec_open rsp with Some a => Some (a, s) | None => None end) with
                              | Some p => Ok p | None => Unr end) mo')
             (inl (exist _ (eff0 fd, with_fds (fd_insert (m_fds mo) fd ent) mo, []) HokB)) Hmi (or_introl I)).
    intros rsp mo' evs H. cbn. destruct (dec_open rsp) as [a|]; apply trzA_ret.
  - (* [comment removed for export] *)
    intros tr. split.
    + intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; [| exfalso; exact Hxt].
      cbn [ansA fst snd] in Hi.
      pose proof Hst as Hst'. cbn [fst snd] in Hst'. apply nstep_open_iff in Hst'. rewrite HC in Hst'. destruct Hst' as [-> HR].
      apply t_emit_nil_l in Hi. destruct Hi as [-> | Hi].
      { left. exact HA0. }
      destruct HR as [(e & HIn & -> & ->) | (Hlk & -> & ->)].
      * left. apply (HA e HIn). unfold dec_open in Hi. rewrite dec_plain_err in Hi by (apply openat_errnos_range; exact HIn). exact Hi.
      * right. apply HB.
        (* [comment removed for export] *)
        assert (E : dec_open (eff0 (alloc_fd (m_fds mo))) = Some (SVal (bv_unsigned fd))).
        { unfold dec_open. change (alloc_fd (m_fds mo)) with fd.
          rewrite <- (Z_to_bv_bv_unsigned fd) at 1. apply dec_plain_val; [lia|].
          apply andb_true_intro; split; apply Z.leb_le; lia. }
        rewrite E in Hi. exact Hi.
    + intros [Ht | Ht].
      * exists (inl (exist _ (efferr ENOMEM, mo, []) HokA)). cbn [ansA fst snd]. apply t_emit_nil_l. right.
        unfold dec_open. rewrite dec_plain_err by (unfold ENOMEM; lia). apply (HA ENOMEM); [cbn; auto | exact Ht].
      * exists (inl (exist _ (eff0 fd, with_fds (fd_insert (m_fds mo) fd ent) mo, []) HokB)). cbn [ansA fst snd].
        apply t_emit_nil_l. right. unfold dec_open.
        rewrite <- (Z_to_bv_bv_unsigned fd) at 1. rewrite dec_plain_val; [apply HB; exact Ht | lia |].
        apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma trzA_writev_loop : forall fuel fd iovs (s : St) mo (K : exc (unit * St) -> Model -> TSet),
  minvA mo -> (fd = 1 \/ fd = 2) -> (length iovs <= 2)%nat ->
  (length (zconcat iovs) <= fuel)%nat -> zlength (zconcat iovs) < 2^64 ->
  K (Ok (tt, s)) mo [] ->
  trzN (writev_loop fuel fd iovs s) mo K
       (t_emit (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (zconcat iovs))) (K (Ok (tt, s)) mo)).
Proof.
  induction fuel as [|fuel IH]; intros fd iovs s mo K Hmi Hfd Hlen Hfuel H64 HK.
  - (* [comment removed for export] *)
    assert (E : zconcat iovs = []) by (destruct (zconcat iovs); [reflexivity | cbn in Hfuel; lia]).
    cbn [writev_loop]. unfold mbind, ebind. rewrite msys_unfold. cbn [ITree.bind].
    rewrite E. cbn [map to_bytes zlength length Z.of_nat].
    assert (H0 : nstep (NWritev fd (map to_bytes iovs)) mo (eff0 (Z_to_bv 64 0)) mo []).
    { cbn [nstep]. split; [reflexivity|]. left. rewrite zconcat_concat_to_bytes, E. auto. }
    eapply trzA_conseq.
    + apply (trzA_vis_silent (NWritev fd (map to_bytes iovs)) _ mo K (K (Ok (tt, s)) mo) Hmi (or_introl I)).
      * exists (eff0 (Z_to_bv 64 0)), mo, []. exact H0.
      * intros rsp mo' evs H. cbn [nstep] in H. rewrite zconcat_concat_to_bytes, E in H.
        destruct H as [-> [(_ & -> & ->) | (k & Hk & _)]]; [| cbn in Hk; lia].
        split; [reflexivity|]. unfold dec_writev. change (zlength (@nil Z)) with 0.
        rewrite dec_count_full by lia. cbn. apply trzA_ret.
      * intros code mo' H. exact H.
      * exact HK.
    + apply t_eq_sym. apply t_emit_nil_eq. exact HK.
  -     (* [comment removed for export] *)
    change (writev_loop (S fuel) fd iovs s) with
      ((k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (zlength (zconcat iovs))) ;;
        if k =? zlength (zconcat iovs) then mret tt else writev_loop fuel fd (advance_iovs iovs k)) s).
    unfold mbind at 1. unfold ebind. rewrite msys_unfold. cbn [ITree.bind].
    set (total := zlength (zconcat iovs)).
    assert (Htot : total = Z.of_nat (length (to_bytes (zconcat iovs)))) by (unfold total, zlength, to_bytes; rewrite length_map; reflexivity).
    destruct (zconcat iovs) as [|b0 bs'] eqn:EZ.
    + (* [comment removed for export] *)
      assert (H0 : nstep (NWritev fd (map to_bytes iovs)) mo (eff0 (Z_to_bv 64 0)) mo []).
      { cbn [nstep]. split; [reflexivity|]. left. rewrite zconcat_concat_to_bytes, EZ. auto. }
      eapply trzA_conseq.
      * apply (trzA_vis_silent (NWritev fd (map to_bytes iovs)) _ mo K (K (Ok (tt, s)) mo) Hmi (or_introl I)).
        -- exists (eff0 (Z_to_bv 64 0)), mo, []. exact H0.
        -- intros rsp mo' evs H. cbn [nstep] in H. rewrite zconcat_concat_to_bytes, EZ in H.
           destruct H as [-> [(_ & -> & ->) | (k & Hk & _)]]; [| cbn in Hk; lia].
           split; [reflexivity|]. unfold dec_writev. subst total. change (zlength (@nil Z)) with 0.
           rewrite dec_count_full by lia. cbn. apply trzA_ret.
        -- intros code mo' H. exact H.
        -- exact HK.
      * apply t_eq_sym. cbn [to_bytes map]. apply t_emit_nil_eq. exact HK.
    + (* [comment removed for export] *)
      set (bytes := to_bytes (b0 :: bs')) in *.
      assert (Hnb : (1 <= length bytes)%nat) by (subst bytes; cbn; lia).
      assert (HokF : nstep (NWritev fd (map to_bytes iovs)) mo (eff0 (Z_to_bv 64 total)) mo (map (WriteEv (Z_to_bv 64 fd)) bytes)).
      { cbn [nstep]. split; [reflexivity|]. right. exists total. rewrite zconcat_concat_to_bytes, EZ. fold bytes.
        split; [lia|]. split; [reflexivity|]. rewrite Htot, Nat2Z.id, firstn_all. reflexivity. }
      eapply trzA_conseq.
      * apply (trzA_vis (NWritev fd (map to_bytes iovs)) _ mo K
                 (fun rsp mo' evs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (length evs) bytes)) (K (Ok (tt, s)) mo))
                 (inl (exist _ (eff0 (Z_to_bv 64 total), mo, map (WriteEv (Z_to_bv 64 fd)) bytes) HokF)) Hmi (or_introl I)).
        -- intros rsp mo' evs H. cbn [nstep] in H. rewrite zconcat_concat_to_bytes, EZ in H. fold bytes in H.
           destruct H as [-> [(Hb & _ & _) | (k & Hk & -> & ->)]]; [subst bytes; discriminate|].
           cbn [fst snd]. unfold dec_writev.
           assert (DC : dec_count total (eff0 (Z_to_bv 64 k)) = Some k).
           { unfold dec_count, eff0. rewrite unsigned_lit by (unfold total in *; lia).
             replace ((1 <=? k) && (k <=? total)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
             rewrite orb_true_r. reflexivity. }
           rewrite DC. cbn [ITree.bind fst snd].
           rewrite length_map, length_firstn, Nat.min_l by lia.
           destruct (Z.eqb_spec k total) as [-> | NE].
           ++ (* [comment removed for export] *) unfold mret. rewrite Htot, Nat2Z.id, skipn_all. cbn [map].
              eapply trzA_conseq; [apply trzA_ret | apply t_eq_sym; apply t_emit_nil_eq; exact HK].
           ++ (* [comment removed for export] *)
              eapply trzA_conseq.
              ** assert (LB : length bytes = S (length bs')) by (subst bytes; unfold to_bytes; rewrite length_map; reflexivity).
                 assert (HkR : 0 <= k <= zlength (zconcat iovs)) by (rewrite EZ; unfold zlength; cbn [length]; lia).
                 pose proof (zlength_zconcat_advance iovs k HkR Hlen) as EA.
                 apply (f_equal (@length byte)) in EA. rewrite length_skipn in EA. unfold to_bytes in EA. rewrite !length_map in EA.
                 rewrite EZ in EA. cbn [length] in EA.
                 apply (IH fd (advance_iovs iovs k) s mo K Hmi Hfd).
                 --- pose proof (length_advance_iovs iovs k). lia.
                 --- cbn [length] in Hfuel. lia.
                 --- unfold zlength. unfold zlength in H64. cbn [length] in H64. lia.
                 --- exact HK.
              ** assert (LB : length bytes = S (length bs')) by (subst bytes; unfold to_bytes; rewrite length_map; reflexivity).
                 assert (HkR : 0 <= k <= zlength (zconcat iovs)) by (rewrite EZ; unfold zlength; cbn [length]; lia).
                 rewrite (zlength_zconcat_advance iovs k HkR Hlen). rewrite EZ. fold bytes. apply t_eq_refl.
      * (* [comment removed for export] *)
        intros tr. split.
        -- intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; [| exfalso; exact Hxt].
           cbn [ansA fst snd] in Hi.
           pose proof Hst as H. cbn [nstep fst snd] in H. rewrite zconcat_concat_to_bytes, EZ in H. fold bytes in H.
           destruct H as [_ [(Hb & _ & _) | (k & Hk & Er & Eevs)]]; [subst bytes; discriminate|].
           rewrite Eevs in Hi. rewrite length_map, length_firstn, Nat.min_l in Hi by lia.
           rewrite <- (firstn_skipn (Z.to_nat k) bytes). rewrite map_app. apply t_eq_emit_app. exact Hi.
        -- intros Ht. exists (inl (exist _ (eff0 (Z_to_bv 64 total), mo, map (WriteEv (Z_to_bv 64 fd)) bytes) HokF)).
           cbn [ansA fst snd]. rewrite length_map, skipn_all. cbn [map].
           destruct Ht as [Hp | (tr' & -> & Hk)].
           ++ left. exact Hp.
           ++ right. exists tr'. split; [reflexivity|]. apply t_emit_nil_l. right. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma trzA_stdio_writev : forall fd (buf sbytes : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  minvA mo -> (fd = 1 \/ fd = 2) ->
  zlength buf + zlength sbytes <= WRITEV_MAX ->
  K (Ok (tt, st)) mo [] ->
  trzN (stdio_writev fd buf sbytes st) mo K
       (t_emit (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ sbytes))) (K (Ok (tt, st)) mo)).
Proof.
  intros fd buf sbytes st mo K Hmi Hfd Hlen HK. unfold stdio_writev.
  destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength sbytes)); [lia|].
  assert (EI : zconcat (iovs_init buf sbytes) = buf ++ sbytes).
  { unfold iovs_init. destruct buf; cbn; rewrite ?app_nil_r; reflexivity. }
  pose proof (trzA_writev_loop (length buf + length sbytes) fd (iovs_init buf sbytes) st mo K Hmi Hfd) as T.
  rewrite EI in T. apply T; [unfold iovs_init; destruct buf; cbn; lia | rewrite length_app; lia | unfold WRITEV_MAX, zlength in *; rewrite length_app; lia | exact HK].
Qed.

End TrzNodesA.
End RC__1.
