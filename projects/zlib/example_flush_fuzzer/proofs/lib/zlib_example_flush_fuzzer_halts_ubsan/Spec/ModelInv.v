(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITree Nodes Decode Image.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Harness Adapter Driver Prog KInv KLink KEv KEvP TargetSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).


Section DriverSpec.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.
Variable own : list ptr -> assn St.

Definition ARG_MAX_LEN : Z := 131071.
Definition diag_ok (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => zlength a <= ARG_MAX_LEN
  | _ => True
  end.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspec (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspec (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspec (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspec (own X) alloc_count (fun _ => own X).
Hypothesis Hrun : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecP (own X) (run cfg payload) (fun _ => own X).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.

Lemma own_after_node : forall X s mo n rsp mo' evs,
  own X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo'.
Proof.
  intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.

Definition rd_inv (X : list ptr) (st : rd_st) : assn St := fun s mo =>
  own (rd_buf st :: X) s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).

Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
  intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia.
Qed.


Lemma m_vmmaps_with_fds : forall f mo, m_vmmaps (with_fds f mo) = m_vmmaps mo.
Proof. reflexivity. Qed.



Lemma zlength_skipn_le : forall {A} n (l : list A), zlength (skipn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.


End DriverSpec.


Definition so_ok (so : stdout_st) : Prop := zlength (so_buf so) <= STDOUT_BUFSIZ.
Definition Gso : PState -> Model -> Prop := fun s _ => so_ok (ps_so s).

Lemma frame_ok_Gso : frame_ok Gso.
Proof. intros s s' mo mo' _ Hso _ H. unfold Gso in *. rewrite Hso. exact H. Qed.

Definition GI (X : list bptr) : assn PState := OWN X Gso.

Lemma KL_fds : forall L pbrk mo mo',
  KL L pbrk mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hvm Hmi Hh. destruct K. constructor; try (rewrite Hvm); auto.
Qed.

Lemma GI_minv : forall X s mo, GI X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [(L & _ & K & _) _]. split; [exact (kl_minv _ _ _ K)| exact (kl_halt _ _ _ K)]. Qed.

Lemma GI_fds : forall X s mo mo', GI X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GI X s mo'.
Proof.
  intros X s mo mo' [(L & Hc & K & Hi) [Hnd HG]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact HG]].
  exists L. split; [exact Hc|]. split; [eapply KL_fds; eauto| exact Hi].
Qed.

Lemma GI_perm : forall X Y s mo, Permutation X Y -> GI X s mo -> GI Y s mo.
Proof. intros. eapply OWN_perm; eauto. Qed.

Lemma GI_after_node : forall X s mo n rsp mo' evs,
  GI X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> GI X s mo'.
Proof.
  intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply GI_fds; eauto.
Qed.

Lemma GI_set_so : forall X s mo v, GI X s mo -> so_ok v -> GI X (set_so_ps v s) mo.
Proof. intros X s mo v H Hv. eapply OWN_other; [exact H|reflexivity|reflexivity| exact Hv]. Qed.



Lemma startup_GI : forall X, mspec (GI X) startup (fun _ => GI X).
Proof.
  intros X. unfold startup. eapply mspec_seq; [|intros _; apply mspec_ret; intros s mo H; exact H].
  apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
  pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
  exists t. split; [exact Hdec|]. eapply GI_after_node; [exact Ho| exact Hst|].
  destruct Hmo as [[_ ->]|[_ ->]]; reflexivity.
Qed.


Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma length_concat_to_bytes : forall iov, length (concat (map to_bytes iov)) = length (concat iov).
Proof. induction iov as [|a iov IH]; cbn; [reflexivity|]. rewrite !length_app, length_to_bytes, IH. reflexivity. Qed.

Lemma iov_total_eq : forall iov, iov_total iov = Z.of_nat (length (concat iov)).
Proof. intros. reflexivity. Qed.

Lemma iov_advance_shrinks : forall iov cnt, 1 <= cnt -> (0 < length (concat iov))%nat ->
  (length (concat (iov_advance iov cnt)) < length (concat iov))%nat.
Proof.
  intros iov cnt Hc Hpos. assert (1 <= Z.to_nat cnt)%nat by lia.
  destruct iov as [|a [|b rest]]; cbn in *.
  - lia.
  - rewrite !app_nil_r in *. rewrite length_skipn. lia.
  - rewrite !length_app in Hpos. destruct (Z.ltb_spec (zlength a) cnt); cbn; rewrite ?app_nil_r, ?length_app, ?length_skipn; unfold zlength in *.
    + assert (1 <= Z.to_nat (cnt - Z.of_nat (length a)))%nat by lia. lia.
    + lia.
Qed.

Lemma stdio_write_loop_GI : forall X fd fuel iov,
  (length (concat iov) < fuel)%nat -> Z.of_nat (length (concat iov)) < 2^63 ->
  mspec (GI X) (stdio_write_loop fuel fd iov) (fun _ => GI X).
Proof.
  intros X fd fuel. induction fuel as [|fuel IH]; intros iov Hf Hb; [lia|].
  cbn [stdio_write_loop].
  eapply mspec_bind with (Q1 := fun cnt s mo => GI X s mo /\
     ((length (concat iov) = 0%nat /\ cnt = 0) \/ 1 <= cnt <= Z.of_nat (length (concat iov)))).
  - apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
    pose proof (nstep_dec_writev fd (map to_bytes iov) mo rsp mo' evs ltac:(rewrite length_concat_to_bytes; lia) Hst) as (k & Hdec & Hk & -> & _).
    rewrite length_concat_to_bytes in Hdec, Hk. exists k. rewrite iov_total_eq. split; [exact Hdec|]. split; [exact Ho| exact Hk].
  - intros cnt. apply mspec_if_pre.
    + apply mspec_ret. intros s mo [[H _] _]. exact H.
    + apply mspec_pointwise. intros s0 mo0 [[Ho Hk] Hne]. rewrite iov_total_eq in Hne. apply Z.eqb_neq in Hne.
      assert (1 <= cnt /\ (0 < length (concat iov))%nat) as [H1 H2] by (destruct Hk as [[? ?]|?]; lia).
      pose proof (iov_advance_shrinks iov cnt H1 H2).
      eapply mspec_pre; [apply IH; lia|]. intros s mo [-> ->]. exact Ho.
Qed.

Lemma stdio_write_GI : forall X fd buf s, zlength buf + zlength s <= WRITE_MAX ->
  mspec (GI X) (stdio_write fd buf s) (fun _ => GI X).
Proof.
  intros X fd buf s Hlen. unfold stdio_write.
  destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)); [lia|].
  assert (E : length (concat (match buf with [] => [s] | _ :: _ => [buf; s] end)) = (length buf + length s)%nat).
  { destruct buf; cbn; rewrite ?app_nil_r, ?length_app; cbn; lia. }
  apply stdio_write_loop_GI; rewrite E; unfold zlength, WRITE_MAX in *; lia.
Qed.

Lemma upd_so_GI : forall X f,
  mspec (fun s mo => GI X s mo /\ so_ok (f (ps_so s))) (upd_so ps_so set_so_ps f)
        (fun _ s mo => GI X s mo /\ exists so0, ps_so s = f so0).
Proof.
  intros X f. unfold upd_so. apply mspec_upd'. intros s mo [Ho Hok]. split; [apply GI_set_so; [exact Ho| exact Hok]|]. cbn. eauto.
Qed.

Lemma rd_so_GI : forall (X : list bptr) (P : assn PState), mspec P (rd_so ps_so) (fun so s mo => P s mo /\ so = ps_so s).
Proof.
  intros X P. unfold rd_so. eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret.
  intros s mo [-> Ho]. split; [exact Ho| reflexivity].
Qed.

Lemma GI_so_ok : forall X s mo, GI X s mo -> so_ok (ps_so s).
Proof. intros X s mo H. exact (OWN_G _ _ _ _ H). Qed.

Definition PIECE_MAX : Z := 1048576.

Lemma stdout_stdio_write_GI : forall X s, zlength s <= PIECE_MAX ->
  mspec (GI X) (stdout_stdio_write ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
  intros X s Hs. unfold stdout_stdio_write. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
  eapply mspec_seq. { eapply mspec_pre; [apply stdio_write_GI; unfold PIECE_MAX, WRITE_MAX in *; lia|]. intros s' mo' [-> ->]; exact Ho. }
  intros _. eapply mspec_conseq; [apply upd_so_GI| |].
  - intros s' mo' Ho'. split; [exact Ho'|]. unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
  - intros [] s' mo' [Ho' [so0 ->]]. split; [exact Ho'| reflexivity].
Qed.

Lemma stdout_writefn_GI : forall X s, zlength s <= PIECE_MAX ->
  mspec (GI X) (stdout_writefn ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
  intros X s Hs. unfold stdout_writefn. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->].
  eapply mspec_seq with (R := GI X).
  - destruct (so_first (ps_so s1)).
    + eapply mspec_seq.
      { eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [-> ->]; split; [exact Ho| exact (GI_so_ok _ _ _ Ho)]| intros [] s' mo' [H _]; exact H]. }
      intros _. eapply mspec_bind with (Q1 := fun r s mo => GI X s mo /\ match r with SErr _ => True | SVal _ => False end).
      * apply mspec_sys. intros s' mo' Ho'. split; [exact I|]. intros rsp mo'' evs Hst.
        pose proof (nstep_dec_ioctl 1 TIOCGWINSZ mo' rsp mo'' evs Hst) as (Hdec & -> & _).
        eexists. split; [exact Hdec|]. split; [exact Ho'| exact I].
      * intros [e|v]; [| intros s' mo' [_ []]].
        eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [H _]; split; [exact H| exact (GI_so_ok _ _ _ H)]| intros [] s' mo' [H _]; exact H].
    + apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
  - intros _. apply stdout_stdio_write_GI. exact Hs.
Qed.

Lemma zlength_firstn_le' : forall {A} n (l : list A), zlength (firstn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite firstn_length. lia. Qed.

Lemma stdout_towrite_GI : forall X, mspec (GI X) (stdout_towrite ps_so set_so_ps) (fun _ => GI X).
Proof.
  intros X. unfold stdout_towrite. eapply mspec_conseq; [apply upd_so_GI| |].
  - intros s mo Ho. split; [exact Ho|]. pose proof (GI_so_ok _ _ _ Ho) as Hok. destruct (so_active (ps_so s)); [exact Hok|].
    unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
  - intros [] s mo [H _]; exact H.
Qed.

Lemma stdout_fwritex_GI : forall X s, zlength s <= PIECE_MAX ->
  mspec (GI X) (stdout_fwritex ps_so set_so_ps s) (fun _ => GI X).
Proof.
  intros X s Hs. unfold stdout_fwritex.
  eapply mspec_seq; [apply stdout_towrite_GI|]. intros _.
  eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
  apply mspec_if; intros C1.
  { eapply mspec_conseq; [apply stdout_writefn_GI; exact Hs| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H]. }
  apply Z.ltb_ge in C1.
  destruct (so_lbf_nl (ps_so s1)).
  - set (i := after_last_nl s).
    eapply mspec_seq with (R := fun s' mo => GI X s' mo /\ zlength (so_buf (ps_so s')) + zlength (skipn (Z.to_nat i) s) <= STDOUT_BUFSIZ).
    + destruct (0 <? i).
      * eapply mspec_conseq; [apply stdout_writefn_GI; pose proof (zlength_firstn_le' (Z.to_nat i) s); lia| intros s' mo' [-> ->]; exact Ho|].
        intros [] s' mo' [H Hb]. split; [exact H|]. rewrite Hb. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold zlength, STDOUT_BUFSIZ in *; cbn; lia.
      * apply mspec_ret. intros s' mo' [-> ->]. split; [exact Ho|]. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold STDOUT_BUFSIZ in *; lia.
    + intros _. eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
      intros s' mo' [H Hb]. split; [exact H|]. unfold so_ok. cbn. rewrite zlength_app. exact Hb.
  - eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
    intros s' mo' [-> ->]. split; [exact Ho|]. unfold so_ok. cbn. rewrite zlength_app. unfold STDOUT_BUFSIZ in *; lia.
Qed.

Lemma out_pieces_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
  mspec (GI X) (out_pieces ps_so set_so_ps ps) (fun _ => GI X).
Proof.
  intros X ps Hps. induction Hps as [|p ps Hp Hps IH]; cbn [out_pieces].
  - apply mspec_ret. intros s mo H; exact H.
  - eapply mspec_seq; [apply stdout_fwritex_GI; exact Hp|]. intros _. exact IH.
Qed.

Lemma stdout_vprintf_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
  mspec (GI X) (stdout_vprintf ps_so set_so_ps ps) (fun _ => GI X).
Proof.
  intros X ps Hps. unfold stdout_vprintf. eapply mspec_seq; [apply stdout_towrite_GI|]. intros _. apply out_pieces_GI. exact Hps.
Qed.

Lemma stdout_exit_flush_GI : forall X, mspec (GI X) (stdout_exit_flush ps_so set_so_ps) (fun _ => GI X).
Proof.
  intros X. unfold stdout_exit_flush. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
  apply mspec_pointwise. intros s1 mo1 [Ho ->]. destruct (0 <? _).
  - eapply mspec_conseq; [apply stdout_writefn_GI; unfold zlength, PIECE_MAX; cbn; lia| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H].
  - apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
Qed.

Lemma stderr_pieces_GI : forall X ps buf, zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p <= PIECE_MAX) ps ->
  mspec (GI X) (stderr_pieces buf ps) (fun buf' s mo => GI X s mo /\ zlength buf' <= INTERNAL_BUFSIZ).
Proof.
  intros X ps. induction ps as [|p ps IH]; intros buf Hbuf Hps; cbn [stderr_pieces].
  - apply mspec_ret. intros s mo H. auto.
  - inversion Hps; subst. unfold INTERNAL_BUFSIZ, PIECE_MAX in *. apply mspec_if; intros C.
    + eapply mspec_seq; [apply stdio_write_GI; unfold zlength, WRITE_MAX in *; lia|]. intros _. apply IH; [unfold zlength; cbn; lia| assumption].
    + apply Z.ltb_ge in C. apply IH; [rewrite zlength_app; lia| assumption].
Qed.

Lemma stderr_fprintf_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
  mspec (GI X) (stderr_fprintf ps) (fun _ => GI X).
Proof.
  intros X ps Hps. unfold stderr_fprintf. eapply mspec_bind; [apply stderr_pieces_GI; [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps]|].
  intros buf. apply mspec_pointwise. intros s1 mo1 [Ho Hb]. unfold INTERNAL_BUFSIZ in Hb.
  eapply mspec_pre; [apply stdio_write_GI; unfold zlength, WRITE_MAX in *; cbn; lia|]. intros s mo [-> ->]; exact Ho.
Qed.

Lemma stderr_fwrite_GI : forall X s, zlength s <= PIECE_MAX -> mspec (GI X) (stderr_fwrite s) (fun _ => GI X).
Proof.
  intros X s Hs. unfold stderr_fwrite. apply mspec_if; intros _; [|apply mspec_ret; intros s0 mo H; exact H].
  apply stdio_write_GI. unfold zlength, PIECE_MAX, WRITE_MAX in *; cbn; lia.
Qed.


Lemma s_diag_GI : forall X d, diag_ok d -> mspec (GI X) (s_diag d) (fun _ => GI X).
Proof.
  intros X d Hd. unfold s_diag. destruct d; cbn in Hd; unfold ARG_MAX_LEN in *.
  all: try (apply stderr_fprintf_GI; repeat constructor; unfold zlength, PIECE_MAX in *; cbn; lia).
  all: apply stderr_fwrite_GI; unfold zlength, PIECE_MAX; cbn; lia.
Qed.

Lemma fmt_u_length : forall fuel n acc, (length (digits_aux fuel n acc) <= fuel + length acc)%nat.
Proof.
  induction fuel as [|fuel IH]; intros n acc; cbn [digits_aux]; [lia|].
  destruct (n =? 0); [cbn; lia|]. etransitivity; [apply IH|]. cbn. lia.
Qed.

Lemma pieces_pct_d_short : forall v, Forall (fun p => zlength p <= PIECE_MAX) (pieces_pct_d v).
Proof.
  intros v. unfold pieces_pct_d, fmt_u.
  pose proof (fmt_u_length 20 v []) as L1. pose proof (fmt_u_length 20 (- v) []) as L2. cbn [length] in L1, L2.
  destruct (v =? 0); [|destruct (v <? 0)]; repeat constructor; unfold zlength, PIECE_MAX; cbn [length]; lia.
Qed.

Lemma s_emit_GI : forall X v, mspec (GI X) (s_emit ps_so set_so_ps v) (fun _ => GI X).
Proof. intros X v. unfold s_emit. apply stdout_vprintf_GI. apply pieces_pct_d_short. Qed.







Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* the start model is with_vdso of init_model (TopLevel mo0 at
   ), for any vDSO run v; + the image bound, mmap_base_min <= mbase and the channel reader (APPENDED; the
   facts KLink KL_init takes, as LB_Init QI_init). The KL launch proof is KLink KL_init. *)
Lemma GI_init : forall segs brk0 mbase sp lim inp atop v,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase ->
  in_channel_reader inp = true ->
  GI [] (ps_init (reservedZ segs) atop) (with_vdso v (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs brk0 mbase sp lim inp atop v Hvb Hpos Hsp Eatop Hceil Hlow Hmb Hrdr. unfold GI, OWN.
  pose proof alloc_ceiling_lo_val as Hclo.
  assert (Hat : 0 < atop <= atop_hi) by (unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *; lia).
  split; [|split; [apply List.NoDup_nil| unfold Gso, so_ok; cbn [ps_so ps_init so_buf stdout_init]; unfold zlength, STDOUT_BUFSIZ; cbn; lia]].
  exists (led_init (reservedZ segs) atop). split; [apply creach_init; exact Hat|]. split; [|intros c []].
  apply KL_with_vdso.
  exact (KL_init segs brk0 mbase sp lim inp (reservedZ segs) atop _ eq_refl Hvb Hpos Hsp Eatop Hceil Hlow Hmb Hrdr).
Qed.


Lemma argv_Z_short : forall argv, valid_argv argv -> Forall (fun a => zlength a <= ARG_MAX_LEN) (argv_Z argv).
Proof.
  intros argv (_ & _ & HF & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [|exact HF].
  intros a Ha. unfold zlength, ARG_MAX_LEN in *. rewrite length_map. lia.
Qed.


