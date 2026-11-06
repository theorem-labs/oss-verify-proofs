(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RelSpec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma syscall_spec_93 : forall i m o,
  bv_unsigned (in_sysno i) = 93%Z ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_94 : forall i m o,
  bv_unsigned (in_sysno i) = 94%Z ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_216 : forall i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec i m o <->
  mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma exit_outcome : forall code i m o,
  exit_spec code i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [].
Proof.
  intros code i m o. unfold exit_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma set_tid_known_outcome : forall i m o t0,
  m_tid m = Some t0 ->
  set_tid_address_spec i m o <-> o = Ok (mkEffect t0 [] []) m [].
Proof.
  intros i m o t0 Htid. unfold set_tid_address_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Htid. split; reflexivity.
Qed.

Lemma close_ebadf_outcome : forall fd i m o,
  fd_lookup (m_fds m) fd = None ->
  close_spec fd i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd i m o Hlk. unfold close_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma read_ebadf_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = None ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o Hlk. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma ioctl_ebadf_outcome : forall fd req i m o,
  fd_lookup (m_fds m) fd = None ->
  ioctl_spec fd req i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd req i m o Hlk. unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Definition mremap_out (m : Model) (old old_size new_size : word)
    (o : outcome SyscallEffect) : Prop :=
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in
  let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  (old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (old_nZ <> new_nZ /\ exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ ((new_nZ < old_nZ)%Z
      /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
  \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
      /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
  \/ ((old_nZ < new_nZ)%Z /\ exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true
      /\ o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []).

Lemma mremap_outcome : forall old old_size new_size flags i m o,
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b new_size = false ->
  page_align_is0_b old_size = false ->
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in
  mremap_source_b (m_vmmaps m) old (Z_to_bv 64 old_nZ) old_nZ = true ->
  mremap_backing_uniform_b m old (Z_to_bv 64 old_nZ) = true ->
  mremap_spec old old_size new_size flags i m o <-> mremap_out m old old_size new_size o.
Proof.
  intros old old_size new_size flags i m o Hfl Hal Hnew Hold. cbv zeta. intros Hsrc Huni.
  unfold mremap_spec, mremap_out.
  rewrite Hfl, Z.eqb_refl, (proj2 (Z.eqb_eq _ _) Hal), Hnew, Hold. cbn [negb].
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)) in *.
  set (new_nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  destruct (Z.eqb_spec old_nZ new_nZ) as [E|NE].
  {
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hsrc, ?Huni in *; cbn [andb negb] in *; inv_sys.
      left. split; [exact E|reflexivity].
    - intros [(_ & ->)|[(NE & _)|[(L & _)|[(L & _)|(L & _)]]]]; try (exfalso; lia).
      eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Huni. cbn [andb negb]. split; reflexivity. }
  destruct (Z.ltb_spec new_nZ old_nZ) as [L|GE].
  {
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hsrc, ?Huni in *; cbn [andb negb] in *; inv_sys.
      + right; left. split; [exact NE|]. eexists; split; [eassumption|reflexivity].
      + right; right; left. split; [exact L|reflexivity].
    - intros [(E & _)|[(_ & e & He & ->)|[(_ & ->)|[(L2 & _)|(L2 & _)]]]]; try (exfalso; lia);
        eexists _, _, _, _; (split; [reflexivity|]); rewrite Hsrc, Huni; cbn [andb negb]; (split; [|reflexivity]).
      + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + right. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity. }
  {
    sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?Hsrc, ?Huni in *; cbn [andb negb] in *; inv_sys;
        try (destruct (mremap_inplace_grow_b m old (Z_to_bv 64 old_nZ) (Z_to_bv 64 new_nZ) old_nZ new_nZ) eqn:G; inv_sys).
      all: match goal with
        | He : In ?e mremap_errnos |- _ =>
            right; left; split; [exact NE|]; exists e; split; [exact He|reflexivity]
        | Hd : mremap_fresh_b _ _ _ _ _ ?d _ = true |- _ =>
            do 4 right; split; [lia|]; exists d; split; [exact Hd|reflexivity]
        | G : mremap_inplace_grow_b _ _ _ _ _ _ = true |- _ =>
            right; right; right; left; split; [lia|]; split; [first [exact G|reflexivity]|reflexivity]
        end.
    - intros [(E & _)|[(_ & e & He & ->)|[(L & _)|[(L & G & ->)|(L & dst & Hd & ->)]]]]; try (exfalso; lia);
        eexists _, _, _, _; (split; [reflexivity|]); rewrite Hsrc, Huni; cbn [andb negb]; (split; [|reflexivity]).
      + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + right. rewrite G. left. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
      + right. destruct (mremap_inplace_grow_b m old (Z_to_bv 64 old_nZ) (Z_to_bv 64 new_nZ) old_nZ new_nZ).
        * right. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
          split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
        * eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
          split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity. }
Qed.

Lemma syscall_spec_35 : forall i m o,
  bv_unsigned (in_sysno i) = 35%Z ->
  syscall_spec i m o <-> unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_62 : forall i m o,
  bv_unsigned (in_sysno i) = 62%Z ->
  syscall_spec i m o <-> lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_65 : forall i m o,
  bv_unsigned (in_sysno i) = 65%Z ->
  syscall_spec i m o <-> readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Definition reseek (e : FdEntry) (r : word) : FdEntry :=
  match e with
  | FdFile p _ => FdFile p r
  | FdFileW p _ => FdFileW p r
  | other => other
  end.

Definition lseek_file_out (m : Model) (fd : word) (e : FdEntry) (base off : word)
    (o : outcome SyscallEffect) : Prop :=
  match lseek_dest base off with
  | None => o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
  | Some r => o = Ok (mkEffect r [] []) (with_fds (fd_insert (m_fds m) fd (reseek e r)) m) []
  end.

Lemma lseek_file_outcome : forall fd off whence i m o e p cur data base,
  fd_lookup (m_fds m) fd = Some e ->
  (e = FdFile p cur \/ e = FdFileW p cur) ->
  fs_lookup (m_fs m) p = Some data ->
  (bv_unsigned whence <= SEEK_MAX)%Z ->
  lseek_base whence cur (len_word data) = Some base ->
  lseek_spec fd off whence i m o <-> lseek_file_out m fd e base off o.
Proof.
  intros fd off whence i m o e p cur data base Hlk He Hfs Hwh Hb.
  assert (Hw : (SEEK_MAX <? bv_unsigned whence)%Z = false) by (apply Z.ltb_ge; lia).
  unfold lseek_spec, lseek_file_out. sys_unfold.
  destruct He as [-> | ->]; cbn [reseek]; split.
  1,3: destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; rewrite Hw in *; cbn beta iota in *;
       rewrite Hfs in *; rewrite Hb in *; destruct (lseek_dest base off) as [r|]; inv_sys; reflexivity.
  all: destruct (lseek_dest base off) as [r|] eqn:Hd; intros ->.
  all: eexists _, _, _, _; split; [reflexivity|]; rewrite Hlk, Hw; cbn beta iota; rewrite Hfs, Hb, Hd.
  1,3: split; [eexists _, _, _, _; repeat split; reflexivity| reflexivity].
  all: split; reflexivity.
Qed.

Definition unlink_out (R : list (word * nat)) (m : Model) (p : list byte) (o : outcome SyscallEffect) : Prop :=
  match fs_lookup (m_fs m) p with
  | None => o = Ok (with_copyins R (mkEffect (errno_ret ENOENT) [] [])) m []
  | Some _ => (exists e, In e unlinkat_errnos /\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
              \/ o = Ok (with_copyins R (mkEffect (Z_to_bv 64 0) [] [])) (with_fs (fs_remove (m_fs m) p) m) []
  end.

Lemma modeled_unlink_flags_0 : modeled_unlink_flags (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma unlink_rmdir_0 : unlink_rmdir (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma drop_leading_slashes_noslash : forall p,
  existsb (fun b => bv_eqb b slash_byte) p = false -> drop_leading_slashes p = p.
Proof.
  intros [|b r] H; [reflexivity|]. cbn [drop_leading_slashes]. cbn [existsb] in H.
  destruct (bv_eqb b slash_byte); [discriminate|reflexivity].
Qed.

Lemma existsb_rev : forall {A} (f : A -> bool) (l : list A), existsb f (rev l) = existsb f l.
Proof.
  intros A f l. induction l as [|x l IH]; [reflexivity|]. cbn [rev existsb].
  rewrite existsb_app, IH. cbn [existsb]. rewrite Bool.orb_false_r. apply Bool.orb_comm.
Qed.

Lemma path_strip_trailing_slashes_plain : forall p,
  path_has_slash p = false -> path_strip_trailing_slashes p = p.
Proof.
  intros p H. unfold path_strip_trailing_slashes.
  rewrite drop_leading_slashes_noslash by (unfold path_has_slash in H; rewrite existsb_rev; exact H).
  apply rev_involutive.
Qed.

Lemma path_trailing_slash_plain : forall p,
  path_has_slash p = false -> path_trailing_slash p = false.
Proof.
  intros p H. unfold path_trailing_slash. rewrite (path_strip_trailing_slashes_plain p H).
  now rewrite Nat.eqb_refl.
Qed.

Lemma unlinkat_outcome : forall pathp i m o p,
  read_cstr (in_mem i) pathp = CstrOk p ->
  p <> [] -> path_has_slash p = false -> p <> dot_path -> p <> dotdot_path ->
  Nat.ltb NAME_MAX (length p) = false ->
  fs_under (m_fs m) p = false ->
  (forall d, fs_lookup (m_fs m) p = Some d -> fd_names_path (m_fds m) p = false) ->
  unlinkat_spec AT_FDCWD32 pathp (Z_to_bv 64 0) i m o <-> unlink_out (open_reads i pathp) m p o.
Proof.
  intros pathp i m o p Hp Hne Hsl Hnd Hndd Hnm Hun Hfn.
  assert (E0 : path_eqb p [] = false) by (destruct p; [congruence| reflexivity]).
  assert (E1 : path_eqb p dot_path = false)
    by (destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence| reflexivity]).
  assert (E2 : path_eqb p dotdot_path = false)
    by (destruct (path_eqb p dotdot_path) eqn:E; [apply path_eqb_eq in E; congruence| reflexivity]).
  unfold unlinkat_spec.
  transitivity (record_copyins (open_reads i pathp) (unlinkat_body_spec AT_FDCWD32 pathp (Z_to_bv 64 0) i m) i m o).
  { rewrite (bind_input_get_model (fun i0 m0 => _)). cbv beta.
    rewrite modeled_unlink_flags_0. cbn [negb]. unfold open_reads. reflexivity. }
  rewrite record_copyins_iff.
  assert (BODY : forall o', unlinkat_body_spec AT_FDCWD32 pathp (Z_to_bv 64 0) i m i m o' <->
            match fs_lookup (m_fs m) p with
            | None => o' = Ok (mkEffect (errno_ret ENOENT) [] []) m []
            | Some _ => (exists e, In e unlinkat_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m [])
                        \/ o' = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fs (fs_remove (m_fs m) p) m) []
            end).
  { intros o'. unfold unlinkat_body_spec. rewrite Hp, E0, bv_eqb_refl. cbn [negb].
    rewrite (path_strip_trailing_slashes_plain p Hsl), E0, Hsl, E1, E2, Hnm, Hun.
    unfold unlink_found_spec. rewrite unlink_rmdir_0, (path_trailing_slash_plain p Hsl).
    destruct (fs_lookup (m_fs m) p) as [d|] eqn:Hfs.
    - rewrite (Hfn d eq_refl). sys_unfold. destruct o' as [x m' evs|]; split.
      + intros H; inv_sys; [left; eexists; split; [eassumption| reflexivity] | right; reflexivity].
      + intros [(e & He & H) | H]; apply Ok_inj in H as (-> & -> & ->).
        * left. eexists _, _, _, _. split; [exists e; split; [exact He| reflexivity]|]. split; reflexivity.
        * right. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
      + intros H; inv_sys.
      + intros [(e & _ & H) | H]; discriminate.
    - apply err_ret_outcome. }
  unfold after_copyins, unlink_out. destruct (fs_lookup (m_fs m) p) as [d|] eqn:Hfs; destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply BODY in Hc. destruct Hc as [(e & He & Hc) | Hc]; apply Ok_inj in Hc as (-> & -> & ->);
      cbn [eff_copyins]; rewrite app_nil_r; [left; exists e; auto| right; reflexivity].
  - intros [(e & He & H) | H]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [apply BODY; left; exists e; auto|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + exists (mkEffect (Z_to_bv 64 0) [] []). split; [apply BODY; right; reflexivity|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply BODY in H. destruct H as [(e & _ & H) | H]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros [(e & _ & H) | H]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros (core & Hc & ->). apply BODY in Hc. apply Ok_inj in Hc as (-> & -> & ->). cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). exists (mkEffect (errno_ret ENOENT) [] []). split; [apply BODY; reflexivity|].
    cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply BODY in H. exfalso. exact (Unmodeled_Ok _ _ _ H).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

Lemma writev_file_outcome : forall fd iov iovcnt i m o p off data iovs bs,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  fs_lookup (m_fs m) p = Some data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= MAX_RW_COUNT)%Z ->
  gather_iovecs (in_mem i) iovs = Some bs ->
  (1 <= Z.of_nat (length bs))%Z ->
  rw_pos_einvalb off (iovs_total iovs) = false ->
  modeled_zero_fill (bv_unsigned off) data = true ->
  let CA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
  writev_spec fd iov iovcnt i m o <->
  o = Ok (mkEffectU (len_word bs) [] [] [] [] (CA ++ iov_prefix_accesses iovs (length bs)))
         (with_fds (fd_insert (m_fds m) fd (FdFileW p (off + len_word bs)))
                   (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)) [].
Proof.
  intros fd iov iovcnt i m o p off data iovs bs Hfd Hfs Himp Htot Hg Hbs1 Hpos Hgap.
  cbv zeta.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; exact Htot).
  assert (Herr : addr_is_error_b (len_word bs) = false).
  { unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (unfold two_pow_64; unfold MAX_RW_COUNT in Htot; lia).
    unfold MAX_RW_COUNT in Htot. lia. }
  unfold writev_spec. rewrite (bind_input_get_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. unfold writev_file_arm.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
        set_fds (fd_insert (m_fds m) fd (FdFileW p (off + len_word bs))) ;;
        writev_ledger iovs bs)%sys i m o).
  { rewrite Himp. cbv zeta. unfold writev_gathered.
    rewrite Hcap, (gather_prefix_full _ _ _ Hg).
    replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Hpos.
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Hfs. unfold modeled_file_gap. destruct bs as [|b0 bs'] eqn:Ebs; [cbn in Hbs1; lia|].
    rewrite <- Ebs in *. rewrite Hgap. cbn [negb]. rewrite Herr. reflexivity. }
  unfold writev_ledger. rewrite Hcap. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys. rewrite !app_nil_r. reflexivity.
  - intros ->. eexists _, _, _, _. split.
    + eexists _, _, _, _. split; [reflexivity|]. split; [| reflexivity].
      eexists _, _, _, _. split; [reflexivity|]. split; [| reflexivity].
      eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + rewrite !app_nil_r. split; reflexivity.
Qed.

Lemma length_file_read_le' : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

Lemma readv_file_outcome : forall fd iov iovcnt i m o p off data iovs bs writes,
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  fs_lookup (m_fs m) p = Some data ->
  readv_heap_iovecb iovcnt = false ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (0 < iovs_total iovs <= MAX_RW_COUNT)%Z ->
  rw_pos_einvalb off (iovs_total iovs) = false ->
  bs = file_read data off (Z_to_bv 64 (iovs_total iovs)) ->
  scatter_iovecs (in_wmem i) iovs bs = Some writes ->
  let IA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
  readv_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins IA (mkEffect (len_word bs) writes []))
         (with_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) m) [].
Proof.
  intros fd iov iovcnt i m o p off data iovs bs writes Hfd Hfs Hheap Himp Htot Hpos Hbs Hsc.
  cbv zeta.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; lia).
  assert (Hlen : (Z.of_nat (length bs) <= iovs_total iovs)%Z).
  { rewrite Hbs. pose proof (length_file_read_le' data off (Z_to_bv 64 (iovs_total iovs))) as L.
    unfold word_to_nat in L. rewrite Z_to_bv_unsigned in L. unfold bv_wrap, bv_modulus in L.
    change (Z.of_N 64) with 64%Z in L. rewrite Z.mod_small in L by (unfold MAX_RW_COUNT in Htot; lia). lia. }
  assert (Herr : addr_is_error_b (len_word bs) = false).
  { unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (unfold two_pow_64; unfold MAX_RW_COUNT in Htot; lia).
    unfold MAX_RW_COUNT in Htot. lia. }
  assert (Htot0 : Z.eqb (iovs_total iovs) 0 = false) by (apply Z.eqb_neq; lia).
  unfold readv_spec. rewrite (bind_input_get_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. cbn [readable_fd]. rewrite Hheap.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (set_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) ;;
        pure (mkEffect (len_word bs) writes []))%sys i m o).
  { rewrite Himp. unfold readv_imported.
    rewrite Hcap, Htot0, Hfs, Hpos, <- Hbs, Hsc, Herr. reflexivity. }
  sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys. rewrite !app_nil_r. reflexivity.
  - intros ->. eexists _, _, _, _. split.
    + eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + cbn [eff_copyins]. rewrite !app_nil_r. split; reflexivity.
Qed.

Lemma read_wronly_outcome : forall fd buf count i m o p off,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o p off Hlk. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma lseek_ebadf_outcome : forall fd off whence i m o,
  fd_lookup (m_fds m) fd = None ->
  lseek_spec fd off whence i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd off whence i m o Hlk. unfold lseek_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Definition create_out (R : list (word * nat)) (m : Model) (p : list byte) (o : outcome SyscallEffect) : Prop :=
  if path_is_dirref p then o = Ok (with_copyins R (mkEffect (errno_ret EISDIR) [] [])) m []
  else if fs_under (m_fs m) p then o = Ok (with_copyins R (mkEffect (errno_ret EISDIR) [] [])) m []
  else
    (exists e, In e openat_errnos /\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
    \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None /\
        o = Ok (with_copyins R (mkEffect (alloc_fd (m_fds m)) [] []))
               (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) (FdFileW p (Z_to_bv 64 0)))
                         (with_fs (fs_set (m_fs m) p []) m)) []).

Lemma wr_create_flags_ne0 : Z.eqb wr_create_flags 0 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma openat_create_outcome : forall pathp flags i m o p,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = wr_create_flags ->
  read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
  openat_spec AT_FDCWD32 pathp flags i m o <-> create_out (open_reads i pathp) m p o.
Proof.
  intros pathp flags i m o p Hwr Hp Hne Hsl.
  rewrite (openat_spec_body _ _ _ _ _ _ (modeled_open_flags_wr _ Hwr)).
  assert (E0 : path_eqb p [] = false) by (destruct p; [congruence| reflexivity]).
  assert (BODY : forall o', openat_body_spec i m AT_FDCWD32 pathp flags i m o' <-> openat_create_spec p m i m o').
  { intros o'. unfold openat_body_spec. rewrite Hp, E0, bv_eqb_refl. cbn [negb].
    unfold openat_resolved_spec. rewrite Hsl, Hwr, wr_create_flags_ne0, Z.eqb_refl. reflexivity. }
  unfold create_out, openat_create_spec in *.
  destruct (path_is_dirref p) eqn:E1.
  { apply after_copyins_det. intros o'. rewrite BODY. apply err_ret_outcome. }
  destruct (fs_under (m_fs m) p) eqn:E3.
  { apply after_copyins_det. intros o'. rewrite BODY. apply err_ret_outcome. }
  assert (CW : forall o', create_wronly p m i m o' <->
            (exists e, In e openat_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m [])
            \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None /\
                o' = Ok (mkEffect (alloc_fd (m_fds m)) [] [])
                        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) (FdFileW p (Z_to_bv 64 0)))
                                  (with_fs (fs_set (m_fs m) p []) m)) [])).
  { intros o'. unfold create_wronly. sys_unfold. destruct o' as [x m' evs|]; split.
    - intros H; inv_sys; [left; eexists; split; [eassumption| reflexivity] | right; split; [assumption| reflexivity]].
    - intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
      + left. eexists _, _, _, _. split; [exists e; split; [exact He| reflexivity]|]. split; reflexivity.
      + right. eexists _, _, _, _. split; [eexists; split; [split; [exact Hfree| reflexivity]| reflexivity]|].
        split; [| reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; [| reflexivity].
        eexists _, _, _, _. repeat split; reflexivity.
    - intros H; inv_sys.
    - intros [(e & _ & H) | (_ & H)]; discriminate. }
  unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply BODY, CW in Hc.
    destruct Hc as [(e & He & Hc) | (Hfree & Hc)]; apply Ok_inj in Hc as (-> & -> & ->); cbn [eff_copyins]; rewrite app_nil_r.
    + left. exists e. auto.
    + right. auto.
  - intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [apply BODY, CW; left; exists e; auto|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + exists (mkEffect (alloc_fd (m_fds m)) [] []). split; [apply BODY, CW; right; auto|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply BODY, CW in H. destruct H as [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
Qed.

