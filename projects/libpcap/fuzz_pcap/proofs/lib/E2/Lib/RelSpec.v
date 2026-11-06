(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Abbreviation FdNull := (FdDevNull false true).

(* [comment removed for export] *)
Definition write_dirref (p : path) (m : Model) : bool :=
  path_is_dirref p || fs_under (m_fs m) p.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb_refl : forall {n : N} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

Lemma word_unsigned_range : forall (w : word),
  (0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
  intros w. pose proof (bv_unsigned_in_range _ w) as H.
  unfold two_pow_64. unfold bv_modulus in H.
  change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

Lemma errno_ret_unsigned : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  bv_unsigned (errno_ret e) = (two_pow_64 - e)%Z.
Proof.
  intros e H1 H2. unfold errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma errno_ret_error_b : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z -> addr_is_error_b (errno_ret e) = true.
Proof.
  intros e H1 H2. unfold addr_is_error_b.
  rewrite (errno_ret_unsigned e H1 H2). unfold two_pow_64.
  apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Definition errnos_ok (es : list Z) : bool :=
  forallb (fun e => (1 <=? e)%Z && (e <=? 4095)%Z) es.

Lemma errnos_ok_range : forall es e,
  errnos_ok es = true -> In e es -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof.
  induction es as [|x es IH]; intros e Hok HIn; [destruct HIn|].
  cbn in Hok. apply andb_true_iff in Hok as [Hx Hok].
  apply andb_true_iff in Hx as [H1 H2].
  destruct HIn as [-> | HIn];
    [ split; apply Z.leb_le; assumption
    | apply IH; assumption ].
Qed.

(* [comment removed for export] *)
Lemma read_bytes_aux_prefix : forall k n mp a w,
  (k <= n)%nat -> read_bytes_aux mp a n = Some w ->
  read_bytes_aux mp a k = Some (firstn k w).
Proof.
  induction k as [|k IH]; intros n mp a w Hk Hw; [reflexivity|].
  destruct n as [|n]; [lia|].
  cbn in Hw. destruct (mp a) as [b|] eqn:Hb; [|discriminate].
  destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
  inversion Hw; subst w.
  cbn. rewrite Hb. rewrite (IH n mp (a + 1) r ltac:(lia) Hr). reflexivity.
Qed.

Lemma read_bytes_map_prefix : forall mp a len k w,
  (bv_unsigned k <= bv_unsigned len)%Z -> read_bytes_map mp a len = Some w ->
  read_bytes_map mp a k = Some (firstn (word_to_nat k) w).
Proof.
  intros mp a len k w Hk Hw. rewrite read_bytes_map_eq in *.
  unfold word_to_nat in *.
  apply read_bytes_aux_prefix with (n := Z.to_nat (bv_unsigned len));
    [lia | assumption].
Qed.

Lemma read_bytes_aux_length : forall mp k a w,
  read_bytes_aux mp a k = Some w -> length w = k.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in Hw.
  - inversion Hw. reflexivity.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. cbn. now rewrite (IH _ _ Hr).
Qed.

Lemma read_bytes_map_length : forall mp a len w,
  read_bytes_map mp a len = Some w -> Z.of_nat (length w) = bv_unsigned len.
Proof.
  intros mp a len w Hw. rewrite read_bytes_map_eq in Hw.
  unfold word_to_nat in Hw.
  rewrite (read_bytes_aux_length _ _ _ _ Hw).
  pose proof (word_unsigned_range len). lia.
Qed.

Lemma readable_bytes_aux_full : forall mp k a w,
  read_bytes_aux mp a k = Some w -> readable_bytes_aux mp a k = w.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in *.
  - now inversion Hw.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. now rewrite (IH _ _ Hr).
Qed.

Lemma readable_bytes_full : forall mp a len w,
  read_bytes_map mp a len = Some w -> readable_bytes mp a len = w.
Proof.
  intros. rewrite read_bytes_map_eq in *. rewrite readable_bytes_eq.   (* [comment removed for export] *)
  now apply readable_bytes_aux_full.
Qed.

Lemma len_word_unsigned : forall {A} (l : list A),
  (Z.of_nat (length l) < two_pow_64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l Hl. unfold len_word.
  rewrite Z_to_bv_small; [reflexivity|].
  unfold bv_modulus. change (Z.of_N 64) with 64%Z.
  unfold two_pow_64 in Hl. lia.
Qed.

Lemma firstn_length_le_Z : forall {A} (l : list A) r,
  (0 <= r)%Z -> (r <= Z.of_nat (length l))%Z ->
  Z.of_nat (length (firstn (Z.to_nat r) l)) = r.
Proof.
  intros A l r H0 Hle. rewrite firstn_length_le; lia.
Qed.

Lemma len_word_firstn_ret : forall (ret : word) {A} (l : list A),
  (0 <= bv_unsigned ret <= Z.of_nat (length l))%Z ->
  len_word (firstn (Z.to_nat (bv_unsigned ret)) l) = ret.
Proof.
  intros ret A l H. unfold len_word.
  rewrite (firstn_length_le_Z l (bv_unsigned ret)) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma gather_prefix_full : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> gather_prefix mp iovs = bs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite (readable_bytes_full _ _ _ _ Hw).
    rewrite (read_bytes_map_length _ _ _ _ Hw), Z.eqb_refl.
    now rewrite (IH _ eq_refl).
Qed.

Lemma gather_iovecs_length : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> Z.of_nat (length bs) = iovs_total iovs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite length_app, Nat2Z.inj_add.
    rewrite (read_bytes_map_length _ _ _ _ Hw), (IH _ eq_refl). reflexivity.
Qed.

Lemma page_round_up_Z_nonneg : forall z,
  (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  apply Z.mul_nonneg_nonneg; [|lia].
  apply Z.div_pos; lia.
Qed.

Lemma page_round_up_Z_mono : forall a b,
  (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|].
  apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

(* [comment removed for export] *)
Lemma Ok_inj {A} : forall (x x' : A) m m' e e',
  Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Lemma Ok_Unmodeled {A} : forall (x : A) m e, Ok x m e = Unmodeled -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Unmodeled_Ok {A} : forall (x : A) m e, Unmodeled = Ok x m e -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Some_inj' {A} : forall (x y : A), Some x = Some y -> x = y.
Proof. intros x y H. injection H. auto. Qed.

Lemma Some_None {A} : forall (x : A), Some x = None -> False.
Proof. intros x H. discriminate H. Qed.

Lemma None_Some {A} : forall (x : A), None = Some x -> False.
Proof. intros x H. discriminate H. Qed.

(* [comment removed for export] *)
Ltac inv_sys :=
  repeat first
  [ progress subst
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
    | H : Ok _ _ _ = Unmodeled |- _ => exfalso; exact (Ok_Unmodeled _ _ _ H)
    | H : Unmodeled = Ok _ _ _ |- _ => exfalso; exact (Unmodeled_Ok _ _ _ H)
    | H : Some _ = Some _ |- _ => apply Some_inj' in H; subst
    | H : Some _ = None |- _ => exfalso; exact (Some_None _ H)
    | H : None = Some _ |- _ => exfalso; exact (None_Some _ H)
    | H : False |- _ => contradiction
    | H : true = false |- _ => exfalso; exact (Bool.diff_true_false H)
    | H : false = true |- _ => exfalso; exact (Bool.diff_false_true H)
    | H : _ \/ _ |- _ => destruct H
    end
  | progress cbv beta zeta in * ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition out_det (eff : SyscallEffect) (m' : Model) (evs : list event)
    (o : outcome SyscallEffect) : Prop :=
  o = Ok eff m' evs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_29 : forall i m o,
  bv_unsigned (in_sysno i) = 29%Z ->
  syscall_spec i m o <-> ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_56 : forall i m o,
  bv_unsigned (in_sysno i) = 56%Z ->
  syscall_spec i m o <-> openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_57 : forall i m o,
  bv_unsigned (in_sysno i) = 57%Z ->
  syscall_spec i m o <-> close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_63 : forall i m o,
  bv_unsigned (in_sysno i) = 63%Z ->
  syscall_spec i m o <-> read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_64 : forall i m o,
  bv_unsigned (in_sysno i) = 64%Z ->
  syscall_spec i m o <-> write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_66 : forall i m o,
  bv_unsigned (in_sysno i) = 66%Z ->
  syscall_spec i m o <-> writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_96 : forall i m o,
  bv_unsigned (in_sysno i) = 96%Z ->
  syscall_spec i m o <-> set_tid_address_spec i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_214 : forall i m o,
  bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec i m o <-> brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_215 : forall i m o,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec i m o <-> munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_222 : forall i m o,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o <->
  mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_226 : forall i m o,
  bv_unsigned (in_sysno i) = 226%Z ->
  syscall_spec i m o <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma close_outcome : forall fd i m e o,
  fd_lookup (m_fds m) fd = Some e ->
  close_spec fd i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds m) fd) m) [].
Proof.
  intros fd i m e o Hlk. unfold close_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ioctl_tty_outcome : forall fd req i m e o,
  fd_lookup (m_fds m) fd = Some e ->
  tty_only_request req = true ->
  bv_eqb req TIOCGWINSZ = true ->
  e <> FdUrandom ->
  ioctl_spec fd req i m o <->
  o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [].
Proof.
  intros fd req i m e o Hlk Hreq Hwz Hnu. unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *;
      destruct e; try (exfalso; apply Hnu; reflexivity); rewrite ?Hreq, ?Hwz in *; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. destruct e; try (exfalso; apply Hnu; reflexivity); rewrite ?Hreq, ?Hwz; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma set_tid_fresh_outcome : forall i m o,
  m_tid m = None ->
  set_tid_address_spec i m o <->
  exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
            /\ o = Ok (mkEffect t [] []) (with_tid t m) [].
Proof.
  intros i m o Htid. unfold set_tid_address_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys.
    eexists; split; [split; eassumption|reflexivity].
  - intros (t & Ht & ->). eexists _, _, _, _. split; [reflexivity|]. rewrite Htid.
    split; [|reflexivity]. eexists _, _, _, _. split; [exists t; split; [exact Ht|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma brk_outcome : forall req i m o,
  brk_spec req i m o <->
  exists r, brk_r_ok m req r = true
            /\ o = Ok (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
                                   (brk_unmaps r (vm_brk (m_vmmaps m))) [] [])
                      (with_brk_next m req r) [].
Proof.
  intros req i m o. unfold brk_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    eexists; split; [eassumption|reflexivity].
  - intros (r & Hr & ->). eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. split; [exists r; split; [exact Hr|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munmap_exact_outcome : forall addr len i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE)%Z ->   (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  map_has (vm_maps (m_vmmaps m)) addr n = true ->
  munmap_spec addr len i m o <->
  o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
         (with_mmap_destroyed addr n
            (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m) [].
Proof.
  intros addr len i m o Hal Hlen Hnw. cbv zeta. intros Hhas. unfold munmap_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hlen. cbn [negb orb].
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hhas in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hhas.
    split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_dir_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = Some FdDir ->
  access_okb buf (bv_unsigned count) = true ->
  read_spec fd buf count i m o <->
  o = Ok (mkEffect (errno_ret EISDIR) [] []) m [].
Proof.
  intros fd buf count i m o Hlk Hacc. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, ?Hacc in *; cbn [negb] in *; inv_sys.
    reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_file_outcome : forall fd buf count i m o p off data w,
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  access_okb buf (bv_unsigned count) = true ->
  fs_lookup (m_fs m) p = Some data ->
  let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
  read_bytes_map (in_wmem i) buf (len_word bs) = Some w ->
  read_spec fd buf count i m o <->
  o = Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
         (with_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) m) [].
Proof.
  intros fd buf count i m o p off data w Hlk Hacc Hfs. cbv zeta. intros Hw.
  unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, Hacc in *; cbn [negb] in *;
      rewrite Hfs in *; cbv zeta in *; rewrite Hw in *; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb].
    rewrite Hfs. cbv zeta. rewrite Hw.
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
  [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

(* [comment removed for export] *)
Definition after_copyins (R : list (word * nat)) (body : outcome SyscallEffect -> Prop)
    (o : outcome SyscallEffect) : Prop :=
  match o with
  | Ok eff m' evs => exists core, body (Ok core m' evs)
                                  /\ eff = with_copyins (R ++ eff_copyins core) core
  | Unmodeled => body Unmodeled
  end.

Lemma record_copyins_iff : forall R (spec : Sys SyscallEffect) i m o,
  record_copyins R spec i m o <-> after_copyins R (spec i m) o.
Proof.
  intros R spec i m o. unfold record_copyins, after_copyins, bind, pure.
  destruct o as [eff m' evs|]; split.
  - intros (core & m1 & evs1 & evs2 & Hc & Hp & ->). apply Ok_inj in Hp as (-> & -> & ->).
    exists core. rewrite app_nil_r. auto.
  - intros (core & Hc & ->). exists core, m', evs, []. rewrite app_nil_r. auto.
  - intros [H | (core & m1 & evs1 & _ & Hp)]; [exact H|]. exfalso. exact (Unmodeled_Ok _ _ _ Hp).
  - intros H. left. exact H.
Qed.

(* [comment removed for export] *)
Lemma after_copyins_det : forall R body r m0 evs0,
  (forall o, body o <-> o = Ok (mkEffect r [] []) m0 evs0) ->
  forall o, after_copyins R body o <-> o = Ok (with_copyins R (mkEffect r [] [])) m0 evs0.
Proof.
  intros R body r m0 evs0 Hb o. unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply Hb in Hc. apply Ok_inj in Hc as (-> & -> & ->).
    cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). exists (mkEffect r [] []).
    split; [apply Hb; reflexivity|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. exfalso. exact (Unmodeled_Ok _ _ _ H).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Definition open_res (m : Model) (mk : word -> Model) (o : outcome SyscallEffect) : Prop :=
  (exists e, In e openat_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
      /\ o = Ok (mkEffect (alloc_fd (m_fds m)) [] []) (mk (alloc_fd (m_fds m))) []).

(* [comment removed for export] *)
Definition open_out (R : list (word * nat)) (m : Model) (mk : word -> Model)
    (o : outcome SyscallEffect) : Prop :=
  (exists e, In e openat_errnos
             /\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
  \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
      /\ o = Ok (with_copyins R (mkEffect (alloc_fd (m_fds m)) [] []))
                (mk (alloc_fd (m_fds m))) []).

Lemma open_result_outcome : forall m (mk : word -> Model -> Model) i o,
  open_result_spec m mk i m o <-> open_res m (fun fd => mk fd m) o.
Proof.
  intros m mk i o. unfold open_result_spec, open_res. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hfree & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [eexists; split; [split; [exact Hfree|reflexivity]|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma after_copyins_open : forall R body m mk,
  (forall o, body o <-> open_res m mk o) ->
  forall o, after_copyins R body o <-> open_out R m mk o.
Proof.
  intros R body m mk Hb o. unfold after_copyins, open_out. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply Hb in Hc.
    destruct Hc as [(e & He & Hc) | (Hfree & Hc)]; apply Ok_inj in Hc as (-> & -> & ->);
      cbn [eff_copyins]; rewrite app_nil_r.
    + left. exists e. auto.
    + right. auto.
  - intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [apply Hb; left; exists e; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + exists (mkEffect (alloc_fd (m_fds m)) [] []). split; [apply Hb; right; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. destruct H as [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma openat_spec_body : forall dirfd pathp flags i m o,
  modeled_open_flags flags = true ->
  openat_spec dirfd pathp flags i m o <->
  after_copyins (open_reads i pathp) (openat_body_spec i m dirfd pathp flags i m) o.
Proof.
  intros dirfd pathp flags i m o Hfl. unfold openat_spec.
  transitivity (record_copyins (open_reads i pathp) (openat_core_spec dirfd pathp flags) i m o).
  { unfold bind, input, open_reads. destruct o as [eff m' evs|]; split.
    - intros (i0 & m1 & evs1 & evs2 & Hi & Hk & ->). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. right. exists i, m, []. split; [reflexivity|exact Hk]. }
  rewrite record_copyins_iff.
  assert (Hcore : forall o', openat_core_spec dirfd pathp flags i m o' <->
                            openat_body_spec i m dirfd pathp flags i m o').
  { intros o'. unfold openat_core_spec. rewrite Hfl. cbn [negb].
    unfold bind, input, get_model. destruct o' as [eff m' evs|]; split.
    - intros (i0 & m1 & evs1 & evs2 & Hi & (m0 & m2 & evs3 & evs4 & Hm & Hb & ->) & ->).
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
      exists m, m, [], evs. split; [reflexivity|]. split; [exact Hb|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & [H | (m0 & m2 & evs2 & Hm & Hb)])];
        [exfalso; exact (Unmodeled_Ok _ _ _ H)| exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. right. exists i, m, []. split; [reflexivity|]. right.
      exists m, m, []. split; [reflexivity|exact Hb]. }
  unfold after_copyins. destruct o as [eff m' evs|]; [|apply Hcore].
  split; intros (core & Hc & ->); exists core; (split; [apply Hcore; exact Hc|reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma err_ret_outcome : forall e i m o,
  err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

Section Openat.
  Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
  Hypothesis Hfl : modeled_open_flags flags = true.

  (* [comment removed for export] *)
  #[using="Hfl"] Lemma openat_toolong_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrTooLong ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  #[using="Hfl"] Lemma openat_empty_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk [] ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. cbn [path_eqb]. apply err_ret_outcome.
  Qed.

  Hypothesis Hdir : dirfd = AT_FDCWD32.
  Hypothesis Hrd : Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z.

  (* [comment removed for export] *)
  #[using="Type"] Lemma no_slash_not_devnull : forall p, path_has_slash p = false -> path_eqb p devnull_path = false.
  Proof.
    intros p Hs. destruct (path_eqb p devnull_path) eqn:E; [|reflexivity].
    apply path_eqb_eq in E. subst p. discriminate Hs.
  Qed.

  #[using="Hdir Hrd"] Lemma openat_body_resolved : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    openat_body_spec i m dirfd pathp flags i m o <-> openat_read_spec p m i m o.
  Proof.
    intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec.
    rewrite Hsl, Hrd.
    reflexivity.
  Qed.

  #[using="Type"] Lemma not_dirref : forall p, p <> dot_path -> path_eqb p dotdot_path = false -> path_is_dirref p = false.
  Proof.
    intros p Hnd Hdd. unfold path_is_dirref. rewrite Hdd, orb_false_r.
    destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Hfl Hdir Hrd"] Lemma openat_absent_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
    path_has_slash p = false -> path_eqb p dotdot_path = false ->
    fs_lookup (m_fs m) p = None ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros p o Hp Hne Hnd Hsl Hdd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite (not_dirref p Hnd Hdd).
    rewrite Hfs. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  #[using="Hfl Hdir Hrd"] Lemma openat_dot_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk dot_path ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m) o.
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    intros o'. rewrite (openat_body_resolved dot_path o' Hp ltac:(discriminate) ltac:(reflexivity)).
    unfold openat_read_spec. change (path_is_dirref dot_path) with true. cbv iota. apply open_result_outcome.
  Qed.

  (* [comment removed for export] *)
  #[using="Hfl Hdir Hrd"] Lemma openat_file_outcome : forall p d o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
    path_has_slash p = false -> path_eqb p dotdot_path = false ->
    fs_lookup (m_fs m) p = Some d ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) o.
  Proof.
    intros p d o Hp Hne Hnd Hsl Hdd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite (not_dirref p Hnd Hdd).
    rewrite Hfs. apply open_result_outcome.
  Qed.
End Openat.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bind_input_model {A} : forall (k : SyscallInput -> Model -> Sys A) i m o,
  (bind input (fun i0 => bind get_model (fun m0 => k i0 m0))) i m o <-> k i m i m o.
Proof.
  intros k i m o. unfold bind, input, get_model. destruct o as [eff m' evs|]; split.
  - intros (i0 & m1 & e1 & e2 & Hi & (m0 & m2 & e3 & e4 & Hm & Hk & ->) & ->).
    apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
    exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
  - intros [H | (i0 & m1 & e1 & Hi & [H | (m0 & m2 & e2 & Hm & Hk)])];
      [exfalso; exact (Unmodeled_Ok _ _ _ H) | exfalso; exact (Unmodeled_Ok _ _ _ H) |].
    apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. right. exists i, m, []. split; [reflexivity|]. right.
    exists m, m, []. split; [reflexivity| exact Hk].
Qed.

Lemma cap_iovecs_aux_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned, IH by lia. reflexivity.
Qed.

Lemma cap_iovecs_id_rw : forall iovs,
  (iovs_total iovs <= rw_bytes_max)%Z -> cap_iovecs iovs = iovs.
Proof.
  intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
  unfold MAX_RW_COUNT. unfold rw_bytes_max in H. lia.
Qed.

(* [comment removed for export] *)
Lemma cap_iovecs_id_max : forall iovs,
  (iovs_total iovs <= MAX_RW_COUNT)%Z -> cap_iovecs iovs = iovs.
Proof. intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id. exact H. Qed.

Lemma gather_prefix_total0 : forall mp iovs,
  iovs_total iovs = 0%Z -> gather_prefix mp iovs = [].
Proof.
  intros mp iovs; induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  cbn [iovs_total] in H. pose proof (iovs_total_nonneg r). pose proof (word_unsigned_range n).
  assert (Hn : bv_unsigned n = 0%Z) by lia.
  cbn [gather_prefix]. unfold readable_bytes, word_to_nat. rewrite Hn.
  cbn [Z.to_nat readable_bytes_aux length Z.of_nat Z.eqb app]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma writev_chan_outcome : forall fd iov iovcnt i m o ch iovs bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= MAX_RW_COUNT)%Z ->
  gather_iovecs (in_mem i) iovs = Some bs ->
  (1 <= Z.of_nat (length bs))%Z ->
  let CA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
  writev_spec fd iov iovcnt i m o <->
  exists k, (1 <= k <= length bs)%nat /\
    o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
           m (map (WriteEv ch) (firstn k bs)).
Proof.
  intros fd iov iovcnt i m o ch iovs bs Hfd Hch Himp Htot Hg Hbs1.
  cbv zeta.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; exact Htot).
  assert (Herrk : forall k, (k <= length bs)%nat ->
            addr_is_error_b (len_word (firstn k bs)) = false).
  { intros k Hk. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (rewrite firstn_length_le by lia; unfold two_pow_64;
                                   unfold MAX_RW_COUNT in Htot; lia).
    rewrite firstn_length_le by lia. unfold MAX_RW_COUNT in Htot. lia. }
  unfold writev_spec.
  (* [comment removed for export] *)
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ds <- choose (fun ds : list byte =>
                       (1 <= Z.of_nat (length ds))%Z
                       /\ (Z.of_nat (length ds) < two_pow_64)%Z
                       /\ addr_is_error_b (len_word ds) = false
                       /\ ds = firstn (length ds) bs) ;;
        emit (map (WriteEv ch) ds) ;;
        record_copyins (iov_prefix_accesses (cap_iovecs iovs) (length ds))
          (ret_only (len_word ds)))%sys i m o).
  { rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
    rewrite Hfd, Hch, Himp. cbv zeta.
    unfold writev_gathered.
    rewrite Hcap, (gather_prefix_full _ _ _ Hg).
    replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (addr_is_error_b (len_word bs)) with false
      by (symmetry; rewrite <- (firstn_all bs); rewrite (Herrk (length bs)) by lia; reflexivity).
    reflexivity. }
  rewrite Hcap. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
      exists (length ds); rewrite <- Hds;
      assert (Hk : (length ds <= length bs)%nat)
        by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
    end.
    split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
  - intros (k & Hk & ->).
    assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
    eexists _, _, _, _. split.
    + eexists _, _, _, _. split.
      * exists (firstn k bs). split; [|reflexivity].
        rewrite Hlk. split; [lia|]. split; [unfold two_pow_64, MAX_RW_COUNT in *; lia|].
        split; [apply Herrk; lia|reflexivity].
      * split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
        eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + rewrite Hlk, !app_nil_r. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma writev_chan_zero_outcome : forall fd iov iovcnt i m o ch iovs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  iovs_total iovs = 0%Z ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
                       (mkEffect (Z_to_bv 64 0) [] [])) m [].
Proof.
  intros fd iov iovcnt i m o ch iovs Hfd Hch Himp Htot.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; unfold MAX_RW_COUNT; lia).
  unfold writev_spec.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ret_only (Z_to_bv 64 0)) i m o).
  { rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
    rewrite Hfd, Hch, Himp. cbv zeta. rewrite Hcap, Htot. cbn [Z.eqb].
    reflexivity. }
  rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition iirr {A} (c : Sys A) : Prop := forall i i' m o, c i m o -> c i' m o.

Lemma iirr_iff {A} : forall (c : Sys A), iirr c -> forall i i' m o, c i m o <-> c i' m o.
Proof. intros c H i i' m o. split; apply H. Qed.

Lemma iirr_const {A} : forall (f : Model -> outcome A -> Prop), iirr (fun _ => f).
Proof. intros f i i' m o H. exact H. Qed.

Lemma iirr_bind {A B} : forall (c : Sys A) (k : A -> Sys B),
  iirr c -> (forall x, iirr (k x)) -> iirr (bind c k).
Proof.
  intros c k Hc Hk i i' m o. unfold bind. destruct o as [y m2 evs|].
  - intros (x & m1 & evs1 & evs2 & H1 & H2 & ->). exists x, m1, evs1, evs2.
    split; [exact (Hc _ _ _ _ H1)|]. split; [exact (Hk _ _ _ _ _ H2)|reflexivity].
  - intros [H | (x & m1 & evs1 & H1 & H2)].
    + left. exact (Hc _ _ _ _ H).
    + right. exists x, m1, evs1. split; [exact (Hc _ _ _ _ H1)| exact (Hk _ _ _ _ _ H2)].
Qed.

Lemma iirr_alt {A} : forall (c1 c2 : Sys A), iirr c1 -> iirr c2 -> iirr (alt c1 c2).
Proof. intros c1 c2 H1 H2 i i' m o [H|H]; [left; exact (H1 _ _ _ _ H) | right; exact (H2 _ _ _ _ H)]. Qed.

Lemma iirr_if {A} : forall (b : bool) (c1 c2 : Sys A),
  iirr c1 -> iirr c2 -> iirr (if b then c1 else c2).
Proof. intros [|] c1 c2 H1 H2; assumption. Qed.

Lemma iirr_pure {A} : forall (x : A), iirr (pure x).            Proof. intros x. apply iirr_const. Qed.
Lemma iirr_unmodeled {A} : iirr (@unmodeled A).                 Proof. apply iirr_const. Qed.
Lemma iirr_choose {A} : forall (P : A -> Prop), iirr (choose P). Proof. intros P. apply iirr_const. Qed.
Lemma iirr_emit : forall evs, iirr (emit evs).                   Proof. intros evs. apply iirr_const. Qed.
Lemma iirr_get_model : iirr get_model.                           Proof. apply iirr_const. Qed.
Lemma iirr_get_fds : iirr get_fds.                               Proof. apply iirr_const. Qed.
Lemma iirr_get_vmmaps : iirr get_vmmaps.                         Proof. apply iirr_const. Qed.
Lemma iirr_modify : forall f, iirr (modify f).                   Proof. intros f. apply iirr_const. Qed.
Lemma iirr_ret_only : forall r, iirr (ret_only r).               Proof. intros r. apply iirr_const. Qed.
Lemma iirr_err_ret : forall e, iirr (err_ret e).                 Proof. intros e. apply iirr_const. Qed.
Lemma iirr_errno_from : forall es, iirr (errno_from es).         Proof. intros es. apply iirr_const. Qed.

Ltac solve_iirr :=
  lazymatch goal with
  | |- iirr (bind _ _) => apply iirr_bind; [solve_iirr | intros; solve_iirr]
  | |- iirr (alt _ _) => apply iirr_alt; solve_iirr
  | |- iirr (if _ then _ else _) => apply iirr_if; solve_iirr
  | |- iirr (match ?x with _ => _ end) => destruct x; solve_iirr
  | |- iirr ?c =>
      first [ apply iirr_const
            | apply iirr_pure | apply iirr_unmodeled | apply iirr_choose | apply iirr_emit
            | apply iirr_get_model | apply iirr_get_fds | apply iirr_get_vmmaps
            | apply iirr_modify | apply iirr_ret_only | apply iirr_err_ret | apply iirr_errno_from
            | let h := lazymatch c with ?h _ _ _ _ _ _ => h | ?h _ _ _ _ _ => h | ?h _ _ _ _ => h
                                        | ?h _ _ _ => h | ?h _ _ => h | ?h _ => h | ?h => h end in
              unfold h; cbv zeta; solve_iirr ]
  end.

Lemma brk_spec_iirr : forall req, iirr (brk_spec req).
Proof. intros. unfold brk_spec. cbv zeta. solve_iirr. Qed.

Lemma mmap_spec_iirr : forall a l p f d off, iirr (mmap_spec a l p f d off).
Proof. intros. unfold mmap_spec. cbv zeta. solve_iirr. Qed.

Lemma munmap_spec_iirr : forall a l, iirr (munmap_spec a l).
Proof. intros. unfold munmap_spec. cbv zeta. solve_iirr. Qed.

Lemma mprotect_spec_iirr : forall a l p, iirr (mprotect_spec a l p).
Proof. intros. unfold mprotect_spec. cbv zeta. solve_iirr. Qed.

Lemma mremap_spec_iirr : forall a ol nl f, iirr (mremap_spec a ol nl f).
Proof. intros. unfold mremap_spec. cbv zeta. solve_iirr. Qed.

(* [comment removed for export] *)

Lemma syscall_spec_25 : forall i m o,
  bv_unsigned (in_sysno i) = 25%Z ->
  syscall_spec i m o <-> fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

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
  syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bind_model : forall (k : Model -> Sys SyscallEffect) i m o,
  (bind get_model (fun m0 => k m0)) i m o <-> k m i m o.
Proof.
  intros k i m o. unfold bind, get_model. destruct o as [eff m' evs|]; split.
  - intros (m0 & m2 & e3 & e4 & Hm & Hk & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
  - intros [H | (m0 & m2 & e2 & Hm & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H) |].
    apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. right. exists m, m, []. split; [reflexivity| exact Hk].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_chan_outcome : forall fd buf count i m o ch bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  w_is0 count = false ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  write_spec fd buf count i m o <->
  exists k, (1 <= k <= length bs)%nat /\
    o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] [(buf, k)])
           m (map (WriteEv ch) (firstn k bs)).
Proof.
  intros fd buf count i m o ch bs Hfd Hch Hmax Hcnt0 Hbs.
  pose proof (read_bytes_map_length _ _ _ _ Hbs) as Hlen.
  assert (Hpos : (1 <= length bs)%nat).
  { destruct bs; [|cbn; lia]. cbn in Hlen. exfalso.
    unfold w_is0, bv_eqb in Hcnt0. rewrite <- Hlen in Hcnt0. cbn in Hcnt0. discriminate. }
  assert (Hrange : modeled_rw_range buf count = true).
  { unfold modeled_rw_range, modeled_rw_count. rewrite (proj2 (Z.leb_le _ _) Hmax). reflexivity. }
  assert (Hclamp : rw_count_clamp count = bv_unsigned count).
  { apply rw_count_clamp_small. unfold rw_bytes_max in Hmax. unfold MAX_RW_COUNT. lia. }
  unfold write_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd, Hch, Hrange, Hcnt0. cbn [negb]. cbv zeta.
  unfold write_source. rewrite Hclamp, Z_to_bv_bv_unsigned.
  rewrite (readable_bytes_full _ _ _ _ Hbs).
  replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
      exists (length ds); rewrite <- Hds;
      assert (Hk : (length ds <= length bs)%nat)
        by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
    end.
    split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
  - intros (k & Hk & ->).
    assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
    eexists _, _, _, _. split.
    + exists (firstn k bs). split; [|reflexivity]. rewrite Hlk. split; [lia|]. split; [|reflexivity].
      rewrite <- Hlen. lia.
    + split; [|rewrite app_nil_l; reflexivity].
      eexists _, _, _, _. split; [reflexivity|]. split; [|symmetry; apply app_nil_r].
      eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma exit_outcome : forall code i m o,
  exit_spec code i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [].
Proof.
  intros code i m o. unfold exit_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma close_badfd_outcome : forall fd i m o,
  fd_lookup (m_fds m) fd = None ->
  close_spec fd i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd i m o Hlk. unfold close_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma ioctl_badfd_outcome : forall fd req i m o,
  fd_lookup (m_fds m) fd = None ->
  ioctl_spec fd req i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd req i m o Hlk. unfold ioctl_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma set_tid_known_outcome : forall i m o t0,
  m_tid m = Some t0 ->
  set_tid_address_spec i m o <-> o = Ok (mkEffect t0 [] []) m [].
Proof.
  intros i m o t0 Htid. unfold set_tid_address_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Htid. split; reflexivity.
Qed.

Lemma read_badfd_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = None ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o Hlk. unfold read_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hlk. apply err_ret_outcome.
Qed.

Lemma read_filew_outcome : forall fd buf count i m o p off,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o p off Hlk. unfold read_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hlk. apply err_ret_outcome.
Qed.

(* [comment removed for export] *)
Lemma ioctl_any_outcome : forall fd req i m o e,
  fd_lookup (m_fds m) fd = Some e ->
  tty_only_request req = true ->
  bv_eqb req TIOCGWINSZ = true ->
  e <> FdUrandom ->      (* [comment removed for export] *)
  ioctl_spec fd req i m o <-> o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [].
Proof. intros. eapply ioctl_tty_outcome; eassumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_fd_aux_le : forall fuel fds cand,
  (bv_unsigned cand + Z.of_nat fuel < two_pow_64)%Z ->
  (bv_unsigned (alloc_fd_aux fds cand fuel)
     <= bv_unsigned cand + Z.of_nat fuel)%Z.
Proof.
  induction fuel as [|f IH]; intros fds cand Hb; cbn [alloc_fd_aux].
  - lia.
  - destruct (fd_lookup fds cand).
    + assert (Hu : bv_unsigned (cand + 1) = (bv_unsigned cand + 1)%Z).
      { rewrite bv_add_unsigned.
        replace (bv_unsigned (1 : word)) with 1%Z by reflexivity.
        apply bv_wrap_small.
        unfold bv_modulus. change (Z.of_N 64) with 64%Z.
        pose proof (word_unsigned_range cand). unfold two_pow_64 in *. lia. }
      specialize (IH fds (cand + 1)). rewrite Hu in IH. lia.
    + pose proof (word_unsigned_range cand). lia.
Qed.

Lemma alloc_fd_le : forall fds, (bv_unsigned (alloc_fd fds) <= 4096)%Z.
Proof.
  intro fds. unfold alloc_fd.
  pose proof (alloc_fd_aux_le 4096 fds (Z_to_bv 64 0)) as H.
  rewrite Z_to_bv_small in H
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  unfold two_pow_64 in H. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint listN_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && listN_eqb r1 r2
  | _, _ => false
  end.

Lemma listN_eqb_eq : forall l1 l2, listN_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|a r1 IH]; destruct l2 as [|b r2]; cbn;
    try (split; congruence).
  rewrite Bool.andb_true_iff, bv_eqb_eq, IH.
  split; [intros [-> ->]; auto | intro H; inversion H; auto].
Qed.

Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false
  end.

Lemma listNN_eqb_eq : forall l1 l2, listNN_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|[a1 n1] r1 IH]; destruct l2 as [|[a2 n2] r2]; cbn;
    try (split; congruence).
  rewrite !Bool.andb_true_iff, !bv_eqb_eq, IH.
  split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lseek_out (m : Model) (fd : word) (mk : word -> FdEntry) (base off : word) (o : outcome SyscallEffect) : Prop :=
  match lseek_dest base off with
  | None => o = Ok (mkEffect (errno_ret EINVAL) [] []) m []
  | Some r => o = Ok (mkEffect r [] []) (with_fds (fd_insert (m_fds m) fd (mk r)) m) []
  end.

Lemma lseek_file_outcome : forall fd off whence i m o p cur data base,
  fd_lookup (m_fds m) fd = Some (FdFile p cur) ->
  fs_lookup (m_fs m) p = Some data ->
  lseek_base whence cur (len_word data) = Some base ->
  lseek_spec fd off whence i m o <-> lseek_out m fd (fun r => FdFile p r) base off o.
Proof.
  intros fd off whence i m o p cur data base Hlk Hfs Hb.
  assert (Hw : (SEEK_MAX <? bv_unsigned whence)%Z = false).
  { unfold lseek_base in Hb. apply Z.ltb_ge. unfold SEEK_MAX.
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_SET); [unfold SEEK_SET in *; lia|].
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_CUR); [unfold SEEK_CUR in *; lia|].
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_END); [unfold SEEK_END in *; lia|]. discriminate. }
  unfold lseek_spec. rewrite bind_model. cbv beta. rewrite Hlk, Hw, Hfs, Hb. unfold lseek_out.
  destruct (lseek_dest base off) as [r|].
  - sys_unfold. split.
    + destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
    + intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
  - apply err_ret_outcome.
Qed.

Lemma lseek_filew_outcome : forall fd off whence i m o p cur data base,
  fd_lookup (m_fds m) fd = Some (FdFileW p cur) ->
  fs_lookup (m_fs m) p = Some data ->
  lseek_base whence cur (len_word data) = Some base ->
  lseek_spec fd off whence i m o <-> lseek_out m fd (fun r => FdFileW p r) base off o.
Proof.
  intros fd off whence i m o p cur data base Hlk Hfs Hb.
  assert (Hw : (SEEK_MAX <? bv_unsigned whence)%Z = false).
  { unfold lseek_base in Hb. apply Z.ltb_ge. unfold SEEK_MAX.
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_SET); [unfold SEEK_SET in *; lia|].
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_CUR); [unfold SEEK_CUR in *; lia|].
    destruct (Z.eqb_spec (bv_unsigned whence) SEEK_END); [unfold SEEK_END in *; lia|]. discriminate. }
  unfold lseek_spec. rewrite bind_model. cbv beta. rewrite Hlk, Hw, Hfs, Hb. unfold lseek_out.
  destruct (lseek_dest base off) as [r|].
  - sys_unfold. split.
    + destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
    + intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
  - apply err_ret_outcome.
Qed.

Lemma lseek_badfd_outcome : forall fd off whence i m o,
  fd_lookup (m_fds m) fd = None ->
  lseek_spec fd off whence i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd off whence i m o Hlk. unfold lseek_spec. rewrite bind_model. cbv beta. rewrite Hlk. apply err_ret_outcome.
Qed.

(* [comment removed for export] *)
Lemma lseek_null_outcome : forall fd off whence i m o,
  fd_lookup (m_fds m) fd = Some FdNull ->
  (bv_unsigned whence <= SEEK_MAX)%Z ->
  lseek_spec fd off whence i m o <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [].
Proof.
  intros fd off whence i m o Hlk Hw. unfold lseek_spec. rewrite bind_model. cbv beta. rewrite Hlk.
  rewrite (proj2 (Z.ltb_ge _ _) Hw). unfold ret_only, pure. reflexivity.
Qed.

Lemma lseek_chan_outcome : forall fd off whence i m o c,
  fd_lookup (m_fds m) fd = Some (FdChannel c) ->
  (bv_unsigned whence <= SEEK_MAX)%Z ->
  lseek_spec fd off whence i m o <-> o = Ok (mkEffect (errno_ret ESPIPE) [] []) m [].
Proof.
  intros fd off whence i m o c Hlk Hw. unfold lseek_spec. rewrite bind_model. cbv beta. rewrite Hlk.
  rewrite (proj2 (Z.ltb_ge _ _) Hw). apply err_ret_outcome.
Qed.

(* [comment removed for export] *)

Lemma create_wronly_outcome : forall p m i o,
  create_wronly p m i m o <->
  open_res m (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs m) p []) m)) o.
Proof.
  intros p m i o. unfold create_wronly, open_res. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hfree & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [eexists; split; [split; [exact Hfree|reflexivity]|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Section OpenatCreate.
  Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
  Hypothesis Hdir : dirfd = AT_FDCWD32.
  Hypothesis Hwr : Z.ldiff (bv_unsigned flags) open_ignored_flags = wr_create_flags.

  #[using="Hwr"] Lemma modeled_open_flags_wr : modeled_open_flags flags = true.
  Proof. unfold modeled_open_flags. rewrite Hwr. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_body_create : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    openat_body_spec i m dirfd pathp flags i m o <-> openat_create_spec p m i m o.
  Proof.
    intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec.
    rewrite Hsl, Hwr. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_body_devnull : forall o,
    read_cstr (in_mem i) pathp = CstrOk devnull_path ->
    fs_lookup (m_fs m) devnull_path = None ->
    fs_under (m_fs m) devnull_path = false ->
    openat_body_spec i m dirfd pathp flags i m o <-> open_devnull m false true i m o.
  Proof.
    intros o Hp Hlk Hun. unfold openat_body_spec. rewrite Hp.
    change (path_eqb devnull_path []) with false. cbv iota.
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec.
    change (path_has_slash devnull_path) with true. cbv iota.
    unfold openat_sep_spec. change (path_eqb devnull_path localtime_path) with false. cbv iota.
    rewrite path_eqb_refl. unfold openat_devnull_spec. rewrite Hlk, Hun. cbv zeta. rewrite Hwr. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_create_dirref_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    write_dirref p m = true ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret EISDIR) [] [])) m [].
  Proof.
    intros p o Hp Hne Hsl Hd. rewrite (openat_spec_body _ _ _ _ _ _ modeled_open_flags_wr). apply after_copyins_det.
    intros o'. rewrite (openat_body_create p o' Hp Hne Hsl).
    unfold openat_create_spec. fold (write_dirref p m). rewrite Hd. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_create_dot_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk dot_path ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret EISDIR) [] [])) m [].
  Proof.
    intros o Hp. apply (openat_create_dirref_outcome dot_path o Hp); [discriminate|reflexivity|reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_create_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    write_dirref p m = false ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs m) p []) m)) o.
  Proof.
    intros p o Hp Hne Hsl Hd. rewrite (openat_spec_body _ _ _ _ _ _ modeled_open_flags_wr). apply after_copyins_open.
    intros o'. rewrite (openat_body_create p o' Hp Hne Hsl). unfold openat_create_spec.
    fold (write_dirref p m). rewrite Hd. apply create_wronly_outcome.
  Qed.

  (* [comment removed for export] *)
  #[using="Hdir Hwr"] Lemma openat_devnull_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk devnull_path ->
    fs_lookup (m_fs m) devnull_path = None ->
    fs_under (m_fs m) devnull_path = false ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdNull) m) o.
  Proof.
    intros o Hp Hlk Hun. rewrite (openat_spec_body _ _ _ _ _ _ modeled_open_flags_wr). apply after_copyins_open.
    intros o'. rewrite (openat_body_devnull o' Hp Hlk Hun). unfold open_devnull.
    apply open_result_outcome.
  Qed.
End OpenatCreate.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs_noabs (fs : Fs) : Prop :=
  Forall (fun pf => key_is_relative (fst pf) \/ exists n, fst pf = tmp_key n) fs.

(* [comment removed for export] *)
Definition key_ok (p : path) : Prop := key_is_relative p \/ exists n, p = tmp_key n.

Lemma fs_noabs_seed : forall fs t, fs_keys_relative fs -> fs_noabs (fs_seed_tmp fs t).
Proof. intros fs t H. exact (seeded_absolute_key_is_tmp t fs H). Qed.

(* [comment removed for export] *)
Lemma in_fs_noabs : forall inp, fs_keys_relative (in_image_fs inp) -> fs_noabs (in_fs inp).
Proof. intros inp H. unfold in_fs. exact (fs_noabs_seed _ _ H). Qed.

(* [comment removed for export] *)
Lemma fs_noabs_divergent : forall fs r i a b,
  fs_noabs fs ->
  nth_error (path_slash_byte :: r) i = Some a ->
  nth_error tmp_prefix i = Some b ->
  a <> b ->
  fs_lookup fs (path_slash_byte :: r) = None /\ fs_under fs (path_slash_byte :: r) = false.
Proof.
  intros fs r i a b Hall Hp Ht Hab.
  assert (Hi : (i < length (path_slash_byte :: r))%nat)
    by (apply nth_error_Some; rewrite Hp; discriminate).
  assert (Hj : (i < length tmp_prefix)%nat)
    by (apply nth_error_Some; rewrite Ht; discriminate).
  split.
  - apply fs_lookup_none_of_keys.
    eapply Forall_impl; [|exact Hall]. intros [q d] Hq. cbn [fst] in Hq |- *.
    destruct Hq as [Hq|[n Hq]]; intros Heq.
    + rewrite Heq in Hq. unfold key_is_relative in Hq. exact (Hq eq_refl).
    + assert (Hx : nth_error q i = Some b)
        by (rewrite Hq; unfold tmp_key; rewrite nth_error_app1 by exact Hj; exact Ht).
      rewrite Heq, Hp in Hx. inversion Hx. now apply Hab.
  - apply fs_under_false_of_keys.
    eapply Forall_impl; [|exact Hall]. intros [q d] Hq. cbn [fst] in Hq |- *.
    destruct Hq as [Hq|[n Hq]].
    + destruct q as [|c q]; [reflexivity|].
      unfold key_is_relative in Hq. cbn [dir_prefixb].
      destruct (bv_eqb path_slash_byte c) eqn:Hc; [|reflexivity].
      exfalso. apply bv_eqb_eq in Hc. apply Hq. now symmetry.
    + destruct (dir_prefixb (path_slash_byte :: r) q) eqn:Hd; [|reflexivity].
      exfalso. apply dir_prefixb_app in Hd. destruct Hd as [rest Hrest].
      assert (Hx : nth_error q i = Some b)
        by (rewrite Hq; unfold tmp_key; rewrite nth_error_app1 by exact Hj; exact Ht).
      rewrite Hrest in Hx. rewrite nth_error_app1 in Hx by exact Hi.
      rewrite Hp in Hx. inversion Hx. now apply Hab.
Qed.

(* [comment removed for export] *)
Lemma fs_noabs_devnull : forall fs, fs_noabs fs ->
  fs_lookup fs devnull_path = None /\ fs_under fs devnull_path = false.
Proof.
  intros fs H.
  assert (Hd : Z_to_bv 8 100 <> Z_to_bv 8 116)
    by (intros E; apply (proj2 (bv_eqb_eq _ _)) in E; vm_compute in E; discriminate).
  change devnull_path with (path_slash_byte :: tl devnull_path).
  apply (fs_noabs_divergent fs (tl devnull_path) 1%nat (Z_to_bv 8 100) (Z_to_bv 8 116) H);
    [reflexivity|reflexivity|exact Hd].
Qed.

Lemma fs_noabs_lookup_devnull : forall fs, fs_noabs fs -> fs_lookup fs devnull_path = None.
Proof. intros fs H. exact (proj1 (fs_noabs_devnull fs H)). Qed.

Lemma fs_noabs_under_devnull : forall fs, fs_noabs fs -> fs_under fs devnull_path = false.
Proof. intros fs H. exact (proj2 (fs_noabs_devnull fs H)). Qed.

(* [comment removed for export] *)
Lemma fs_noabs_key : forall fs p,
  fs_noabs fs -> fs_lookup fs p <> None -> key_ok p.
Proof.
  intros fs p H Hl. induction H as [|[q d] r Hq _ IH]; [exfalso; apply Hl; reflexivity|].
  cbn [fs_lookup fst] in *. destruct (path_eqb p q) eqn:E; [|exact (IH Hl)].
  apply path_eqb_eq in E. subst q. exact Hq.
Qed.

Lemma fs_noabs_set : forall fs p d,
  fs_noabs fs -> key_ok p -> fs_noabs (fs_set fs p d).
Proof.
  intros fs p d H Hp. unfold fs_noabs. apply (fs_set_keys (fun q => key_is_relative q \/ exists n, q = tmp_key n)); assumption.
Qed.

Lemma fs_noabs_remove : forall fs p, fs_noabs fs -> fs_noabs (fs_remove fs p).
Proof.
  intros fs p H. induction H as [|[q e] r Hq Hr IH]; cbn [fs_remove]; [constructor|].
  destruct (path_eqb p q); [exact Hr|]. constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma no_slash_not_absolute : forall p, path_has_slash p = false -> key_ok p.
Proof.
  intros [|b p] H; left; [exact I|]. unfold path_has_slash in H. cbn [existsb] in H.
  apply orb_false_iff in H as [H _]. unfold key_is_relative. intros E. subst b.
  unfold path_slash_byte, slash_byte in H. rewrite bv_eqb_refl in H. discriminate.
Qed.

(* [comment removed for export] *)

Definition unlink_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
  [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

(* [comment removed for export] *)
Lemma strip_no_slash : forall p, path_has_slash p = false -> path_strip_trailing_slashes p = p.
Proof.
  intros p H. unfold path_strip_trailing_slashes.
  assert (Hr : path_has_slash (rev p) = false).
  { unfold path_has_slash in *. destruct (existsb _ (rev p)) eqn:E; [|reflexivity].
    apply existsb_exists in E as (x & Hin & Hx). apply in_rev in Hin.
    assert (existsb (fun b => bv_eqb b slash_byte) p = true) by (apply existsb_exists; exists x; auto). congruence. }
  assert (Hd : forall q, path_has_slash q = false -> drop_leading_slashes q = q).
  { intros [|c q] Hq; [reflexivity|]. cbn [drop_leading_slashes]. unfold path_has_slash in Hq. cbn [existsb] in Hq.
    apply orb_false_iff in Hq as [-> _]. reflexivity. }
  rewrite (Hd _ Hr). apply rev_involutive.
Qed.

Lemma trailing_no_slash : forall p, path_has_slash p = false -> path_trailing_slash p = false.
Proof. intros p H. unfold path_trailing_slash. rewrite (strip_no_slash p H), Nat.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Definition unlink_out (R : list (word * nat)) (m : Model) (p : path) (rmdir : bool)
    (o : outcome SyscallEffect) : Prop :=
  match fs_lookup (m_fs m) p with
  | None => o = Ok (with_copyins R (mkEffect (errno_ret ENOENT) [] [])) m []
  | Some _ =>
      if rmdir then o = Ok (with_copyins R (mkEffect (errno_ret ENOTDIR) [] [])) m []
      else (exists e, In e unlinkat_errnos /\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
           \/ o = Ok (with_copyins R (mkEffect (Z_to_bv 64 0) [] [])) (with_fs (fs_remove (m_fs m) p) m) []
  end.

Lemma unlinkat_outcome : forall dirfd pathp flags i m o p,
  dirfd = AT_FDCWD32 ->
  modeled_unlink_flags flags = true ->
  read_cstr (in_mem i) pathp = CstrOk p ->
  p <> [] -> p <> dot_path -> p <> dotdot_path ->
  path_has_slash p = false -> (length p <= NAME_MAX)%nat ->
  fs_under (m_fs m) p = false ->
  (unlink_rmdir flags = false -> fd_names_path (m_fds m) p = false) ->
  unlinkat_spec dirfd pathp flags i m o <-> unlink_out (unlink_reads i pathp) m p (unlink_rmdir flags) o.
Proof.
  intros dirfd pathp flags i m o p Hdir Hfl Hp Hne Hnd Hndd Hsl Hlen Hu Hfds.
  unfold unlinkat_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta. rewrite Hfl. cbn [negb].
  rewrite record_copyins_iff. fold (unlink_reads i pathp).
  assert (Hbody : forall o', unlinkat_body_spec dirfd pathp flags i m i m o' <->
            (match fs_lookup (m_fs m) p with
             | None => err_ret ENOENT
             | Some _ => if unlink_rmdir flags then err_ret ENOTDIR
                         else alt (e <- errno_from unlinkat_errnos ;; err_ret e)
                                  (set_fs (fs_remove (m_fs m) p) ;; ret_only (Z_to_bv 64 0))
             end)%sys i m o').
  { intros o'. unfold unlinkat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. cbv zeta. rewrite (strip_no_slash p Hsl).
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    replace (path_eqb p dot_path) with false
      by (destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity]).
    replace (path_eqb p dotdot_path) with false
      by (destruct (path_eqb p dotdot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity]).
    rewrite Hsl. replace (NAME_MAX <? length p)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite Hu.
    destruct (fs_lookup (m_fs m) p) eqn:Hl; [|reflexivity].
    unfold unlink_found_spec.   (* [comment removed for export] *)
    destruct (unlink_rmdir flags) eqn:Hr; [reflexivity|].
    rewrite (trailing_no_slash p Hsl), (Hfds eq_refl). reflexivity. }
  unfold unlink_out.
  destruct (fs_lookup (m_fs m) p) eqn:Hl.
  2:{ apply after_copyins_det. intros o'. rewrite Hbody. apply err_ret_outcome. }
  destruct (unlink_rmdir flags) eqn:Hr.
  { apply after_copyins_det. intros o'. rewrite Hbody. apply err_ret_outcome. }
  unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply Hbody in Hc. revert Hc. sys_unfold. intros Hc. inv_sys.
    + left. eexists. split; [eassumption|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + right. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros [(e & He & H) | H]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [|cbn [eff_copyins]; rewrite app_nil_r; reflexivity].
      apply Hbody. sys_unfold. left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + exists (mkEffect (Z_to_bv 64 0) [] []). split; [|cbn [eff_copyins]; rewrite app_nil_r; reflexivity].
      apply Hbody. sys_unfold. right. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
  - intros H. apply Hbody in H. revert H. sys_unfold. intros H. inv_sys.
  - intros [(e & _ & H) | H]; discriminate H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma writev_file_outcome : forall fd iov iovcnt i m o p off data iovs bs,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  fs_lookup (m_fs m) p = Some data ->
  (bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= MAX_RW_COUNT)%Z ->
  (bv_unsigned off + iovs_total iovs <= 2^63 - 1)%Z ->
  gather_iovecs (in_mem i) iovs = Some bs ->
  (1 <= Z.of_nat (length bs))%Z ->
  let CA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
  writev_spec fd iov iovcnt i m o <->
  o = Ok (mkEffectU (len_word bs) [] [] [] [] (CA ++ iov_prefix_accesses iovs (length bs)))
         (with_fds (fd_insert (m_fds m) fd (FdFileW p (off + len_word bs)))
            (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)) [].
Proof.
  intros fd iov iovcnt i m o p off data iovs bs Hfd Hfs Hgap Himp Htot Hpos Hg Hbs1.
  cbv zeta.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; exact Htot).
  assert (Herr : addr_is_error_b (len_word bs) = false).
  { unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (unfold two_pow_64; unfold MAX_RW_COUNT in Htot; lia).
    unfold MAX_RW_COUNT in Htot. lia. }
  unfold writev_spec.
  rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. unfold writev_file_arm. rewrite record_copyins_iff, Himp. cbv zeta.
  unfold writev_gathered.
  rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (rw_pos_einvalb off (iovs_total iovs)) with false
    by (symmetry; unfold rw_pos_einvalb; apply Z.ltb_ge; lia).
  replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hfs. rewrite (file_gap_in_range _ _ _ Hgap). rewrite Herr.
  unfold writev_ledger. rewrite Hcap.
  unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). revert Hc. sys_unfold. intros Hc. inv_sys. rewrite !app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->).
    exists (mkEffectU (len_word bs) [] [] [] [] (iov_prefix_accesses iovs (length bs))). split; [|reflexivity].
    sys_unfold. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite app_nil_r. split; reflexivity.
  - sys_unfold. intros H. inv_sys.
  - intros H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma writev_null_outcome : forall fd iov iovcnt i m o iovs,
  fd_lookup (m_fds m) fd = Some FdNull ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= MAX_RW_COUNT)%Z ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
                       (mkEffect (Z_to_bv 64 (iovs_total iovs)) [] [])) m [].
Proof.
  intros fd iov iovcnt i m o iovs Hfd Himp Htot.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; exact Htot).
  unfold writev_spec.
  rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. cbn [negb]. cbv iota. rewrite Himp, Hcap.
  rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma path_eqb_sym : forall p q, path_eqb p q = path_eqb q p.
Proof.
  intros p q. destruct (path_eqb p q) eqn:E1; destruct (path_eqb q p) eqn:E2; try reflexivity.
  - apply path_eqb_eq in E1. subst. rewrite path_eqb_refl in E2. discriminate.
  - apply path_eqb_eq in E2. subst. rewrite path_eqb_refl in E1. discriminate.
Qed.

Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof. intros p q H. destruct (path_eqb p q) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity]. Qed.

Lemma fs_lookup_set_same : forall fs p data, fs_lookup (fs_set fs p data) p = Some data.
Proof.
  induction fs as [|[q d] r IH]; intros p data; cbn [fs_set fs_lookup].
  - rewrite path_eqb_refl. reflexivity.
  - destruct (path_ltb p q); cbn [fs_lookup]; [rewrite path_eqb_refl; reflexivity|].
    destruct (path_eqb p q) eqn:E; cbn [fs_lookup]; [rewrite path_eqb_refl; reflexivity|].
    rewrite E. apply IH.
Qed.

Lemma fs_lookup_set_other : forall fs p q data, q <> p -> fs_lookup (fs_set fs p data) q = fs_lookup fs q.
Proof.
  induction fs as [|[q0 d] r IH]; intros p q data Hne; cbn [fs_set fs_lookup].
  - rewrite (path_eqb_neq _ _ Hne). reflexivity.
  - destruct (path_ltb p q0); cbn [fs_lookup]; [rewrite (path_eqb_neq _ _ Hne); reflexivity|].
    destruct (path_eqb p q0) eqn:E; cbn [fs_lookup].
    + apply path_eqb_eq in E. subst q0. rewrite (path_eqb_neq _ _ Hne). reflexivity.
    + destruct (path_eqb q q0); [reflexivity|]. apply IH. exact Hne.
Qed.

Lemma fs_lookup_set_not_none : forall fs p q data,
  fs_lookup fs q <> None -> fs_lookup (fs_set fs p data) q <> None.
Proof.
  intros fs p q data H. destruct (list_eq_dec (@bv_eq_dec 8) q p) as [->|Hne].
  - rewrite fs_lookup_set_same. discriminate.
  - rewrite fs_lookup_set_other by exact Hne. exact H.
Qed.

Lemma fs_lookup_remove_other : forall fs p q, q <> p -> fs_lookup (fs_remove fs p) q = fs_lookup fs q.
Proof.
  induction fs as [|[q0 d] r IH]; intros p q Hne; cbn [fs_remove fs_lookup]; [reflexivity|].
  destruct (path_eqb p q0) eqn:E; cbn [fs_lookup].
  - apply path_eqb_eq in E. subst q0. rewrite (path_eqb_neq _ _ Hne). reflexivity.
  - destruct (path_eqb q q0); [reflexivity|]. apply IH. exact Hne.
Qed.

(* [comment removed for export] *)
Lemma dir_prefixb_no_slash : forall p q, path_has_slash q = false -> dir_prefixb p q = false.
Proof.
  induction p as [|a p IH]; intros [|b q] H; cbn [dir_prefixb]; try reflexivity.
  - unfold path_has_slash in H. cbn [existsb] in H. apply orb_false_iff in H as [H _]. exact H.
  - unfold path_has_slash in H. cbn [existsb] in H. apply orb_false_iff in H as [_ H].
    fold (path_has_slash q) in H. rewrite (IH q H). apply andb_false_r.
Qed.

Lemma fs_under_set : forall fs q d p,
  fs_under (fs_set fs q d) p = dir_prefixb p q || fs_under fs p.
Proof.
  induction fs as [|[k e] r IH]; intros q d p; cbn [fs_set fs_under]; [reflexivity|].
  destruct (path_ltb q k); [reflexivity|].
  destruct (path_eqb q k) eqn:E.
  - apply path_eqb_eq in E. subst k. cbn [fs_under]. destruct (dir_prefixb p q); reflexivity.
  - cbn [fs_under]. rewrite IH. destruct (dir_prefixb p k), (dir_prefixb p q); reflexivity.
Qed.

Lemma fs_under_key : forall fs q p,
  fs_lookup fs q <> None -> dir_prefixb p q = true -> fs_under fs p = true.
Proof.
  induction fs as [|[k e] r IH]; intros q p Hl Hd; cbn [fs_lookup fs_under] in *; [congruence|].
  destruct (path_eqb q k) eqn:E.
  - apply path_eqb_eq in E. subst k. rewrite Hd. reflexivity.
  - rewrite (IH q p Hl Hd). apply orb_true_r.
Qed.

Lemma fs_under_set_no_slash : forall fs q d p,
  path_has_slash q = false -> fs_under (fs_set fs q d) p = fs_under fs p.
Proof. intros fs q d p H. rewrite fs_under_set, (dir_prefixb_no_slash p q H). reflexivity. Qed.

Lemma fs_under_set_present : forall fs q d p,
  fs_lookup fs q <> None -> fs_under (fs_set fs q d) p = fs_under fs p.
Proof.
  intros fs q d p Hl. rewrite fs_under_set. destruct (dir_prefixb p q) eqn:E; [|reflexivity].
  cbn [orb]. symmetry. eapply fs_under_key; eassumption.
Qed.

Lemma fs_under_remove_no_slash : forall fs q p,
  path_has_slash q = false -> fs_under (fs_remove fs q) p = fs_under fs p.
Proof.
  induction fs as [|[k e] r IH]; intros q p H; cbn [fs_remove fs_under]; [reflexivity|].
  destruct (path_eqb q k) eqn:E.
  - apply path_eqb_eq in E. subst k. rewrite (dir_prefixb_no_slash p q H). reflexivity.
  - cbn [fs_under]. rewrite IH by exact H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fd_names_path_false : forall fds p k q off,
  fd_names_path fds p = false ->
  (fd_lookup fds k = Some (FdFile q off) \/ fd_lookup fds k = Some (FdFileW q off)) -> q <> p.
Proof.
  induction fds as [|[k0 e0] r IH]; intros p k q off Hn Hk.
  - destruct Hk as [Hk|Hk]; discriminate Hk.
  - cbn [fd_lookup] in Hk. cbn [fd_names_path] in Hn.
    destruct (bv_eqb k0 k).
    + destruct Hk as [Hk|Hk]; inversion Hk; subst; apply orb_false_iff in Hn as [Hn _];
        intros ->; rewrite path_eqb_refl in Hn; discriminate.
    + apply (IH p k q off); [|exact Hk]. destruct e0; try exact Hn; apply orb_false_iff in Hn as [_ Hn]; exact Hn.
Qed.

(* [comment removed for export] *)

Lemma unsigned_small64 : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* [comment removed for export] *)
Fixpoint scatterw (iovs : list (word * word)) (bs : list byte) : list (word * list byte) :=
  match bs with
  | [] => []
  | _ :: _ =>
      match iovs with
      | [] => []
      | (base, len) :: rest =>
          let n := word_to_nat_bounded len (length bs) in
          match firstn n bs with
          | [] => scatterw rest (skipn n bs)
          | here => (base, here) :: scatterw rest (skipn n bs)
          end
      end
  end.

(* [comment removed for export] *)
Definition iov_writable (mp : word -> option byte) (iov : word * word) : Prop :=
  forall n, (Z.of_nat n <= bv_unsigned (snd iov))%Z -> read_bytes_map mp (fst iov) (Z_to_bv 64 (Z.of_nat n)) <> None.

Lemma scatter_iovecs_writable : forall mp iovs bs,
  Forall (iov_writable mp) iovs ->
  (Z.of_nat (length bs) <= iovs_total iovs)%Z ->
  scatter_iovecs mp iovs bs = Some (scatterw iovs bs).
Proof.
  intros mp iovs. induction iovs as [|[base len] rest IH]; intros bs Hw Hlen.
  - cbn in Hlen. destruct bs; [reflexivity|cbn in Hlen; lia].
  - destruct bs as [|b bs']; [reflexivity|].
    apply Forall_cons_iff in Hw as [H1 Hrest]. cbn [iovs_total fst snd] in Hlen.
    cbn [scatter_iovecs scatterw].
    set (n := word_to_nat_bounded len (length (b :: bs'))).
    assert (Hn : (n <= word_to_nat len)%nat /\ (n <= length (b :: bs'))%nat).
    { subst n. rewrite word_to_nat_bounded_eq_min. split; [apply Nat.le_min_l|apply Nat.le_min_r]. }
    assert (Hlater : (Z.of_nat (length (skipn n (b :: bs'))) <= iovs_total rest)%Z).
    { rewrite length_skipn. subst n. rewrite word_to_nat_bounded_eq_min. unfold word_to_nat.
      pose proof (bv_unsigned_in_range 64 len). pose proof (iovs_total_nonneg rest). cbn [length] in *.
      destruct (Nat.le_ge_cases (Z.to_nat (bv_unsigned len)) (S (length bs'))).
      - rewrite Nat.min_l by lia. lia.
      - rewrite Nat.min_r by lia. lia. }
    destruct (firstn n (b :: bs')) as [|h here'] eqn:Eh.
    + apply IH; assumption.
    + rewrite (IH _ Hrest Hlater).
      assert (Hr : read_bytes_map mp base (len_word (h :: here')) <> None).
      { unfold len_word. rewrite <- Eh. apply H1. cbn [snd]. rewrite length_firstn.
        unfold word_to_nat in Hn. pose proof (bv_unsigned_in_range 64 len). lia. }
      destruct (read_bytes_map mp base (len_word (h :: here'))); [reflexivity|congruence].
Qed.

(* [comment removed for export] *)
Lemma readv_file_outcome : forall fd iov iovcnt i m o p off data iovs,
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  fs_lookup (m_fs m) p = Some data ->
  iovcnt32 iovcnt = iovcnt ->
  (bv_unsigned iovcnt <= UIO_FASTIOV)%Z ->
  import_iovecs (in_mem i) iov iovcnt = ImpOk iovs ->
  (1 <= iovs_total iovs <= MAX_RW_COUNT)%Z ->
  (bv_unsigned off + iovs_total iovs <= 2^63 - 1)%Z ->
  Forall (iov_writable (in_wmem i)) iovs ->
  let bs := file_read data off (Z_to_bv 64 (iovs_total iovs)) in
  readv_spec fd iov iovcnt i m o <->
  o = Ok (mkEffectU (len_word bs) (scatterw iovs bs) [] [] [] (import_iovecs_accesses (in_mem i) iov iovcnt))
         (with_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) m) [].
Proof.
  intros fd iov iovcnt i m o p off data iovs Hfd Hfs Hcnt32 Hcnt Himp Htot Hpos Hwr. cbv zeta.
  set (bs := file_read data off (Z_to_bv 64 (iovs_total iovs))).
  unfold MAX_RW_COUNT in Htot.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; unfold MAX_RW_COUNT; lia).
  assert (Hlenbs : (Z.of_nat (length bs) <= iovs_total iovs)%Z).
  { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat.
    rewrite unsigned_small64 by lia. lia. }
  assert (Herr : addr_is_error_b (len_word bs) = false).
  { unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (unfold two_pow_64; lia). lia. }
  assert (Hheap : readv_heap_iovecb iovcnt = false).
  { unfold readv_heap_iovecb. rewrite Hcnt32. cbv zeta. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  unfold readv_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. cbn [readable_fd]. rewrite Hheap, record_copyins_iff, !Hcnt32, Himp.
  unfold readv_imported. rewrite Hcap. cbv zeta.
  replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Hfs.
  replace (rw_pos_einvalb off (iovs_total iovs)) with false
    by (symmetry; unfold rw_pos_einvalb; apply Z.ltb_ge; lia).
  fold bs. rewrite (scatter_iovecs_writable _ _ _ Hwr Hlenbs), Herr.
  unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). revert Hc. sys_unfold. intros Hc. inv_sys. rewrite !app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->).
    exists (mkEffect (len_word bs) (scatterw iovs bs) []). split; [|rewrite app_nil_r; reflexivity].
    sys_unfold. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
  - sys_unfold. intros H. inv_sys.
  - intros H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma readv_dir_outcome : forall fd iov iovcnt i m o iovs,
  fd_lookup (m_fds m) fd = Some FdDir ->
  iovcnt32 iovcnt = iovcnt ->
  (bv_unsigned iovcnt <= UIO_FASTIOV)%Z ->
  import_iovecs (in_mem i) iov iovcnt = ImpOk iovs ->
  (1 <= iovs_total iovs <= MAX_RW_COUNT)%Z ->
  readv_spec fd iov iovcnt i m o <->
  o = Ok (mkEffectU (errno_ret EISDIR) [] [] [] [] (import_iovecs_accesses (in_mem i) iov iovcnt)) m [].
Proof.
  intros fd iov iovcnt i m o iovs Hfd Hcnt32 Hcnt Himp Htot.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_max; lia).
  assert (Hheap : readv_heap_iovecb iovcnt = false).
  { unfold readv_heap_iovecb. rewrite Hcnt32. cbv zeta. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  unfold readv_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hfd. cbn [readable_fd]. rewrite Hheap, record_copyins_iff, !Hcnt32, Himp.
  unfold readv_imported. rewrite Hcap. cbv zeta.
  replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). revert Hc. sys_unfold. intros Hc. inv_sys. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->).
    exists (mkEffect (errno_ret EISDIR) [] []). split; [|cbn [eff_copyins]; rewrite app_nil_r; reflexivity]. sys_unfold. reflexivity.
  - sys_unfold. intros H. inv_sys.
  - intros H. discriminate H.
Qed.

Lemma readv_badfd_outcome : forall fd iov iovcnt i m o,
  fd_lookup (m_fds m) fd = None ->
  readv_spec fd iov iovcnt i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd iov iovcnt i m o Hfd.
  unfold readv_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta. rewrite Hfd. apply err_ret_outcome.
Qed.

Lemma readv_filew_outcome : forall fd iov iovcnt i m o p off,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  readv_spec fd iov iovcnt i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd iov iovcnt i m o p off Hfd.
  unfold readv_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta. rewrite Hfd. cbn [readable_fd]. apply err_ret_outcome.
Qed.

(* [comment removed for export] *)
Lemma readv_null_outcome : forall fd iov iovcnt i m o,
  fd_lookup (m_fds m) fd = Some FdNull ->
  readv_spec fd iov iovcnt i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd iov iovcnt i m o Hfd.
  unfold readv_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta. rewrite Hfd. cbn [readable_fd]. apply err_ret_outcome.
Qed.

Lemma read_null_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = Some FdNull ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o Hlk. unfold read_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
  rewrite Hlk. apply err_ret_outcome.
Qed.

