(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start model's vDSO state, channel reader and reserved ledger). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State.
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Module SpecConsts.
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MAX_RW_COUNT_ge31 : (2147479552 <= MAX_RW_COUNT)%Z.
Proof. unfold MAX_RW_COUNT. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma TASK_SIZE_val : TASK_SIZE = 140737488355328%Z.
Proof. reflexivity. Qed.

Lemma access_okb_intro_num : forall buf cnt : word,
  (bv_unsigned buf + bv_unsigned cnt <= 140737488355328)%Z ->
  access_okb buf (bv_unsigned cnt) = true.
Proof. intros buf cnt H. apply access_okb_intro. rewrite TASK_SIZE_val. exact H. Qed.

(* [comment removed for export] *)
End SpecConsts.

Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts.
Import ListNotations.
Open Scope bv_scope.

Record AmbIn := mkAmbIn {
  ia_stdin  : InputStream;   (* [comment removed for export] *)
  ia_uid    : word;          (* [comment removed for export] *)
  ia_gid    : word;          (* [comment removed for export] *)
  ia_groups : list word;     (* [comment removed for export] *)
  ia_net    : NetQueue;      (* [comment removed for export] *)
  (* [comment removed for export] *)
  ia_nofile : word;          (* [comment removed for export] *)
  ia_sigmask : word;         (* [comment removed for export] *)
  ia_hwcap  : word;          (* [comment removed for export] *)
  ia_abort_terminal : bool;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ia_va_size : VaSize;
  (* [comment removed for export] *)
  ia_urandom : InputStream;
  ia_kernel : KernelBuild;
  ia_execfn : list byte;
  ia_channel_reader : bool;
  ia_sigpipe_default : bool;
  ia_sigpipe_terminal : bool;
  (* LPS 75d69e00: the run's vDSO state.  [Run.init_config] installs [vdso_run_init (ed_vdso draw)]
     over [init_model] (whose own is [vdso_run_init vdso_draw_keep]); the ambient record carries it
     so a model built by [mkModelA] is the start-up model, for every draw. *)
  ia_vdso : VdsoRun
}.

(* [comment removed for export] *)
Definition amb_creds (a : AmbIn) : Creds :=
  mkCreds (ia_uid a) (ia_uid a) (ia_uid a) (ia_gid a) (ia_gid a) (ia_gid a) (ia_groups a).

(* [comment removed for export] *)
Definition mkModelA (fds : list (word * FdEntry)) (vm : VmMaps) (a : AmbIn)
    (fs : Fs.Fs) (halted : option word) (tid : option word)
    (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [] (ia_kernel a) (ia_vdso a))
            (mkIoState (ia_stdin a) (ia_urandom a) (ia_net a) (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid (amb_creds a) false (ia_sigmask a) false None false
                         false false (ia_abort_terminal a) [] false (ia_channel_reader a)
               (sigpipe_action_at_exec (ia_sigpipe_default a)) (ia_sigpipe_terminal a))
            (mkLimState rlim (ia_nofile a))
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkProcInputA (argv envp : list (list byte)) (fs : Fs.Fs) (a : AmbIn) : ProcInput :=
  mkProcInput_full argv envp fs (ia_stdin a) (ia_uid a) (ia_gid a) (ia_groups a) (ia_net a)
              (ia_nofile a) (ia_sigmask a) (ia_hwcap a) (ia_abort_terminal a) (ia_va_size a)
              (ia_urandom a) []
              (ia_kernel a) (ia_execfn a) (ia_channel_reader a) (ia_sigpipe_default a) (ia_sigpipe_terminal a).

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_argv_A : forall argv envp fs a, in_argv (mkProcInputA argv envp fs a) = argv.
Proof. reflexivity. Qed.
Lemma in_envp_A : forall argv envp fs a, in_envp (mkProcInputA argv envp fs a) = envp.
Proof. reflexivity. Qed.
Lemma in_fs_A : forall argv envp fs a, in_fs (mkProcInputA argv envp fs a) = fs.
Proof. reflexivity. Qed.
Lemma in_uid_A : forall argv envp fs a, in_uid (mkProcInputA argv envp fs a) = ia_uid a.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma in_hwcap_A : forall argv envp fs a, in_hwcap (mkProcInputA argv envp fs a) = ia_hwcap a.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma m_fds_mkModelA : forall fds vm a fs halted tid rlim,
  m_fds (mkModelA fds vm a fs halted tid rlim) = fds.
Proof. reflexivity. Qed.
Lemma m_pipes_mkModelA : forall fds vm a fs halted tid rlim,
  m_pipes (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_vmmaps_mkModelA : forall fds vm a fs halted tid rlim,
  m_vmmaps (mkModelA fds vm a fs halted tid rlim) = vm.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_mkModelA : forall fds vm a fs halted tid rlim,
  m_vm_lazy (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_vm_materialized_mkModelA : forall fds vm a fs halted tid rlim,
  m_vm_materialized (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
Lemma m_stdin_mkModelA : forall fds vm a fs halted tid rlim,
  m_stdin (mkModelA fds vm a fs halted tid rlim) = ia_stdin a.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma m_net_mkModelA : forall fds vm a fs halted tid rlim,
  m_net (mkModelA fds vm a fs halted tid rlim) = ia_net a.
Proof. reflexivity. Qed.
Lemma m_fs_mkModelA : forall fds vm a fs halted tid rlim,
  m_fs (mkModelA fds vm a fs halted tid rlim) = fs.
Proof. reflexivity. Qed.
Lemma m_halted_mkModelA : forall fds vm a fs halted tid rlim,
  m_halted (mkModelA fds vm a fs halted tid rlim) = halted.
Proof. reflexivity. Qed.
Lemma m_tid_mkModelA : forall fds vm a fs halted tid rlim,
  m_tid (mkModelA fds vm a fs halted tid rlim) = tid.
Proof. reflexivity. Qed.
Lemma m_rlimit_core_mkModelA : forall fds vm a fs halted tid rlim,
  m_rlimit_core (mkModelA fds vm a fs halted tid rlim) = rlim.
Proof. reflexivity. Qed.
Lemma m_creds_mkModelA : forall fds vm a fs halted tid rlim,
  m_creds (mkModelA fds vm a fs halted tid rlim) = amb_creds a.
Proof. reflexivity. Qed.
Lemma m_killed_mkModelA : forall fds vm a fs halted tid rlim,
  m_killed (mkModelA fds vm a fs halted tid rlim) = None.
Proof. reflexivity. Qed.
Lemma m_sigabrt_pending_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigabrt_pending (mkModelA fds vm a fs halted tid rlim) = false.
Proof. reflexivity. Qed.
Lemma m_abort_terminal_mkModelA : forall fds vm a fs halted tid rlim,
  m_abort_terminal (mkModelA fds vm a fs halted tid rlim) = ia_abort_terminal a.
Proof. reflexivity. Qed.
Lemma m_nofile_mkModelA : forall fds vm a fs halted tid rlim,
  m_nofile (mkModelA fds vm a fs halted tid rlim) = ia_nofile a.
Proof. reflexivity. Qed.
Lemma m_sigmask_mkModelA : forall fds vm a fs halted tid rlim,
  m_sigmask (mkModelA fds vm a fs halted tid rlim) = ia_sigmask a.
Proof. reflexivity. Qed.
Lemma m_statpins_mkModelA : forall fds vm a fs halted tid rlim,
  m_statpins (mkModelA fds vm a fs halted tid rlim) = [].
Proof. reflexivity. Qed.
(* LPS 75d69e00: [mkModelA] seeds the proc state's channel-reader field from the
   ambient input ([ia_channel_reader]); the writev specs now read it, so the
   accessor belongs beside the others. *)
Lemma m_channel_reader_mkModelA : forall fds vm a fs halted tid rlim,
  m_channel_reader (mkModelA fds vm a fs halted tid rlim) = ia_channel_reader a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite m_fds_mkModelA m_pipes_mkModelA m_vmmaps_mkModelA
  m_vm_lazy_mkModelA m_vm_materialized_mkModelA m_stdin_mkModelA m_net_mkModelA
  m_fs_mkModelA m_halted_mkModelA m_tid_mkModelA m_rlimit_core_mkModelA
  m_creds_mkModelA m_killed_mkModelA m_sigabrt_pending_mkModelA m_abort_terminal_mkModelA
  m_nofile_mkModelA m_sigmask_mkModelA m_statpins_mkModelA
  m_channel_reader_mkModelA : model.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* ------------------------------------------------------------------ *)
(* The reserved ledger the S0 world carries at the revision.           *)
(* ------------------------------------------------------------------ *)

(* At the revision [init_model]'s reserved list is the binary's segments
   followed by the vDSO/vvar pair ([State.init_reserved]).  The world keeps
   what its consumers read: the segments are reserved, the list is short and
   made of small entries (what [Heap.S0H_Tight.VMT] bounds), and no mapping
   meets any reserved entry (every grant checks [region_free] over
   [vm_reserved ++ vm_maps]).  The pair's own place needs the kernel build,
   so it is carried beside the model ([S0SymPlanSoundA.stdm_vdso]). *)
Definition res_ok (seg : list (word * word)) (VM : VmMaps) : Prop :=
  incl seg (vm_reserved VM)
  /\ (length (vm_reserved VM) <= length seg + 2)%nat
  /\ Forall (fun e => (0 < bv_unsigned (snd e) <= 2 ^ 27)%Z
                      /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64)%Z) (vm_reserved VM)
  /\ (forall r, In r (vm_reserved VM) -> forall e, In e (vm_maps VM) ->
        (bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst r)
         \/ bv_unsigned (fst r) + bv_unsigned (snd r) <= bv_unsigned (fst e))%Z).

Lemma vdso_reserved_len : forall kb top, (length (vdso_reserved kb top) <= 2)%nat.
Proof. intros kb top. unfold vdso_reserved. cbv zeta. destruct (_ <? _)%Z; cbn; lia. Qed.

(* Every entry of the pair lies in the twenty pages below [top]. *)
Lemma vdso_reserved_window : forall kb top a n,
  (top < two_pow_64)%Z -> In (a, n) (vdso_reserved kb top) ->
  (top - 20 * 4096 <= bv_unsigned a)%Z /\ (0 < bv_unsigned n)%Z /\ (bv_unsigned a + bv_unsigned n <= top)%Z.
Proof.
  intros kb top a n Ht Hin.
  destruct (vdso_reserved_above kb top a n Ht Hin) as [H1 H2].
  pose proof (vdso_reserved_nonzero kb top a n Ht Hin) as H3.
  pose proof (vdso_len_bounds kb) as [_ H4]. unfold page_size in H4. lia.
Qed.

(* The pair [init_model] reserves ([State.init_reserved]) lies within
   twenty pages under [page_round_down (min mbase (sp - stack_max_size))].
   With a valid mmap base ([Run.valid_mmap_base]) and a stack top in the Sv48
   window that is far above the program's own low addresses. *)
Lemma vdso_init_above : forall kb (mbase sp : word) a n,
  (mmap_base_min <= bv_unsigned mbase)%Z -> (0x7fff80000000 <= bv_unsigned sp)%Z ->
  In (a, n) (vdso_reserved kb (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))) ->
  (2 ^ 44 <= bv_unsigned a)%Z /\ (0 < bv_unsigned n <= 2 ^ 27)%Z /\ (bv_unsigned a + bv_unsigned n <= 2 ^ 64)%Z.
Proof.
  intros kb mbase sp a n Hmb Hsp Hin.
  pose proof (bv_unsigned_in_range 64 sp) as [_ Hsp2]. unfold bv_modulus in Hsp2.
  set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) in *.
  assert (Hx : (2 ^ 44 + 2 ^ 20 <= x < 2 ^ 64)%Z) by (unfold x, mmap_base_min, stack_max_size in *; lia).
  unfold page_round_down_Z, page_size in Hin.
  pose proof (Z_div_mod_eq_full x 4096) as Hq. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as Hr.
  set (top := (x / 4096 * 4096)%Z) in *.
  assert (Ht : (x - 4096 < top <= x)%Z) by (unfold top; lia).
  destruct (vdso_reserved_window kb top a n ltac:(unfold two_pow_64; lia) Hin) as (H1 & H2 & H3).
  split; [lia|]. split; [split; lia|]. lia.
Qed.

Lemma vdso_reserved_small : forall kb top, (top < two_pow_64)%Z ->
  Forall (fun e => (0 < bv_unsigned (snd e) <= 2 ^ 27)%Z
                   /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64)%Z) (vdso_reserved kb top).
Proof.
  intros kb top Ht. apply Forall_forall. intros [a n] Hin. cbn [fst snd].
  destruct (vdso_reserved_window kb top a n Ht Hin) as (H1 & H2 & H3).
  pose proof (bv_unsigned_in_range 64 a) as [Ha _]. unfold two_pow_64 in Ht. lia.
Qed.

Lemma region_free_app_split : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [app region_free]. rewrite IH. apply Bool.andb_assoc.
Qed.

Lemma region_free_below_all : forall l (lo n : word),
  (forall a sz, In (a, sz) l -> bv_unsigned lo + bv_unsigned n <= bv_unsigned a)%Z ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  pose proof (H a sz (or_introl eq_refl)) as Ha.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned lo + bv_unsigned n))) by lia.
  rewrite Bool.andb_false_r. cbn [negb andb]. apply IH.
  intros a' s' Hin. exact (H a' s' (or_intror Hin)).
Qed.

Lemma region_free_above_all : forall l (lo n : word),
  (forall a sz, In (a, sz) l -> bv_unsigned a + bv_unsigned sz <= bv_unsigned lo)%Z ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  pose proof (H a sz (or_introl eq_refl)) as Ha.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz))) by lia.
  cbn [negb andb]. apply IH.
  intros a' s' Hin. exact (H a' s' (or_intror Hin)).
Qed.

Lemma region_free_within : forall l (lo n lo' n' : word),
  region_free l lo n = true ->
  (bv_unsigned lo <= bv_unsigned lo')%Z -> (bv_unsigned lo' + bv_unsigned n' <= bv_unsigned lo + bv_unsigned n)%Z ->
  region_free l lo' n' = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n lo' n' H H1 H2; [reflexivity|].
  cbn [region_free] in H |- *. apply Bool.andb_true_iff in H as [Ha Hr].
  rewrite (IH lo n lo' n' Hr H1 H2), Bool.andb_true_r.
  unfold iv_overlap in *. apply Bool.negb_true_iff in Ha. apply Bool.negb_true_iff.
  apply Bool.andb_false_iff in Ha as [Ha|Ha]; apply Z.ltb_ge in Ha; apply Bool.andb_false_iff;
    [left|right]; apply Z.ltb_ge; lia.
Qed.

(* the vDSO top of a VM with a page-aligned mmap base is the one
   [init_model] reserved the pair under *)
Lemma vdso_top_launch : forall h,
  (bv_unsigned (vm_mmap_base h) mod page_size = 0)%Z ->
  vdso_top h = page_round_down_Z (Z.min (bv_unsigned (vm_mmap_base h)) (bv_unsigned (vm_init_sp h) - stack_max_size)).
Proof.
  intros h Hal. unfold vdso_top, mmap_top, alloc_top, page_round_down_Z, page_size in *.
  set (m := bv_unsigned (vm_mmap_base h)) in *. set (y := (bv_unsigned (vm_init_sp h) - stack_max_size)%Z).
  pose proof (Z_div_mod_eq_full y 4096) as Hy. pose proof (Z.mod_pos_bound y 4096 ltac:(lia)) as Hy2.
  pose proof (Z_div_mod_eq_full m 4096) as Hm.
  set (q := (y / 4096)%Z) in *. set (r := (m / 4096)%Z) in *.
  destruct (Z.le_gt_cases m (q * 4096)) as [Hle|Hgt].
  - rewrite (Z.min_l m (q * 4096)) by lia. rewrite (Z.min_l m y) by lia. reflexivity.
  - rewrite (Z.min_r m (q * 4096)) by lia.
    assert (Hmy : (y <= m)%Z) by nia.
    rewrite (Z.min_r m y) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma vdso_in_init_reserved : forall seg kb (mbase sp : word) maps na sb b lim,
  (bv_unsigned mbase mod page_size = 0)%Z ->
  incl (vdso_reserved kb (vdso_top (mkVmMapsFull (init_reserved seg mbase sp kb) maps na sb b lim mbase sp)))
       (init_reserved seg mbase sp kb).
Proof.
  intros seg kb mbase sp maps na sb b lim Hal.
  rewrite (vdso_top_launch (mkVmMapsFull (init_reserved seg mbase sp kb) maps na sb b lim mbase sp) Hal).
  cbn [vm_mmap_base vm_init_sp]. unfold init_reserved. apply incl_appr, incl_refl.
Qed.

(* the run's ledger, built from the binary's segment ledger [seg]:
   small entries, two more than [seg], and the low windows free *)
Definition small_ent (e : word * word) : Prop :=
  (0 < bv_unsigned (snd e) <= 2 ^ 27)%Z /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= 2 ^ 64)%Z.

Lemma init_reserved_shape : forall seg (mbase sp : word) kb,
  (mmap_base_min <= bv_unsigned mbase)%Z -> (0x7fff80000000 <= bv_unsigned sp)%Z ->
  Forall small_ent seg ->
  Forall small_ent (init_reserved seg mbase sp kb)
  /\ (length (init_reserved seg mbase sp kb) <= length seg + 2)%nat.
Proof.
  intros seg mbase sp kb Hmb Hsp Hs. unfold init_reserved. split.
  - apply Forall_app. split; [exact Hs|].
    apply Forall_forall. intros [a n] Hin. unfold small_ent. cbn [fst snd].
    destruct (vdso_init_above kb mbase sp a n Hmb Hsp Hin) as (H1 & H2 & H3). split; lia.
  - rewrite length_app.
    pose proof (vdso_reserved_len kb (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))).
    lia.
Qed.

Lemma init_reserved_low_free : forall seg (mbase sp : word) kb (b n : word),
  (mmap_base_min <= bv_unsigned mbase)%Z -> (0x7fff80000000 <= bv_unsigned sp)%Z ->
  (forall a sz, In (a, sz) seg -> bv_unsigned a + bv_unsigned sz <= bv_unsigned b)%Z ->
  (bv_unsigned b + bv_unsigned n <= 2 ^ 44)%Z ->
  region_free (init_reserved seg mbase sp kb) b n = true.
Proof.
  intros seg mbase sp kb b n Hmb Hsp Hseg Hn. unfold init_reserved.
  rewrite region_free_app_split. apply Bool.andb_true_iff. split.
  - apply region_free_above_all. exact Hseg.
  - apply region_free_below_all. intros a sz Hin.
    destruct (vdso_init_above kb mbase sp a sz Hmb Hsp Hin) as (H1 & _). lia.
Qed.

(* a VM over the run's ledger meets [res_ok] once every mapping is free of
   the ledger *)
Lemma res_ok_init : forall seg (mbase sp : word) kb VM,
  (mmap_base_min <= bv_unsigned mbase)%Z -> (0x7fff80000000 <= bv_unsigned sp)%Z ->
  Forall small_ent seg ->
  vm_reserved VM = init_reserved seg mbase sp kb ->
  (forall e, In e (vm_maps VM) -> region_free (init_reserved seg mbase sp kb) (fst e) (snd e) = true) ->
  res_ok seg VM.
Proof.
  intros seg mbase sp kb VM Hmb Hsp Hs Hr Hm.
  destruct (init_reserved_shape seg mbase sp kb Hmb Hsp Hs) as [RS RL].
  unfold res_ok. rewrite Hr. split; [|split; [|split]].
  - unfold init_reserved. apply incl_appl, incl_refl.
  - exact RL.
  - exact RS.
  - intros [ra rs] Hr' e He.
    pose proof (region_free_In _ _ _ ra rs (Hm e He) Hr') as D. cbn [fst snd].
    unfold iv_overlap in D. apply Bool.andb_false_iff in D as [D|D]; apply Z.ltb_ge in D; [right|left]; lia.
Qed.

