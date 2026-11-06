(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

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

Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

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

Definition out_det (eff : SyscallEffect) (m' : Model) (evs : list event)
    (o : outcome SyscallEffect) : Prop :=
  o = Ok eff m' evs.

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

Lemma munmap_exact_outcome : forall addr len i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE)%Z ->
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
  intros addr len i m o Hal Hlen Hts. cbv zeta. intros Hhas. unfold munmap_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hlen. cbn [negb orb].
  sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite ?(proj2 (Z.ltb_ge _ _) Hts) in *; rewrite ?Hhas in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _) Hts). rewrite Hhas.
    split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Definition mmap_err_out (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma mmap_rw_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ mmap_noreserve_backed_ok flags m nZ = true)
               /\ o = Ok (mkEffect a [] [(a, n)])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                               (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.

  intros addr len prot flags fd off i m o Hoff Han Hlen Hmod. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Han, Hlen, Hmod. cbn [negb]. unfold alt. rewrite bind_get_model. cbv zeta.
  unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
               /\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
                               (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.

  intros addr len prot flags fd off i m o Hoff Han Hlen Hmod Hna. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Han, Hlen, Hmod, Hna. cbn [negb]. unfold alt. rewrite bind_get_model. cbv zeta.
  unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_fixed_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_replacement flags addr n
              (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                 ((addr, n) :: maps_subtract (vm_noaccess h)
                                 (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []
  \/ exists e, In e mmap_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Han Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har. pose proof (alloc_top_room (m_vmmaps m)) as Htop.
  unfold stack_max_size in Htop.
  unfold mmap_spec. rewrite Hoff, Han, Hlen, Hmod, Hna, Hfx. cbv zeta. cbn [negb].
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. lia. }
  rewrite E1. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys;
      rewrite ?(proj2 (Z.leb_le _ _) Hce), ?(proj2 (Z.eqb_eq _ _) Hal), ?(proj2 (Z.ltb_lt _ _) Hpos) in *; cbn [negb] in *;
      rewrite ?Hrf, ?Hmc in *; cbn [andb] in *; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. reflexivity.
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [-> | (e & He & ->)]]; eexists _, _, _, _; (split; [reflexivity|]);
      rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos); cbn [negb];
      rewrite Hrf, Hmc; cbn [andb]; (split; [|reflexivity]).
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mprotect_expose_outcome : forall addr len prot i m o,
  mprotect_grows_conflict_b prot = false ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  mprotect_modeled_b prot = true ->
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  map_contains (vm_noaccess h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mprotect_spec addr len prot i m o <->
  (exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (mprotect_budget_ok m addr n = true
      /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
  intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
  unfold mprotect_spec.
  rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod. cbn [negb].
  sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hna, Hma in *; cbn [andb] in *; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hb & ->)]; eexists _, _, _, _; (split; [reflexivity|]);
      rewrite Hna, Hma; cbn [andb]; (split; [|reflexivity]).
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma err_ret_outcome : forall e i m o,
  err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

