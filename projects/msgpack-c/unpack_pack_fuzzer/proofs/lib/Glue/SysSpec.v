(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev_outcome takes the far-end reader premise; read_cstr_aux_ok and read_cstr_aux_toolong take the path's below-TASK_SIZE premises and cstr_access_len_le covers the walk's stop at TASK_SIZE; iovec_entry_accesses_in added and copy_iovecs_accesses_in, import_iovecs_accesses_in, wv_cps_in and wv_eff0_in restated for a descriptor's partial copy-in record; openat_rob and writev_rob give RomBase.sys_rob at the openat and writev nodes, through the memory-view lemmas read_u64_ext, read_iovec_entry_at, iovec_entry_accesses_ext, copy_iovecs_accesses_ext, import_iovecs_accesses_ext, iov_at_ext, read_bytes_map_Forall2_ext and CP_ext; imports RomBase). *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require RomBase.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module SysSpec.

Section WithSegs.
Variable segs : list Segment.

Lemma step_nonspur_of_spec : forall ms model x8 (I : Type) (eff : I -> SyscallEffect) (mo : I -> Model)
    (evs : I -> list event),
  ms_svc_pending ms = Some x8 ->
  (forall i, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model (eff i)) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (eff i) (mo i) (evs i)) ->
  step_nonspur segs (mkCfg ms model).
Proof.
  intros ms model x8 I eff mo evs Hsvc Hns Hspec y8 e m' ev Hy Hs. cbn [cfg_ms cfg_model] in *.
  rewrite Hsvc in Hy. injection Hy as <-.
  apply (proj1 (Hspec _)) in Hs. destruct Hs as [i Ei]. injection Ei as -> _ _. apply Hns.
Qed.

Lemma nonspur_nonalloc : forall ms model x8 e,
  ~ In (bv_unsigned x8) alloc_mark_sysnos -> ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model e.
Proof. intros ms model x8 e H. apply fcfg_nonalloc_nonspur. exact H. Qed.

Lemma nonspur_det : forall i model eff mo evs,
  (forall o, syscall_spec i model o <-> o = Ok eff mo evs) -> ~ spurious_refusal_cfg fcfg i model eff.
Proof.
  intros i model eff mo evs Hspec (_ & Hr & (eff' & m' & evs' & Hs & Hnr)).
  apply Hspec in Hs. injection Hs as -> _ _. congruence.
Qed.

Lemma nonalloc_eq : forall (x8 : word) (k : Z), bv_unsigned x8 = k ->
  existsb (Z.eqb k) alloc_mark_sysnos = false -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 k -> Hb Hin.
  assert (Ht : existsb (Z.eqb k) alloc_mark_sysnos = true)
    by (apply existsb_exists; exists k; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

Theorem node_silent : forall ms model x8 (I : Type) (eff : I -> SyscallEffect) (mo : I -> Model),
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = Some x8 ->
  (forall i, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model (eff i)) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (eff i) (mo i) []) ->
  (forall i, m_halted (mo i) = None /\ m_vm_lazy (mo i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i))) (mo i)).
Proof.
  intros ms model x8 I eff mo Hh Hlazy Hsvc Hns Hspec Hmo.
  apply two_sided_lift; [exact (step_nonspur_of_spec ms model x8 I eff mo (fun _ => []) Hsvc Hns Hspec) |]. split.
  - intros i. destruct (Hmo i) as [Hhi Hli].
    apply (sstep_syscall segs ms model x8 (eff i) (mo i) (mo i) []); [exact Hh | exact Hsvc | | exact Hhi |].
    + apply (proj2 (Hspec _)). exists i. reflexivity.
    + apply materialize_model_accesses_no_lazy. exact Hli.
  - intros e st Hss. inversion Hss; subst; try congruence;
      match goal with
      | Hsv : ms_svc_pending ms = Some ?y |- _ => assert (Ey : y = x8) by congruence; subst y
      end;
      match goal with
      | Hsp : syscall_spec _ _ ?o |- _ =>
          pose proof (proj1 (Hspec _) Hsp) as Ho;
          first [ destruct Ho as [i Ei]; try discriminate Ei; injection Ei as E1 E2 E3; subst
                | idtac ]
      end.
    +
      destruct (Hmo i) as [Hhi Hli].
      match goal with Hm : materialize_model_accesses _ _ = Some ?m'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hli) in Hm; injection Hm as <- end.
      exists i. split; reflexivity.
    + destruct (Hmo i) as [Hhi Hli].
      match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hli) in Hm; discriminate Hm end.
    + destruct (Hmo i) as [Hhi Hli]. congruence.
    + destruct (Hmo i) as [Hhi Hli].
      match goal with Hk : m_killed (mo i) = Some _ |- _ => rewrite (m_killed_of_m_halted_none _ Hhi) in Hk; discriminate Hk end.
Qed.

Theorem node_gen : forall ms model x8 (I : Type) (eff : I -> SyscallEffect) (mo : I -> Model) (evs : I -> list event),
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = Some x8 ->
  (forall i, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model (eff i)) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (eff i) (mo i) (evs i)) ->
  (forall i, m_halted (mo i) = None /\ m_vm_lazy (mo i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i))) (mo i)).
Proof.
  intros ms model x8 I eff mo evs Hh Hlazy Hsvc Hns Hspec Hmo.
  apply two_sided_lift; [exact (step_nonspur_of_spec ms model x8 I eff mo evs Hsvc Hns Hspec) |]. split.
  - intros i. destruct (Hmo i) as [Hhi Hli].
    apply (sstep_syscall segs ms model x8 (eff i) (mo i) (mo i) (evs i)); [exact Hh | exact Hsvc | | exact Hhi |].
    + apply (proj2 (Hspec _)). exists i. reflexivity.
    + apply materialize_model_accesses_no_lazy. exact Hli.
  - intros e st Hss. inversion Hss; subst; try congruence;
      match goal with
      | Hsv : ms_svc_pending ms = Some ?y |- _ => assert (Ey : y = x8) by congruence; subst y
      end;
      match goal with
      | Hsp : syscall_spec _ _ ?o |- _ =>
          pose proof (proj1 (Hspec _) Hsp) as Ho;
          first [ destruct Ho as [i Ei]; try discriminate Ei; injection Ei as E1 E2 E3; subst
                | idtac ]
      end.
    + destruct (Hmo i) as [Hhi Hli].
      match goal with Hm : materialize_model_accesses _ _ = Some ?m'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hli) in Hm; injection Hm as <- end.
      exists i. split; reflexivity.
    + destruct (Hmo i) as [Hhi Hli].
      match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hli) in Hm; discriminate Hm end.
    + destruct (Hmo i) as [Hhi Hli]. congruence.
    + destruct (Hmo i) as [Hhi Hli].
      match goal with Hk : m_killed (mo i) = Some _ |- _ => rewrite (m_killed_of_m_halted_none _ Hhi) in Hk; discriminate Hk end.
Qed.

Theorem node_gen_a : forall ms model x8 (I : Type) (eff : I -> SyscallEffect) (mo mo2 : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model (eff i)) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (eff i) (mo i) (evs i)) ->
  (forall i, m_halted (mo i) = None /\ materialize_model_accesses (mo i) (syscall_effect_accesses (eff i)) = Some (mo2 i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i))) (mo2 i)).
Proof.
  intros ms model x8 I eff mo mo2 evs Hh Hsvc Hns Hspec Hmo.
  apply two_sided_lift; [exact (step_nonspur_of_spec ms model x8 I eff mo evs Hsvc Hns Hspec) |]. split.
  - intros i. destruct (Hmo i) as [Hhi Hmi].
    apply (sstep_syscall segs ms model x8 (eff i) (mo i) (mo2 i) (evs i)); [exact Hh | exact Hsvc | | exact Hhi | exact Hmi].
    apply (proj2 (Hspec _)). exists i. reflexivity.
  - intros e st Hss. inversion Hss; subst; try congruence;
      match goal with
      | Hsv : ms_svc_pending ms = Some ?y |- _ => assert (Ey : y = x8) by congruence; subst y
      end;
      match goal with
      | Hsp : syscall_spec _ _ ?o |- _ =>
          pose proof (proj1 (Hspec _) Hsp) as Ho;
          first [ destruct Ho as [i Ei]; try discriminate Ei; injection Ei as E1 E2 E3; subst
                | idtac ]
      end.
    + destruct (Hmo i) as [Hhi Hmi].
      match goal with Hm : materialize_model_accesses _ _ = Some ?m'' |- _ => rewrite Hmi in Hm; injection Hm as <- end.
      exists i. split; reflexivity.
    + destruct (Hmo i) as [Hhi Hmi].
      match goal with Hm : materialize_model_accesses _ _ = None |- _ => rewrite Hmi in Hm; discriminate Hm end.
    + destruct (Hmo i) as [Hhi Hmi]. congruence.
    + destruct (Hmo i) as [Hhi Hmi].
      match goal with Hk : m_killed (mo i) = Some _ |- _ => rewrite (m_killed_of_m_halted_none _ Hhi) in Hk; discriminate Hk end.
Qed.

Theorem node_silent_a : forall ms model x8 (I : Type) (eff : I -> SyscallEffect) (mo mo2 : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) model (eff i)) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (eff i) (mo i) []) ->
  (forall i, m_halted (mo i) = None /\ materialize_model_accesses (mo i) (syscall_effect_accesses (eff i)) = Some (mo2 i)) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i))) (mo2 i)).
Proof. intros. apply (node_gen_a ms model x8 I eff mo mo2 (fun _ => [])); assumption. Qed.

End WithSegs.

Lemma sys57 : forall i m o, bv_unsigned (in_sysno i) = 57 -> syscall_spec i m o = close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o Hno. unfold syscall_spec, dispatch. rewrite Hno. reflexivity. Qed.
Lemma sys29 : forall i m o, bv_unsigned (in_sysno i) = 29 -> syscall_spec i m o = ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o Hno. unfold syscall_spec, dispatch. rewrite Hno. reflexivity. Qed.
Lemma sys63 : forall i m o, bv_unsigned (in_sysno i) = 63 -> syscall_spec i m o = read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o Hno. unfold syscall_spec, dispatch. rewrite Hno. reflexivity. Qed.
Lemma sys56 : forall i m o, bv_unsigned (in_sysno i) = 56 -> syscall_spec i m o = openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o Hno. unfold syscall_spec, dispatch. rewrite Hno. reflexivity. Qed.

Ltac unsys := unfold ret_only, err_ret, set_fds, modify, errno_from, choose, alt, bind, pure, unmodeled.

Lemma ioctl_outcome : forall i m c o,
  bv_unsigned (in_sysno i) = 29 -> fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some (FdChannel c) ->
  tty_only_request (cmd32 (in_arg i 1)) = true ->
  (syscall_spec i m o <-> o = Ok (mkEffect (errno_ret ENOTTY) [] []) m []).
Proof.
  intros i m c o Hno Hfd Hreq. rewrite (sys29 i m o Hno). unfold ioctl_spec. rewrite bind_get_model. rewrite Hfd.
  rewrite Hreq. unfold ret_only, pure. reflexivity.
Qed.

Lemma bind_input : forall {A} (k : SyscallInput -> Sys A) i m o, bind input k i m o <-> k i i m o.
Proof.
  intros A k i m o. unfold bind, input. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists i, m, [], evs. split; [reflexivity|]. split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|]. injection H1 as -> -> ->. exact H2.
  - intros H. right. exists i, m, []. split; [reflexivity | exact H].
Qed.

Lemma ret_only_iff : forall r i m o, ret_only r i m o <-> o = Ok (mkEffect r [] []) m [].
Proof. intros. unfold ret_only, pure. reflexivity. Qed.
Lemma err_ret_iff : forall e i m o, err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret. apply ret_only_iff. Qed.

Lemma modify_ret_iff : forall f r i m o, (bind (modify f) (fun _ => ret_only r)) i m o <-> o = Ok (mkEffect r [] []) (f m) [].
Proof.
  intros f r i m o. unfold bind, modify, ret_only, pure. destruct o as [x m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & E1 & E2 & E3). injection E1 as Ea Eb Ec. injection E2 as Ed Ee Ef. subst. reflexivity.
  - intros E. injection E as E1 E2 E3; subst. exists tt, (f m), [], []. repeat split; reflexivity.
  - intros [E | (u & m1 & e1 & E1 & E2)]; discriminate.
  - intros E; discriminate E.
Qed.

Lemma read_dir_outcome : forall i m o,
  bv_unsigned (in_sysno i) = 63 -> fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some FdDir ->
  access_okb (in_arg i 1) (bv_unsigned (in_arg i 2)) = true ->
  (syscall_spec i m o <-> o = Ok (mkEffect (errno_ret EISDIR) [] []) m []).
Proof.
  intros i m o Hno Hfd Hacc. rewrite (sys63 i m o Hno). unfold read_spec. rewrite bind_input, bind_get_model, Hfd, Hacc.
  cbn [negb]. apply err_ret_iff.
Qed.

Lemma close_outcome : forall i m e o,
  bv_unsigned (in_sysno i) = 57 -> fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some e ->
  (syscall_spec i m o <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds m) (fd32 (in_arg i 0))) m) []).
Proof.
  intros i m e o Hno Hfd. rewrite (sys57 i m o Hno). unfold close_spec. rewrite bind_get_model, Hfd. unfold set_fds. apply modify_ret_iff.
Qed.

Lemma read_file_outcome : forall i m o p off data bs w,
  bv_unsigned (in_sysno i) = 63 -> fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some (FdFile p off) ->
  access_okb (in_arg i 1) (bv_unsigned (in_arg i 2)) = true ->
  fs_lookup (m_fs m) p = Some data ->
  bs = file_read data off (Z_to_bv 64 (rw_count_clamp (in_arg i 2))) ->
  read_bytes_map (in_wmem i) (in_arg i 1) (len_word bs) = Some w ->
  (syscall_spec i m o <->
   o = Ok (mkEffect (len_word bs) (delivered_writes (in_arg i 1) bs) [])
          (with_fds (fd_insert (m_fds m) (fd32 (in_arg i 0)) (FdFile p (off + len_word bs)%bv)) m) []).
Proof.
  intros i m o p off data bs w Hno Hfd Hacc Hfs Hbs Hw. rewrite (sys63 i m o Hno). unfold read_spec.
  rewrite bind_input, bind_get_model, Hfd, Hacc, Hfs. cbn [negb]. rewrite <- Hbs, Hw.
  unfold set_fds, bind, modify, pure. destruct o as [x m2 evs|]; split.
  - intros (u & m1 & e1 & e2 & E1 & E2 & E3). injection E1 as Ea Eb Ec. injection E2 as Ed Ee Ef. subst. reflexivity.
  - intros E. injection E as E1 E2 E3; subst. eexists tt, _, [], []. repeat split; reflexivity.
  - intros [E | (u & m1 & e1 & E1 & E2)]; discriminate.
  - intros E; discriminate E.
Qed.

Lemma record_copyins_ok_iff : forall reads spec i m eff' m' evs,
  record_copyins reads spec i m (Ok eff' m' evs) <->
  exists eff, spec i m (Ok eff m' evs) /\ eff' = with_copyins (reads ++ eff_copyins eff) eff.
Proof.
  intros. unfold record_copyins, bind, pure. split.
  - intros (eff & m1 & e1 & e2 & H1 & H2 & H3). injection H2 as E1 E2 E3; subst. rewrite app_nil_r. exists eff. split; [exact H1 | reflexivity].
  - intros (eff & H1 & ->). exists eff, m', evs, []. rewrite app_nil_r. repeat split; try reflexivity. exact H1.
Qed.
Lemma record_copyins_unmodeled_iff : forall reads spec i m,
  record_copyins reads spec i m Unmodeled <-> spec i m Unmodeled.
Proof.
  intros. unfold record_copyins, bind, pure. split.
  - intros [H | (eff & m1 & e1 & H1 & H2)]; [exact H | discriminate H2].
  - intros H. left. exact H.
Qed.

Lemma openat_core_rd : forall i m o p,
  modeled_open_flags (in_arg i 2) = true ->
  read_cstr (in_mem i) (in_arg i 1) = CstrOk p -> path_eqb p [] = false ->
  bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true -> path_has_slash p = false ->
  Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0 ->
  (openat_core_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o <-> openat_read_spec p m i m o).
Proof.
  intros i m o p Hfl Hcs Hne Hfd Hsl Hld. unfold openat_core_spec. rewrite bind_input, bind_get_model, Hfl. cbn [negb].
  unfold openat_body_spec. rewrite Hcs, Hne, Hfd. cbn [negb]. unfold openat_resolved_spec. rewrite Hsl, Hld. cbn [Z.eqb]. reflexivity.
Qed.

Lemma open_result_iff : forall m mk i o,
  open_result_spec m mk i m o <->
  (exists e, In e openat_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m []) \/
  (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m) /\ o = Ok (mkEffect fd [] []) (mk fd m) []).
Proof.
  intros m mk i o. unfold open_result_spec, alt, errno_from, lowest_fd, choose, err_ret, ret_only, modify, bind, pure.
  destruct o as [x m2 evs|]; split.
  - intros [(e & m1 & e1 & e2 & (e0 & He0 & E1) & E2 & E3) | (fd & m1 & e1 & e2 & (fd0 & Hfd0 & E1) & (u & m3 & e3 & e4 & E4 & E5 & E6) & E7)].
    + injection E1 as Ea Eb Ec. injection E2 as Ed Ee Ef. subst. left. exists e0. split; [exact He0|]. rewrite app_nil_r. reflexivity.
    + injection E1 as Ea Eb Ec. injection E4 as Eg Eh Ei. injection E5 as Ej Ek El. subst. right. exists fd0.
      destruct Hfd0 as [H1 H2]. subst. repeat split; try assumption; try reflexivity.
  - intros [(e & He & E) | (fd & H1 & H2 & E)]; injection E as E1 E2 E3; subst.
    + left. exists e, m, [], []. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. exists (alloc_fd (m_fds m)), m, [], []. split; [eexists; split; [split; [exact H1|reflexivity]|reflexivity]|].
      split; [|reflexivity]. exists tt, (mk (alloc_fd (m_fds m)) m), [], []. repeat split; reflexivity.
  - intros [[E|(e & m1 & e1 & (e0 & _ & E1) & E2)] | [E | (fd & m1 & e1 & (fd0 & _ & E1) & [E2 | (u & m3 & e3 & E2 & E3)])]]; try discriminate.
    + destruct E as (e0 & _ & E). discriminate E.
    + destruct E as (f0 & _ & E). discriminate E.
  - intros [(e & _ & E) | (fd & _ & _ & E)]; discriminate E.
Qed.

Definition CP (i : SyscallInput) : list (word * nat) := [(in_arg i 1, cstr_access_len_aux (in_mem i) (in_arg i 1) path_max)].
Definition open_err (e : Z) (i : SyscallInput) : SyscallEffect := mkEffectU (errno_ret e) [] [] [] [] (CP i).
Definition open_ret (fd : word) (i : SyscallInput) : SyscallEffect := mkEffectU fd [] [] [] [] (CP i).

Lemma openat_wrap : forall i m o (CORE : outcome SyscallEffect -> Prop),
  bv_unsigned (in_sysno i) = 56 ->
  (forall o', openat_core_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o' <-> CORE o') ->
  (syscall_spec i m o <->
   match o with
   | Ok eff' m' evs => exists eff, CORE (Ok eff m' evs) /\ eff' = with_copyins (CP i ++ eff_copyins eff) eff
   | Unmodeled => CORE Unmodeled
   end).
Proof.
  intros i m o CORE Hno HC. rewrite (sys56 i m o Hno). unfold openat_spec. rewrite bind_input. fold (CP i).
  destruct o as [eff' m' evs|].
  - rewrite record_copyins_ok_iff. split; intros (eff & H1 & H2); exists eff; split; try assumption; [apply HC; exact H1 | apply HC; exact H1].
  - rewrite record_copyins_unmodeled_iff. apply HC.
Qed.

Lemma openat_toolong_outcome : forall i m o,
  bv_unsigned (in_sysno i) = 56 -> modeled_open_flags (in_arg i 2) = true ->
  read_cstr (in_mem i) (in_arg i 1) = CstrTooLong ->
  (syscall_spec i m o <-> o = Ok (open_err ENAMETOOLONG i) m []).
Proof.
  intros i m o Hno Hfl Hcs.
  rewrite (openat_wrap i m o (fun o' => o' = Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m []) Hno).
  2:{ intros o'. unfold openat_core_spec. rewrite bind_input, bind_get_model, Hfl. cbn [negb]. unfold openat_body_spec. rewrite Hcs. apply err_ret_iff. }
  destruct o as [eff' m' evs|]; split.
  - intros (eff & E1 & ->). injection E1 as -> -> ->. reflexivity.
  - intros E. injection E as -> -> ->. eexists. split; reflexivity.
  - intros E; discriminate E.
  - intros E; discriminate E.
Qed.

Lemma openat_absent_outcome : forall i m o p,
  bv_unsigned (in_sysno i) = 56 -> Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0 ->
  read_cstr (in_mem i) (in_arg i 1) = CstrOk p -> bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true -> path_has_slash p = false ->
  path_is_dirref p = false -> (path_eqb p [] = true \/ fs_lookup (m_fs m) p = None) ->
  (syscall_spec i m o <-> o = Ok (open_err ENOENT i) m []).
Proof.
  intros i m o p Hno Hld Hcs Hfd Hsl Hdr Habs.
  rewrite (openat_wrap i m o (fun o' => o' = Ok (mkEffect (errno_ret ENOENT) [] []) m []) Hno).
  2:{ intros o'. destruct (path_eqb p []) eqn:He.
      - unfold openat_core_spec. rewrite bind_input, bind_get_model, (modeled_open_flags_rd _ Hld). cbn [negb].
        unfold openat_body_spec. rewrite Hcs, He. apply err_ret_iff.
      - rewrite (openat_core_rd i m o' p (modeled_open_flags_rd _ Hld) Hcs He Hfd Hsl Hld).
        unfold openat_read_spec. rewrite Hdr. destruct Habs as [Habs|Habs]; [discriminate Habs|]. rewrite Habs. apply err_ret_iff. }
  destruct o as [eff' m' evs|]; split.
  - intros (eff & E1 & ->). injection E1 as -> -> ->. reflexivity.
  - intros E. injection E as -> -> ->. eexists. split; reflexivity.
  - intros E; discriminate E.
  - intros E; discriminate E.
Qed.

Lemma openat_file_outcome : forall i m o p data,
  bv_unsigned (in_sysno i) = 56 -> Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0 ->
  read_cstr (in_mem i) (in_arg i 1) = CstrOk p -> path_eqb p [] = false -> bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true ->
  path_has_slash p = false -> path_is_dirref p = false -> fs_lookup (m_fs m) p = Some data ->
  (syscall_spec i m o <->
   (exists e, In e openat_errnos /\ o = Ok (open_err e i) m []) \/
   (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m) /\
               o = Ok (open_ret fd i) (with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) [])).
Proof.
  intros i m o p data Hno Hld Hcs Hne Hfd Hsl Hdr Hfs.
  rewrite (openat_wrap i m o (fun o' => (exists e, In e openat_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m []) \/
     (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m) /\
                 o' = Ok (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) [])) Hno).
  2:{ intros o'. rewrite (openat_core_rd i m o' p (modeled_open_flags_rd _ Hld) Hcs Hne Hfd Hsl Hld).
      unfold openat_read_spec. rewrite Hdr, Hfs. apply open_result_iff. }
  destruct o as [eff' m' evs|]; split.
  - intros (eff & [(e & He & E1)|(fd & H1 & H2 & E1)] & ->); injection E1 as -> -> ->.
    + left. exists e. split; [exact He | reflexivity].
    + right. exists fd. repeat split; try assumption.
  - intros [(e & He & E) | (fd & H1 & H2 & E)]; injection E as -> -> ->.
    + eexists. split; [left; exists e; split; [exact He | reflexivity] | reflexivity].
    + eexists. split; [right; exists fd; repeat split; assumption | reflexivity].
  - intros [(e & _ & E) | (fd & _ & _ & E)]; discriminate E.
  - intros [(e & _ & E) | (fd & _ & _ & E)]; discriminate E.
Qed.

Lemma openat_dir_outcome : forall i m o p,
  bv_unsigned (in_sysno i) = 56 -> Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0 ->
  read_cstr (in_mem i) (in_arg i 1) = CstrOk p -> path_eqb p [] = false -> bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true ->
  path_has_slash p = false -> path_is_dirref p = true ->
  (syscall_spec i m o <->
   (exists e, In e openat_errnos /\ o = Ok (open_err e i) m []) \/
   (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m) /\
               o = Ok (open_ret fd i) (with_fds (fd_insert (m_fds m) fd FdDir) m) [])).
Proof.
  intros i m o p Hno Hld Hcs Hne Hfd Hsl Hdr.
  rewrite (openat_wrap i m o (fun o' => (exists e, In e openat_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m []) \/
     (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m) /\
                 o' = Ok (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd FdDir) m) [])) Hno).
  2:{ intros o'. rewrite (openat_core_rd i m o' p (modeled_open_flags_rd _ Hld) Hcs Hne Hfd Hsl Hld).
      unfold openat_read_spec. rewrite Hdr. apply open_result_iff. }
  destruct o as [eff' m' evs|]; split.
  - intros (eff & [(e & He & E1)|(fd & H1 & H2 & E1)] & ->); injection E1 as -> -> ->.
    + left. exists e. split; [exact He | reflexivity].
    + right. exists fd. repeat split; try assumption.
  - intros [(e & He & E) | (fd & H1 & H2 & E)]; injection E as -> -> ->.
    + eexists. split; [left; exists e; split; [exact He | reflexivity] | reflexivity].
    + eexists. split; [right; exists fd; repeat split; assumption | reflexivity].
  - intros [(e & _ & E) | (fd & _ & _ & E)]; discriminate E.
  - intros [(e & _ & E) | (fd & _ & _ & E)]; discriminate E.
Qed.

Lemma sys66 : forall i m o, bv_unsigned (in_sysno i) = 66 -> syscall_spec i m o = writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o Hno. unfold syscall_spec, dispatch. rewrite Hno. reflexivity. Qed.

Fixpoint iov_at (mp : word -> option byte) (a : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, l) :: r => read_u64 mp a = Some b /\ read_u64 mp (a + Z_to_bv 64 8)%bv = Some l /\ bv_unsigned l < 2 ^ 62 /\
                  iov_at mp (a + Z_to_bv 64 16)%bv r
  end.

Lemma copy_iovecs_aux_ok : forall mp iovs a, iov_at mp a iovs -> copy_iovecs_aux mp a (length iovs) = ImpOk iovs.
Proof.
  intros mp iovs. induction iovs as [|[b l] r IH]; intros a H; [reflexivity|].
  cbn [length copy_iovecs_aux]. destruct H as (Hb & Hl & Hlt & Hr).
  unfold read_iovec_entry. change (a + 8)%bv with (a + Z_to_bv 64 8)%bv. rewrite Hb, Hl.
  replace (2 ^ 63 <=? bv_unsigned l) with false by (symmetry; apply Z.leb_gt; lia).
  change (a + 16)%bv with (a + Z_to_bv 64 16)%bv. rewrite (IH _ Hr). reflexivity.
Qed.

Lemma readable_of_read : forall mp k a bs, read_bytes_aux mp a k = Some bs -> readable_bytes_aux mp a k = bs.
Proof.
  intros mp k. induction k as [|k IH]; intros a bs H; cbn [read_bytes_aux readable_bytes_aux] in *.
  - injection H as <-. reflexivity.
  - destruct (mp a) as [b|]; [|discriminate H]. destruct (read_bytes_aux mp (a + 1)%bv k) as [r|] eqn:Hr; [|discriminate H].
    injection H as <-. rewrite (IH _ _ Hr). reflexivity.
Qed.

Lemma read_bytes_aux_length : forall mp k a bs, read_bytes_aux mp a k = Some bs -> length bs = k.
Proof.
  intros mp k. induction k as [|k IH]; intros a bs H; cbn [read_bytes_aux] in H.
  - injection H as <-. reflexivity.
  - destruct (mp a) as [b|]; [|discriminate H]. destruct (read_bytes_aux mp (a + 1)%bv k) as [r|] eqn:Hr; [|discriminate H].
    injection H as <-. cbn. rewrite (IH _ _ Hr). reflexivity.
Qed.

Lemma gather_prefix_all : forall mp iovs bss,
  Forall2 (fun bl bs => read_bytes_map mp (fst bl) (snd bl) = Some bs) iovs bss ->
  gather_prefix mp iovs = concat bss /\ Z.of_nat (length (concat bss)) = iovs_total iovs.
Proof.
  intros mp iovs bss H. induction H as [|[b l] bs iovs bss Hr H IH]; [split; reflexivity|].
  cbn [gather_prefix concat iovs_total fst snd] in *. destruct IH as [IH1 IH2].
  rewrite read_bytes_map_eq in Hr. rewrite readable_bytes_eq, (readable_of_read _ _ _ _ Hr).
  pose proof (read_bytes_aux_length _ _ _ _ Hr) as HL. unfold word_to_nat in HL.
  pose proof (bv_unsigned_in_range _ l) as Hl.
  replace (Z.of_nat (length bs) =? bv_unsigned l) with true by (symmetry; apply Z.eqb_eq; lia).
  rewrite IH1, length_app. split; [reflexivity | lia].
Qed.

Lemma cap_iovecs_small : forall iovs left, iovs_total iovs <= left -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b l] r IH]; intros left H; cbn [cap_iovecs_aux iovs_total] in *; [reflexivity|].
  pose proof (iovs_total_nonneg r). pose proof (bv_unsigned_in_range _ l).
  rewrite Z.min_r by lia. rewrite (IH (left - bv_unsigned l)) by lia. f_equal. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact H1.
Qed.

Definition wv_cps (i : SyscallInput) (iovs : list (word * word)) (k : nat) : list (word * nat) :=
  import_iovecs_accesses (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2)) ++ (iov_prefix_accesses iovs k ++ []).
Definition wv_eff (i : SyscallInput) (iovs : list (word * word)) (k : nat) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (wv_cps i iovs k).
Definition wv_eff0 (i : SyscallInput) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [] [] (import_iovecs_accesses (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2)) ++ []).

Lemma writev_outcome : forall i m o ch (iovs : list (word * word)) (bss : list (list byte)),
  bv_unsigned (in_sysno i) = 66 ->
  fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some (FdChannel ch) -> w_is0 ch = false ->
  m_channel_reader m = true ->
  (length iovs = 1%nat \/ length iovs = 2%nat) ->
  iovcnt32 (in_arg i 2) = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  access_okb (in_arg i 1) (16 * Z.of_nat (length iovs)) = true ->
  iov_at (in_mem i) (in_arg i 1) iovs ->
  Forall (fun bl => access_okb (fst bl) (bv_unsigned (snd bl)) = true) iovs ->
  Forall2 (fun bl bs => read_bytes_map (in_mem i) (fst bl) (snd bl) = Some bs) iovs bss ->
  iovs_total iovs <= 2 ^ 30 ->
  let bs := concat bss in
  (syscall_spec i m o <->
     (bs = [] /\ o = Ok (wv_eff0 i) m []) \/
     (exists k, (1 <= k)%nat /\ (k <= length bs)%nat /\ o = Ok (wv_eff i iovs k) m (map (WriteEv ch) (firstn k bs)))).
Proof.
  intros i m o ch iovs bss Hno Hfd Hch Hrdr Hlen Hcnt Hacc Hat Haccs Hrd Htot bs.
  destruct (gather_prefix_all _ _ _ Hrd) as [Hg HL]. fold bs in Hg, HL.
  rewrite (sys66 i m o Hno). unfold writev_spec. rewrite bind_input, bind_get_model, Hfd, Hch. cbv iota.
  assert (Himp : import_iovecs (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2)) = ImpOk iovs).
  { unfold import_iovecs. rewrite Hcnt. destruct Hlen as [H1|H2].
    - destruct iovs as [|[b l] [|? ?]]; try discriminate H1. change (Z.of_nat (length [(b, l)])) with 1 in *.
      replace (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 1)) with true by reflexivity.
      replace (access_okb (in_arg i 1) 16) with true by (symmetry; exact Hacc). cbn [negb]. destruct Hat as (Hb & Hl & Hlt & _). unfold read_iovec_entry.
      change (in_arg i 1 + 8)%bv with (in_arg i 1 + Z_to_bv 64 8)%bv. rewrite Hb, Hl.
      replace (2 ^ 63 <=? bv_unsigned l) with false by (symmetry; apply Z.leb_gt; lia).
      apply Forall_inv in Haccs. cbn [fst snd] in Haccs. unfold access_okb in Haccs |- *.
      apply andb_prop in Haccs as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
      replace ((Z.min (bv_unsigned l) MAX_RW_COUNT <=? TASK_SIZE) && (bv_unsigned b <=? TASK_SIZE - Z.min (bv_unsigned l) MAX_RW_COUNT))%bool with true; [reflexivity|].
      symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
    - destruct iovs as [|e1 [|e2 [|? ?]]]; try discriminate H2. change (Z.of_nat (length [e1; e2])) with 2 in *.
      replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 1)) with false by reflexivity.
      replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 0)) with false by reflexivity.
      replace (IOV_MAX <? bv_unsigned (Z_to_bv 64 2)) with false by reflexivity.
      replace (access_okb (in_arg i 1) (16 * bv_unsigned (Z_to_bv 64 2))) with true by (symmetry; exact Hacc). cbn [negb].
      change (word_to_nat (Z_to_bv 64 2)) with (length [e1; e2]).
      rewrite (copy_iovecs_aux_ok _ _ _ Hat). unfold iovs_access_okb.
      replace (forallb (fun bl : word * word => access_okb (fst bl) (bv_unsigned (snd bl))) [e1; e2]) with true; [reflexivity|].
      symmetry. apply forallb_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Haccs x Hx). }
  rewrite Himp.
  assert (Hcap : cap_iovecs iovs = iovs) by (unfold cap_iovecs; apply cap_iovecs_small; unfold MAX_RW_COUNT; lia).
  rewrite Hcap. unfold writev_gathered. rewrite Hcap, Hg. cbv zeta.
  pose proof (iovs_total_nonneg iovs) as Hnn.
  destruct (Z.eqb_spec (iovs_total iovs) 0) as [Hz|Hnz].
  -
    assert (Hbs : bs = []) by (destruct bs; [reflexivity | cbn in HL; lia]).
    unfold record_copyins, ret_only, bind, pure. destruct o as [x m2 evs|]; split.
    + intros (eff & m1 & e1 & e2 & E1 & E2 & E3). injection E1 as -> -> ->. injection E2 as -> -> ->. subst evs. left. split; [exact Hbs | reflexivity].
    + intros [[_ E] | (k & Hk1 & Hk2 & E)]; [| exfalso; rewrite Hbs in Hk2; cbn in Hk2; lia].
      injection E as -> -> ->. eexists _, m, [], []. repeat split; reflexivity.
    + intros [E | (eff & m1 & e1 & E1 & E2)]; discriminate.
    + intros [[_ E] | (k & _ & _ & E)]; discriminate E.
  - assert (Hbs : bs <> []) by (intros E; rewrite E in HL; cbn in HL; lia).
    (* LPS 08b1429: a writev to a channel with no reader raises SIGPIPE; the model invariant pins a reader *)
    rewrite Hrdr. cbn [negb].
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; destruct bs; [congruence | cbn; lia]).
    assert (Hne : forall ds : list byte, Z.of_nat (length ds) <= Z.of_nat (length bs) -> addr_is_error_b (len_word ds) = false).
    { intros ds Hds. unfold addr_is_error_b, two_pow_64, len_word. apply Z.ltb_ge. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
    rewrite (Hne bs) by lia.
    unfold record_copyins, ret_only, choose, emit, bind, pure. destruct o as [x m2 evs|]; split.
    + intros (eff & m1 & e1 & e2 & (ds & m3 & e3 & e4 & (ds' & (D1 & D2 & D3 & D4) & E0) & (u & m4 & e5 & e6 & E4 & (eff' & m5 & e7 & e8 & E5 & E6 & E7) & E8) & E9) & E2 & E3).
      injection E0 as -> -> ->. injection E4 as -> -> ->. injection E5 as -> -> ->. injection E6 as -> -> ->. injection E2 as -> -> ->.
      subst. right. exists (length ds').
      assert (Hk : (length ds' <= length bs)%nat).
      { rewrite D4. rewrite length_firstn. lia. }
      split; [lia|]. split; [exact Hk|]. rewrite <- D4. unfold wv_eff, wv_cps, len_word. rewrite !app_nil_r. reflexivity.
    + intros [[E _] | (k & Hk1 & Hk2 & E)]; [exfalso; exact (Hbs E)|]. injection E as -> -> ->.
      set (ds := firstn k bs).
      assert (Hds : length ds = k) by (subst ds; rewrite length_firstn; lia).
      exists (mkEffectU (len_word ds) [] [] [] [] (iov_prefix_accesses iovs (length ds) ++ [])), m, (map (WriteEv ch) ds), [].
      split; [|split; [rewrite Hds; unfold wv_eff, wv_cps, len_word; rewrite Hds, !app_nil_r; reflexivity | rewrite app_nil_r; reflexivity]].
      exists ds, m, [], (map (WriteEv ch) ds). split.
      * exists ds. split; [|reflexivity]. rewrite Hds. split; [lia|]. split; [unfold two_pow_64; lia|]. split; [apply Hne; lia | reflexivity].
      * split; [|reflexivity]. exists tt, m, (map (WriteEv ch) ds), []. split; [reflexivity|]. split; [|rewrite app_nil_r; reflexivity].
        eexists _, m, [], []. repeat split; reflexivity.
    + intros [E | (eff & m1 & e1 & E1 & E2)].
      * destruct E as [(x0 & _ & E0) | (ds & m3 & e3 & (ds' & _ & E0) & [E4 | (u & m4 & e5 & E4 & [E5 | (eff' & m5 & e7 & E5 & E6)])])]; discriminate.
      * discriminate E2.
    + intros [[_ E] | (k & _ & _ & E)]; discriminate E.
Qed.

Lemma bv_add_Z_of_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = Z_to_bv 64 (bv_unsigned a + Z.of_nat j).
Proof.
  intros a j. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_r. reflexivity.
Qed.

Lemma word_succ : forall (a : word), (a + 1)%bv = Z_to_bv 64 (bv_unsigned a + 1).
Proof. intros a. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z_to_bv_add1 : forall z, (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
Proof.
  intros z. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1.
  rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.

(* LPS 08b1429: [read_cstr_aux] tests [access_okb] at every byte, so the NUL lies below TASK_SIZE. *)
Lemma read_cstr_aux_ok : forall mp (p : list byte) (A : Z) k,
  ~ In (Z_to_bv 8 0) p -> (length p < k)%nat ->
  0 <= A -> A + Z.of_nat (length p) < TASK_SIZE ->
  (forall j, (j <= length p)%nat -> mp (Z_to_bv 64 (A + Z.of_nat j)) = Some (nth j (p ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) ->
  read_cstr_aux mp (Z_to_bv 64 A) k = CstrOk p.
Proof.
  intros mp p. induction p as [|b p IH]; intros A k Hnz Hk HA Htop Hmem.
  - destruct k as [|k]; [cbn in Hk; lia|]. cbn [read_cstr_aux].
    replace (access_okb (Z_to_bv 64 A) 1) with true.
    2:{ symmetry. unfold access_okb. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, TASK_SIZE in *; cbn [length Z.of_nat] in Htop; lia).
        apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; cbn [length Z.of_nat] in Htop; lia. }
    cbn [negb].
    specialize (Hmem 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hmem. rewrite Hmem. cbn [nth app].
    unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
  - destruct k as [|k]; [cbn in Hk; lia|]. cbn [read_cstr_aux].
    replace (access_okb (Z_to_bv 64 A) 1) with true.
    2:{ symmetry. cbn [length] in Htop. unfold access_okb. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, TASK_SIZE in *; lia).
        apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
    cbn [negb].
    pose proof (Hmem 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0. cbn [nth app].
    destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Hb.
    { exfalso. apply Hnz. left. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq. exact Hb. }
    rewrite Z_to_bv_add1. rewrite (IH (A + 1) k).
    + reflexivity.
    + intros Hin. apply Hnz. right. exact Hin.
    + cbn in Hk. lia.
    + lia.
    + cbn [length] in Htop. lia.
    + intros j Hj. replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) by lia. rewrite (Hmem (S j)) by (cbn; lia). reflexivity.
Qed.

(* LPS 08b1429: [read_cstr_aux] tests [access_okb] at every byte, so the [k]
   non-NUL bytes the fuel counts out lie below TASK_SIZE.  Premise shape taken
   from the model's own [Common.FileSim.read_cstr_aux_toolong_of_rdn]: it is
   stated for [k <> 0] because at [k = 0] the walk steps no byte and the
   lemma holds wherever [A] is. *)
Lemma read_cstr_aux_toolong : forall mp (A : Z) k (f : nat -> byte),
  0 <= A -> (k <> 0%nat -> A + Z.of_nat k <= TASK_SIZE) ->
  (forall j, (j < k)%nat -> mp (Z_to_bv 64 (A + Z.of_nat j)) = Some (f j) /\ f j <> Z_to_bv 8 0) ->
  read_cstr_aux mp (Z_to_bv 64 A) k = CstrTooLong.
Proof.
  intros mp A k. revert A. induction k as [|k IH]; intros A f HA Htop Hmem; [reflexivity|].
  specialize (Htop ltac:(discriminate)). cbn [read_cstr_aux].
  replace (access_okb (Z_to_bv 64 A) 1) with true.
  2:{ symmetry. unfold access_okb. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, TASK_SIZE in *; lia).
      apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
  cbn [negb].
  destruct (Hmem 0%nat ltac:(lia)) as [H0 Hnz]. rewrite Z.add_0_r in H0. rewrite H0.
  destruct (bv_eqb (f 0%nat) (Z_to_bv 8 0)) eqn:Hb.
  { exfalso. apply Hnz. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq. exact Hb. }
  rewrite Z_to_bv_add1. rewrite (IH (A + 1) (fun j => f (S j))); [reflexivity | lia | intros _; lia |].
  intros j Hj. replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) by lia. apply Hmem. lia.
Qed.

Lemma cstr_access_len_le : forall mp (p : list byte) (A : Z) k,
  ~ In (Z_to_bv 8 0) p ->
  (forall j, (j <= length p)%nat -> mp (Z_to_bv 64 (A + Z.of_nat j)) = Some (nth j (p ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) ->
  (cstr_access_len_aux mp (Z_to_bv 64 A) k <= length p + 1)%nat.
Proof.
  intros mp p. induction p as [|b p IH]; intros A k Hnz Hmem.
  - destruct k as [|k]; [cbn; lia|]. cbn [cstr_access_len_aux].
    (* LPS 08b1429: the walk stops without counting at or above TASK_SIZE. *)
    destruct (access_okb (Z_to_bv 64 A) 1) eqn:Hacc; cbn [negb]; [|lia].
    specialize (Hmem 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hmem. rewrite Hmem. cbn [nth app].
    unfold bv_eqb. rewrite Z.eqb_refl. cbn. lia.
  - destruct k as [|k]; [cbn; lia|]. cbn [cstr_access_len_aux].
    destruct (access_okb (Z_to_bv 64 A) 1) eqn:Hacc; cbn [negb]; [|lia].
    pose proof (Hmem 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0. cbn [nth app].
    destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Hb; [cbn [length]; lia|].
    rewrite Z_to_bv_add1. cbn [length].
    assert (X : (cstr_access_len_aux mp (Z_to_bv 64 (A + 1)) k <= length p + 1)%nat).
    { apply IH; [intros Hin; apply Hnz; right; exact Hin|].
      intros j Hj. replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) by lia. rewrite (Hmem (S j)) by (cbn [length]; lia). reflexivity. }
    lia.
Qed.

Lemma read_bytes_aux_some : forall mp (A : Z) k,
  (forall j, (j < k)%nat -> mp (Z_to_bv 64 (A + Z.of_nat j)) <> None) ->
  exists bs, read_bytes_aux mp (Z_to_bv 64 A) k = Some bs.
Proof.
  intros mp A k. revert A. induction k as [|k IH]; intros A Hmem; [eexists; reflexivity|].
  cbn [read_bytes_aux]. pose proof (Hmem 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (mp (Z_to_bv 64 A)) as [b|]; [|congruence].
  rewrite Z_to_bv_add1. destruct (IH (A + 1)) as [bs Hbs].
  { intros j Hj. replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) by lia. apply Hmem. lia. }
  rewrite Hbs. eexists. reflexivity.
Qed.

Lemma apply_effect_writes : forall ms r ws cps,
  apply_effect ms (mkEffectU r ws [] [] [] cps) =
  {| ms_regs := ms_regs (set_gpr0 ms r); ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := apply_writes (ms_mem ms) ws; ms_rom := ms_rom ms |}.
Proof. intros ms r ws cps. reflexivity. Qed.

Lemma apply_effect_nowrite : forall ms r cps, apply_effect ms (mkEffectU r [] [] [] [] cps) = set_gpr0 ms r.
Proof. intros. reflexivity. Qed.

(* 75d69e00 State.v:1713-1737.  [copy_iovecs_accesses] records
   [iovec_entry_accesses] per descriptor, and that is no longer always the whole
   16 bytes: [iov_len], at [a + 8], is read FIRST, so a descriptor whose
   [iov_len] reads and whose [iov_base] faults records the 8 bytes at [a + 8]
   alone, and one whose [iov_len] faults records nothing.  The old conclusion
   [n = 16] is FALSE at the revision.  The true one -- every recorded access
   lies inside the descriptor's own 16 bytes -- is exactly what the only
   consumer needs: Glue/StdioWrite.v's [DESC] covers [16 * i, 16 * i + 16). *)
Lemma iovec_entry_accesses_in : forall mp a x n, In (x, n) (iovec_entry_accesses mp a) ->
  exists d, 0 <= d /\ d + Z.of_nat n <= 16 /\ bv_unsigned x = bv_wrap 64 (bv_unsigned a + d).
Proof.
  intros mp a x n H. unfold iovec_entry_accesses in H.
  destruct (read_u64 mp (a + 8)) as [v8|]; [|destruct H].
  destruct (read_u64 mp a) as [v0|].
  - destruct H as [H|[]]. injection H as <- <-. exists 0. split; [lia|]. split; [lia|].
    rewrite Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct H as [H|[]]. injection H as <- <-. exists 8. split; [lia|]. split; [lia|].
    rewrite bv_add_unsigned. change (bv_unsigned (8%bv : bv 64)) with 8. reflexivity.
Qed.

Lemma copy_iovecs_accesses_in : forall mp k a x n, In (x, n) (copy_iovecs_accesses mp a k) ->
  exists i d, (i < k)%nat /\ 0 <= d /\ d + Z.of_nat n <= 16 /\
    bv_unsigned x = bv_wrap 64 (bv_unsigned a + 16 * Z.of_nat i + d).
Proof.
  intros mp. induction k as [|k IH]; intros a x n H; cbn [copy_iovecs_accesses] in H; [destruct H|].
  apply in_app_or in H as [H|H].
  - destruct (iovec_entry_accesses_in mp a x n H) as (d & Hd0 & Hd1 & Hx).
    exists 0%nat, d. split; [lia|]. split; [exact Hd0|]. split; [exact Hd1|].
    rewrite Hx. f_equal. lia.
  - destruct (read_iovec_entry mp a); try (destruct H; fail).
    destruct (IH _ _ _ H) as (i & d & Hi & Hd0 & Hd1 & Hx).
    exists (S i), d. split; [lia|]. split; [exact Hd0|]. split; [exact Hd1|].
    rewrite Hx, bv_add_unsigned. change (bv_unsigned (16%bv : bv 64)) with 16.
    rewrite <- !Z.add_assoc, bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma import_iovecs_accesses_in : forall mp a (c : nat) x n, (c = 1 \/ c = 2)%nat ->
  In (x, n) (import_iovecs_accesses mp a (Z_to_bv 64 (Z.of_nat c))) ->
  exists i d, (i < c)%nat /\ 0 <= d /\ d + Z.of_nat n <= 16 /\
    bv_unsigned x = bv_wrap 64 (bv_unsigned a + 16 * Z.of_nat i + d).
Proof.
  intros mp a c x n Hc H. unfold import_iovecs_accesses in H. destruct Hc as [-> | ->].
  - change (bv_eqb (Z_to_bv 64 (Z.of_nat 1)) (Z_to_bv 64 1)) with true in H. cbv iota in H.
    destruct (negb (access_okb a 16)); [destruct H|].
    destruct (iovec_entry_accesses_in mp a x n H) as (d & Hd0 & Hd1 & Hx).
    exists 0%nat, d. split; [lia|]. split; [exact Hd0|]. split; [exact Hd1|].
    rewrite Hx. f_equal. lia.
  - change (bv_eqb (Z_to_bv 64 (Z.of_nat 2)) (Z_to_bv 64 1)) with false in H.
    change (bv_eqb (Z_to_bv 64 (Z.of_nat 2)) (Z_to_bv 64 0)) with false in H. cbv iota in H.
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat 2)))%Z; [destruct H|].
    destruct (negb (access_okb a (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat 2))))); [destruct H|].
    change (word_to_nat (Z_to_bv 64 (Z.of_nat 2))) with 2%nat in H.
    exact (copy_iovecs_accesses_in mp 2 a x n H).
Qed.

Lemma iov_prefix_accesses_in : forall iovs left x n, In (x, n) (iov_prefix_accesses iovs left) ->
  exists len, In (x, len) iovs /\ Z.of_nat n <= bv_unsigned len.
Proof.
  induction iovs as [|[b l] r IH]; intros left x n H; destruct left as [|left]; cbn [iov_prefix_accesses] in H; try (destruct H; fail).
  cbv zeta in H. destruct (Nat.eqb (word_to_nat_bounded l (S left)) 0) eqn:Q.
  - destruct (IH _ _ _ H) as (len & Hin & Hle). exists len. split; [right; exact Hin | exact Hle].
  - destruct H as [H|H].
    + injection H as <- <-. exists l. split; [left; reflexivity|]. rewrite word_to_nat_bounded_eq_min. unfold word_to_nat.
      pose proof (bv_unsigned_in_range 64 l). lia.
    + destruct (IH _ _ _ H) as (len & Hin & Hle). exists len. split; [right; exact Hin | exact Hle].
Qed.

Lemma wv_cps_in : forall i iovs k x n,
  (length iovs = 1 \/ length iovs = 2)%nat ->
  iovcnt32 (in_arg i 2) = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  In (x, n) (wv_cps i iovs k) ->
  (exists j d, (j < length iovs)%nat /\ 0 <= d /\ d + Z.of_nat n <= 16 /\
     bv_unsigned x = bv_wrap 64 (bv_unsigned (in_arg i 1) + 16 * Z.of_nat j + d)) \/
  (exists len, In (x, len) iovs /\ Z.of_nat n <= bv_unsigned len).
Proof.
  intros i iovs k x n Hl Hc H. unfold wv_cps in H. rewrite app_nil_r, Hc in H. apply in_app_or in H as [H|H].
  - left. exact (import_iovecs_accesses_in _ _ _ x n Hl H).
  - right. exact (iov_prefix_accesses_in _ _ x n H).
Qed.

Lemma wv_eff0_in : forall i (c : nat) x n, (c = 1 \/ c = 2)%nat ->
  iovcnt32 (in_arg i 2) = Z_to_bv 64 (Z.of_nat c) ->
  In (x, n) (syscall_effect_accesses (wv_eff0 i)) ->
  exists j d, (j < c)%nat /\ 0 <= d /\ d + Z.of_nat n <= 16 /\
    bv_unsigned x = bv_wrap 64 (bv_unsigned (in_arg i 1) + 16 * Z.of_nat j + d).
Proof.
  intros i c x n Hl Hc H. unfold syscall_effect_accesses, wv_eff0 in H. cbn [eff_copyins eff_writes write_accesses] in H.
  rewrite !app_nil_r, Hc in H. exact (import_iovecs_accesses_in _ _ _ x n Hl H).
Qed.

Lemma wv_eff_accesses : forall i iovs k, syscall_effect_accesses (wv_eff i iovs k) = wv_cps i iovs k.
Proof. intros. unfold syscall_effect_accesses, wv_eff. cbn [eff_copyins eff_writes write_accesses]. apply app_nil_r. Qed.

(** ** LPS 727298f3: the same answers over a larger read-only backing

    [ShapeAlg.rz_node] asks [RomBase.sys_rob] at each node.  openat (56) and writev (66) read
    [in_mem].  At the input of a larger backing ([RomBase.wrom]) the view extends the
    original ([RomBase.mem_ext]); every read these calls make here succeeds there the same way,
    so their outcome lemmas hold there with the same right side. *)
Lemma read_u64_ext : forall mp mp' a w, RomBase.mem_ext mp mp' ->
  read_u64 mp a = Some w -> read_u64 mp' a = Some w.
Proof.
  intros mp mp' a w Hx H. unfold read_u64 in *.
  destruct (read_bytes_map mp a (Z_to_bv 64 8)) as [bs|] eqn:E; [|discriminate H].
  rewrite (RomBase.read_bytes_map_ext mp mp' a _ bs Hx E). exact H.
Qed.

Lemma read_iovec_entry_at : forall mp a b l,
  read_u64 mp a = Some b -> read_u64 mp (a + Z_to_bv 64 8)%bv = Some l -> bv_unsigned l < 2 ^ 62 ->
  read_iovec_entry mp a = IovEntry b l.
Proof.
  intros mp a b l Hb Hl Hlt. unfold read_iovec_entry. change (a + 8)%bv with (a + Z_to_bv 64 8)%bv. rewrite Hb, Hl.
  replace (2 ^ 63 <=? bv_unsigned l) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma iovec_entry_accesses_ext : forall mp mp' a b l, RomBase.mem_ext mp mp' ->
  read_u64 mp a = Some b -> read_u64 mp (a + Z_to_bv 64 8)%bv = Some l ->
  iovec_entry_accesses mp' a = iovec_entry_accesses mp a.
Proof.
  intros mp mp' a b l Hx Hb Hl. unfold iovec_entry_accesses. change (a + 8)%bv with (a + Z_to_bv 64 8)%bv.
  rewrite (read_u64_ext mp mp' _ _ Hx Hl), (read_u64_ext mp mp' _ _ Hx Hb), Hl, Hb. reflexivity.
Qed.

Lemma copy_iovecs_accesses_ext : forall iovs mp mp' a, RomBase.mem_ext mp mp' -> iov_at mp a iovs ->
  copy_iovecs_accesses mp' a (length iovs) = copy_iovecs_accesses mp a (length iovs).
Proof.
  induction iovs as [|[b l] r IH]; intros mp mp' a Hx H; [reflexivity|].
  cbn [length copy_iovecs_accesses]. cbn [iov_at] in H. destruct H as (Hb & Hl & Hlt & Hr).
  rewrite (iovec_entry_accesses_ext mp mp' a b l Hx Hb Hl).
  rewrite (read_iovec_entry_at mp' a b l (read_u64_ext mp mp' _ _ Hx Hb) (read_u64_ext mp mp' _ _ Hx Hl) Hlt).
  rewrite (read_iovec_entry_at mp a b l Hb Hl Hlt).
  change (a + 16)%bv with (a + Z_to_bv 64 16)%bv. rewrite (IH mp mp' _ Hx Hr). reflexivity.
Qed.

Lemma import_iovecs_accesses_ext : forall mp mp' a iovs, RomBase.mem_ext mp mp' -> iov_at mp a iovs ->
  (length iovs = 1 \/ length iovs = 2)%nat ->
  import_iovecs_accesses mp' a (Z_to_bv 64 (Z.of_nat (length iovs)))
  = import_iovecs_accesses mp a (Z_to_bv 64 (Z.of_nat (length iovs))).
Proof.
  intros mp mp' a iovs Hx Hat Hlen.
  assert (Hn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; destruct Hlen; lia).
    apply Nat2Z.id. }
  unfold import_iovecs_accesses. rewrite Hn, (copy_iovecs_accesses_ext iovs mp mp' a Hx Hat).
  destruct iovs as [|[b l] r]; [destruct Hlen as [H|H]; discriminate H|].
  cbn [iov_at] in Hat. destruct Hat as (Hb & Hl & _ & _). rewrite (iovec_entry_accesses_ext mp mp' a b l Hx Hb Hl). reflexivity.
Qed.

Lemma iov_at_ext : forall iovs mp mp' a, RomBase.mem_ext mp mp' -> iov_at mp a iovs -> iov_at mp' a iovs.
Proof.
  induction iovs as [|[b l] r IH]; intros mp mp' a Hx H; [exact I|].
  cbn [iov_at] in H |- *. destruct H as (Hb & Hl & Hlt & Hr).
  split; [exact (read_u64_ext mp mp' _ _ Hx Hb)|]. split; [exact (read_u64_ext mp mp' _ _ Hx Hl)|].
  split; [exact Hlt | exact (IH mp mp' _ Hx Hr)].
Qed.

Lemma read_bytes_map_Forall2_ext : forall mp mp' (iovs : list (word * word)) bss, RomBase.mem_ext mp mp' ->
  Forall2 (fun bl bs => read_bytes_map mp (fst bl) (snd bl) = Some bs) iovs bss ->
  Forall2 (fun bl bs => read_bytes_map mp' (fst bl) (snd bl) = Some bs) iovs bss.
Proof.
  intros mp mp' iovs bss Hx H. induction H as [|bl bs iovs bss Hr H IH]; [constructor|].
  constructor; [exact (RomBase.read_bytes_map_ext mp mp' (fst bl) (snd bl) bs Hx Hr) | exact IH].
Qed.

(** openat's copy-in record: the path's bytes, counted the same over a larger view when the
    path read does not fault. *)
Lemma CP_ext : forall i i', in_arg i' 1 = in_arg i 1 -> RomBase.mem_ext (in_mem i) (in_mem i') ->
  read_cstr (in_mem i) (in_arg i 1) <> CstrFault -> CP i' = CP i.
Proof.
  intros i i' Ha Hx Hnf. unfold CP. rewrite Ha.
  rewrite (RomBase.cstr_access_len_aux_ext path_max (in_mem i) (in_mem i') (in_arg i 1) Hx Hnf). reflexivity.
Qed.

(** An openat whose path read does not fault: its outcomes, given at each larger backing's
    input as [Q] of that input's copy-in record, are the same there ([CP_ext]). *)
Lemma openat_rob : forall segs ms m x8 (Q : list (word * nat) -> outcome SyscallEffect -> Prop),
  ms_svc_pending ms = Some x8 ->
  read_cstr (in_mem (sys_input segs ms x8)) (in_arg (sys_input segs ms x8) 1) <> CstrFault ->
  (forall r, RomBase.rom_ext (ms_rom ms) r ->
     read_cstr (in_mem (sys_input segs (RomBase.wrom ms r) x8)) (in_arg (sys_input segs (RomBase.wrom ms r) x8) 1)
       = read_cstr (in_mem (sys_input segs ms x8)) (in_arg (sys_input segs ms x8) 1) ->
     forall o, syscall_spec (sys_input segs (RomBase.wrom ms r) x8) m o <->
               Q (CP (sys_input segs (RomBase.wrom ms r) x8)) o) ->
  RomBase.sys_rob segs (mkCfg ms m).
Proof.
  intros segs ms m x8 Q Hsvc Hnf HQ.
  apply (RomBase.sys_rob_of_char segs ms m x8 (Q (CP (sys_input segs ms x8))) Hsvc).
  intros r Hr o.
  pose proof (RomBase.mem_ext_read_byte_wrom ms r Hr) as Hx.
  eapply iff_trans;
    [exact (HQ r Hr (RomBase.read_cstr_ext (in_mem (sys_input segs ms x8)) (in_mem (sys_input segs (RomBase.wrom ms r) x8))
                       (in_arg (sys_input segs ms x8) 1) Hx Hnf) o) |].
  rewrite (CP_ext (sys_input segs ms x8) (sys_input segs (RomBase.wrom ms r) x8) eq_refl Hx Hnf).
  apply iff_refl.
Qed.

(** A writev under [writev_outcome]'s premises at the configuration's own input: the same
    answers at every larger backing ([import_iovecs_accesses_ext] for the copy-in record). *)
Lemma writev_rob : forall segs ms m x8 ch (iovs : list (word * word)) (bss : list (list byte)),
  ms_svc_pending ms = Some x8 ->
  bv_unsigned (in_sysno (sys_input segs ms x8)) = 66 ->
  fd_lookup (m_fds m) (fd32 (in_arg (sys_input segs ms x8) 0)) = Some (FdChannel ch) -> w_is0 ch = false ->
  m_channel_reader m = true ->
  (length iovs = 1%nat \/ length iovs = 2%nat) ->
  iovcnt32 (in_arg (sys_input segs ms x8) 2) = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  access_okb (in_arg (sys_input segs ms x8) 1) (16 * Z.of_nat (length iovs)) = true ->
  iov_at (in_mem (sys_input segs ms x8)) (in_arg (sys_input segs ms x8) 1) iovs ->
  Forall (fun bl => access_okb (fst bl) (bv_unsigned (snd bl)) = true) iovs ->
  Forall2 (fun bl bs => read_bytes_map (in_mem (sys_input segs ms x8)) (fst bl) (snd bl) = Some bs) iovs bss ->
  iovs_total iovs <= 2 ^ 30 ->
  RomBase.sys_rob segs (mkCfg ms m).
Proof.
  intros segs ms m x8 ch iovs bss Hsvc Hno Hfd Hch Hrdr Hlen Hcnt Hacc Hat Haccs Hrd Htot.
  set (i := sys_input segs ms x8) in *.
  apply (RomBase.sys_rob_of_char segs ms m x8
           (fun o => (concat bss = [] /\ o = Ok (wv_eff0 i) m []) \/
                     (exists k, (1 <= k)%nat /\ (k <= length (concat bss))%nat /\
                                o = Ok (wv_eff i iovs k) m (map (WriteEv ch) (firstn k (concat bss))))) Hsvc).
  intros r Hr o. cbv beta.
  set (i' := sys_input segs (RomBase.wrom ms r) x8).
  assert (Hx : RomBase.mem_ext (in_mem i) (in_mem i')) by exact (RomBase.mem_ext_read_byte_wrom ms r Hr).
  assert (EQI : import_iovecs_accesses (in_mem i') (in_arg i' 1) (iovcnt32 (in_arg i' 2))
              = import_iovecs_accesses (in_mem i) (in_arg i 1) (iovcnt32 (in_arg i 2))).
  { change (in_arg i' 1) with (in_arg i 1). change (in_arg i' 2) with (in_arg i 2). rewrite Hcnt.
    exact (import_iovecs_accesses_ext (in_mem i) (in_mem i') (in_arg i 1) iovs Hx Hat Hlen). }
  assert (EQ0 : wv_eff0 i' = wv_eff0 i) by (unfold wv_eff0; rewrite EQI; reflexivity).
  assert (EQK : forall k, wv_eff i' iovs k = wv_eff i iovs k) by (intros k; unfold wv_eff, wv_cps; rewrite EQI; reflexivity).
  destruct (writev_outcome i' m o ch iovs bss Hno Hfd Hch Hrdr Hlen Hcnt Hacc
              (iov_at_ext iovs (in_mem i) (in_mem i') (in_arg i 1) Hx Hat) Haccs
              (read_bytes_map_Forall2_ext (in_mem i) (in_mem i') iovs bss Hx Hrd) Htot) as [W1 W2].
  split.
  - intros Hs. destruct (W1 Hs) as [H|(k & H1 & H2 & H3)].
    + left. rewrite <- EQ0. exact H.
    + right. exists k. rewrite <- EQK. repeat split; assumption.
  - intros Ho. apply W2. destruct Ho as [H|(k & H1 & H2 & H3)].
    + left. rewrite EQ0. exact H.
    + right. exists k. rewrite EQK. repeat split; assumption.
Qed.

End SysSpec.
