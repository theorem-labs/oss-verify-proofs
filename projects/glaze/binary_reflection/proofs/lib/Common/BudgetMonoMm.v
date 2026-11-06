(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoDefs.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition vmrelim (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h)
    (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).

Definition relim (L : Z) (m : Model) : Model :=
  mkModelOf (m_fd m)
    (mkVmState (vmrelim L (m_vmmaps m)) (m_vm_lazy m) (m_vm_materialized m))
    (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

(* [comment removed for export] *)
Definition revs (s : VmState) (m : Model) : Model :=
  mkModelOf (m_fd m) s (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

(* [comment removed for export] *)
Definition mlim (m : Model) : Z := vm_limit (m_vmmaps m).

Definition relimc (L : Z) (c : config) : config :=
  mkCfg (cfg_ms c) (relim L (cfg_model c)).

Definition relims (L : Z) (s : step_to) : step_to :=
  match s with
  | SNext c => SNext (relimc L c)
  | SError => SError
  end.

Definition cr_map (f : Model -> Model) (r : check_result) : check_result :=
  match r with
  | CheckOk m evs => CheckOk (f m) evs
  | CheckReject => CheckReject
  | CheckUnmodeled => CheckUnmodeled
  end.






Lemma relim_as_revs : forall L m,
  relim L m = revs (mkVmState (vmrelim L (m_vmmaps m)) (m_vm_lazy m) (m_vm_materialized m)) m.
Proof. reflexivity. Qed.

Lemma revs_self : forall m, revs (m_vm m) m = m.
Proof. intros [fd vm io fs pr li ti]. reflexivity. Qed.




End BudgetMonoDefs.
Module BudgetMonoTac.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import BudgetMonoDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma bm_app_cong : forall (A B : Type) (f g : A -> B) (x y : A),
  f = g -> x = y -> f x = g y.
Proof. intros A B f g x y -> ->. reflexivity. Qed.

Ltac bm_head t :=
  lazymatch t with
  | ?f _ => bm_head f
  | ?f => f
  end.

(* [comment removed for export] *)
Ltac bm_limit_type T :=
  lazymatch T with
  | Model => idtac
  | VmState => idtac
  | VmMaps => idtac
  | check_result => idtac
  | option ?A => bm_limit_type A
  | list ?A => bm_limit_type A
  | prod ?A ?B => first [ bm_limit_type A | bm_limit_type B ]
  | _ -> _ => idtac
  | _ => fail
  end.

(* [comment removed for export] *)
Ltac bm_spine_bad l r :=
  lazymatch l with
  | ?g ?la =>
    lazymatch r with
    | ?f ?ra =>
      tryif constr_eq la ra then bm_spine_bad g f
      else (let T := type of ra in
            tryif bm_limit_type T then idtac else bm_spine_bad g f)
    | _ => fail
    end
  | _ => fail
  end.

Ltac bm_unfold_head r :=
  let h := bm_head r in
  is_const h;
  unfold h.

(* [comment removed for export] *)
Ltac bm_whd_side t :=
  lazymatch t with
  | match ?s with _ => _ end => bm_whd_side s
  | _ => bm_unfold_head t
  end.

Ltac bm_unfold_F F :=
  lazymatch F with
  | relim _ => unfold relim, vmrelim
  | revs _ => unfold revs
  end.

Ltac bm_split F sl sr :=
  let T := type of sr in
  let E := fresh "E" in
  lazymatch T with
  | check_result =>
      assert (E : sl = cr_map F sr) by bm_sync F;
      rewrite E; clear E; destruct sr; cbn [cr_map]
  | option Model =>
      assert (E : sl = option_map F sr) by bm_sync F;
      rewrite E; clear E; destruct sr; cbn [option_map]
  | _ =>
      first [ constr_eq sl sr
            | assert (E : sl = sr) by bm_sync F; rewrite E; clear E ];
      destruct sr
  end

(* [comment removed for export] *)
with bm_matches F sl sr :=
  let T := type of sr in
  tryif bm_limit_type T then
    (lazymatch T with
     | check_result => bm_split F sl sr
     | option Model => bm_split F sl sr
     | _ => first [ bm_whd_side sl | bm_whd_side sr
                  | (idtac "bm_matches: stuck on a model-carrying scrutinee"; fail 100) ]
     end)
  else bm_split F sl sr

with bm_sync F :=
  cbv beta iota zeta;
  lazymatch goal with
  (* [comment removed for export] *)
  | |- ?l = cr_map F ?r =>
    lazymatch r with
    | CheckOk _ _ => cbn [cr_map]; bm_sync F
    | CheckReject => reflexivity
    | CheckUnmodeled => reflexivity
    | match ?sr with _ => _ end =>
        lazymatch l with
        | match ?sl with _ => _ end => bm_matches F sl sr; bm_sync F
        | _ => idtac "K1: LHS not a match"; fail 100
        end
    | _ => bm_unfold_head r; bm_sync F
    end
  (* [comment removed for export] *)
  | |- ?l = option_map F ?r =>
    lazymatch r with
    | Some _ => cbn [option_map]; bm_sync F
    | None => reflexivity
    | match ?sr with _ => _ end =>
        lazymatch l with
        | match ?sl with _ => _ end => bm_matches F sl sr; bm_sync F
        | _ => idtac "K4: LHS not a match"; fail 100
        end
    | _ => bm_unfold_head r; bm_sync F
    end
  (* [comment removed for export] *)
  | |- ?l = F ?r =>
    lazymatch r with
    | mkModelOf _ _ _ _ _ _ _ => bm_unfold_F F; bm_sync F
    | match ?sr with _ => _ end =>
        lazymatch l with
        | match ?sl with _ => _ end => bm_matches F sl sr; bm_sync F
        | _ => idtac "K2: LHS not a match"; fail 100
        end
    | _ => bm_unfold_head r; bm_sync F
    end
  (* [comment removed for export] *)
  | |- ?l = ?r =>
    tryif constr_eq l r then reflexivity else
    lazymatch r with
    | match ?sr with _ => _ end =>
        lazymatch l with
        | match ?sl with _ => _ end => bm_matches F sl sr; bm_sync F
        | _ => first [ bm_whd_side l | bm_whd_side r ]; bm_sync F
        end
    | _ =>
      let hl := bm_head l in
      let hr := bm_head r in
      tryif constr_eq hl hr then
        (tryif is_constructor hr then (apply bm_app_cong; bm_sync F)
         else tryif bm_spine_bad l r then (bm_unfold_head r; bm_sync F)
         else (apply bm_app_cong; bm_sync F))
      else
        (first [ bm_whd_side l | bm_whd_side r
               | (idtac "K3 stuck"; match goal with |- ?g => idtac g end; fail 100) ]; bm_sync F)
    end
  end.

(* [comment removed for export] *)
Ltac bm_go_revs :=
  lazymatch goal with
  | m : Model |- _ =>
    destruct m as [?fd ?vm ?io ?fs ?pr ?li ?ti];
    lazymatch goal with
    | |- context [revs ?S (mkModelOf ?a ?b ?c ?d ?e ?f ?g)] =>
      change (revs S (mkModelOf a b c d e f g)) with (mkModelOf a S c d e f g)
    end
  end;
  lazymatch goal with
  | |- _ = cr_map (revs ?S) _ => bm_sync (revs S)
  end.

(* [comment removed for export] *)
Ltac bm_go_relim :=
  lazymatch goal with
  | m : Model |- _ =>
    destruct m as [?fd [[?r ?mp ?na ?sb ?b ?lim ?mb ?isp] ?lz ?mat] ?io ?fs ?pr ?li ?ti];
    lazymatch goal with
    | |- context [relim ?L (mkModelOf ?a (mkVmState (mkVmMapsFull ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) ?y1 ?y2) ?c ?d ?e ?f ?g)] =>
      change (relim L (mkModelOf a (mkVmState (mkVmMapsFull x1 x2 x3 x4 x5 x6 x7 x8) y1 y2) c d e f g))
        with (mkModelOf a (mkVmState (mkVmMapsFull x1 x2 x3 x4 x5 L x7 x8) y1 y2) c d e f g)
    end
  end;
  lazymatch goal with
  | |- _ = cr_map (relim ?L) _ => bm_sync (relim L)
  end.
End BudgetMonoTac.
Module BudgetMonoArmsA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import BudgetMonoDefs BudgetMonoTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma revs_arm_getcwd : forall i eff m S,
  ca_check arm_getcwd i eff (revs S m) = cr_map (revs S) (ca_check arm_getcwd i eff m).
Proof. intros. rewrite !ca_check_arm_getcwd. bm_go_revs. Qed.

Lemma revs_arm_epoll_ctl : forall i eff m S,
  ca_check arm_epoll_ctl i eff (revs S m) = cr_map (revs S) (ca_check arm_epoll_ctl i eff m).
Proof. intros. rewrite !ca_check_arm_epoll_ctl. bm_go_revs. Qed.

Lemma revs_arm_dup3 : forall i eff m S,
  ca_check arm_dup3 i eff (revs S m) = cr_map (revs S) (ca_check arm_dup3 i eff m).
Proof. intros. rewrite !ca_check_arm_dup3. bm_go_revs. Qed.

Lemma revs_arm_flock : forall i eff m S,
  ca_check arm_flock i eff (revs S m) = cr_map (revs S) (ca_check arm_flock i eff m).
Proof. intros. rewrite !ca_check_arm_flock. bm_go_revs. Qed.

Lemma revs_arm_faccessat : forall i eff m S,
  ca_check arm_faccessat i eff (revs S m) = cr_map (revs S) (ca_check arm_faccessat i eff m).
Proof. intros. rewrite !ca_check_arm_faccessat. bm_go_revs. Qed.

Lemma revs_arm_pipe2 : forall i eff m S,
  ca_check arm_pipe2 i eff (revs S m) = cr_map (revs S) (ca_check arm_pipe2 i eff m).
Proof. intros. rewrite !ca_check_arm_pipe2. bm_go_revs. Qed.

Lemma revs_arm_read : forall i eff m S,
  ca_check arm_read i eff (revs S m) = cr_map (revs S) (ca_check arm_read i eff m).
Proof. intros. rewrite !ca_check_arm_read. bm_go_revs. Qed.

Lemma revs_arm_writev : forall i eff m S,
  ca_check arm_writev i eff (revs S m) = cr_map (revs S) (ca_check arm_writev i eff m).
Proof. intros. rewrite !ca_check_arm_writev. bm_go_revs. Qed.

Lemma revs_arm_pselect6 : forall i eff m S,
  ca_check arm_pselect6 i eff (revs S m) = cr_map (revs S) (ca_check arm_pselect6 i eff m).
Proof. intros. rewrite !ca_check_arm_pselect6. bm_go_revs. Qed.

Lemma revs_arm_newfstatat : forall i eff m S,
  ca_check arm_newfstatat i eff (revs S m) = cr_map (revs S) (ca_check arm_newfstatat i eff m).
Proof. intros. rewrite !ca_check_arm_newfstatat. bm_go_revs. Qed.

Lemma revs_arm_fdatasync : forall i eff m S,
  ca_check arm_fdatasync i eff (revs S m) = cr_map (revs S) (ca_check arm_fdatasync i eff m).
Proof. intros. rewrite !ca_check_arm_fdatasync. bm_go_revs. Qed.

Lemma revs_arm_exit_group : forall i eff m S,
  ca_check arm_exit_group i eff (revs S m) = cr_map (revs S) (ca_check arm_exit_group i eff m).
Proof. intros. rewrite !ca_check_arm_exit_group. bm_go_revs. Qed.

Lemma revs_arm_nanosleep : forall i eff m S,
  ca_check arm_nanosleep i eff (revs S m) = cr_map (revs S) (ca_check arm_nanosleep i eff m).
Proof. intros. rewrite !ca_check_arm_nanosleep. bm_go_revs. Qed.

Lemma revs_arm_sched_getaffinity : forall i eff m S,
  ca_check arm_sched_getaffinity i eff (revs S m) = cr_map (revs S) (ca_check arm_sched_getaffinity i eff m).
Proof. intros. rewrite !ca_check_arm_sched_getaffinity. bm_go_revs. Qed.

Lemma revs_arm_sched_yield : forall i eff m S,
  ca_check arm_sched_yield i eff (revs S m) = cr_map (revs S) (ca_check arm_sched_yield i eff m).
Proof. intros. rewrite !ca_check_arm_sched_yield. bm_go_revs. Qed.

Lemma revs_arm_sigaltstack : forall i eff m S,
  ca_check arm_sigaltstack i eff (revs S m) = cr_map (revs S) (ca_check arm_sigaltstack i eff m).
Proof. intros. rewrite !ca_check_arm_sigaltstack. bm_go_revs. Qed.

Lemma revs_arm_setgid : forall i eff m S,
  ca_check arm_setgid i eff (revs S m) = cr_map (revs S) (ca_check arm_setgid i eff m).
Proof. intros. rewrite !ca_check_arm_setgid. bm_go_revs. Qed.

Lemma revs_arm_setresgid : forall i eff m S,
  ca_check arm_setresgid i eff (revs S m) = cr_map (revs S) (ca_check arm_setresgid i eff m).
Proof. intros. rewrite !ca_check_arm_setresgid. bm_go_revs. Qed.

Lemma revs_arm_setgroups : forall i eff m S,
  ca_check arm_setgroups i eff (revs S m) = cr_map (revs S) (ca_check arm_setgroups i eff m).
Proof. intros. rewrite !ca_check_arm_setgroups. bm_go_revs. Qed.

Lemma revs_arm_gettimeofday : forall i eff m S,
  ca_check arm_gettimeofday i eff (revs S m) = cr_map (revs S) (ca_check arm_gettimeofday i eff m).
Proof. intros. rewrite !ca_check_arm_gettimeofday. bm_go_revs. Qed.

Lemma revs_arm_geteuid : forall i eff m S,
  ca_check arm_geteuid i eff (revs S m) = cr_map (revs S) (ca_check arm_geteuid i eff m).
Proof. intros. rewrite !ca_check_arm_geteuid. bm_go_revs. Qed.

Lemma revs_arm_gettid : forall i eff m S,
  ca_check arm_gettid i eff (revs S m) = cr_map (revs S) (ca_check arm_gettid i eff m).
Proof. intros. rewrite !ca_check_arm_gettid. bm_go_revs. Qed.

Lemma revs_arm_bind : forall i eff m S,
  ca_check arm_bind i eff (revs S m) = cr_map (revs S) (ca_check arm_bind i eff m).
Proof. intros. rewrite !ca_check_arm_bind. bm_go_revs. Qed.

Lemma revs_arm_connect : forall i eff m S,
  ca_check arm_connect i eff (revs S m) = cr_map (revs S) (ca_check arm_connect i eff m).
Proof. intros. rewrite !ca_check_arm_connect. bm_go_revs. Qed.

Lemma revs_arm_sendto : forall i eff m S,
  ca_check arm_sendto i eff (revs S m) = cr_map (revs S) (ca_check arm_sendto i eff m).
Proof. intros. rewrite !ca_check_arm_sendto. bm_go_revs. Qed.

Lemma revs_arm_getsockopt : forall i eff m S,
  ca_check arm_getsockopt i eff (revs S m) = cr_map (revs S) (ca_check arm_getsockopt i eff m).
Proof. intros. rewrite !ca_check_arm_getsockopt. bm_go_revs. Qed.

Lemma revs_arm_recvmsg : forall i eff m S,
  ca_check arm_recvmsg i eff (revs S m) = cr_map (revs S) (ca_check arm_recvmsg i eff m).
Proof. intros. rewrite !ca_check_arm_recvmsg. bm_go_revs. Qed.

Lemma revs_arm_wait4 : forall i eff m S,
  ca_check arm_wait4 i eff (revs S m) = cr_map (revs S) (ca_check arm_wait4 i eff m).
Proof. intros. rewrite !ca_check_arm_wait4. bm_go_revs. Qed.

Lemma revs_arm_clone3 : forall i eff m S,
  ca_check arm_clone3 i eff (revs S m) = cr_map (revs S) (ca_check arm_clone3 i eff m).
Proof. intros. rewrite !ca_check_arm_clone3. bm_go_revs. Qed.
End BudgetMonoArmsA.
Module BudgetMonoArmsB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import BudgetMonoDefs BudgetMonoTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma revs_arm_eventfd2 : forall i eff m S,
  ca_check arm_eventfd2 i eff (revs S m) = cr_map (revs S) (ca_check arm_eventfd2 i eff m).
Proof. intros. rewrite !ca_check_arm_eventfd2. bm_go_revs. Qed.

Lemma revs_arm_epoll_pwait : forall i eff m S,
  ca_check arm_epoll_pwait i eff (revs S m) = cr_map (revs S) (ca_check arm_epoll_pwait i eff m).
Proof. intros. rewrite !ca_check_arm_epoll_pwait. bm_go_revs. Qed.

Lemma revs_arm_fcntl : forall i eff m S,
  ca_check arm_fcntl i eff (revs S m) = cr_map (revs S) (ca_check arm_fcntl i eff m).
Proof. intros. rewrite !ca_check_arm_fcntl. bm_go_revs. Qed.

Lemma revs_arm_unlinkat : forall i eff m S,
  ca_check arm_unlinkat i eff (revs S m) = cr_map (revs S) (ca_check arm_unlinkat i eff m).
Proof. intros. rewrite !ca_check_arm_unlinkat. bm_go_revs. Qed.

Lemma revs_arm_openat : forall i eff m S,
  ca_check arm_openat i eff (revs S m) = cr_map (revs S) (ca_check arm_openat i eff m).
Proof. intros. rewrite !ca_check_arm_openat. bm_go_revs. Qed.

Lemma revs_arm_getdents64 : forall i eff m S,
  ca_check arm_getdents64 i eff (revs S m) = cr_map (revs S) (ca_check arm_getdents64 i eff m).
Proof. intros. rewrite !ca_check_arm_getdents64. bm_go_revs. Qed.

Lemma revs_arm_write : forall i eff m S,
  ca_check arm_write i eff (revs S m) = cr_map (revs S) (ca_check arm_write i eff m).
Proof. intros. rewrite !ca_check_arm_write. bm_go_revs. Qed.

Lemma revs_arm_pread64 : forall i eff m S,
  ca_check arm_pread64 i eff (revs S m) = cr_map (revs S) (ca_check arm_pread64 i eff m).
Proof. intros. rewrite !ca_check_arm_pread64. bm_go_revs. Qed.

Lemma revs_arm_ppoll : forall i eff m S,
  ca_check arm_ppoll i eff (revs S m) = cr_map (revs S) (ca_check arm_ppoll i eff m).
Proof. intros. rewrite !ca_check_arm_ppoll. bm_go_revs. Qed.

Lemma revs_arm_fstat : forall i eff m S,
  ca_check arm_fstat i eff (revs S m) = cr_map (revs S) (ca_check arm_fstat i eff m).
Proof. intros. rewrite !ca_check_arm_fstat. bm_go_revs. Qed.

Lemma revs_arm_timerfd_create : forall i eff m S,
  ca_check arm_timerfd_create i eff (revs S m) = cr_map (revs S) (ca_check arm_timerfd_create i eff m).
Proof. intros. rewrite !ca_check_arm_timerfd_create. bm_go_revs. Qed.

Lemma revs_arm_set_tid_address : forall i eff m S,
  ca_check arm_set_tid_address i eff (revs S m) = cr_map (revs S) (ca_check arm_set_tid_address i eff m).
Proof. intros. rewrite !ca_check_arm_set_tid_address. bm_go_revs. Qed.

Lemma revs_arm_clock_gettime : forall i eff m S,
  ca_check arm_clock_gettime i eff (revs S m) = cr_map (revs S) (ca_check arm_clock_gettime i eff m).
Proof. intros. rewrite !ca_check_arm_clock_gettime. bm_go_revs. Qed.

Lemma revs_arm_tkill : forall i eff m S,
  ca_check arm_tkill i eff (revs S m) = cr_map (revs S) (ca_check arm_tkill i eff m).
Proof. intros. rewrite !ca_check_arm_tkill. bm_go_revs. Qed.

Lemma revs_arm_rt_sigaction : forall i eff m S,
  ca_check arm_rt_sigaction i eff (revs S m) = cr_map (revs S) (ca_check arm_rt_sigaction i eff m).
Proof. intros. rewrite !ca_check_arm_rt_sigaction. bm_go_revs. Qed.

Lemma revs_arm_setuid : forall i eff m S,
  ca_check arm_setuid i eff (revs S m) = cr_map (revs S) (ca_check arm_setuid i eff m).
Proof. intros. rewrite !ca_check_arm_setuid. bm_go_revs. Qed.

Lemma revs_arm_setsid : forall i eff m S,
  ca_check arm_setsid i eff (revs S m) = cr_map (revs S) (ca_check arm_setsid i eff m).
Proof. intros. rewrite !ca_check_arm_setsid. bm_go_revs. Qed.

Lemma revs_arm_uname : forall i eff m S,
  ca_check arm_uname i eff (revs S m) = cr_map (revs S) (ca_check arm_uname i eff m).
Proof. intros. rewrite !ca_check_arm_uname. bm_go_revs. Qed.

Lemma revs_arm_getpid : forall i eff m S,
  ca_check arm_getpid i eff (revs S m) = cr_map (revs S) (ca_check arm_getpid i eff m).
Proof. intros. rewrite !ca_check_arm_getpid. bm_go_revs. Qed.

Lemma revs_arm_getgid : forall i eff m S,
  ca_check arm_getgid i eff (revs S m) = cr_map (revs S) (ca_check arm_getgid i eff m).
Proof. intros. rewrite !ca_check_arm_getgid. bm_go_revs. Qed.

Lemma revs_arm_socket : forall i eff m S,
  ca_check arm_socket i eff (revs S m) = cr_map (revs S) (ca_check arm_socket i eff m).
Proof. intros. rewrite !ca_check_arm_socket. bm_go_revs. Qed.

Lemma revs_arm_listen : forall i eff m S,
  ca_check arm_listen i eff (revs S m) = cr_map (revs S) (ca_check arm_listen i eff m).
Proof. intros. rewrite !ca_check_arm_listen. bm_go_revs. Qed.

Lemma revs_arm_getsockname : forall i eff m S,
  ca_check arm_getsockname i eff (revs S m) = cr_map (revs S) (ca_check arm_getsockname i eff m).
Proof. intros. rewrite !ca_check_arm_getsockname. bm_go_revs. Qed.

Lemma revs_arm_recvfrom : forall i eff m S,
  ca_check arm_recvfrom i eff (revs S m) = cr_map (revs S) (ca_check arm_recvfrom i eff m).
Proof. intros. rewrite !ca_check_arm_recvfrom. bm_go_revs. Qed.

Lemma revs_arm_shutdown : forall i eff m S,
  ca_check arm_shutdown i eff (revs S m) = cr_map (revs S) (ca_check arm_shutdown i eff m).
Proof. intros. rewrite !ca_check_arm_shutdown. bm_go_revs. Qed.

Lemma revs_arm_clone : forall i eff m S,
  ca_check arm_clone i eff (revs S m) = cr_map (revs S) (ca_check arm_clone i eff m).
Proof. intros. rewrite !ca_check_arm_clone. bm_go_revs. Qed.

Lemma revs_arm_prlimit64 : forall i eff m S,
  ca_check arm_prlimit64 i eff (revs S m) = cr_map (revs S) (ca_check arm_prlimit64 i eff m).
Proof. intros. rewrite !ca_check_arm_prlimit64. bm_go_revs. Qed.

Lemma revs_arm_faccessat2 : forall i eff m S,
  ca_check arm_faccessat2 i eff (revs S m) = cr_map (revs S) (ca_check arm_faccessat2 i eff m).
Proof. intros. rewrite !ca_check_arm_faccessat2. bm_go_revs. Qed.
End BudgetMonoArmsB.
Module BudgetMonoArmsC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import BudgetMonoDefs BudgetMonoTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma revs_arm_epoll_create1 : forall i eff m S,
  ca_check arm_epoll_create1 i eff (revs S m) = cr_map (revs S) (ca_check arm_epoll_create1 i eff m).
Proof. intros. rewrite !ca_check_arm_epoll_create1. bm_go_revs. Qed.

Lemma revs_arm_dup : forall i eff m S,
  ca_check arm_dup i eff (revs S m) = cr_map (revs S) (ca_check arm_dup i eff m).
Proof. intros. rewrite !ca_check_arm_dup. bm_go_revs. Qed.

Lemma revs_arm_ioctl : forall i eff m S,
  ca_check arm_ioctl i eff (revs S m) = cr_map (revs S) (ca_check arm_ioctl i eff m).
Proof. intros. rewrite !ca_check_arm_ioctl. bm_go_revs. Qed.

Lemma revs_arm_ftruncate : forall i eff m S,
  ca_check arm_ftruncate i eff (revs S m) = cr_map (revs S) (ca_check arm_ftruncate i eff m).
Proof. intros. rewrite !ca_check_arm_ftruncate. bm_go_revs. Qed.

Lemma revs_arm_close : forall i eff m S,
  ca_check arm_close i eff (revs S m) = cr_map (revs S) (ca_check arm_close i eff m).
Proof. intros. rewrite !ca_check_arm_close. bm_go_revs. Qed.

Lemma revs_arm_lseek : forall i eff m S,
  ca_check arm_lseek i eff (revs S m) = cr_map (revs S) (ca_check arm_lseek i eff m).
Proof. intros. rewrite !ca_check_arm_lseek. bm_go_revs. Qed.

Lemma revs_arm_readv : forall i eff m S,
  ca_check arm_readv i eff (revs S m) = cr_map (revs S) (ca_check arm_readv i eff m).
Proof. intros. rewrite !ca_check_arm_readv. bm_go_revs. Qed.

Lemma revs_arm_pwrite64 : forall i eff m S,
  ca_check arm_pwrite64 i eff (revs S m) = cr_map (revs S) (ca_check arm_pwrite64 i eff m).
Proof. intros. rewrite !ca_check_arm_pwrite64. bm_go_revs. Qed.

Lemma revs_arm_readlinkat : forall i eff m S,
  ca_check arm_readlinkat i eff (revs S m) = cr_map (revs S) (ca_check arm_readlinkat i eff m).
Proof. intros. rewrite !ca_check_arm_readlinkat. bm_go_revs. Qed.

Lemma revs_arm_fsync : forall i eff m S,
  ca_check arm_fsync i eff (revs S m) = cr_map (revs S) (ca_check arm_fsync i eff m).
Proof. intros. rewrite !ca_check_arm_fsync. bm_go_revs. Qed.

Lemma revs_arm_exit : forall i eff m S,
  ca_check arm_exit i eff (revs S m) = cr_map (revs S) (ca_check arm_exit i eff m).
Proof. intros. rewrite !ca_check_arm_exit. bm_go_revs. Qed.

Lemma revs_arm_futex : forall i eff m S,
  ca_check arm_futex i eff (revs S m) = cr_map (revs S) (ca_check arm_futex i eff m).
Proof. intros. rewrite !ca_check_arm_futex. bm_go_revs. Qed.

Lemma revs_arm_sched_setscheduler : forall i eff m S,
  ca_check arm_sched_setscheduler i eff (revs S m) = cr_map (revs S) (ca_check arm_sched_setscheduler i eff m).
Proof. intros. rewrite !ca_check_arm_sched_setscheduler. bm_go_revs. Qed.

Lemma revs_arm_tgkill : forall i eff m S,
  ca_check arm_tgkill i eff (revs S m) = cr_map (revs S) (ca_check arm_tgkill i eff m).
Proof. intros. rewrite !ca_check_arm_tgkill. bm_go_revs. Qed.

Lemma revs_arm_rt_sigprocmask : forall i eff m S,
  ca_check arm_rt_sigprocmask i eff (revs S m) = cr_map (revs S) (ca_check arm_rt_sigprocmask i eff m).
Proof. intros. rewrite !ca_check_arm_rt_sigprocmask. bm_go_revs. Qed.

Lemma revs_arm_setresuid : forall i eff m S,
  ca_check arm_setresuid i eff (revs S m) = cr_map (revs S) (ca_check arm_setresuid i eff m).
Proof. intros. rewrite !ca_check_arm_setresuid. bm_go_revs. Qed.

Lemma revs_arm_getgroups : forall i eff m S,
  ca_check arm_getgroups i eff (revs S m) = cr_map (revs S) (ca_check arm_getgroups i eff m).
Proof. intros. rewrite !ca_check_arm_getgroups. bm_go_revs. Qed.

Lemma revs_arm_prctl : forall i eff m S,
  ca_check arm_prctl i eff (revs S m) = cr_map (revs S) (ca_check arm_prctl i eff m).
Proof. intros. rewrite !ca_check_arm_prctl. bm_go_revs. Qed.

Lemma revs_arm_getuid : forall i eff m S,
  ca_check arm_getuid i eff (revs S m) = cr_map (revs S) (ca_check arm_getuid i eff m).
Proof. intros. rewrite !ca_check_arm_getuid. bm_go_revs. Qed.

Lemma revs_arm_getegid : forall i eff m S,
  ca_check arm_getegid i eff (revs S m) = cr_map (revs S) (ca_check arm_getegid i eff m).
Proof. intros. rewrite !ca_check_arm_getegid. bm_go_revs. Qed.

Lemma revs_arm_socketpair : forall i eff m S,
  ca_check arm_socketpair i eff (revs S m) = cr_map (revs S) (ca_check arm_socketpair i eff m).
Proof. intros. rewrite !ca_check_arm_socketpair. bm_go_revs. Qed.

Lemma revs_arm_accept : forall i eff m S,
  ca_check arm_accept i eff (revs S m) = cr_map (revs S) (ca_check arm_accept i eff m).
Proof. intros. rewrite !ca_check_arm_accept. bm_go_revs. Qed.

Lemma revs_arm_getpeername : forall i eff m S,
  ca_check arm_getpeername i eff (revs S m) = cr_map (revs S) (ca_check arm_getpeername i eff m).
Proof. intros. rewrite !ca_check_arm_getpeername. bm_go_revs. Qed.

Lemma revs_arm_setsockopt : forall i eff m S,
  ca_check arm_setsockopt i eff (revs S m) = cr_map (revs S) (ca_check arm_setsockopt i eff m).
Proof. intros. rewrite !ca_check_arm_setsockopt. bm_go_revs. Qed.

Lemma revs_arm_sendmsg : forall i eff m S,
  ca_check arm_sendmsg i eff (revs S m) = cr_map (revs S) (ca_check arm_sendmsg i eff m).
Proof. intros. rewrite !ca_check_arm_sendmsg. bm_go_revs. Qed.

Lemma revs_arm_accept4 : forall i eff m S,
  ca_check arm_accept4 i eff (revs S m) = cr_map (revs S) (ca_check arm_accept4 i eff m).
Proof. intros. rewrite !ca_check_arm_accept4. bm_go_revs. Qed.

Lemma revs_arm_getrandom : forall i eff m S,
  ca_check arm_getrandom i eff (revs S m) = cr_map (revs S) (ca_check arm_getrandom i eff m).
Proof. intros. rewrite !ca_check_arm_getrandom. bm_go_revs. Qed.
End BudgetMonoArmsC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require Import AllocEd.
Import BudgetMonoDefs BudgetMonoTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)

Lemma m_vmmaps_relim : forall L m, m_vmmaps (relim L m) = vmrelim L (m_vmmaps m).
Proof. reflexivity. Qed.

Lemma vm_backing_used_relim : forall L m, vm_backing_used (relim L m) = vm_backing_used m.
Proof. reflexivity. Qed.

Lemma vm_backing_within_limit_relim : forall L m,
  vm_backing_within_limit (relim L m) = (vm_backing_used m <=? L)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_backing_within_limit_mono : forall L m,
  (L <= mlim m)%Z ->
  vm_backing_within_limit (relim L m) = true ->
  vm_backing_within_limit m = true.
Proof.
  intros L m HL H. rewrite vm_backing_within_limit_relim in H.
  unfold vm_backing_within_limit. unfold mlim in HL.
  apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.

(* [comment removed for export] *)

Lemma brk_r_ok_relim : forall L m req r,
  (L <= mlim m)%Z ->
  brk_budget_refused_b (relim L m) req = false ->
  brk_r_ok (relim L m) req r = brk_r_ok m req r.
Proof.
  intros L m req r HL Hmk.
  unfold brk_budget_refused_b, brk_r_ok, brk_grow_ok, brk_budget_ok in *.
  cbv zeta in *.
  rewrite !m_vmmaps_relim, !vm_backing_used_relim in *.
  unfold mlim in HL.
  set (h := m_vmmaps m) in *.
  change (min_brk (vmrelim L h)) with (min_brk h) in *.
  change (alloc_top (vmrelim L h)) with (alloc_top h) in *.
  cbn [vmrelim vm_brk vm_reserved vm_maps vm_limit] in *.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk h))%Z) eqn:Eq;
    [reflexivity |].
  cbn [negb andb] in Hmk.
  destruct (bv_unsigned req <? bv_unsigned (vm_brk h))%Z eqn:Es; [reflexivity |].
  destruct (bv_eqb r req) eqn:E1.
  - apply bv_eqb_eq in E1. subst r. cbn [orb andb].
    destruct ((0 <? bv_unsigned (vm_brk h))%Z && (bv_unsigned (vm_brk h) <? bv_unsigned req)%Z)
      eqn:E2; [| reflexivity].
    cbn [andb] in Hmk.
    apply negb_false_iff in Hmk. rewrite Hmk.
    apply Z.leb_le in Hmk.
    assert (Hb : (vm_backing_used m + bv_unsigned (req - vm_brk h) <=? vm_limit h)%Z = true)
      by (apply Z.leb_le; lia).
    rewrite Hb. reflexivity.
  - cbn [orb].
    destruct (bv_eqb r (vm_brk h)) eqn:E3; [| reflexivity].
    apply bv_eqb_eq in E3. subst r. cbn [andb].
    rewrite (proj2 (Z.ltb_ge (bv_unsigned (vm_brk h)) (bv_unsigned (vm_brk h))) (Z.le_refl _)).
    rewrite andb_false_r. reflexivity.
Qed.

Lemma forget_vm_ranges_relim : forall l L m,
  forget_vm_ranges l (relim L m) = relim L (forget_vm_ranges l m).
Proof.
  induction l as [|[a n] l IH]; intros L m; [reflexivity |].
  cbn [forget_vm_ranges]. rewrite <- IH. reflexivity.
Qed.

Lemma with_brk_next_relim : forall L m req r,
  with_brk_next (relim L m) req r = relim L (with_brk_next m req r).
Proof.
  intros L m req r. unfold with_brk_next. cbv zeta.
  rewrite <- forget_vm_ranges_relim. reflexivity.
Qed.

Lemma relim_arm_brk : forall i eff m L,
  (L <= mlim m)%Z ->
  brk_budget_refused_b (relim L m) (in_arg i 0) = false ->
  ca_check arm_brk i eff (relim L m) = cr_map (relim L) (ca_check arm_brk i eff m).
Proof.
  intros i eff m L HL Hmk. rewrite !ca_check_arm_brk. unfold check_brk.
  destruct eff as [r l1 zs us l4 l5].
  rewrite (brk_r_ok_relim L m (in_arg i 0) r HL Hmk).
  rewrite with_brk_next_relim.
  change (vm_brk (m_vmmaps (relim L m))) with (vm_brk (m_vmmaps m)).
  destruct l1, l4, l5; try reflexivity.
  destruct (brk_r_ok m (in_arg i 0) r && listNN_eqb zs (brk_zeros (in_arg i 0) r (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))); reflexivity.
Qed.

(* [comment removed for export] *)

Lemma relim_arm_munmap : forall i eff m L,
  ca_check arm_munmap i eff (relim L m) = cr_map (relim L) (ca_check arm_munmap i eff m).
Proof. intros. rewrite !ca_check_arm_munmap. bm_go_relim. Qed.

Lemma relim_arm_madvise : forall i eff m L,
  ca_check arm_madvise i eff (relim L m) = cr_map (relim L) (ca_check arm_madvise i eff m).
Proof. intros. rewrite !ca_check_arm_madvise. bm_go_relim. Qed.

(* [comment removed for export] *)

Lemma mprotect_budget_ok_relim : forall L m addr n,
  mprotect_budget_ok (relim L m) addr n
  = vm_backing_within_limit (relim L (mprotect_model_next m addr n)).
Proof. reflexivity. Qed.

Lemma mprotect_budget_ok_mono : forall L m addr n,
  (L <= mlim m)%Z ->
  mprotect_budget_ok (relim L m) addr n = true ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros L m addr n HL H. rewrite mprotect_budget_ok_relim in H.
  exact (vm_backing_within_limit_mono L (mprotect_model_next m addr n) HL H).
Qed.

Ltac bm_vm_proj :=
  cbn [vmrelim vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit
       vm_mmap_base vm_init_sp] in *.

Lemma relim_arm_mprotect : forall i eff m L,
  (L <= mlim m)%Z ->
  mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false ->
  ca_check arm_mprotect i eff (relim L m) = cr_map (relim L) (ca_check arm_mprotect i eff m).
Proof.
  intros i eff m L HL Hmk. rewrite !ca_check_arm_mprotect. unfold check_mprotect.
  unfold mprotect_budget_refused_b in Hmk.
  set (addr := in_arg i 0) in *. set (len := in_arg i 1) in *. set (prot := in_arg i 2) in *.
  cbv zeta in *.
  rewrite !m_vmmaps_relim in *. bm_vm_proj.
  destruct (mprotect_grows_conflict_b prot); [bm_go_relim |].
  destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [bm_go_relim |].
  destruct (w_is0 len); [bm_go_relim |].
  destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z;
    [bm_go_relim |].
  destruct (mprotect_modeled_b prot); cbn [negb]; [| reflexivity].
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) in *.
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr n
            && map_contains (vm_maps (m_vmmaps m)) addr n).
  - apply negb_false_iff in Hmk.
    pose proof (mprotect_budget_ok_mono L m addr n HL Hmk) as Hm2.
    rewrite Hmk, Hm2. bm_go_relim.
  - bm_go_relim.
Qed.

(* [comment removed for export] *)

Lemma alloc_top_vmrelim : forall L h, alloc_top (vmrelim L h) = alloc_top h.
Proof. reflexivity. Qed.

Lemma vm_gap_available_vmrelim : forall L h nZ,
  vm_gap_available (vmrelim L h) nZ = vm_gap_available h nZ.
Proof. reflexivity. Qed.

Lemma mmap_noreserve_backed_ok_mono : forall L m flags nZ,
  (L <= mlim m)%Z ->
  mmap_noreserve_backed_ok flags (relim L m) nZ = true ->
  mmap_noreserve_backed_ok flags m nZ = true.
Proof.
  intros L m flags nZ HL H. unfold mmap_noreserve_backed_ok in *.
  destruct (mmap_noreserve_b flags); [reflexivity |].
  rewrite vm_backing_used_relim in H. unfold mlim in HL.
  change (vm_limit (m_vmmaps (relim L m))) with L in H.
  apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.

Lemma mmap_fixed_rw_budget_ok_mono : forall L m flags addr n,
  (L <= mlim m)%Z ->
  mmap_fixed_rw_budget_ok flags (relim L m) addr n = true ->
  mmap_fixed_rw_budget_ok flags m addr n = true.
Proof.
  intros L m flags addr n HL H. unfold mmap_fixed_rw_budget_ok in *.
  assert (E : with_mmap_replacement flags addr n
                (with_vmmaps (mmap_fixed_rw_next (m_vmmaps (relim L m)) addr n) (relim L m))
              = relim L (with_mmap_replacement flags addr n
                (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m))).
  { unfold with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
    destruct (mmap_noreserve_b flags); reflexivity. }
  rewrite E in H. eapply vm_backing_within_limit_mono; [| exact H].
  unfold with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
  destruct (mmap_noreserve_b flags); exact HL.
Qed.

Lemma mmap_fixed_rw_span_budget_ok_mono : forall L m flags addr n,
  (L <= mlim m)%Z ->
  mmap_fixed_rw_span_budget_ok flags (relim L m) addr n = true ->
  mmap_fixed_rw_span_budget_ok flags m addr n = true.
Proof.
  intros L m flags addr n HL H. unfold mmap_fixed_rw_span_budget_ok in *.
  assert (E : with_mmap_replacement flags addr n
                (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps (relim L m)) addr n) (relim L m))
              = relim L (with_mmap_replacement flags addr n
                (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m))).
  { unfold with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
    destruct (mmap_noreserve_b flags); reflexivity. }
  rewrite E in H. eapply vm_backing_within_limit_mono; [| exact H].
  unfold with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
  destruct (mmap_noreserve_b flags); exact HL.
Qed.

Lemma relim_arm_mmap : forall i eff m L,
  (L <= mlim m)%Z ->
  mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) (relim L m) = false ->
  ca_check arm_mmap i eff (relim L m) = cr_map (relim L) (ca_check arm_mmap i eff m).
Proof.
  intros i eff m L HL Hmk. rewrite !ca_check_arm_mmap. unfold check_mmap.
  unfold mmap_budget_refused_b in Hmk.
  set (addr := in_arg i 0) in *. set (len := in_arg i 1) in *. set (prot := in_arg i 2) in *.
  set (flags := in_arg i 3) in *. set (off := in_arg i 5) in *.
  cbv zeta in *.
  rewrite !m_vmmaps_relim in *. rewrite !alloc_top_vmrelim in *.
  bm_vm_proj.
  set (nZ := page_round_up_Z (bv_unsigned len)) in *.
  set (n := Z_to_bv 64 nZ) in *.
  destruct (negb (mmap_off_aligned_b off)); [bm_go_relim |].
  destruct (negb (mmap_anon_b flags)); [reflexivity |].
  destruct (w_is0 len); [bm_go_relim |].
  destruct (mmap_modeled_b prot flags off).
  { apply negb_false_iff in Hmk.
    rewrite Hmk, (mmap_noreserve_backed_ok_mono L m flags nZ HL Hmk). bm_go_relim. }
  destruct (mmap_noaccess_b prot flags off); [bm_go_relim |].
  destruct (mmap_fixed_noaccess_b prot flags off); [bm_go_relim |].
  destruct (mmap_fixed_rw_b prot flags off).
  { destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z; [bm_go_relim |].
    destruct (negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z); [reflexivity |].
    destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [bm_go_relim |].
    destruct (negb (0 <? bv_unsigned addr)%Z); [reflexivity |].
    destruct (region_free (vm_reserved (m_vmmaps m)) addr n
              && map_contains (vm_maps (m_vmmaps m)) addr n).
    { apply negb_false_iff in Hmk.
      rewrite Hmk, (mmap_fixed_rw_budget_ok_mono L m flags addr n HL Hmk). bm_go_relim. }
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
    { apply negb_false_iff in Hmk.
      rewrite Hmk, (mmap_noreserve_backed_ok_mono L m flags nZ HL Hmk). bm_go_relim. }
    destruct (region_free (vm_reserved (m_vmmaps m)) addr n).
    { apply negb_false_iff in Hmk.
      rewrite Hmk, (mmap_fixed_rw_span_budget_ok_mono L m flags addr n HL Hmk). bm_go_relim. }
    reflexivity. }
  destruct (mmap_noreplace_noaccess_b prot flags off); [bm_go_relim |].
  destruct (mmap_noreplace_rw_b prot flags off); [| reflexivity].
  destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z; [bm_go_relim |].
  destruct (negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z); [reflexivity |].
  destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [bm_go_relim |].
  destruct (negb (0 <? bv_unsigned addr)%Z); [reflexivity |].
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
  { apply negb_false_iff in Hmk.
    rewrite Hmk, (mmap_noreserve_backed_ok_mono L m flags nZ HL Hmk). bm_go_relim. }
  bm_go_relim.
Qed.
