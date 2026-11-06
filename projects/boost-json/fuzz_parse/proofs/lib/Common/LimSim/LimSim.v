(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State06VmMaps37Corelib7Numbers7BinNumsj61Z0cmkVmMapsFull06vm_brk0avm_init_sp07vm_maps0cvm_mmap_base0bvm_noaccess0bvm_reserved0cvm_start_brk07VmState09mkVmState09vmst_lazy09vmst_maps0h1vmst_materialized89OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim6LimSim~~~~~~v26relimV05Model04m_fd06m_fsys04m_io05m_lim06m_proc06m_time04m_vm09mkModelOfv26relimS3h5LinuxProcessSemanticsfLinuxProcessSem3Runhoe6confighoe9cfg_modelhoe6cfg_mshoe5mkCfgv25relim37Corelib4Init5Logichuc2eq08m_vmmaps08vm_limit0fvm_backing_used08m_halted37Corelib4Init9Datatypesij56optionj64Npos35stdpp9bitvectorbdefinitionsile2bv08m_killed04m_fs3h5LinuxProcessSemanticsfLinuxProcessSem2Fsip12Fsij54listij54Someij54prod0h4materialize_accessesij53nat46Stdlib6ZArith6BinInt1Ziv82leij54Nonehuc3not0hamaterialize_model_accesseshuc3andhuc2ex3h5LinuxProcessSemanticsfLinuxProcessSem5Monadjkf4emitij54boolij54unit0cSyscallInput05event99OSSVerify6Proofsaboost_jsonafuzz_parse3lib6Common6LimSim6LimSim3Dir~~~~~~jqa3DIRjqa3MOKjkf6modifyjkf5inputjkf5sysnojkf3argjkf7get_fds07FdEntry05m_fds07m_pipes07PipeBuf09m_vm_lazy0h1m_vm_materialized07m_stdin0bInputStream09m_urandom05m_net08NetQueue09m_conn_ix05m_tid0h2m_setsid_succeeded0em_has_children0h7m_sigaltstack_installed09m_sigmask0h1m_sigabrt_pending0h0m_abort_terminal09m_utsname0am_statpinsip14path0dm_rlimit_core08m_nofile07m_clock07m_creds05Creds07FdState07IoState07FsState09ProcState08LimState09TimeState09alloc_top0evm_backed_maps" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Open Scope bv_scope.
Open Scope sys_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition relimV : ltac2:(zQ "20!ie!kf>1L$1>1h$0$0") := ltac2:(zQ "a0!kf!ie!l3!m1!m9!n5!ne!oc!p9!q6\1L$0\1h$1@8$2@1$8^1@1$5^1@1$7^1@1$9^1@1$3^1^2@1$6^1@1$4^1").
Definition relimS : ltac2:(zQ "20!r4!kf>1L$1>1v$0$0") := ltac2:(zQ "70!kf!r4!rd!s8!t3!te!hj9\1L$0\1v$1@3$2@2$6^2@1$4^1@1$3^1@1$5^1").
Definition relim : ltac2:(zQ "20!hk2!kf>1L$1>1m$0$0") := ltac2:(zQ "b0!kf!hk2!hk9!hkf!hl7!hld!hm4!hmc!hn4!hna!ho5\1L$0\1m$1@7$9@1$2^1@2$a^2@1$8^1@1$4^1@1$3^1@1$6^1@1$5^1@1$7^1").
Definition relim_cfg : ltac2:(zQ "20!hra!kf>1L$1>1c$0$0") := ltac2:(zQ "60!kf!hs4!ht1!hra!htb!hu4\1L$0\1c$3@2$4@1$2^1@2$5^2@1$1^1").

Lemma relim_limit : ltac2:(zQ "60!kf!ig0!hk2!ig6!ih0!hu4>1L$0>1m$2@3$1$0@1$4@1$3@2$5^2^1^2").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma relim_vm_backing_used : ltac2:(zQ "50!kf!iha!ig0!hk2!hu4>1L$0>1m$3@3$2$0@1$1@2$4^2^1@1$1^1").
Proof. reflexivity. Qed.
Lemma relim_halted : ltac2:(zQ "80!iib!ikd!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1").
Proof. reflexivity. Qed.
Lemma relim_killed : ltac2:(zQ "80!io1!ikd!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1").
Proof. reflexivity. Qed.
Lemma relim_fs : ltac2:(zQ "60!iob!ig0!kf!irc!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma materialize_accesses_mono : ltac2:(zQ "b0!il7!inb!is2!kf!isa!ikd!it2!ig0!ita!iv1!jh0>4lazy@1$2@2$6@1$1@1$0#k0@1$1@1$0#k0>3mat@1$2@1$1@1$0#k0>4used$3>1L$3>2L0$3>3acc@1$2@2$6@1$1@1$0#k0$9>5pages@1$2@1$1@1$0#k0>0@2$a^4^3>0@3$7@1$5@1$2@1$1@1$0#k0@5$8^8^7^6^5^3@2$4@1$2@1$1@1$0#k0^2@3$7@1$5@1$2@1$1@1$0#k0@5$8^9^8^7^5^4@2$4@1$2@1$1@1$0#k0^3").
Proof.
  intros lazy mat used L L0 acc pages HLE. unfold materialize_accesses.
  destruct (newly_materialized_pages lazy mat acc) as [|p ps]; [intros H; exact H|].
  intros H. destruct (Z.leb_spec (used + Z.of_nat (length (p :: ps)) * page_size) L); [|discriminate].
  destruct (Z.leb_spec (used + Z.of_nat (length (p :: ps)) * page_size) L0); [exact H | lia].
Qed.

Lemma materialize_accesses_down : ltac2:(zQ "c0!il7!inb!is2!ikd!ig0!kf!ita!isa!it2!jh6!iv1!jhe>4lazy@1$2@2$8@1$1@1$0#k0@1$1@1$0#k0>3mat@1$2@1$1@1$0#k0>4used$5>1L$5>2L0$5>3acc@1$2@2$8@1$1@1$0#k0$a>5pages@1$2@1$1@1$0#k0>0@3$4@1$3@1$2@1$1@1$0#k0@5$6^7^6^5^3^2@2$7@1$2@1$1@1$0#k0^1>0@1$b@3$4@1$3@1$2@1$1@1$0#k0@5$6^8^7^6^5^3@1$9@1$2@1$1@1$0#k0@3$4@1$3@1$2@1$1@1$0#k0@5$6^9^8^7^6^4@2$7@1$2@1$1@1$0#k0^3").
Proof.
  intros lazy mat used L L0 acc pages. unfold materialize_accesses.
  destruct (newly_materialized_pages lazy mat acc) as [|p ps]; [intros H _; exact H|].
  destruct (Z.leb (used + Z.of_nat (length (p :: ps)) * page_size) L0); [|discriminate].
  destruct (Z.leb (used + Z.of_nat (length (p :: ps)) * page_size) L); [intros H _; exact H | intros _ H; exfalso; apply H; reflexivity].
Qed.

Lemma materialize_relim_up : ltac2:(zQ "h10!hk2!ig0!isa!ikd!ji5!hu4!is2!iv1!it2!jk2!jk9!il7!kf!ig6!ih0!jh0!inb>1L$c>1m$0>3acc@1$6@2$8@1$h0@1$b#k0$7>2m1$0>0@2$f^4@1$e@1$d^3>0@3$1@1$3$0@2$4@2$5^5^4^3@2$2$0^2@2$a$0\2m0$0@2$9@3$1@1$3$0@2$4^6^5@2$2$0^1@3$1$0^4@2$5^7^1").
Proof.
  intros L m acc m1 HLE. unfold materialize_model_accesses.
  change (m_vm_lazy (relim L m)) with (m_vm_lazy m). change (m_vm_materialized (relim L m)) with (m_vm_materialized m).
  rewrite relim_vm_backing_used, relim_limit.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc) as [pages|] eqn:E; [|discriminate].
  rewrite (materialize_accesses_mono _ _ _ _ _ _ _ HLE E). intros H; injection H as <-.
  eexists; split; [reflexivity|]. destruct m as [fd [h lz mt] io fsys pr li ti]; reflexivity.
Qed.

Lemma materialize_relim_down : ltac2:(zQ "e0!hk2!ikd!ig0!ji5!hu4!isa!jh6!is2!iv1!it2!jhe!il7!kf!inb>1L$c>1m$0>3acc@1$7@2$9@1$d@1$b#k0$8>2m0$0>0@3$2@1$1$0@2$3^3^2@2$5$0^1>0@1$a@3$2@1$1$0@2$3@2$4^5^4^3@1$6$0@3$2@1$1$0@2$3@2$4^6^5^4@2$5$0@2$4^6^3").
Proof.
  intros L m acc m0. unfold materialize_model_accesses.
  change (m_vm_lazy (relim L m)) with (m_vm_lazy m). change (m_vm_materialized (relim L m)) with (m_vm_materialized m).
  rewrite relim_vm_backing_used, relim_limit.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) (vm_limit (m_vmmaps m)) acc) as [pages|] eqn:E; [|discriminate].
  intros H HN; injection H as <-.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc) as [pages'|] eqn:E'; [|exfalso; apply HN; reflexivity].
  pose proof (materialize_accesses_down _ _ _ L _ _ _ E) as E''. rewrite E' in E''.
  assert (E3 : Some pages' = Some pages) by (apply E''; discriminate). injection E3 as ->.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma materialize_limit : ltac2:(zQ "d0!hk2!ig0!ig6!ih0!isa!is2!iv1!ikd!it2!il7!kf!ji5!inb>1m$0>3acc@1$5@2$8@1$c@1$9#k0$6>2m0$0>0@3$1@1$7$0@2$b^3^2@2$4$0^1@3$1$a@1$3@1$2^2@1$3@1$2^4").
Proof.
  intros m acc m0 H. destruct (materialize_model_accesses_frame m acc m0 H) as (_ & E & _). rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Dir.
Variable L0 L : Z.          (* [comment removed for export] *)

Definition MOK : ltac2:(zQ "10!hk2>1m$0P") := ltac2:(zQ "50!ig0!kf!hk2!ig6!ih0\1m$2@3$0$1@1$4@1$3^1?2L0").

Definition orel {A} (o : outcome A) (o0 : outcome A) : Prop :=
  match o, o0 with
  | Ok x m1 e, Ok x0 m0 e0 => x = x0 /\ m1 = relim L m0 /\ e = e0 /\ MOK m0
  | Unmodeled, Unmodeled => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition DIR {A} (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) : Prop :=
  if d then forall o, c i (relim L m) o -> exists o0, c' i m o0 /\ orel o o0
  else forall o0, c' i m o0 -> exists o, c i (relim L m) o /\ orel o o0.

Lemma orel_refl_ok {A} : forall (x : A) m e, MOK m -> orel (Ok x (relim L m) e) (Ok x m e).
Proof. intros; cbn; repeat split; auto. Qed.

(* [comment removed for export] *)
Lemma dir_pure {A} : forall (d : bool) (i : SyscallInput) (m : Model) (x x' : A), x = x' -> MOK m -> DIR d i m (pure x) (pure x').
Proof.
  intros d i m x x' <- HM; destruct d; cbn; intros o ->.
  - eexists; split; [reflexivity|]. apply orel_refl_ok; exact HM.
  - eexists; split; [reflexivity|]. apply orel_refl_ok; exact HM.
Qed.

Lemma dir_unmodeled {A} : forall (d : bool) (i : SyscallInput) (m : Model), DIR d i m (@unmodeled A) (@unmodeled A).
Proof. intros d i m; destruct d; cbn; intros o ->; eexists; split; [reflexivity| exact I | reflexivity | exact I]. Qed.

Lemma dir_emit : ltac2:(zQ "90!jnd!jo5!is2!jod!hk2!jp5!jq3!jv5!jvc>1d$1>1i$5>1m$4>1e@1$2$6>0@1$8^2@6$7$3^5^4^3@1$0^2@1$0^2").
Proof. intros d i m e HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.

Lemma dir_modify : ltac2:(zQ "90!hk2!kg3!hu4!jo5!jod!ig0!jp5!jv5!jvc>1d$3>1i$6>1m$0>1f>1x$0$0>2f'>1x$0$0>0@3$5$0@1^2@2$2?1L^3@2$2?1L@1^1^3>0@1$8@1^2^4@6$7$4^7^6^5@1$1^4@1$1^3").
Proof.
  intros d i m f f' E HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; rewrite E; apply orel_refl_ok; exact HM.
Qed.

Lemma dir_choose {A} : forall (d : bool) (i : SyscallInput) (m : Model) (P P' : A -> Prop),
  (if d then forall x, P x -> P' x else forall x, P' x -> P x) -> MOK m -> DIR d i m (choose P) (choose P').
Proof.
  intros d i m P P' HP HM; destruct d; cbn; intros o (x & Hx & ->); eexists; (split; [exists x; split; [apply HP; exact Hx|reflexivity]|]);
    apply orel_refl_ok; exact HM.
Qed.

Lemma dir_choose_same {A} : forall (d : bool) (i : SyscallInput) (m : Model) (P : A -> Prop), MOK m -> DIR d i m (choose P) (choose P).
Proof. intros d i m P HM. apply dir_choose; [destruct d; intros x H; exact H | exact HM]. Qed.

Lemma dir_input : ltac2:(zQ "60!kgd!jp5!jo5!hk2!jv5!jvc>1d$2>1i$1>1m$3>0@1$5^1@6$4$1^4^3^2$0$0").
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_sysno : ltac2:(zQ "80!kh6!jo5!il7!hk2!jp5!jv5!jvc!inb>1d$1>1i$4>1m$3>0@1$6^1@6$5@1$7@1$2#k0^4^3^2$0$0").
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_arg : ltac2:(zQ "90!khf!jo5!iv1!il7!hk2!jp5!jv5!jvc!inb>1d$1>1i$5>1m$4>1k$2>0@1$7^2@6$6@1$8@1$3#k0^5^4^3@1$0^2@1$0^2").
Proof. intros d i m k HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_get_fds : ltac2:(zQ "b0!ki6!jo5!is2!it2!il7!kj1!hk2!jp5!jv5!jvc!inb>1d$1>1i$7>1m$6>0@1$9^1@6$8@1$2@2$3@1$a@1$4#k0$5^4^3^2$0$0").
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.

(* [comment removed for export] *)
Lemma dir_alt {A} : forall (d : bool) (i : SyscallInput) (m : Model) (c1 c2 c1' c2' : Sys A),
  DIR d i m c1 c1' -> DIR d i m c2 c2' -> DIR d i m (alt c1 c2) (alt c1' c2').
Proof.
  intros d i m c1 c2 c1' c2' H1 H2; destruct d; cbn in *; intros o [Ho|Ho].
  - destruct (H1 o Ho) as (o0 & ? & ?). exists o0; split; [left|]; assumption.
  - destruct (H2 o Ho) as (o0 & ? & ?). exists o0; split; [right|]; assumption.
  - destruct (H1 o Ho) as (o0 & ? & ?). exists o0; split; [left|]; assumption.
  - destruct (H2 o Ho) as (o0 & ? & ?). exists o0; split; [right|]; assumption.
Qed.

Lemma dir_bind {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) (k k' : A -> Sys B),
  DIR d i m c c' -> (forall x m1, MOK m1 -> DIR d i m1 (k x) (k' x)) -> DIR d i m (bind c k) (bind c' k').
Proof.
  intros d i m c c' k k' Hc Hk; destruct d; cbn in *.
  - intros [y m2 e|] Hb; cbn in Hb.
    + destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
      destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
      destruct R1 as (<- & -> & <- & M1).
      destruct (Hk x m10 M1 _ H2) as ([y0 m20 e20|] & H2' & R2); cbn in R2; [|contradiction].
      destruct R2 as (<- & -> & <- & M2).
      exists (Ok y m20 (e1 ++ e2)). split; [apply (bind_ok _ _ _ _ _ _ _ _ _ _ H1' H2') | cbn; repeat split; auto].
    + destruct Hb as [H1 | (x & m1 & e1 & H1 & H2)].
      * destruct (Hc _ H1) as ([|] & H1' & R1); cbn in R1; [contradiction|].
        exists Unmodeled. split; [apply bind_unmodeled1; exact H1' | exact I].
      * destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
        destruct R1 as (<- & -> & <- & M1).
        destruct (Hk x m10 M1 _ H2) as ([|] & H2' & R2); cbn in R2; [contradiction|].
        exists Unmodeled. split; [eapply bind_unmodeled2; [exact H1' | exact H2'] | exact I].
  - intros [y m2 e|] Hb; cbn in Hb.
    + destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
      destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
      destruct R1 as (-> & -> & -> & M1).
      destruct (Hk x m1 M1 _ H2) as ([y0 m20 e20|] & H2' & R2); cbn in R2; [|contradiction].
      destruct R2 as (-> & -> & -> & M2).
      exists (Ok y (relim L m2) (e1 ++ e2)). split; [apply (bind_ok _ _ _ _ _ _ _ _ _ _ H1' H2') | cbn; repeat split; auto].
    + destruct Hb as [H1 | (x & m1 & e1 & H1 & H2)].
      * destruct (Hc _ H1) as ([|] & H1' & R1); cbn in R1; [contradiction|].
        exists Unmodeled. split; [apply bind_unmodeled1; exact H1' | exact I].
      * destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
        destruct R1 as (-> & -> & -> & M1).
        destruct (Hk x m1 M1 _ H2) as ([|] & H2' & R2); cbn in R2; [contradiction|].
        exists Unmodeled. split; [eapply bind_unmodeled2; [exact H1' | exact H2'] | exact I].
Qed.

(* [comment removed for export] *)
Lemma dir_bind_get_model {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : Model -> Sys B),
  DIR d i m (k (relim L m)) (k' m) -> DIR d i m (bind get_model k) (bind get_model k').
Proof.
  intros d i m k k' Hk; destruct d; cbn in Hk |- *; intros o Ho.
  - apply bind_get_model in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_model; exact H | exact R].
  - apply bind_get_model in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_model; exact H | exact R].
Qed.

(* [comment removed for export] *)
Lemma dir_bind_reader {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) (v v' : SyscallInput -> Model -> A) (k k' : A -> Sys B),
  (forall i0 m0 o, c i0 m0 o <-> o = Ok (v i0 m0) m0 []) ->
  (forall i0 m0 o, c' i0 m0 o <-> o = Ok (v' i0 m0) m0 []) ->
  DIR d i m (k (v i (relim L m))) (k' (v' i m)) -> DIR d i m (bind c k) (bind c' k').
Proof.
  intros d i m c c' v v' k k' Hc Hc' Hk.
  assert (E : forall (cc : Sys A) vv (kk : A -> Sys B) i0 m0 o, (forall i1 m1 o1, cc i1 m1 o1 <-> o1 = Ok (vv i1 m1) m1 []) -> (bind cc kk i0 m0 o <-> kk (vv i0 m0) i0 m0 o)).
  { intros cc vv kk i0 m0 o Hcc. unfold bind. destruct o as [x m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). apply Hcc in H1. injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
    - intros H. exists (vv i0 m0), m0, [], evs. split; [apply Hcc; reflexivity|]. split; [exact H | reflexivity].
    - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [apply Hcc in H; discriminate|]. apply Hcc in H1. injection H1 as -> -> ->. exact H2.
    - intros H. right. exists (vv i0 m0), m0, []. split; [apply Hcc; reflexivity | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho.
  - apply (E _ _ _ _ _ _ Hc) in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply (E _ _ _ _ _ _ Hc'); exact H | exact R].
  - apply (E _ _ _ _ _ _ Hc') in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply (E _ _ _ _ _ _ Hc); exact H | exact R].
Qed.

Lemma dir_bind_input {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : SyscallInput -> Sys B),
  DIR d i m (k i) (k' i) -> DIR d i m (bind input k) (bind input k').
Proof. intros. apply (dir_bind_reader d i m input input (fun i0 _ => i0) (fun i0 _ => i0)); [intros; unfold input; reflexivity | intros; unfold input; reflexivity | exact H]. Qed.
Lemma dir_bind_sysno {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : word -> Sys B),
  DIR d i m (k (in_sysno i)) (k' (in_sysno i)) -> DIR d i m (bind sysno k) (bind sysno k').
Proof. intros. apply (dir_bind_reader d i m sysno sysno (fun i0 _ => in_sysno i0) (fun i0 _ => in_sysno i0)); [intros; unfold sysno; reflexivity | intros; unfold sysno; reflexivity | exact H]. Qed.
Lemma dir_bind_arg {B} : forall (d : bool) (i : SyscallInput) (m : Model) n (k k' : word -> Sys B),
  DIR d i m (k (in_arg i n)) (k' (in_arg i n)) -> DIR d i m (bind (arg n) k) (bind (arg n) k').
Proof. intros. apply (dir_bind_reader d i m (arg n) (arg n) (fun i0 _ => in_arg i0 n) (fun i0 _ => in_arg i0 n)); [intros; unfold arg; reflexivity | intros; unfold arg; reflexivity | exact H]. Qed.
Lemma dir_bind_get_fds {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : list (word * FdEntry) -> Sys B),
  DIR d i m (k (m_fds m)) (k' (m_fds m)) -> DIR d i m (bind get_fds k) (bind get_fds k').
Proof. intros. apply (dir_bind_reader d i m get_fds get_fds (fun _ m0 => m_fds m0) (fun _ m0 => m_fds m0)); [intros; unfold get_fds; reflexivity | intros; unfold get_fds; reflexivity | exact H]. Qed.
Lemma dir_bind_get_vmmaps' {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : VmMaps -> Sys B),
  DIR d i m (k (relimV L (m_vmmaps m))) (k' (m_vmmaps m)) -> DIR d i m (bind get_vmmaps k) (bind get_vmmaps k').
Proof. intros. apply (dir_bind_reader d i m get_vmmaps get_vmmaps (fun _ m0 => m_vmmaps m0) (fun _ m0 => m_vmmaps m0)); [intros; unfold get_vmmaps; reflexivity | intros; unfold get_vmmaps; reflexivity | exact H]. Qed.

(* [comment removed for export] *)
Lemma dir_bind_choose {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (P P' : A -> Prop) (k k' : A -> Sys B),
  (if d then forall x, P x -> P' x else forall x, P' x -> P x) ->
  (forall x, (if d then P x else P' x) -> DIR d i m (k x) (k' x)) ->
  DIR d i m (bind (choose P) k) (bind (choose P') k').
Proof.
  intros d i m P P' k k' HP Hk.
  assert (E : forall (PP : A -> Prop) (kk : A -> Sys B) i0 m0 o, bind (choose PP) kk i0 m0 o <-> exists x, PP x /\ kk x i0 m0 o).
  { intros PP kk i0 m0 o. unfold bind, choose. destruct o as [y m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & (x & Px & H1) & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exists x; split; assumption.
    - intros (x & Px & H). exists x, m0, [], evs. split; [exists x; split; [exact Px|reflexivity]|]. split; [exact H|reflexivity].
    - intros [(x & Px & H) | (x0 & m1 & evs1 & (x & Px & H1) & H2)]; [discriminate|]. injection H1 as -> -> ->. exists x; split; assumption.
    - intros (x & Px & H). right. exists x, m0, []. split; [exists x; split; [exact Px|reflexivity] | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho.
  - apply E in Ho. destruct Ho as (x & Px & Ho). destruct (Hk x Px _ Ho) as (o0 & H & R). exists o0. split; [apply E; exists x; split; [apply HP; exact Px | exact H] | exact R].
  - apply E in Ho. destruct Ho as (x & Px & Ho). destruct (Hk x Px _ Ho) as (o0 & H & R). exists o0. split; [apply E; exists x; split; [apply HP; exact Px | exact H] | exact R].
Qed.

Lemma dir_bind_choose_same {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (P : A -> Prop) (k k' : A -> Sys B),
  (forall x, P x -> DIR d i m (k x) (k' x)) -> DIR d i m (bind (choose P) k) (bind (choose P) k').
Proof. intros d i m P k k' Hk. apply dir_bind_choose; [destruct d; intros x H; exact H | intros x Hx; apply Hk; destruct d; exact Hx]. Qed.

(* [comment removed for export] *)
Lemma dir_bind_emit {B} : forall (d : bool) (i : SyscallInput) (m : Model) e (k k' : unit -> Sys B),
  DIR d i m (k tt) (k' tt) -> DIR d i m (bind (emit e) k) (bind (emit e) k').
Proof.
  intros d i m e k k' Hk.
  assert (E : forall (kk : unit -> Sys B) i0 m0 o, bind (emit e) kk i0 m0 o <->
             match o with Ok y m2 evs => exists evs2, kk tt i0 m0 (Ok y m2 evs2) /\ evs = e ++ evs2 | Unmodeled => kk tt i0 m0 Unmodeled end).
  { intros kk i0 m0 o. unfold bind, emit. destruct o as [y m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. exists evs2; split; assumption.
    - intros (evs2 & H & ->). exists tt, m0, e, evs2. repeat split; assumption.
    - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|]. injection H1 as -> -> ->. exact H2.
    - intros H. right. exists tt, m0, e. split; [reflexivity | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho; apply E in Ho.
  - destruct o as [y m2 evs|].
    + destruct Ho as (evs2 & Ho & ->). destruct (Hk _ Ho) as ([y0 m0 e0|] & H & R); cbn in R; [|contradiction]. destruct R as (<- & -> & <- & M).
      exists (Ok y m0 (e ++ evs2)). split; [apply E; exists evs2; split; [exact H|reflexivity] | cbn; repeat split; auto].
    + destruct (Hk _ Ho) as ([|] & H & R); cbn in R; [contradiction|]. exists Unmodeled. split; [apply E; exact H | exact I].
  - destruct o as [y m2 evs|].
    + destruct Ho as (evs2 & Ho & ->). destruct (Hk _ Ho) as ([y0 m0 e0|] & H & R); cbn in R; [|contradiction]. destruct R as (-> & -> & -> & M).
      exists (Ok y (relim L m2) (e ++ evs2)). split; [apply E; exists evs2; split; [exact H|reflexivity] | cbn; repeat split; auto].
    + destruct (Hk _ Ho) as ([|] & H & R); cbn in R; [contradiction|]. exists Unmodeled. split; [apply E; exact H | exact I].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dir_table_form {A} : forall (d : bool) (i : SyscallInput) (m : Model) (F F' : SyscallInput -> Sys A),
  DIR d i m (F i) (F' i) -> DIR d i m (fun i0 => F i0 i0) (fun i0 => F' i0 i0).
Proof. intros d i m F F' H. destruct d; exact H. Qed.

End Dir.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rr_m_fds : ltac2:(zQ "a0!kja!is2!it2!ig0!il7!kf!kj1!hk2!hu4!inb>1L$5>1m$7@3$3@1$1@2$2@1$9@1$4#k0$6@1$0@2$8^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_pipes : ltac2:(zQ "a0!kk1!is2!it2!ig0!il7!kf!hk2!kka!hu4!inb>1L$5>1m$6@3$3@1$1@2$2@1$9@1$4#k0$7@1$0@2$8^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_vm_lazy : ltac2:(zQ "90!il7!kl3!inb!is2!it2!ig0!kf!hk2!hu4>1L$6>1m$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_m_vm_materialized : ltac2:(zQ "80!kle!is2!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_stdin : ltac2:(zQ "60!kn2!ig0!kf!knb!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_urandom : ltac2:(zQ "60!ko8!ig0!kf!knb!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_net : ltac2:(zQ "60!kp3!ig0!kf!hk2!kpa!hu4>1L$2>1m$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_conn_ix : ltac2:(zQ "70!kq4!ig0!il7!kf!hk2!hu4!inb>1L$3>1m$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_fs : ltac2:(zQ "60!iob!ig0!kf!irc!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_halted : ltac2:(zQ "80!iib!ikd!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_tid : ltac2:(zQ "80!kqf!ikd!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_setsid_succeeded : ltac2:(zQ "60!kr6!jo5!ig0!kf!hk2!hu4>1L$3>1m$4@3$2$1@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_has_children : ltac2:(zQ "60!ksb!jo5!ig0!kf!hk2!hu4>1L$3>1m$4@3$2$1@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_sigaltstack_installed : ltac2:(zQ "60!ktb!jo5!ig0!kf!hk2!hu4>1L$3>1m$4@3$2$1@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_sigmask : ltac2:(zQ "70!kv5!ig0!il7!kf!hk2!hu4!inb>1L$3>1m$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_killed : ltac2:(zQ "80!io1!ikd!ig0!il7!kf!hk2!hu4!inb>1L$4>1m$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_sigabrt_pending : ltac2:(zQ "60!lg0!jo5!ig0!kf!hk2!hu4>1L$3>1m$4@3$2$1@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_abort_terminal : ltac2:(zQ "60!lh4!jo5!ig0!kf!hk2!hu4>1L$3>1m$4@3$2$1@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_utsname : ltac2:(zQ "90!li7!is2!ikd!ig0!il7!kf!hk2!hu4!inb>1L$5>1m$6@3$3@1$2@1$1@1$8@1$4#8@1$0@2$7^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_statpins : ltac2:(zQ "a0!is2!lj2!it2!ig0!il7!kf!lje!hk2!hu4!inb>1L$5>1m$7@3$3@1$0@2$2$6@1$0@1$9@1$4#8@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_m_rlimit_core : ltac2:(zQ "90!lk6!is2!ikd!ig0!il7!kf!hk2!hu4!inb>1L$5>1m$6@3$3@1$2@1$1@1$8@1$4#8@1$0@2$7^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_nofile : ltac2:(zQ "70!ll5!ig0!il7!kf!hk2!hu4!inb>1L$3>1m$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_clock : ltac2:(zQ "70!llf!ig0!il7!kf!hk2!hu4!inb>1L$3>1m$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_creds : ltac2:(zQ "60!lm8!ig0!kf!ln1!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_fd : ltac2:(zQ "60!hk9!ig0!kf!ln8!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_io : ltac2:(zQ "60!hl7!ig0!kf!lo1!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_fsys : ltac2:(zQ "60!hkf!ig0!kf!loa!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_proc : ltac2:(zQ "60!hm4!ig0!kf!hk2!lp3!hu4>1L$2>1m$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_lim : ltac2:(zQ "60!hld!ig0!kf!lpe!hk2!hu4>1L$2>1m$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_time : ltac2:(zQ "60!hmc!ig0!kf!hk2!lq8!hu4>1L$2>1m$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_vmmaps : ltac2:(zQ "70!ig6!ig0!kf!hk2!ie!hu4!hj9>1L$2>1m$3@3$1$4@1$0@2$5^2^1@2$6^2@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_m_vm : ltac2:(zQ "70!hn4!ig0!kf!hk2!r4!hu4!ho5>1L$2>1m$3@3$1$4@1$0@2$5^2^1@2$6^2@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vmst_maps : ltac2:(zQ "70!t3!ig0!kf!ie!r4!ho5!hj9>1L$2>1v$4@3$1$3@1$0@2$5^2^1@2$6^2@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vmst_lazy : ltac2:(zQ "90!il7!s8!inb!is2!it2!ig0!kf!r4!ho5>1L$6>1v$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vmst_materialized : ltac2:(zQ "80!te!is2!ig0!il7!kf!r4!ho5!inb>1L$4>1v$5@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vm_reserved : ltac2:(zQ "90!il7!p9!inb!is2!it2!ig0!kf!ie!hj9>1L$6>1h$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vm_maps : ltac2:(zQ "90!il7!n5!inb!is2!it2!ig0!kf!ie!hj9>1L$6>1h$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vm_noaccess : ltac2:(zQ "90!il7!oc!inb!is2!it2!ig0!kf!ie!hj9>1L$6>1h$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vm_start_brk : ltac2:(zQ "70!q6!ig0!il7!kf!ie!hj9!inb>1L$3>1h$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vm_brk : ltac2:(zQ "70!m1!ig0!il7!kf!ie!hj9!inb>1L$3>1h$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vm_mmap_base : ltac2:(zQ "70!ne!ig0!il7!kf!ie!hj9!inb>1L$3>1h$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vm_init_sp : ltac2:(zQ "70!m9!ig0!il7!kf!ie!hj9!inb>1L$3>1h$4@3$1@1$6@1$2#k0@1$0@2$5^2^1@1$0^1"). Proof. reflexivity. Qed.
Lemma rr_vm_limit : ltac2:(zQ "50!kf!ig0!ie!ih0!hj9>1L$0>1h$2@3$1$0@1$3@2$4^2^1^2"). Proof. reflexivity. Qed.
Lemma rr_alloc_top : ltac2:(zQ "50!kf!lr3!ig0!ie!hj9>1L$0>1h$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vm_backed_maps : ltac2:(zQ "90!il7!lre!inb!is2!it2!ig0!kf!ie!hj9>1L$6>1h$7@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1"). Proof. reflexivity. Qed.
Lemma rr_vm_backing_used : ltac2:(zQ "50!kf!iha!ig0!hk2!hu4>1L$0>1m$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. reflexivity. Qed.
#[export] Hint Rewrite rr_m_fds rr_m_pipes rr_m_vm_lazy rr_m_vm_materialized rr_m_stdin rr_m_urandom rr_m_net rr_m_conn_ix rr_m_fs rr_m_halted rr_m_tid rr_m_setsid_succeeded rr_m_has_children rr_m_sigaltstack_installed rr_m_sigmask rr_m_killed rr_m_sigabrt_pending rr_m_abort_terminal rr_m_utsname rr_m_statpins rr_m_rlimit_core rr_m_nofile rr_m_clock rr_m_creds rr_m_fd rr_m_io rr_m_fsys rr_m_proc rr_m_lim rr_m_time rr_m_vmmaps rr_m_vm rr_vmst_maps rr_vmst_lazy rr_vmst_materialized rr_vm_reserved rr_vm_maps rr_vm_noaccess rr_vm_start_brk rr_vm_brk rr_vm_mmap_base rr_vm_init_sp rr_vm_limit rr_alloc_top rr_vm_backed_maps rr_vm_backing_used : relim_rw.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 rec lz_head (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => lz_head f
  | _ => c
  end.
Ltac2 lz_unfold_head (c : constr) : unit :=
  let h := lz_head c in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant cst _ =>
      Std.unfold [(Std.ConstRef cst, Std.AllOccurrences)] { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
  | _ => Control.zero (Tactic_failure (Some (Message.of_string "lz_unfold_head: head is not a constant")))
  end.
Ltac unfold_head c := let tac := ltac2:(c1 |- lz_unfold_head (Option.get (Ltac1.to_constr c1))) in tac c.

(* [comment removed for export] *)
Ltac red_proj_in_goal :=
  lazy beta iota zeta delta [relim relimS relimV
    vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp fdst_table fdst_pipes vmst_maps vmst_lazy vmst_materialized
    iost_stdin iost_urandom iost_net iost_conn_ix fsst_image cr_uid cr_euid cr_suid cr_gid cr_egid cr_sgid cr_groups procst_halted procst_tid procst_creds
    procst_setsid_succeeded procst_sigmask procst_children procst_utsname procst_sigaltstack_installed procst_killed procst_sigabrt_pending
    procst_abort_terminal procst_statpins limst_core limst_nofile timest_clock m_fd m_vm m_io m_fsys m_proc m_lim m_time
    m_fds m_pipes m_vmmaps m_vm_lazy m_vm_materialized m_stdin m_urandom m_net m_conn_ix m_fs m_halted m_tid m_setsid_succeeded m_has_children
    m_sigaltstack_installed m_sigmask m_killed m_sigabrt_pending m_abort_terminal m_utsname m_statpins m_rlimit_core m_nofile m_clock m_creds].
Ltac red_proj_in H :=
  lazy beta iota zeta delta [relim relimS relimV
    vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp fdst_table fdst_pipes vmst_maps vmst_lazy vmst_materialized
    iost_stdin iost_urandom iost_net iost_conn_ix fsst_image cr_uid cr_euid cr_suid cr_gid cr_egid cr_sgid cr_groups procst_halted procst_tid procst_creds
    procst_setsid_succeeded procst_sigmask procst_children procst_utsname procst_sigaltstack_installed procst_killed procst_sigabrt_pending
    procst_abort_terminal procst_statpins limst_core limst_nofile timest_clock m_fd m_vm m_io m_fsys m_proc m_lim m_time
    m_fds m_pipes m_vmmaps m_vm_lazy m_vm_materialized m_stdin m_urandom m_net m_conn_ix m_fs m_halted m_tid m_setsid_succeeded m_has_children
    m_sigaltstack_installed m_sigmask m_killed m_sigabrt_pending m_abort_terminal m_utsname m_statpins m_rlimit_core m_nofile m_clock m_creds] in H.

(* [comment removed for export] *)
Ltac rw_proj :=
  lazy beta zeta; autorewrite with relim_rw;
  repeat match goal with H : vm_limit (m_vmmaps ?mm) = _ |- context [vm_limit (m_vmmaps ?mm)] => rewrite !H end.

(* [comment removed for export] *)
Ltac destruct_model m :=
  first [ match goal with HM : vm_limit (m_vmmaps m) = _ |- _ =>
            destruct m as [?fd [[?vr ?vmp ?vna ?vsb ?vb ?vl ?vmb ?visp] ?vlz ?vmt] ?io ?fsy ?pr ?li ?ti]; red_proj_in HM; subst vl
          | |- _ => destruct m as [?fd [[?vr ?vmp ?vna ?vsb ?vb ?vl ?vmb ?visp] ?vlz ?vmt] ?io ?fsy ?pr ?li ?ti] end;
          red_proj_in_goal ].
Ltac destruct_models := repeat match goal with m : Model |- _ => destruct_model m end.

(* [comment removed for export] *)
Ltac model_norm_step :=
  first
    [ progress red_proj_in_goal
    | match goal with |- context [match ?e with _ => _ end] =>
        lazymatch e with
        | match _ with _ => _ end => fail
        | _ => let T := type of e in
               lazymatch eval hnf in T with
               | Model => unfold_head e | VmMaps => unfold_head e | VmState => unfold_head e | FdState => unfold_head e
               | ProcState => unfold_head e | IoState => unfold_head e | LimState => unfold_head e | Creds => unfold_head e
               | _ => destruct e
               end
        end
      end ].
Ltac mok := unfold MOK; destruct_models; repeat first [ reflexivity | assumption | model_norm_step ].
Ltac commute := destruct_models; repeat first [ reflexivity | model_norm_step | lazymatch goal with |- ?l = _ => unfold_head l end ].
Ltac sim_leaf_modify := apply dir_modify; [ commute | mok ].

(* [comment removed for export] *)
Ltac sim_destruct e := destruct e.

(* [comment removed for export] *)
Ltac sim_scrut e e' :=
  lazymatch e with
  | match ?e2 with _ => _ end =>
      lazymatch e' with
      | match ?e2' with _ => _ end => sim_scrut e2 e2'
      | _ => fail "sim_scrut: shapes differ" e e'
      end
  | _ => first [ constr_eq e e'; sim_destruct e | unfold_head e; rw_proj ]
  end.

(* [comment removed for export] *)
Ltac sim_hook := fail.

(* [comment removed for export] *)
Ltac sim_step :=
  lazymatch goal with
  | |- DIR _ _ _ _ _ ?c ?c' =>
    first [ sim_hook |
    lazymatch c with
    | bind get_model _ => apply dir_bind_get_model; rw_proj
    | bind get_vmmaps _ => apply dir_bind_get_vmmaps'; rw_proj
    | bind get_fds _ => apply dir_bind_get_fds; rw_proj
    | bind input _ => apply dir_bind_input
    | bind sysno _ => apply dir_bind_sysno
    | bind (arg _) _ => apply dir_bind_arg
    | bind (emit _) _ => apply dir_bind_emit
    | bind (choose _) _ => first [ apply dir_bind_choose_same; intros ? ? | apply dir_bind_choose; [ | intros ? ?] ]
    | bind _ _ => apply dir_bind; [ | let x := fresh "x" in let m1 := fresh "m" in let HM1 := fresh "HM" in intros x m1 HM1; unfold MOK in HM1 ]
    | alt _ _ => apply dir_alt
    | pure _ => apply dir_pure; [ reflexivity | mok ]
    | unmodeled => apply dir_unmodeled
    | emit _ => apply dir_emit; mok
    | modify _ => sim_leaf_modify
    | choose _ => first [ apply dir_choose_same; mok | apply dir_choose; [ | mok ] ]
    | input => apply dir_input; mok
    | sysno => apply dir_sysno; mok
    | arg _ => apply dir_arg; mok
    | get_fds => apply dir_get_fds; mok
    | match ?e with _ => _ end =>
        lazymatch c' with
        | match ?e' with _ => _ end => sim_scrut e e'
        | _ => fail "sim: match vs non-match" c c'
        end
    | _ => unfold_head c; rw_proj
    end ]
  end.

Ltac sim := repeat sim_step.
(* [comment removed for export] *)
Ltac sim_arm m HM := unfold MOK in HM; lazy beta zeta; sim.
(* [comment removed for export] *)
