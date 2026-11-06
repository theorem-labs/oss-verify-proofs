(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Sys.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Inductive getid_no : Z -> (Creds -> word) -> Prop :=
| getid_uid  : getid_no 174 cr_uid
| getid_euid : getid_no 175 cr_euid
| getid_gid  : getid_no 176 cr_gid
| getid_egid : getid_no 177 cr_egid.

Lemma syscall_spec_getid : forall segs ms x8 m o no sel,
  getid_no no sel -> bv_unsigned x8 = no ->
  (syscall_spec (sys_input segs ms x8) m o <-> getid_spec sel (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o no sel Hsel Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. destruct Hsel; reflexivity.
Qed.

Lemma getid_spec_iff : forall segs ms x8 m no sel,
  getid_no no sel -> bv_unsigned x8 = no ->
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (sel (m_creds m)) [] []) m [].
Proof.
  intros segs ms x8 m no sel Hsel Hno o.
  rewrite (syscall_spec_getid segs ms x8 m o no sel Hsel Hno).
  unfold getid_spec. rewrite bind_get_model. unfold ret_only, pure. reflexivity.
Qed.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Theorem getid_step_iff : forall ms x8 m no sel,
  getid_no no sel -> bv_unsigned x8 = no ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (sel (m_creds m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m no sel Hsel Hno Hh Hl Hsvc e st.
  rewrite (sstep_cfg_det_iff cfg segs ms m x8 _ _ _ Hh Hsvc
             (getid_spec_iff segs ms x8 m no sel Hsel Hno) Hh Hl).
  reflexivity.
Qed.

Theorem node_getid_cfg : forall ms x8 m no sel,
  getid_no no sel -> bv_unsigned x8 = no ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 ->
  node_ok_cfg cfg segs (mkCfg ms m) unit (fun _ => [])
    (fun _ => mkCfg (sysret ms (sel (m_creds m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m no sel Hsel Hno Hh Hl Hsvc. apply node_ok_cfg_of_step_iff_det.
  apply (getid_step_iff ms x8 m no sel); assumption.
Qed.

Theorem rzc_getid : forall ms x8 m no sel T,
  getid_no no sel -> bv_unsigned x8 = no ->
  m_halted m = None -> m_vm_lazy m = [] ->
  ms_svc_pending ms = Some x8 ->
  realizes_cfg cfg segs (mkCfg (sysret ms (sel (m_creds m)) (ms_mem ms)) m) T ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros ms x8 m no sel T Hsel Hno Hh Hl Hsvc HT.
  eapply rzc_silent1; [apply (node_getid_cfg ms x8 m no sel); assumption | exact HT].
Qed.

End WithCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition creds_of_input (inp : ProcInput) : Creds :=
  mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
          (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp).

Definition creds_from (inp : ProcInput) (m : Model) : Prop := m_creds m = creds_of_input inp.

Lemma creds_from_init : forall reserved brk0 mbase sp lim inp,
  creds_from inp (init_model reserved brk0 mbase sp lim inp).
Proof. intros. reflexivity. Qed.

Lemma creds_from_init_cfg : forall img lim en inp,
  creds_from inp (cfg_model (init_cfg img lim en inp)).
Proof. intros [s pc ph] lim [sp brk0 mb rnd] inp. reflexivity. Qed.

Lemma getid_ret_from : forall inp m no sel,
  creds_from inp m -> getid_no no sel ->
  sel (m_creds m) = if (no <? 176) then in_uid inp else in_gid inp.
Proof. intros inp m no sel H Hsel. rewrite H. destruct Hsel; reflexivity. Qed.

Lemma getid_uid_euid_same : forall inp m,
  creds_from inp m -> cr_euid (m_creds m) = cr_uid (m_creds m).
Proof. intros inp m H. rewrite H. reflexivity. Qed.

Lemma getid_gid_egid_same : forall inp m,
  creds_from inp m -> cr_egid (m_creds m) = cr_gid (m_creds m).
Proof. intros inp m H. rewrite H. reflexivity. Qed.

Lemma valid_id_bound : forall inp, valid_input inp ->
  bv_unsigned (in_uid inp) < 2 ^ 32 - 1 /\ bv_unsigned (in_gid inp) < 2 ^ 32 - 1.
Proof.
  intros inp H. unfold valid_input in H.
  assert (Hc : valid_creds inp) by tauto. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma creds_from_eq : forall inp m m', m_creds m' = m_creds m -> creds_from inp m -> creds_from inp m'.
Proof. intros inp m m' He H. unfold creds_from. rewrite He. exact H. Qed.

Lemma m_creds_with_vmmaps' : forall h m, m_creds (with_vmmaps h m) = m_creds m.
Proof. reflexivity. Qed.

Lemma m_creds_account_step : forall segs ms m ms' m',
  mi_account_step segs ms m = MachineOk (ms', m') -> m_creds m' = m_creds m.
Proof.
  intros segs ms m ms' m' H.
  destruct (mi_account_step_model_frame segs ms m ms' m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_creds. rewrite Hp. reflexivity.
Qed.

Lemma m_creds_asteps : forall segs n ms m ms' m',
  asteps segs n (ms, m) = MachineOk (ms', m') -> m_creds m' = m_creds m.
Proof.
  intros segs n ms m ms' m' H.
  destruct (asteps_frame segs n ms m ms' m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_creds. rewrite Hp. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma creds_from_alloc_models : forall inp m,
  creds_from inp m ->
  (forall a nZ, creds_from inp (mmap_grant_model a nZ m))
  /\ (forall a n, creds_from inp (with_vmmaps (ledger_unmap a n (m_vmmaps m)) m))
  /\ (forall req, creds_from inp (brk_grow_model req m))
  /\ (forall a nZ, creds_from inp (mmap_guard_model a nZ m))
  /\ (forall a nZ, creds_from inp (mmap_na_model a nZ m))
  /\ (forall a nZ, creds_from inp (mprotect_rw_model a nZ m)).
Proof. intros inp m H. repeat split; intros; exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition addr_off (a : word) (i : nat) : word := bv_add a (Z_to_bv 64 (Z.of_nat i)).

Lemma addr_off_0 : forall a, addr_off a 0 = a.
Proof. intros. unfold addr_off. bv_solve. Qed.

Lemma addr_off_S : forall a i, addr_off (a + 1)%bv i = addr_off a (S i).
Proof. intros. unfold addr_off. bv_solve. Qed.

Definition nul_byte : byte := Z_to_bv 8 0.

(* [comment removed for export] *)
Definition no_nul (p : list byte) : bool := forallb (fun b => negb (bv_eqb b nul_byte)) p.

Lemma read_cstr_aux_intro : forall p mp a k,
  (length p < k)%nat ->
  no_nul p = true ->
  (forall i, (i < length p)%nat -> mp (addr_off a i) = nth_error p i) ->
  mp (addr_off a (length p)) = Some nul_byte ->
  read_cstr_aux mp a k = CstrOk p.
Proof.
  induction p as [|b p IH]; intros mp a k Hk Hnn Hbytes Hnul.
  - destruct k as [|k]; [cbn in Hk; lia |]. cbn [read_cstr_aux].
    cbn [length] in Hnul. rewrite addr_off_0 in Hnul. rewrite Hnul.
    unfold nul_byte. change (bv_eqb (Z_to_bv 8 0) (Z_to_bv 8 0)) with true. reflexivity.
  - destruct k as [|k]; [cbn in Hk; lia |]. cbn [read_cstr_aux].
    pose proof (Hbytes 0%nat ltac:(cbn; lia)) as H0. cbn [nth_error] in H0.
    rewrite addr_off_0 in H0. rewrite H0.
    cbn [no_nul forallb] in Hnn. apply andb_true_iff in Hnn as [Hb Hnn].
    apply negb_true_iff in Hb. unfold nul_byte in Hb. rewrite Hb.
    rewrite (IH mp (a + 1)%bv k); [reflexivity | cbn [length] in Hk; lia | exact Hnn | |].
    + intros i Hi. rewrite addr_off_S. apply (Hbytes (S i)). cbn [length]. lia.
    + rewrite addr_off_S. exact Hnul.
Qed.

Lemma read_cstr_intro : forall p mp a,
  (length p < path_max)%nat ->
  no_nul p = true ->
  (forall i, (i < length p)%nat -> mp (addr_off a i) = nth_error p i) ->
  mp (addr_off a (length p)) = Some nul_byte ->
  read_cstr mp a = CstrOk p.
Proof. intros. unfold read_cstr. apply read_cstr_aux_intro; assumption. Qed.

(* [comment removed for export] *)
Lemma fd32_at_fdcwd : forall w : word,
  bv_unsigned w mod 2 ^ 32 = 2 ^ 32 - 100 -> fd32 w = AT_FDCWD32.
Proof.
  intros w H. unfold AT_FDCWD32, fd32, abi_low32. rewrite H. reflexivity.
Qed.

Lemma fd32_at_fdcwd_lit : fd32 (Z_to_bv 64 (-100)) = AT_FDCWD32.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma modeled_open_flags_largefile : forall fl : word,
  bv_unsigned fl = 32768 -> modeled_open_flags fl = true.
Proof. intros fl H. unfold modeled_open_flags. rewrite H. reflexivity. Qed.

Lemma path_has_slash_nonempty : forall p, path_has_slash p = true -> path_eqb p [] = false.
Proof. intros [|b p] H; [discriminate H | reflexivity]. Qed.

Lemma syscall_spec_openat : forall segs ms x8 m o,
  bv_unsigned x8 = 56 ->
  (syscall_spec (sys_input segs ms x8) m o
   <-> openat_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) m o).
Proof.
  intros segs ms x8 m o Hno. unfold syscall_spec, Sys.Dispatch.dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem openat_sep_unmodeled : forall segs ms x8 m p,
  bv_unsigned x8 = 56 ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_has_slash p = true ->
  path_eqb p localtime_path = false ->
  path_eqb p devnull_path = false ->
  path_eqb p urandom_path = false ->   (* [comment removed for export] *)
  tmp_name p = None ->
  syscall_spec (sys_input segs ms x8) m Unmodeled.
Proof.
  intros segs ms x8 m p Hno Hfd Hfl Hread Hslash Hlt Hdn Hur Htmp.
  apply (syscall_spec_openat segs ms x8 m Unmodeled Hno).
  unfold openat_spec, record_copyins.
  (* [comment removed for export] *)
  unfold bind at 1. right. exists (sys_input segs ms x8), m, [].
  split; [reflexivity |].
  unfold bind at 1. left.
  unfold openat_core_spec.
  unfold bind at 1. right. exists (sys_input segs ms x8), m, []. split; [reflexivity |].
  unfold bind at 1. right. exists m, m, []. split; [reflexivity |].
  rewrite Hfl. cbn [negb].
  unfold openat_body_spec.
  change (in_mem (sys_input segs ms x8)) with (ms_read_byte ms). rewrite Hread.
  rewrite (path_has_slash_nonempty p Hslash).
  rewrite Hfd. change (bv_eqb AT_FDCWD32 AT_FDCWD32) with true. cbn [negb].
  unfold openat_resolved_spec. rewrite Hslash.
  unfold openat_sep_spec. rewrite Hlt, Hdn, Hur, Htmp. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem openat_sep_reaches_error : forall cfg segs ms x8 m p,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56 ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  (length p < path_max)%nat -> no_nul p = true ->
  (forall i, (i < length p)%nat -> ms_read_byte ms (addr_off (ms_gpr ms 1) i) = nth_error p i) ->
  ms_read_byte ms (addr_off (ms_gpr ms 1) (length p)) = Some nul_byte ->
  path_has_slash p = true ->
  path_eqb p localtime_path = false ->
  path_eqb p devnull_path = false ->
  path_eqb p urandom_path = false ->   (* [comment removed for export] *)
  tmp_name p = None ->
  reaches_error_cfg segs cfg (mkCfg ms m).
Proof.
  intros cfg segs ms x8 m p Hh Hsvc Hno Hfd Hfl Hlen Hnn Hbytes Hnul Hslash Hlt Hdn Hur Htmp.
  apply (reaches_error_cfg_unmodeled_here cfg segs ms m x8 Hh Hsvc).
  apply (openat_sep_unmodeled segs ms x8 m p Hno Hfd Hfl); try assumption.
  apply read_cstr_intro; assumption.
Qed.

(* [comment removed for export] *)
Corollary openat_sep_reaches_error_star : forall cfg segs c tr ms x8 m p,
  star_cfg segs cfg c tr (mkCfg ms m) ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56 ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  (length p < path_max)%nat -> no_nul p = true ->
  (forall i, (i < length p)%nat -> ms_read_byte ms (addr_off (ms_gpr ms 1) i) = nth_error p i) ->
  ms_read_byte ms (addr_off (ms_gpr ms 1) (length p)) = Some nul_byte ->
  path_has_slash p = true ->
  path_eqb p localtime_path = false ->
  path_eqb p devnull_path = false ->
  path_eqb p urandom_path = false ->   (* [comment removed for export] *)
  tmp_name p = None ->
  reaches_error_cfg segs cfg c.
Proof.
  intros cfg segs c tr ms x8 m p Hstar Hh Hsvc Hno Hfd Hfl Hlen Hnn Hbytes Hnul Hslash Hlt Hdn Hur Htmp.
  eapply reaches_error_cfg_star; [exact Hstar |].
  eapply openat_sep_reaches_error; eassumption.
Qed.
