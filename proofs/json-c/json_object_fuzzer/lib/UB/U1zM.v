(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Class SrcLim : Type := mkSrcLim { LIM : Z; LIM_ge : (2 ^ 31 <= LIM)%Z }.
End FPGEN1.

#[using="Type"] Lemma SrcLim_shipped_ge : (2 ^ 31 <= source_alloc_limit)%Z.
Proof. rewrite source_alloc_limit_val. apply Z.leb_le. reflexivity. Qed.
#[using="Type"] Lemma SrcLim_sanitizer_ge : (2 ^ 31 <= sanitizer_source_limit)%Z.
Proof. apply Z.leb_le. reflexivity. Qed.
Definition SrcLim_shipped : SrcLim := mkSrcLim source_alloc_limit SrcLim_shipped_ge.
Definition SrcLim_sanitizer : SrcLim := mkSrcLim sanitizer_source_limit SrcLim_sanitizer_ge.

Section Pilot.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Context {SL : SrcLim}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable fdata : list byte.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
Hypothesis Hbrk : valid_brk RSEGS brk.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hpne : path <> [].
Hypothesis Hpnd : path <> dot_path.
Hypothesis Hplen : (length path <= 4095)%nat.

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

Definition fds0 : list (word * FdEntry) :=
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Definition model0 : Model :=
with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0)).
Definition vm0 : VmMaps := mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0.

Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
Definition model1g (fd3 : FdEntry) : Model :=
mkModelC (fds1g fd3) vm0 stdin0 fs0 None (Some tid) None.
Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

Definition above_sp0 (M : word -> option byte) : Prop :=
forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

#[using="Type"] Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = vm0.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma m0_fds : m_fds model0 = fds0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma m0_fs : m_fs model0 = fs0.
Proof. reflexivity. Qed.

#[using="Hvsp Hplen"] Lemma above_sp0_block : forall vals log M,
vals_ev vals 0 = sp0 -> log_below_b 0 0x99000 log = true -> above_sp0 M ->
above_sp0 (mem_denot (ENV vals) M log).
Proof.
intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
rewrite (mem_denot_above (ENV vals) M log 0%nat 0x99000 a Hb); [apply HA; exact Ha | | |];
cbn [ev ENV]; rewrite ?P0; lia.
Qed.

#[using="Type"] Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
Proof. exact (alloc_fd_init _ _ _). Qed.
#[using="Type"] Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
Proof. reflexivity. Qed.

#[using="Type"] Lemma msg_oom_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10d1d) 19 = Some msg_oom.
Proof. vm_compute. reflexivity. Qed.

#[using="a0s Hva"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.

#[using="a0s tid Hva Htid"] Lemma path_noslash : path_has_slash path = false.
Proof. destruct Hva as (_ & _ & _ & _ & Ht). cbn [tl] in Ht. inversion Ht; subst. tauto. Qed.
#[using="a0s tid Hva Htid"] Lemma path_notdotdot : path_eqb path dotdot_path = false.
Proof. destruct Hva as (_ & _ & _ & _ & Ht). cbn [tl] in Ht. inversion Ht; subst. tauto. Qed.
#[using="a0s tid Hva Htid"] Lemma path_not_dirref : path <> dot_path -> Open.path_is_dirref path = false.
Proof.
intros Hnd. unfold Open.path_is_dirref.
replace (path_eqb path Namei.dotdot_path) with false by (symmetry; exact path_notdotdot).
rewrite Bool.orb_false_r.
destruct (path_eqb path Uapi.dot_path) eqn:E; [| reflexivity]. exfalso. apply Hnd. apply path_eqb_eq. exact E.
Qed.

Definition open_err_branch (KA : TSet) : Prop :=
forall e vals R M,
In e openat_errnos ->
length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 39 = errno_ret e ->
vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 5 = tid ->
regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 39)) R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x6086c) M (seg_rom RSEGS)) model0) KA.
End Pilot.
