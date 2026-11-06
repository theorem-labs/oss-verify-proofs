(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0l.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0n YP0o YK04 YA0i YA0m YA0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section a.
Context {fx : FPState}.
Section b.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
#[local] Notation OCI regs pc mem rom := (open_copyins (pend_at regs pc mem rom)).
Definition errno_ix : Type := {e : Z | In e openat_errnos}.
Lemma node_open_core_full_lazy : forall regs pc mem rom model reads (mk : word -> Model),
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_open_result_copyins reads eff model mk) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) <> None ->
ranges_avoid H reads ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) errno_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig i))) (v_addi pc 4) mem rom) (materialized_succ model reads))
/\ AI segs H A (materialized_succ model reads) /\ same_but_materialized model (materialized_succ model reads).
Proof.
intros regs pc mem rom model reads mk HAI Hchk Hocc Hav Hna.
pose (ef := fun i : errno_ix => with_copyins reads (mkEffect (errno_ret (proj1_sig i)) [] [])).
assert (Hacc : forall i, syscall_effect_accesses (ef i) = reads) by (intros i; cbn; apply app_nil_r).
destruct (node_chk_lazy segs H A (pend_at regs pc mem rom) model (getr regs 17) errno_ix (exist _ ENOMEM ENOMEM_in_openat_errnos)
ef (fun _ => model) (fun _ => []) HAI eq_refl) as [Hn Hs].
- intros [e He]; unfold ef; cbn [proj1_sig]. rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
- intros _. exact (AI_halted segs H A model HAI).
- intros _. apply ledgers_same.
- intros i. rewrite Hacc. exact Hav.
- intros eff m' evs Hk. rewrite Hchk in Hk. apply check_open_result_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (fd & Hfree & Efd & _ & _ & _)].
+ exists (exist _ e He). unfold ef; cbn [proj1_sig]. auto.
+ exfalso. apply Hocc. rewrite <- Efd. exact Hfree.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- split.
+ eapply node_ok_ext; [exact Hn|]. intros i. cbn beta. rewrite adv_pend, Hacc.
unfold ef. cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. reflexivity.
+ pose proof (Hs (exist _ ENOMEM ENOMEM_in_openat_errnos)) as [HA HS]. rewrite Hacc in HA, HS. exact (conj HA HS).
Qed.
Lemma node_openat_tmp_create_lazy : forall regs pc mem rom model p n,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H (OCI regs pc mem rom) ->
let mk := fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) open_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (open_ret (m_fds model) i)) (v_addi pc 4) mem rom)
(materialized_succ (open_md model mk i) (OCI regs pc mem rom)))
/\ (forall i, AI segs H A (materialized_succ (open_md model mk i) (OCI regs pc mem rom))
/\ same_but_materialized (open_md model mk i) (materialized_succ (open_md model mk i) (OCI regs pc mem rom))).
Proof.
intros regs pc mem rom model p n HAI Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hfree Hav mk.
apply (node_open_core_lazy segs H A regs pc mem rom model (OCI regs pc mem rom) mk HAI).
- intro eff.
rewrite (openat_tmp_wr_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- intro fd. unfold mk. rewrite with_fds_halted, with_fs_halted. exact (AI_halted segs H A model HAI).
- intro fd. apply ledgers_with_fds_fs.
- exact Hfree.
- exact Hav.
- rewrite Hno; reflexivity.
Qed.
Lemma node_openat_tmp_full_lazy : forall regs pc mem rom model p n,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) <> None ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) errno_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig i))) (v_addi pc 4) mem rom) (materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom)) /\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model p n HAI Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hocc Hav.
apply (node_open_core_full_lazy regs pc mem rom model (OCI regs pc mem rom)
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model)) HAI).
- intro eff.
rewrite (openat_tmp_wr_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- exact Hocc.
- exact Hav.
- rewrite Hno; reflexivity.
Qed.
Lemma node_openat_tmp_isdir_lazy : forall regs pc mem rom model p n,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = true ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) (materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom)) /\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model p n HAI Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hav.
apply (node_ret_only_copyins_lazy segs H A regs pc mem rom model (OCI regs pc mem rom) (errno_ret EISDIR) model [] HAI).
- intro eff.
rewrite (openat_tmp_wr_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Definition unlink_ix : Type := ({e : Z | In e unlinkat_errnos} + unit)%type.
Definition unlink_ret (i : unlink_ix) : word := match i with inl e => errno_ret (proj1_sig e) | inr _ => Z_to_bv 64 0 end.
Definition unlink_md (model : Model) (p : path) (i : unlink_ix) : Model :=
match i with inl _ => model | inr _ => with_fs (fs_remove (m_fs model) p) model end.
Lemma node_unlink_core_lazy : forall regs pc mem rom model reads p,
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model = check_unlink_present_copyins reads eff model p) ->
ranges_avoid H reads ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unlink_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (unlink_ret i)) (v_addi pc 4) mem rom) (materialized_succ (unlink_md model p i) reads))
/\ (forall i, AI segs H A (materialized_succ (unlink_md model p i) reads)
/\ same_but_materialized (unlink_md model p i) (materialized_succ (unlink_md model p i) reads)).
Proof.
intros regs pc mem rom model reads p HAI Hchk Hav Hna.
pose (ef := fun i : unlink_ix => with_copyins reads (mkEffect (unlink_ret i) [] [])).
assert (Hacc : forall i, syscall_effect_accesses (ef i) = reads) by (intros i; cbn; apply app_nil_r).
destruct (node_chk_lazy segs H A (pend_at regs pc mem rom) model (getr regs 17) unlink_ix (inr tt) ef (unlink_md model p) (fun _ => []) HAI eq_refl) as [Hn Hs].
- intros [[e He] | []]; unfold ef, unlink_md, unlink_ret; cbn [proj1_sig]; rewrite Hchk; apply check_unlink_present_copyins_ok_iff.
+ left. exists e. auto.
+ right. auto.
- intros [[e He] | []]; unfold unlink_md; [exact (AI_halted segs H A model HAI) | rewrite with_fs_halted; exact (AI_halted segs H A model HAI)].
- intros [[e He] | []]; unfold unlink_md; [apply ledgers_same | repeat split; reflexivity].
- intros i. rewrite Hacc. exact Hav.
- intros eff m' evs Hk. rewrite Hchk in Hk. apply check_unlink_present_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (-> & -> & ->)].
+ exists (inl (exist _ e He)). unfold ef, unlink_md, unlink_ret; cbn [proj1_sig]. auto.
+ exists (inr tt). unfold ef, unlink_md, unlink_ret. auto.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- split.
+ eapply node_ok_ext; [exact Hn|]. intros i. cbn beta. rewrite adv_pend, Hacc.
unfold ef. cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. reflexivity.
+ intros i. rewrite <- (Hacc i). exact (Hs i).
Qed.
Lemma node_unlink_tmp_present_lazy : forall regs pc mem rom model p n d,
AI segs H A model ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fd_names_path (m_fds model) p = false ->
fs_under (m_fs model) p = false -> fs_lookup (m_fs model) p = Some d ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unlink_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (unlink_ret i)) (v_addi pc 4) mem rom) (materialized_succ (unlink_md model p i) (OCI regs pc mem rom)))
/\ (forall i, AI segs H A (materialized_succ (unlink_md model p i) (OCI regs pc mem rom))
/\ same_but_materialized (unlink_md model p i) (materialized_succ (unlink_md model p i) (OCI regs pc mem rom))).
Proof.
intros regs pc mem rom model p n d HAI Hno Hdir Hp Hfl Hpe Hstrip Hsl Htmp Hnm Hfdn Hun Hlk Hav.
apply (node_unlink_core_lazy regs pc mem rom model (OCI regs pc mem rom) p HAI);
[| exact Hav | rewrite Hno; reflexivity].
intro eff. rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl) Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun, Hlk. reflexivity.
Qed.
Lemma node_unlink_tmp_absent_lazy : forall regs pc mem rom model p n,
AI segs H A model ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fd_names_path (m_fds model) p = false ->
fs_under (m_fs model) p = false -> fs_lookup (m_fs model) p = None ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom) (materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom)) /\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model p n HAI Hno Hdir Hp Hfl Hpe Hstrip Hsl Htmp Hnm Hfdn Hun Hlk Hav.
apply (node_ret_only_copyins_lazy segs H A regs pc mem rom model (OCI regs pc mem rom) (errno_ret ENOENT) model [] HAI).
- intro eff. rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl) Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun, Hlk. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Lemma node_unlink_tmp_isdir_lazy : forall regs pc mem rom model p n,
AI segs H A model ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fd_names_path (m_fds model) p = false ->
fs_under (m_fs model) p = true ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) (materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom)) /\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model p n HAI Hno Hdir Hp Hfl Hpe Hstrip Hsl Htmp Hnm Hfdn Hun Hav.
apply (node_ret_only_copyins_lazy segs H A regs pc mem rom model (OCI regs pc mem rom) (errno_ret EISDIR) model [] HAI).
- intro eff. rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl) Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
End b.
End a.
