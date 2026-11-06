(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI00 YI14.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Export YI17.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Definition unlink_x (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md (TA TB : TSet),
fn_pre B MR UNLINK_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 sk_path_addr ->
sink_none B mem md ->
(forall c', (exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR UNLINK_STK (spZ regs) [sink_token] L A mem md L A mem' md' /\
regs_preserved regs regs' /\
sink_none B mem' md' /\ m_fds md' = m_fds md /\ m_fs md' = m_fs md) -> realizes segs c' TA) ->
(forall c', (exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR UNLINK_STK (spZ regs) [sink_token] L A mem md L A mem' md' /\
regs_preserved regs regs' /\
sink_none B mem' md' /\ m_fds md' = m_fds md /\
m_fs md' = Fs.fs_remove (m_fs md) sink_path /\ Fs.fs_lookup (m_fs md) sink_path <> None) -> realizes segs c' TB) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (unlink_shape (m_fs md) TA TB).
Definition fclose_spec_res (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md (f : Z) (S : list Z) (rest : list (Z * Z)) (b : rbound),
fn_pre B MR FCLOSE_STK L A regs mem md -> st_init_done A = true ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 f ->
Permutation (blocks L A) ((f, FILE_BLOCK) :: rest) -> sink_at B mem md f S ->
res_ok A b ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FCLOSE_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\
Permutation (blocks L' A') rest /\
sink_none B mem' md' /\ Fs.fs_lookup (m_fs md') sink_path = Some (bytes S) /\ res_ok A' b).
Definition fopen_x (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md (b : rbound) (TA TB : TSet),
fn_pre B MR FOPEN_STK L A regs mem md -> st_init_done A = true ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 sk_path_addr -> getr regs 11 = Z_to_bv 64 sk_mode_addr ->
sink_none B mem md ->
res_ok A b -> room b FILE_BLOCK ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
(forall c', (exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FOPEN_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
Permutation (blocks L' A') (blocks L A) /\ sink_none B mem' md' /\ m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
res_ok A' b) -> realizes segs c' TA) ->
(forall c', (exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FOPEN_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\
Permutation (blocks L' A') ((res, FILE_BLOCK) :: blocks L A) /\ sink_at B mem' md' res [] /\
m_fs md' = Fs.fs_set (m_fs md) sink_path [] /\
res_ok A' (rb_malloc b FILE_BLOCK)) -> realizes segs c' TB) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (openat_shape (m_fs md) TA TB).
End a.
