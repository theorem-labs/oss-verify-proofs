(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO00.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v UH00 UH01 UH03 UN3e UN35 UN3f UN3g UN34 UN3i UN3b UL0v UL0k UL0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma msg_read_error_eq : forall p, msg_read_error p = strB "cli: read error on " ++ p ++ nl.
Proof using. intros p. unfold msg_read_error. vm_compute. reflexivity. Qed.
Section b.
Variable sp : word.
Variable a0 path : list byte.
Variable envp : list (list byte).
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; path].
Hypothesis Hve : valid_envp envp.
Hypothesis Hfits : entry_stack_fits sp [a0; path] envp.
Hypothesis Hlen60 : Z.of_nat (length path) <= 60.
Theorem ubs0_read_error : forall (E : env) ms model,
env_agree 10 (E_main sp [a0; path] envp tid rnd) E ->
st_ok ubs0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] envp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
Proof using Hfits Hlen60 Hsp Hva Hve.
intros E ms model HEA HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_read_error_eq.
pose proof (layout_facts sp [a0; path] envp Hsp Hva Hve) as L. unfold SP_LO, SP_HI in L.
pose proof (z_argv_bounds sp [a0; path] envp 1 ltac:(cbn; lia)) as B1. cbn [nth] in B1.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
pose proof (argv_str_len [a0; path] Hva 1 ltac:(cbn; lia)) as Hlen1. cbn [nth] in Hlen1.
pose proof (ew0 sp [a0; path] envp (xw_main sp [a0; path] envp tid rnd) (xd_main rnd)) as H0.
change (E0 _ _ _ _ _) with (E_main sp [a0; path] envp tid rnd) in H0.
pose proof (ew2' sp [a0; path] envp Hsp Hva Hve (xw_main sp [a0; path] envp tid rnd) (xd_main rnd) ltac:(cbn; lia)) as H2.
change (E0 _ _ _ _ _) with (E_main sp [a0; path] envp tid rnd) in H2.
pose proof (z_argv_fits sp [a0; path] envp Hfits 1 ltac:(cbn; lia)) as F1. cbn [nth] in F1. unfold SP_HI in F1.
rewrite <- (proj1 HEA 0%nat ltac:(lia)) in H0. rewrite <- (proj1 HEA 2%nat ltac:(lia)) in H2.
eapply rz_conseq; [| apply (shape_1 (strB "cli: read error on ") path nl)].
sym_run_to_with ubs0tbl_ok HS 0x1e1c8.
fpf_memchr HS HR 2%nat 3%nat 2%nat 27%nat path.
sym_run_with ubs0tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 27%nat path.
sym_run3_with ubs0tbl_ok HS.
sym_add_fact HS 27%nat (mkAF 0 60 0). { atom_fact_lit. }
sym_run3_to_with ubs0tbl_ok HS 0x1dadc.
fpf_split_window HS (-541).
fpf_memcpy_str HS HR HW 2%nat 27%nat 33%nat path (-541).
sym_run3_with ubs0tbl_ok HS.
sym_assume_with3 ubs0tbl_ok HS true.
{ rewrite U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. apply negb_true_iff. apply Z.ltb_ge. lia. }
sym_run3_to_with ubs0tbl_ok HS 0x1dadc.
fpf_memcpy_lit HS HR HW HK 27%nat 44%nat nl rodata_nl2_src1 (-541).
sym_run3_with ubs0tbl_ok HS.
sym_assume_with3 ubs0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs0tbl_ok HS.
wl_writev2 HS Hfd2 55%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit. change (zcanon 0) with 0. lia. }
{ rdn_buf HS HK. }
{ reflexivity. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 0) with 0. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. evalE. lia. }
ubs0_exit_tac HS.
Qed.
End b.
Theorem ubs0_read_error_hyp : read_error_hyp.
Proof using.
unfold read_error_hyp. intros sp a0 path envp tid rnd E ms model Hsp Hva Hve Hfits Htid Hlen HEA HS HR Hh Hlz Hch.
exact (ubs0_read_error sp a0 path envp tid rnd Hsp Hva Hve Hfits Hlen E ms model HEA HS HR Hh Hlz Hch).
Qed.
End a.
