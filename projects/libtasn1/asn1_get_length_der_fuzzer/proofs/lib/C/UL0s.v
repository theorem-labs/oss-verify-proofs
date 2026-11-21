(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: hex addresses and numbers for the binaries of libtasn1/asn1_get_length_der_fuzzer, and module names. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the read-error arm is stated over the run, with the launch premises. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YQ0k.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP07 YP00.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YO3v UH04 UH05 UH07 UO3p UO3k UO3q UO3r UO3j UO3t UO3m UL0q UL0g UL0l.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma msg_read_error_eq : forall p, msg_read_error p = strB "cli: read error on " ++ p ++ nl.
Proof. intros p. unfold msg_read_error. vm_compute. reflexivity. Qed.
Section b.
Variables (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hlen60 : Z.of_nat (length path) <= 60.
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Theorem ubs2_read_error : forall (E : env) ms model,
env_agree 10 (E_main sp inp [a0; path] envp efn tid rnd) E ->
st_ok ubs2segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs2segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
Proof.
intros E ms model HEA HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_read_error_eq.
assert (Hal : (1 < length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L.
pose proof (z_argv_bounds inp rnd 1 Hal) as B1.
pose proof (argv_no_nul inp Hva 1 Hal) as Hnul1.
pose proof (argv_str_len inp Hva 1 Hal) as Hlen1.
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 1 Hal) as F1.
assert (H0 : bv_unsigned (ew (E_main sp inp [a0; path] envp efn tid rnd) 0) = bv_unsigned sp) by reflexivity.
assert (H2 : bv_unsigned (ew (E_main sp inp [a0; path] envp efn tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1).
{ unfold E_main. rewrite <- Hargv. eapply ew2'; first [eassumption | rewrite Hargv; cbn; lia]. }
rewrite Hargv in L, B1, Hnul1, Hlen1, F1. cbn [nth] in B1, Hnul1, Hlen1, F1.
unfold SP_LO, SP_HI in L, F1.
rewrite <- (proj1 HEA 0%nat ltac:(lia)) in H0. rewrite <- (proj1 HEA 2%nat ltac:(lia)) in H2.
eapply rz_conseq; [| apply (shape_1 (strB "cli: read error on ") path nl)].
sym_run_to_with ubs2tbl_ok HS 0x1a948.
fpf_memchr HS HR 2%nat 3%nat 2%nat 27%nat path.
sym_run_with ubs2tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 27%nat path.
sym_run3_with ubs2tbl_ok HS.
sym_add_fact HS 27%nat (mkAF 0 60 0). { atom_fact_lit. }
sym_run3_to_with ubs2tbl_ok HS 0x1a408.
fpf_split_window HS (-541).
fpf_memcpy_str HS HR HW 2%nat 27%nat 33%nat path (-541).
sym_run3_with ubs2tbl_ok HS.
sym_assume_with3 ubs2tbl_ok HS true.
{ rewrite U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. apply negb_true_iff. apply Z.ltb_ge. lia. }
sym_run3_to_with ubs2tbl_ok HS 0x1a408.
fpf_memcpy_lit HS HR HW HK 27%nat 44%nat nl rodata_nl2_src1 (-541).
sym_run3_with ubs2tbl_ok HS.
sym_assume_with3 ubs2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs2tbl_ok HS.
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
ubs2_exit_tac HS.
Qed.
End b.
Theorem ubs2_read_error_hyp : read_error_hyp.
Proof.
unfold read_error_hyp. intros sp brk mbase inp a0 path tid rnd E ms model Hsp Hargv Hva Hve Hvl Hlau Htid Hlen HEA HS HR Hh Hlz Hch.
eapply ubs2_read_error; eassumption.
Qed.
End a.
