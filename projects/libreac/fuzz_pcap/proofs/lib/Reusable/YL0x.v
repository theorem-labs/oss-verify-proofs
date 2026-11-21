From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0x.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed msg_read_error_eq, src0_read_error, src0_read_error_hyp; added envp, HvaI). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO00.
From OSSVerify.libreac.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma msg_read_error_eq : forall p, msg_read_error p = strB "cli: read error on " ++ p ++ nl.
Proof. intros p. unfold msg_read_error. vm_compute. reflexivity. Qed.
Section b.
Local Set Default Proof Using "All".
Variable sp : word.
Variable a0 path : list byte.
Variable inp : ProcInput.
Variables mbase brk : word.
Variable tid : word.
Variable rnd : EntryDraw.
Local Notation envp := (in_envp inp) (only parsing).
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; path].
Hypothesis Hve : valid_envp envp.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hfits : entry_stack_fits sp [a0; path] envp.
Lemma HvaI : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.
Hypothesis Hlen60 : Z.of_nat (length path) <= 60.
Theorem src0_read_error : forall (E : env) ms model,
env_agree 10 (E_main sp inp tid rnd) E ->
st_ok src0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes src0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
Proof.
intros E ms model HEA HS HR Hh Hlz Hfd2. unfold runs_main in HR. rewrite Hargv in HR.
pose proof (stack_tail_end src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau) as STE. rewrite ?Hargv in STE.
unfold diag, wr, ex, ch_stderr. rewrite msg_read_error_eq.
pose proof (layout_facts src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau) as L. rewrite ?Hargv in L. pose proof (auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL. unfold SP_LO, SP_HI in L.
pose proof (z_argv_bounds src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as B1. rewrite ?Hargv in B1. cbn [nth] in B1.
pose proof (argv_no_nul src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hnul1. rewrite ?Hargv in Hnul1. cbn [nth] in Hnul1.
pose proof (argv_str_len src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hlen1. rewrite ?Hargv in Hlen1. cbn [nth] in Hlen1.
pose proof (ew0 src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd)) as H0.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H0. rewrite ?Hargv in H0.
pose proof (ew2' src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd) ltac:(rewrite ?Hargv; cbn; lia)) as H2.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H2. rewrite ?Hargv in H2.
pose proof (z_argv_fits src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as F1. rewrite ?Hargv in F1. cbn [nth] in F1. unfold SP_HI in F1.
rewrite <- (proj1 HEA 0%nat ltac:(lia)) in H0. rewrite <- (proj1 HEA 2%nat ltac:(lia)) in H2.
eapply rz_conseq; [| apply (shape_1 (strB "cli: read error on ") path nl)].
sym_run_to_with src0tbl_ok HS (symaddr Symbols.Plain.s_memchr).
fpf_memchr HS HR 2%nat 3%nat 2%nat 27%nat path.
sym_run_with src0tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 27%nat path.
sym_run3_with src0tbl_ok HS.
sym_add_fact HS 27%nat (mkAF 0 60 0). { atom_fact_lit. }
sym_run3_to_with src0tbl_ok HS (symaddr Symbols.Plain.s_memcpy).
fpf_split_window HS (-541).
fpf_memcpy_str HS HR HW 2%nat 27%nat 33%nat path (-541).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS true.
{ rewrite U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. apply negb_true_iff. apply Z.ltb_ge. lia. }
sym_run3_to_with src0tbl_ok HS (symaddr Symbols.Plain.s_memcpy).
fpf_memcpy_lit HS HR HW HK 27%nat 44%nat nl rodata_nl2_src1 (-541).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src0tbl_ok HS.
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
src0_exit_tac HS.
Qed.
End b.
Theorem src0_read_error_hyp : read_error_hyp.
Proof.
unfold read_error_hyp. intros sp inp mbase brk a0 path tid rnd E ms model Hargv Hsp Hva Hve Hvl Hlau Hfits Htid Hlen HEA HS HR Hh Hlz Hch.
exact (src0_read_error sp a0 path inp mbase brk tid rnd Hargv Hsp Hva Hve Hvl Hlau Hfits Hlen E ms model HEA HS HR Hh Hlz Hch).
Qed.
End a.
