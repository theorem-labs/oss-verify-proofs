(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: hex addresses and numbers for the binaries of libtasn1/asn1_get_length_der_fuzzer, and module names. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the open-failure arm is stated over the run, with the launch premises and the flag-free open state. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YQ0k.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP07 YP00.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YO3v YH04 YH05 YH07 YO3p YO3k YO3q YO3r YO3j YO3t YO3m YL0q YL0g YL0l.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = strB "cli: cannot open " ++ p ++ nl.
Proof. intros p. unfold msg_cannot_open. vm_compute. reflexivity. Qed.
Definition errno_fact : afact := mkAF (2^64 - 4095) (2^64 - 1) 0.
Section b.
Variables (sp brk mbase : word) (inp : ProcInput) (a0 path : list byte) (tid : word) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Theorem src2_open_failed : forall regs mem model (e : Z),
0 < e < 4096 ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
regs_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_regs ss_open_c) regs ->
mem_ok src2segs (E_main sp inp [a0; path] envp efn tid rnd) mem (ss_mem ss_open_c) ->
facts_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_facts ss_open_c) ->
runs_at (bv_unsigned sp) mem (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes src2segs
(mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open_c)) 4) mem (seg_rom src2segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Proof.
intros regs mem model e He Hh Hlz Hfd2 Hregs Hmem HG HR.
unfold diag, wr, ex, ch_stderr. rewrite msg_cannot_open_eq.
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
assert (Hue : bv_unsigned (errno_ret e) = 2^64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z.mod_add _ 1) by lia. replace (- e + 1 * 2 ^ 64) with (2 ^ 64 - e) by lia. apply Z.mod_small. lia. }
pose proof (st_ok_resume_atom src2segs 10 errno_fact _ ss_open_c regs mem (errno_ret e) Hregs Hmem HG
ltac:(vm_compute; reflexivity)
ltac:(cbn [af_lo af_hi errno_fact]; rewrite Hue; lia)
ltac:(cbn [af_al2 errno_fact]; lia)
ltac:(cbn [af_al2 errno_fact]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS.
sym_norm HS.
assert (H9 : bv_unsigned (ew (ewset (E_main sp inp [a0; path] envp efn tid rnd) 10 (errno_ret e)) 10) = 2^64 - e)
by (rewrite ew_ewset_same; exact Hue).
sym_run3_with src2tbl_ok HS.
sym_assume_with3 src2tbl_ok HS false.
{ rewrite U_sextw_high by (rewrite U_off by (evalE; unfold M64; lia); evalE; unfold M64; lia).
rewrite U_off by (evalE; unfold M64; lia). rewrite U_SLit. evalE.
change (zcanon 18446744073709547521) with 18446744073709547521. apply Z.ltb_ge. lia. }
sym_run_to_with src2tbl_ok HS 0x1a91c.
fpf_memchr HS HR 2%nat 3%nat 2%nat 11%nat path.
sym_run_with src2tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 11%nat path.
sym_run3_with src2tbl_ok HS.
destruct (Z_lt_le_dec 63 (Z.of_nat (length path))) as [HL3|HL12].
{
eapply rz_conseq; [| apply (shape_3 (strB "cli: cannot open ") path nl)].
sym_add_fact HS 11%nat (mkAF 64 131071 0). { atom_fact_lit. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 17%nat.
{ rewrite iovcnt_val, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). evalE. change (zcanon 17) with 17. lia. }
{ rdn_lits HS 0%nat. }
{ rdn_run HR 2%nat. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 17) with 17. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 17) with 17. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 17) with 17. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 28%nat.
{ rewrite iovcnt_val, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite !U_SLit. reflexivity. }
{ rdn_lits HS 0%nat. }
{ reflexivity. }
{ rewrite !U_SLit. change (zcanon 1) with 1. change (zcanon 0) with 0. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. evalE. lia. }
src2_exit_tac HS. }
sym_add_fact HS 11%nat (mkAF 0 63 0). { atom_fact_lit. }
sym_run3_to_with src2tbl_ok HS 0x1a3dc.
fpf_split_window HS (-543).
fpf_memcpy_str HS HR HW 2%nat 11%nat 17%nat path (-543).
sym_run3_with src2tbl_ok HS.
sym_branch_with src2tbl_ok HS.
{
assert (HL1 : Z.of_nat (length path) <= 62).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [discriminate| intros _; lia]. }
clear Hc.
eapply rz_conseq; [| apply (shape_1 (strB "cli: cannot open ") path nl)].
sym_run3_to_with src2tbl_ok HS 0x1a3dc.
fpf_memcpy_lit HS HR HW HK 11%nat 28%nat nl rodata_nl_src1 (-543).
sym_run3_with src2tbl_ok HS.
sym_assume_with3 src2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 39%nat.
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
src2_exit_tac HS. }
{
assert (HL2 : 63 <= Z.of_nat (length path)).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "cli: cannot open ") path nl).
sym_run3_with src2tbl_ok HS.
sym_assume_with3 src2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 28%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 1) with 1. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_nl_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66365) with 66365. change (zcanon 1) with 1. lia. }
{ rewrite !U_SLit. change (zcanon 66365) with 66365. change (zcanon 1) with 1. evalE. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev0 HS Hfd2.
src2_exit_tac HS. }
Qed.
End b.
Theorem src2_cannot_open_hyp : cannot_open_hyp.
Proof.
unfold cannot_open_hyp. intros sp brk mbase inp a0 path tid rnd regs mem model e Hsp Hargv Hva Hve Hvl Hlau Htid Hregs Hmem HG HR Hh Hlz Hch He.
eapply src2_open_failed; eassumption.
Qed.
End a.
