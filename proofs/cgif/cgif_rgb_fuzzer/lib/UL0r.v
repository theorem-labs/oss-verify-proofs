(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YQ0k.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP00.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v UH04 UH05 UH07 UO3p UO3k UO3q UO3r UO3j UO3t UO3m UL0q UL0g UL0l.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = strB "cli: cannot open " ++ p ++ nl.
Proof. intros p. unfold msg_cannot_open. vm_compute. reflexivity. Qed.
Definition errno_fact : afact := mkAF (2^64 - 4095) (2^64 - 1) 0.
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
Theorem ubs2_open_failed : forall regs mem model (e : Z),
0 < e < 4096 ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
regs_ok (E_main sp [a0; path] envp tid rnd) (ss_regs ss_open) regs ->
mem_ok ubs2segs (E_main sp [a0; path] envp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp [a0; path] envp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp [a0; path] envp rnd) ->
realizes ubs2segs
(mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom ubs2segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Proof.
intros regs mem model e He Hh Hlz Hfd2 Hregs Hmem HG HR.
unfold diag, wr, ex, ch_stderr. rewrite msg_cannot_open_eq.
pose proof (layout_facts sp [a0; path] envp Hsp Hva Hve) as L. unfold SP_LO, SP_HI in L.
pose proof (z_argv_bounds sp [a0; path] envp 1 ltac:(cbn; lia)) as B1. cbn [nth] in B1.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
pose proof (argv_str_len [a0; path] Hva 1 ltac:(cbn; lia)) as Hlen1. cbn [nth] in Hlen1.
pose proof (ew0 sp [a0; path] envp (xw_main sp [a0; path] envp tid rnd) (xd_main rnd)) as H0.
change (E0 _ _ _ _ _) with (E_main sp [a0; path] envp tid rnd) in H0.
pose proof (ew2' sp [a0; path] envp Hsp Hva Hve (xw_main sp [a0; path] envp tid rnd) (xd_main rnd) ltac:(cbn; lia)) as H2.
change (E0 _ _ _ _ _) with (E_main sp [a0; path] envp tid rnd) in H2.
pose proof (z_argv_fits sp [a0; path] envp Hfits 1 ltac:(cbn; lia)) as F1. cbn [nth] in F1. unfold SP_HI in F1.
assert (Hue : bv_unsigned (errno_ret e) = 2^64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z.mod_add _ 1) by lia. replace (- e + 1 * 2 ^ 64) with (2 ^ 64 - e) by lia. apply Z.mod_small. lia. }
pose proof (st_ok_resume_atom ubs2segs 10 errno_fact _ ss_open regs mem (errno_ret e) Hregs Hmem HG
ltac:(vm_compute; reflexivity)
ltac:(cbn [af_lo af_hi errno_fact]; rewrite Hue; lia)
ltac:(cbn [af_al2 errno_fact]; lia)
ltac:(cbn [af_al2 errno_fact]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS.
sym_norm HS.
assert (H9 : bv_unsigned (ew (ewset (E_main sp [a0; path] envp tid rnd) 10 (errno_ret e)) 10) = 2^64 - e)
by (rewrite ew_ewset_same; exact Hue).
sym_run3_with ubs2tbl_ok HS.
sym_assume_with3 ubs2tbl_ok HS false.
{ rewrite U_sextw_high by (rewrite U_off by (evalE; unfold M64; lia); evalE; unfold M64; lia).
rewrite U_off by (evalE; unfold M64; lia). rewrite U_SLit. evalE.
change (zcanon 18446744073709547521) with 18446744073709547521. apply Z.ltb_ge. lia. }
sym_run_to_with ubs2tbl_ok HS 0x207b8.
fpf_memchr HS HR 2%nat 3%nat 2%nat 11%nat path.
sym_run_with ubs2tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 11%nat path.
sym_run3_with ubs2tbl_ok HS.
destruct (Z_lt_le_dec 63 (Z.of_nat (length path))) as [HL3|HL12].
{
eapply rz_conseq; [| apply (shape_3 (strB "cli: cannot open ") path nl)].
sym_add_fact HS 11%nat (mkAF 64 131071 0). { atom_fact_lit. }
sym_run3_with ubs2tbl_ok HS.
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
sym_run3_with ubs2tbl_ok HS.
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
ubs2_exit_tac HS. }
sym_add_fact HS 11%nat (mkAF 0 63 0). { atom_fact_lit. }
sym_run3_to_with ubs2tbl_ok HS 0x200cc.
fpf_split_window HS (-543).
fpf_memcpy_str HS HR HW 2%nat 11%nat 17%nat path (-543).
sym_run3_with ubs2tbl_ok HS.
sym_branch_with ubs2tbl_ok HS.
{
assert (HL1 : Z.of_nat (length path) <= 62).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [discriminate| intros _; lia]. }
clear Hc.
eapply rz_conseq; [| apply (shape_1 (strB "cli: cannot open ") path nl)].
sym_run3_to_with ubs2tbl_ok HS 0x200cc.
fpf_memcpy_lit HS HR HW HK 11%nat 28%nat nl rodata_nl_src1 (-543).
sym_run3_with ubs2tbl_ok HS.
sym_assume_with3 ubs2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs2tbl_ok HS.
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
ubs2_exit_tac HS. }
{
assert (HL2 : 63 <= Z.of_nat (length path)).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "cli: cannot open ") path nl).
sym_run3_with ubs2tbl_ok HS.
sym_assume_with3 ubs2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs2tbl_ok HS.
wl_writev2 HS Hfd2 28%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 1) with 1. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_nl_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66370) with 66370. change (zcanon 1) with 1. lia. }
{ rewrite !U_SLit. change (zcanon 66370) with 66370. change (zcanon 1) with 1. evalE. lia. }
sym_run3_with ubs2tbl_ok HS.
wl_writev0 HS Hfd2.
ubs2_exit_tac HS. }
Qed.
End b.
Theorem ubs2_cannot_open_hyp : cannot_open_hyp.
Proof.
unfold cannot_open_hyp. intros sp a0 path envp tid rnd regs mem model e Hsp Hva Hve Hfits Htid Hregs Hmem HG HR Hh Hlz Hch He.
exact (ubs2_open_failed sp a0 path envp tid rnd Hsp Hva Hve Hfits regs mem model e He Hh Hlz Hch Hregs Hmem HG HR).
Qed.
End a.
