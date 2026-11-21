(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from YL0t.v: src2_usage restated over BudgetWit.Rzb.rzb as src2_usage_b, with YL0t and the BudgetWit modules imported last; msg_usage_eq (used from YL0t) and src2_usage_hyp left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (src2_usage_b stated over the run's ProcInput, with the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits, the CONFIG_RSEQ-indexed main state with usage_cond, and the strings block anchored at the entry draw's top with the execfn string; YL05 imported). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP00.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YH04 YH05 YH07 YO3p YO3k YO3q YO3r YO3j YO3t YO3m YL0q YL0g YL0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YL05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YL0t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.BudgetWit Require Import Rzb RunB WritevF WritevG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(** * The driver's usage path (argc <> 2) over [BudgetWit.Rzb.rzb]

    [src2_usage_b] is [YL0t.src2_usage] with [realizes] written [rzb]: the same
    binders and the same proof script, with [rz_conseq] written [rzb_conseq].  The
    script's tactics ([sym_run_with], [sym_run3_with], [sym_run_to_with],
    [wl_writev2], [wl_writev0], [fpf_*], [src2_exit_tac], ...) resolve to the copies in
    [BudgetWit.RunB] and [BudgetWit.WritevG], which this file imports after the
    released modules; each copy is the released tactic over [rzb].  No node is built
    in this file, so no [budget_ok] argument appears here. *)
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variables (sp brk mbase tid : word) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hargc : (length (in_argv inp) <> 2)%nat.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Theorem src2_usage_b : forall ms model,
st_ok src2segs (E_main sp inp argv envp efn tid rnd) (add_cond (ss_main false (kb_rseq (in_kernel inp))) usage_cond) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp (ed_top rnd) argv envp efn rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
rzb src2segs (mkCfg ms model) (diag (msg_usage (nth 0 argv [])) (m_fs model)).
Proof.
intros ms model HS0 HR Hh Hlz Hfd2.
pose proof (st_ok_usage _ _ ms HS0) as HS. clear HS0.
unfold diag, wr, ex, ch_stderr. rewrite msg_usage_eq.
pose proof (argc_bounds inp Hva) as HA.
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. unfold SP_LO, SP_HI in L.
pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B0.
pose proof (argv_no_nul inp Hva 0 ltac:(lia)) as Hnul.
pose proof (argv_str_len inp Hva 0 ltac:(lia)) as Hlen0.
pose proof (ewm1 inp mbase sp brk rnd) as H1. lfeed H1. specialize (H1 tid).
assert (H0 : bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0) = bv_unsigned sp) by reflexivity.
assert (H3 : bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 3) = Z.of_nat (length argv)).
{ unfold E_main. eapply ew3; eassumption. }
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 0 ltac:(lia)) as F0. unfold SP_HI in F0.
sym_norm HS.
sym_run_to_with src2tbl_ok HS 0x1f468.
fpf_memchr HS HR 1%nat 2%nat 1%nat 10%nat (nth 0 argv []).
sym_run_with src2tbl_ok HS.
fpf_lbu_nul HS HR 1%nat 1%nat 10%nat (nth 0 argv []).
sym_run3_with src2tbl_ok HS.
destruct (Z_lt_le_dec 73 (Z.of_nat (length (nth 0 argv [])))) as [HL3|HL12].
{
eapply rzb_conseq; [| apply (shape_3 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_add_fact HS 10%nat (mkAF 74 131071 0). { atom_fact_lit. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 16%nat.
{ rewrite iovcnt_val, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rdn_lits HS 0%nat. }
{ rdn_run HR 1%nat. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 27%nat.
{ rewrite iovcnt_val, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite !U_SLit. reflexivity. }
{ rdn_lits HS 0%nat. }
{ reflexivity. }
{ rewrite !U_SLit. change (zcanon 7) with 7. change (zcanon 0) with 0. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. lia. }
{ rewrite !U_SLit. change (zcanon 0) with 0. evalE. lia. }
src2_exit_tac HS. }
sym_add_fact HS 10%nat (mkAF 0 73 0). { atom_fact_lit. }
sym_run3_to_with src2tbl_ok HS 0x1ed7c.
fpf_split_window HS (-553).
fpf_memcpy_str HS HR HW 1%nat 10%nat 16%nat (nth 0 argv []) (-553).
sym_run3_with src2tbl_ok HS.
sym_branch_with src2tbl_ok HS.
{
assert (HL1 : Z.of_nat (length (nth 0 argv [])) <= 66).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [discriminate| intros _; lia]. }
clear Hc.
eapply rzb_conseq; [| apply (shape_1 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_run3_to_with src2tbl_ok HS 0x1ed7c.
fpf_memcpy_lit HS HR HW HK 10%nat 27%nat (strB " INPUT" ++ nl) rodata_input_src1 (-553).
sym_run3_with src2tbl_ok HS.
sym_assume_with3 src2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 38%nat.
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
assert (HL2 : 67 <= Z.of_nat (length (nth 0 argv []))).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl)).
sym_run3_with src2tbl_ok HS.
sym_assume_with3 src2tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev2 HS Hfd2 27%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 7) with 7. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_input_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66268) with 66268. change (zcanon 7) with 7. lia. }
{ rewrite !U_SLit. change (zcanon 66268) with 66268. change (zcanon 7) with 7. evalE. lia. }
sym_run3_with src2tbl_ok HS.
wl_writev0 HS Hfd2.
src2_exit_tac HS. }
Qed.
End c.
End b.
