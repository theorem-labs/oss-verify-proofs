(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from YL0y.v: src0_usage restated over BudgetWit.Rzb.rzb as src0_usage_b, with YL0y and the BudgetWit modules imported last; msg_usage_eq (used from YL0y) and src0_usage_hyp left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the system-call budget checks): changed sp, argv, Hva, Hve, Hargc, src0_usage_b; added inp, Hvl, Hlau, Hvi, envp, efn; removed Hfits. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO00.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.R Require Import Cfg.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL0y.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.BudgetWit Require Import Rzb RunB WritevF WritevG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(** * The driver's usage path (argc <> 2) over [BudgetWit.Rzb.rzb]

    [src0_usage_b] is [YL0y.src0_usage] with [realizes] written [rzb]: the same
    binders (YL0y's section [c]: the launch's input and entry, with the launch
    premises [valid_launch], [entry_launch_ok_va], [valid_input]) and the same proof
    script, with [rz_conseq] written [rzb_conseq].  The script's tactics
    ([sym_run_with], [sym_run3_with], [sym_run_to_with], [wl_writev2], [wl_writev0],
    [fpf_*], [src0_exit_tac], ...) resolve to the copies in [BudgetWit.RunB] and
    [BudgetWit.WritevG], which this file imports after the released modules; each
    copy is the released tactic over [rzb].  No node is built in this file, so no
    [budget_ok] argument appears here. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable sp brk mbase : word.
Variable inp : ProcInput.
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis Hargc : (length (in_argv inp) <> 2)%nat.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem src0_usage_b : forall ms model,
st_ok src0segs (E_main sp inp argv envp efn tid rnd) (add_cond (ss_canon false) (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main (kb_rseq (in_kernel inp)) false sp (ed_top rnd) argv envp efn) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
rzb src0segs (mkCfg ms model) (diag (msg_usage (nth 0 argv [])) (m_fs model)).
Proof.
intros ms model HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_usage_eq.
pose proof (proj1 Hva) as HA.
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi) as L. unfold SP_LO, SP_HI in L.
(* [YL0v.bsb_over_read]'s ceiling premise is discharged against the end of the tail ([STE]). *)
pose proof (STE inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi) as STE0.
(* [AUXV_BYTES] of the run's flag is an atom to [lia]; its range bounds the strings from below. *)
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi 0 ltac:(lia)) as B0.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi 0 ltac:(lia)) as Hnul.
assert (Hlen0 : Z.of_nat (length (nth 0 argv [])) <= 131071)
by (eapply YP08.argv_str_len; first [eassumption | lia]).
pose proof (ewm1 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi tid) as H1.
assert (H0 : bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 0) = bv_unsigned sp) by reflexivity.
assert (H3 : bv_unsigned (ew (E_main sp inp argv envp efn tid rnd) 3) = Z.of_nat (length argv))
by (unfold E_main; eapply YP08.ew3; eassumption).
assert (F0 : z_argv (bv_unsigned (ed_top rnd)) argv envp efn 0
+ Z.of_nat (length (nth 0 argv [])) + 1 <= SP_HI - 9)
by (eapply YP08.z_argv_fits; first [eassumption | lia]).
unfold SP_HI in F0.
sym_norm HS.
sym_run_to_with src0tbl_ok HS 0x1d8a4.
fpf_memchr HS HR 1%nat 2%nat 1%nat 10%nat (nth 0 argv []).
sym_run_with src0tbl_ok HS.
fpf_lbu_nul HS HR 1%nat 1%nat 10%nat (nth 0 argv []).
sym_run3_with src0tbl_ok HS.
destruct (Z_lt_le_dec 73 (Z.of_nat (length (nth 0 argv [])))) as [HL3|HL12].
{
eapply rzb_conseq; [| apply (shape_3 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_add_fact HS 10%nat (mkAF 74 131071 0). { atom_fact_lit. }
sym_run3_with src0tbl_ok HS.
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
sym_run3_with src0tbl_ok HS.
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
src0_exit_tac HS. }
sym_add_fact HS 10%nat (mkAF 0 73 0). { atom_fact_lit. }
sym_run3_to_with src0tbl_ok HS 0x1d1b8.
fpf_split_window HS (-553).
fpf_memcpy_str HS HR HW 1%nat 10%nat 16%nat (nth 0 argv []) (-553).
sym_run3_with src0tbl_ok HS.
sym_branch_with src0tbl_ok HS.
{
assert (HL1 : Z.of_nat (length (nth 0 argv [])) <= 66).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [discriminate| intros _; lia]. }
clear Hc.
eapply rzb_conseq; [| apply (shape_1 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_run3_to_with src0tbl_ok HS 0x1d1b8.
fpf_memcpy_lit HS HR HW HK 10%nat 27%nat (strB " INPUT" ++ nl) rodata_input_src1 (-553).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src0tbl_ok HS.
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
src0_exit_tac HS. }
{
assert (HL2 : 67 <= Z.of_nat (length (nth 0 argv []))).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl)).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src0tbl_ok HS.
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
sym_run3_with src0tbl_ok HS.
wl_writev0 HS Hfd2.
src0_exit_tac HS. }
Qed.
End c.
End b.
