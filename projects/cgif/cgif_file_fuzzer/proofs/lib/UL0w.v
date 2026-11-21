(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN): changed sp, envp, Hsp, Hva, Hve, ubs0_open_failed, ubs0_cannot_open_hyp; added inp, Hargv, Hvl, Hlau, Hvi, efn; removed Hfits. *)
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
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v UH00 UH01 UH03 UN3e UN35 UN3f UN3g UN34 UN3i UN3b UL0v UL0k UL0p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = strB "cli: cannot open " ++ p ++ nl.
Proof using. intros p. unfold msg_cannot_open. vm_compute. reflexivity. Qed.
Definition errno_fact : afact := mkAF (2^64 - 4095) (2^64 - 1) 0.
Section b.
Variable sp brk mbase : word.
Variable inp : ProcInput.
Variable a0 path : list byte.
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
(* The layout facts are now stated over [in_argv inp] rather than over a free [argv]
   (YP08.v:494), so the two-element argv this section is about arrives as an EQUATION and
   the facts below are rewritten with it. *)
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
(* [entry_stack_fits] REPLACED by the premises UN3e's Section f takes (UN3e.v:189-194). *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem ubs0_open_failed : forall regs mem model (e : Z),
0 < e < 4096 ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
regs_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_regs ss_open) regs ->
mem_ok ubs0segs (E_main sp inp [a0; path] envp efn tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] envp efn) ->
realizes ubs0segs
(mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom ubs0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Proof using Hargv Hlau Hsp Hva Hve Hvi Hvl.
intros regs mem model e He Hh Hlz Hfd2 Hregs Hmem HG HR.
unfold diag, wr, ex, ch_stderr. rewrite msg_cannot_open_eq.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
(* [YP08.layout_facts]'s fourth conjunct is now [z_rand + 16 <= z_strs] (YP08.v:757) and no
   longer [< 2^63]; conjuncts 6 and 7 carry it on to [ztop <= SP_HI], and [SP_HI] is
   0x800000000000 = 2^47 (YP08.v:311), so the [unfold] below still hands [lia] a literal
   power-of-two ceiling for every atom in this proof. *)
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi) as L.
(* [UL0v.bsb_over_read]'s ceiling premise is discharged against the end of the tail ([STE]). *)
pose proof (STE inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi) as STE0.
(* [AUXV_BYTES] of the run's flag is an atom to [lia]; its range bounds the strings from below. *)
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi 1 ltac:(lia)) as B1.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi 1 ltac:(lia)) as Hnul1.
assert (Hlen1 : Z.of_nat (length (nth 1 (in_argv inp) [])) <= 131071)
by (eapply YP08.argv_str_len; first [eassumption | lia]).
assert (H0 : bv_unsigned (ew (E_main sp inp [a0; path] envp efn tid rnd) 0) = bv_unsigned sp)
by reflexivity.
assert (H2 : bv_unsigned (ew (E_main sp inp (in_argv inp) envp efn tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1)
by (unfold E_main; eapply YP08.ew2'; first [eassumption | lia]).
assert (F1 : z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1
+ Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 <= SP_HI - 9)
by (eapply YP08.z_argv_fits; first [eassumption | lia]).
rewrite Hargv in L, B1, Hnul1, Hlen1, H2, F1, STE0.
cbn [nth] in B1, Hnul1, Hlen1, F1.
unfold SP_LO, SP_HI in L. unfold SP_HI in F1.
assert (Hue : bv_unsigned (errno_ret e) = 2^64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z.mod_add _ 1) by lia. replace (- e + 1 * 2 ^ 64) with (2 ^ 64 - e) by lia. apply Z.mod_small. lia. }
pose proof (st_ok_resume_atom ubs0segs 10 errno_fact _ ss_open regs mem (errno_ret e) Hregs Hmem HG
ltac:(vm_compute; reflexivity)
ltac:(cbn [af_lo af_hi errno_fact]; rewrite Hue; lia)
ltac:(cbn [af_al2 errno_fact]; lia)
ltac:(cbn [af_al2 errno_fact]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS.
sym_norm HS.
assert (H9 : bv_unsigned (ew (ewset (E_main sp inp [a0; path] envp efn tid rnd) 10 (errno_ret e)) 10) = 2^64 - e)
by (rewrite ew_ewset_same; exact Hue).
sym_run3_with ubs0tbl_ok HS.
sym_assume_with3 ubs0tbl_ok HS false.
{ rewrite U_sextw_high by (rewrite U_off by (evalE; unfold M64; lia); evalE; unfold M64; lia).
rewrite U_off by (evalE; unfold M64; lia). rewrite U_SLit. evalE.
change (zcanon 18446744073709547521) with 18446744073709547521. apply Z.ltb_ge. lia. }
sym_run_to_with ubs0tbl_ok HS 0x1e1c8.
fpf_memchr HS HR 2%nat 3%nat 2%nat 11%nat path.
sym_run_with ubs0tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 11%nat path.
sym_run3_with ubs0tbl_ok HS.
destruct (Z_lt_le_dec 63 (Z.of_nat (length path))) as [HL3|HL12].
{
eapply rz_conseq; [| apply (shape_3 (strB "cli: cannot open ") path nl)].
sym_add_fact HS 11%nat (mkAF 64 131071 0). { atom_fact_lit. }
sym_run3_with ubs0tbl_ok HS.
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
sym_run3_with ubs0tbl_ok HS.
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
ubs0_exit_tac HS. }
sym_add_fact HS 11%nat (mkAF 0 63 0). { atom_fact_lit. }
sym_run3_to_with ubs0tbl_ok HS 0x1dadc.
fpf_split_window HS (-543).
fpf_memcpy_str HS HR HW 2%nat 11%nat 17%nat path (-543).
sym_run3_with ubs0tbl_ok HS.
sym_branch_with ubs0tbl_ok HS.
{
assert (HL1 : Z.of_nat (length path) <= 62).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [discriminate| intros _; lia]. }
clear Hc.
eapply rz_conseq; [| apply (shape_1 (strB "cli: cannot open ") path nl)].
sym_run3_to_with ubs0tbl_ok HS 0x1dadc.
fpf_memcpy_lit HS HR HW HK 11%nat 28%nat nl rodata_nl_src1 (-543).
sym_run3_with ubs0tbl_ok HS.
sym_assume_with3 ubs0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs0tbl_ok HS.
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
ubs0_exit_tac HS. }
{
assert (HL2 : 63 <= Z.of_nat (length path)).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "cli: cannot open ") path nl).
sym_run3_with ubs0tbl_ok HS.
sym_assume_with3 ubs0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with ubs0tbl_ok HS.
wl_writev2 HS Hfd2 28%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 1) with 1. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_nl_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66383) with 66383. change (zcanon 1) with 1. lia. }
{ rewrite !U_SLit. change (zcanon 66383) with 66383. change (zcanon 1) with 1. evalE. lia. }
sym_run3_with ubs0tbl_ok HS.
wl_writev0 HS Hfd2.
ubs0_exit_tac HS. }
Qed.
End b.
Theorem ubs0_cannot_open_hyp : cannot_open_hyp.
Proof using.
unfold cannot_open_hyp. intros sp brk mbase inp a0 path tid rnd regs mem model e Hsp Hargv Hva Hve Hvl Hlau Hvi Htid Hregs Hmem HG HR Hh Hlz Hch He.
exact (ubs0_open_failed sp brk mbase inp a0 path tid rnd Hsp Hargv Hva Hve Hvl Hlau Hvi regs mem model e He Hh Hlz Hch Hregs Hmem HG HR).
Qed.
End a.
