(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN): changed sp, envp, Hva, Hve, ubs0_read_error, ubs0_read_error_hyp; added inp, Hargv, Hvl, Hlau, Hvi, efn; removed Hfits. *)
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
Lemma msg_read_error_eq : forall p, msg_read_error p = strB "cli: read error on " ++ p ++ nl.
Proof using. intros p. unfold msg_read_error. vm_compute. reflexivity. Qed.
Section b.
Variable sp brk mbase : word.
Variable inp : ProcInput.
Variable a0 path : list byte.
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
(* The layout facts are stated over [in_argv inp] now (YP08.v:494), so the two-element argv
   arrives as an equation and the facts below are rewritten with it. *)
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
(* [entry_stack_fits] REPLACED by the premises UN3e's Section f takes (UN3e.v:189-194). *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis Hlen60 : Z.of_nat (length path) <= 60.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem ubs0_read_error : forall (E : env) ms model,
env_agree 10 (E_main sp inp [a0; path] envp efn tid rnd) E ->
st_ok ubs0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] envp efn) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes ubs0segs (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
Proof using Hargv Hlau Hlen60 Hsp Hva Hve Hvi Hvl.
intros E ms model HEA HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_read_error_eq.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
(* [layout_facts]'s dropped [< 2^63] conjunct is not needed: conjuncts 4, 6 and 7 chain
   [z_rand + 16 <= z_strs <= ztop <= SP_HI] and [SP_HI = 0x800000000000 = 2^47]
   (YP08.v:311), which the [unfold] below hands to [lia] as a literal. *)
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
unfold read_error_hyp. intros sp brk mbase inp a0 path tid rnd E ms model Hsp Hargv Hva Hve Hvl Hlau Hvi Htid Hlen HEA HS HR Hh Hlz Hch.
exact (ubs0_read_error sp brk mbase inp a0 path tid rnd Hsp Hargv Hva Hve Hvl Hlau Hvi Hlen E ms model HEA HS HR Hh Hlz Hch).
Qed.
End a.
