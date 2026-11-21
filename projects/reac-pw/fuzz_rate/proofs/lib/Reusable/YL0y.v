(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0y.v, with its module paths, addresses and numbers changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack change of cgif/cgif_file_fuzzer's copy, keeping this unit's ProcInput-owned environment/run APIs, nullary ss_main_f, positional YP08 prefix, module paths and binary addresses; the auxiliary vector sized by the run's CONFIG_RSEQ flag; the launch's ProcInput, mmap base and entry draw; binary addresses; the launch's string area with the exec file name). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO05 YO00.
From OSSVerify.reac_pw.fuzz_rate.images Require Import Plain.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Lemma msg_usage_eq : forall a, msg_usage a = strB "usage: " ++ a ++ strB " INPUT" ++ nl.
Proof. intros a. unfold msg_usage. vm_compute. reflexivity. Qed.
Section c.
Variable sp brk mbase : word.
Variable inp : ProcInput.
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
(* [entry_stack_fits] no longer determines the stack image.  These are the launch
   premises of donor YL0p; the local layout wrappers do not take [Hvi]. *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis Hargc : (length (in_argv inp) <> 2)%nat.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem src0_usage : forall ms model,
st_ok src0segs (E_main sp inp tid rnd) (add_cond ss_main_f (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
realizes src0segs (mkCfg ms model) (diag (msg_usage (nth 0 argv [])) (m_fs model)).
Proof using Hargc Hlau Hsp Hva Hve Hvi Hvl.
intros ms model HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_usage_eq.
pose proof (proj1 Hva) as HA.
(* [YP08.layout_facts] lost [z_rand zsp av ev + 16 < 2^63] and gained
   [z_rand zsp rs av ev + 16 <= z_strs ztop av ev efn] (YP08.v:757).  The 2^63 bound is NOT
   lost to the [lia]s below: conjuncts 4, 6 and 7 chain
   [z_rand + 16 <= z_strs <= ztop <= SP_HI], and [SP_HI] is 0x800000000000 = 2^47
   (YP08.v:311), which the [unfold] on the next line puts in front of [lia] as a literal. *)
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as L. unfold SP_LO, SP_HI in L.
(* Donor YL0v.v:305-307 discharges the over-read ceiling from [STE] with [LF]/[ZAB]. *)
pose proof (STE inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as Htail.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 0 ltac:(lia)) as B0.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 0 ltac:(lia)) as Hnul.
assert (Hlen0 : Z.of_nat (length (nth 0 argv [])) <= 131071)
by (exact (YP08.argv_str_len src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 0 ltac:(lia))).
pose proof (ewm1 inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau tid) as H1.
assert (H0 : bv_unsigned (ew (E_main sp inp tid rnd) 0) = bv_unsigned sp) by reflexivity.
assert (H3 : bv_unsigned (ew (E_main sp inp tid rnd) 3) = Z.of_nat (length argv))
by (exact (YP08.ew3 src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd))).
assert (F0 : z_argv (bv_unsigned (ed_top rnd)) argv envp efn 0
+ Z.of_nat (length (nth 0 argv [])) + 1 <= SP_HI - 9)
by (exact (YP08.z_argv_fits src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 0 ltac:(lia))).
unfold SP_HI in F0.
sym_norm HS.
sym_run_to_with src0tbl_ok HS 0x1d434.
fpf_memchr HS HR 1%nat 2%nat 1%nat 10%nat (nth 0 argv []).
sym_run_with src0tbl_ok HS.
fpf_lbu_nul HS HR 1%nat 1%nat 10%nat (nth 0 argv []).
sym_run3_with src0tbl_ok HS.
destruct (Z_lt_le_dec 73 (Z.of_nat (length (nth 0 argv [])))) as [HL3|HL12].
{
eapply rz_conseq; [| apply (shape_3 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
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
sym_run3_to_with src0tbl_ok HS 0x1ce2c.
fpf_split_window HS (-553).
fpf_memcpy_str HS HR HW 1%nat 10%nat 16%nat (nth 0 argv []) (-553).
sym_run3_with src0tbl_ok HS.
sym_branch_with src0tbl_ok HS.
{
assert (HL1 : Z.of_nat (length (nth 0 argv [])) <= 66).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [discriminate| intros _; lia]. }
clear Hc.
eapply rz_conseq; [| apply (shape_1 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_run3_to_with src0tbl_ok HS 0x1ce2c.
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
{ rewrite !U_SLit. change (zcanon 66379) with 66379. change (zcanon 7) with 7. lia. }
{ rewrite !U_SLit. change (zcanon 66379) with 66379. change (zcanon 7) with 7. evalE. lia. }
sym_run3_with src0tbl_ok HS.
wl_writev0 HS Hfd2.
src0_exit_tac HS. }
Qed.
End c.
Theorem src0_usage_hyp : usage_hyp.
Proof.
unfold usage_hyp. intros sp brk mbase tid rnd inp ms model Hsp Hva Hve Hvl Hlau Hvi Hargc HS HR Hh Hlz Hch.
exact (src0_usage sp brk mbase inp tid rnd Hsp Hva Hve Hvl Hlau Hvi Hargc ms model HS HR Hh Hlz Hch).
Qed.
End b.
