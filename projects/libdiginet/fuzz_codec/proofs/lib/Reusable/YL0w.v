(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0w.v, with its module paths, addresses and numbers changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput and its premises; the top-anchored stack strings; the CONFIG_RSEQ auxv layout; the section variables its proofs use; addresses relocated). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO05 YO00.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Plain.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = strB "cli: cannot open " ++ p ++ nl.
Proof. intros p. unfold msg_cannot_open. vm_compute. reflexivity. Qed.
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
(* The launch premises follow donor YL0p; the local layout wrappers do not take [Hvi]. *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem src0_open_failed : forall regs mem model (e : Z),
0 < e < 4096 ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
realizes src0segs
(mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) model)
(diag (msg_cannot_open path) (m_fs model)).
Proof using Hargv Hlau Hsp Hva Hve Hvi Hvl.
intros regs mem model e He Hh Hlz Hfd2 Hregs Hmem HG HR.
unfold runs_main in HR; rewrite Hargv in HR.
unfold diag, wr, ex, ch_stderr. rewrite msg_cannot_open_eq.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
(* [YP08.layout_facts]'s fourth conjunct is now [z_rand + 16 <= z_strs] (YP08.v:757) and no
   longer [< 2^63]; conjuncts 6 and 7 carry it on to [ztop <= SP_HI], and [SP_HI] is
   0x800000000000 = 2^47 (YP08.v:311), so the [unfold] below still hands [lia] a literal
   power-of-two ceiling for every atom in this proof. *)
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as L.
(* Donor YL0v.v:305-307 discharges the over-read ceiling from [STE] with [LF]/[ZAB]. *)
pose proof (STE inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as Htail.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as B1.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as Hnul1.
assert (Hlen1 : Z.of_nat (length (nth 1 (in_argv inp) [])) <= 131071)
by (exact (YP08.argv_str_len src0segs Plain.M.phdrs inp mbase Plain.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
assert (H0 : bv_unsigned (ew (E_main sp inp tid rnd) 0) = bv_unsigned sp)
by reflexivity.
assert (H2 : bv_unsigned (ew (E_main sp inp tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1)
by (exact (YP08.ew2' src0segs Plain.M.phdrs inp mbase Plain.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd) Hal)).
assert (F1 : z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1
+ Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 <= SP_HI - 9)
by (exact (YP08.z_argv_fits src0segs Plain.M.phdrs inp mbase Plain.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
rewrite Hargv in L, Htail, B1, Hnul1, Hlen1, H2, F1.
cbn [nth] in B1, Hnul1, Hlen1, F1.
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
unfold SP_LO, SP_HI in L. unfold SP_HI in F1.
assert (Hue : bv_unsigned (errno_ret e) = 2^64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z.mod_add _ 1) by lia. replace (- e + 1 * 2 ^ 64) with (2 ^ 64 - e) by lia. apply Z.mod_small. lia. }
pose proof (st_ok_resume_atom src0segs 10 errno_fact _ ss_open regs mem (errno_ret e) Hregs Hmem HG
ltac:(vm_compute; reflexivity)
ltac:(cbn [af_lo af_hi errno_fact]; rewrite Hue; lia)
ltac:(cbn [af_al2 errno_fact]; lia)
ltac:(cbn [af_al2 errno_fact]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS.
sym_norm HS.
assert (H9 : bv_unsigned (ew (ewset (E_main sp inp tid rnd) 10 (errno_ret e)) 10) = 2^64 - e)
by (rewrite ew_ewset_same; exact Hue).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_sextw_high by (rewrite U_off by (evalE; unfold M64; lia); evalE; unfold M64; lia).
rewrite U_off by (evalE; unfold M64; lia). rewrite U_SLit. evalE.
change (zcanon 18446744073709547521) with 18446744073709547521. apply Z.ltb_ge. lia. }
sym_run_to_with src0tbl_ok HS 0x1dd40.
fpf_memchr HS HR 2%nat 3%nat 2%nat 11%nat path.
sym_run_with src0tbl_ok HS.
fpf_lbu_nul HS HR 2%nat 2%nat 11%nat path.
sym_run3_with src0tbl_ok HS.
destruct (Z_lt_le_dec 63 (Z.of_nat (length path))) as [HL3|HL12].
{
eapply rz_conseq; [| apply (shape_3 (strB "cli: cannot open ") path nl)].
sym_add_fact HS 11%nat (mkAF 64 131071 0). { atom_fact_lit. }
sym_run3_with src0tbl_ok HS.
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
sym_run3_with src0tbl_ok HS.
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
src0_exit_tac HS. }
sym_add_fact HS 11%nat (mkAF 0 63 0). { atom_fact_lit. }
sym_run3_to_with src0tbl_ok HS 0x1d7c8.
fpf_split_window HS (-543).
fpf_memcpy_str HS HR HW 2%nat 11%nat 17%nat path (-543).
sym_run3_with src0tbl_ok HS.
sym_branch_with src0tbl_ok HS.
{
assert (HL1 : Z.of_nat (length path) <= 62).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [discriminate| intros _; lia]. }
clear Hc.
eapply rz_conseq; [| apply (shape_1 (strB "cli: cannot open ") path nl)].
sym_run3_to_with src0tbl_ok HS 0x1d7c8.
fpf_memcpy_lit HS HR HW HK 11%nat 28%nat nl rodata_nl_src1 (-543).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src0tbl_ok HS.
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
src0_exit_tac HS. }
{
assert (HL2 : 63 <= Z.of_nat (length path)).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. destruct (Z.ltb_spec (- (Z.of_nat (length path) + -63)) 1); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "cli: cannot open ") path nl).
sym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
sym_run3_with src0tbl_ok HS.
wl_writev2 HS Hfd2 28%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 1) with 1. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_nl_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 1) with 1. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66493) with 66493. change (zcanon 1) with 1. lia. }
{ rewrite !U_SLit. change (zcanon 66493) with 66493. change (zcanon 1) with 1. evalE. lia. }
sym_run3_with src0tbl_ok HS.
wl_writev0 HS Hfd2.
src0_exit_tac HS. }
Qed.
End b.
Theorem src0_cannot_open_hyp : cannot_open_hyp.
Proof.
unfold cannot_open_hyp. intros sp brk mbase inp a0 path tid rnd regs mem model e Hsp Hargv Hva Hve Hvl Hlau Hvi Htid Hregs Hmem HG HR Hh Hlz Hch He.
exact (src0_open_failed sp brk mbase inp a0 path tid rnd Hsp Hargv Hva Hve Hvl Hlau Hvi regs mem model e He Hh Hlz Hch Hregs Hmem HG HR).
Qed.
End a.
