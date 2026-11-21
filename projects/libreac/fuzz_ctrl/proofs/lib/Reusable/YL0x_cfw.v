(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0x.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0x_cfw.v, with its module paths and addresses changed; 3 of its 90 lines of code are new or changed and 3 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed src0_read_error_cf, src0_read_error_hyp_cf; added envp, efn). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO05 YO00.
From OSSVerify.libreac.fuzz_ctrl.images Require Import Plain.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0d YH02 YL0x YK15_cfw YP03_cfw YN35_cfw SymTac_cfw YL0v_cfw YL0p_cfw.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable sp brk mbase : word.
Variable inp : ProcInput.
Variable a0 path : list byte.
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hlen60 : Z.of_nat (length path) <= 60.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Theorem src0_read_error_cf : forall (E : env) ms model,
env_agree 10 (E_main sp inp tid rnd) E ->
st_ok src0segs E ss_rderr ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
crealizes src0_msyms (mkCfg ms model) (diag (msg_read_error path) (m_fs model)).
Proof using Hargv Hlau Hlen60 Hsp Hva Hve Hvl.
intros E ms model HEA HS HR Hh Hlz Hfd2.
unfold runs_main in HR; rewrite Hargv in HR.
unfold diag, wr, ex, ch_stderr. rewrite msg_read_error_eq.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as L.
pose proof (YP08.auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
pose proof (STE inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as Htail.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as B1.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as Hnul1.
assert (Hlen1 : Z.of_nat (length (nth 1 (in_argv inp) [])) <= 131071)
by (exact (YP08.argv_str_len src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
assert (H0 : bv_unsigned (ew (E_main sp inp tid rnd) 0) = bv_unsigned sp)
by reflexivity.
assert (H2 : bv_unsigned (ew (E_main sp inp tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1)
by (exact (YP08.ew2' src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd) Hal)).
assert (F1 : z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1
+ Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 <= SP_HI - 9)
by (exact (YP08.z_argv_fits src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
rewrite Hargv in L, Htail, B1, Hnul1, Hlen1, H2, F1.
cbn [nth] in B1, Hnul1, Hlen1, F1.
unfold SP_LO, SP_HI in L. unfold SP_HI in F1.
rewrite <- (proj1 HEA 0%nat ltac:(lia)) in H0. rewrite <- (proj1 HEA 2%nat ltac:(lia)) in H2.
eapply crz_conseq; [| apply (shape_1 (strB "cli: read error on ") path nl)].
csym_run_to_with src0tbl_ok HS 0x1d2dc.
cfpf_memchr HS HR 2%nat 3%nat 2%nat 27%nat path.
csym_run_with src0tbl_ok HS.
cfpf_lbu_nul HS HR 2%nat 2%nat 27%nat path.
csym_run3_with src0tbl_ok HS.
sym_add_fact HS 27%nat (mkAF 0 60 0). { atom_fact_lit. }
csym_run3_to_with src0tbl_ok HS 0x1d3d8.
fpf_split_window HS (-541).
cfpf_memcpy_str HS HR HW 2%nat 27%nat 33%nat path (-541).
csym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS true.
{ rewrite U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 1) with 1. apply negb_true_iff. apply Z.ltb_ge. lia. }
csym_run3_to_with src0tbl_ok HS 0x1d3d8.
cfpf_memcpy_lit HS HR HW HK 27%nat 44%nat nl rodata_nl2_src1 (-541).
csym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
csym_run3_with src0tbl_ok HS.
cwl_writev2 HS Hfd2 55%nat.
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
csrc0_exit_tac HS.
Qed.
End b.
Theorem src0_read_error_hyp_cf : read_error_hyp_cf.
Proof using.
unfold read_error_hyp_cf. intros sp brk mbase inp a0 path tid rnd E ms model Hsp Hargv Hva Hve Hvl Hlau Htid Hlen HEA HS HR Hh Hlz Hch.
exact (src0_read_error_cf sp brk mbase inp a0 path tid rnd Hsp Hargv Hva Hve Hvl Hlau Hlen E ms model HEA HS HR Hh Hlz Hch).
Qed.
End a.
