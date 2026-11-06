(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0y.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL0y_cfw.v, with its module paths, module names and addresses changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YL0y_cfw.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; 3 image values moved to fuzz_transport's binaries by symbol and offset (provenance/evidence/kit-relocation/values.tsv); module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YP0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO05 YO00.
From OSSVerify.libdiginet.fuzz_transport.images Require Import Ubsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YN3v YH00 YH01 YH03 YN3e YN35 YN3f YN3g YN34 YN3i YN3b YL0v YL0k YL0p.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0d YH02 YL0y YK15_cfw YP03_cfw YN35_cfw SymTac_cfw YL0v_cfw YL0p_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable sp : word.
Variable argv envp : list (list byte).
Variable tid : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfits : entry_stack_fits sp argv envp.
Hypothesis Hargc : (length argv <> 2)%nat.
Theorem src0_usage_cf : forall ms model,
st_ok src0segs (E_main sp argv envp tid rnd) (add_cond ss_main_f (mkAC BC_NE (SOff 3 0) (SLit 2))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main false sp argv envp rnd) ->
m_halted model = None -> m_vm_lazy model = [] -> fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) model ->
crealizes src0_msyms (mkCfg ms model) (diag (msg_usage (nth 0 argv [])) (m_fs model)).
Proof using Hsp Hva Hve Hfits Hargc.
intros ms model HS HR Hh Hlz Hfd2.
unfold diag, wr, ex, ch_stderr. rewrite msg_usage_eq.
pose proof (argc_bounds argv Hva) as HA.
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. unfold SP_LO, SP_HI in L.
pose proof (z_argv_bounds sp argv envp 0 ltac:(lia)) as B0.
pose proof (argv_no_nul argv Hva 0 ltac:(lia)) as Hnul.
pose proof (argv_str_len argv Hva 0 ltac:(lia)) as Hlen0.
pose proof (ewm1 sp argv envp Hsp Hva Hve rnd tid) as H1.
pose proof (ew0 sp argv envp (xw_main sp argv envp tid rnd) (xd_main rnd)) as H0.
change (E0 _ _ _ _ _) with (E_main sp argv envp tid rnd) in H0.
pose proof (ew3 sp argv envp Hva (xw_main sp argv envp tid rnd) (xd_main rnd)) as H3.
change (E0 _ _ _ _ _) with (E_main sp argv envp tid rnd) in H3.
pose proof (z_argv_fits sp argv envp Hfits 0 ltac:(lia)) as F0. unfold SP_HI in F0.
sym_norm HS.
csym_run_to_with src0tbl_ok HS 0x20a48.
cfpf_memchr HS HR 1%nat 2%nat 1%nat 10%nat (nth 0 argv []).
csym_run_with src0tbl_ok HS.
cfpf_lbu_nul HS HR 1%nat 1%nat 10%nat (nth 0 argv []).
csym_run3_with src0tbl_ok HS.
destruct (Z_lt_le_dec 73 (Z.of_nat (length (nth 0 argv [])))) as [HL3|HL12].
{
eapply crz_conseq; [| apply (shape_3 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
sym_add_fact HS 10%nat (mkAF 74 131071 0). { atom_fact_lit. }
csym_run3_with src0tbl_ok HS.
cwl_writev2 HS Hfd2 16%nat.
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
csym_run3_with src0tbl_ok HS.
cwl_writev2 HS Hfd2 27%nat.
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
csrc0_exit_tac HS. }
sym_add_fact HS 10%nat (mkAF 0 73 0). { atom_fact_lit. }
csym_run3_to_with src0tbl_ok HS 0x20440.
fpf_split_window HS (-553).
cfpf_memcpy_str HS HR HW 1%nat 10%nat 16%nat (nth 0 argv []) (-553).
csym_run3_with src0tbl_ok HS.
csym_branch_with src0tbl_ok HS.
{
assert (HL1 : Z.of_nat (length (nth 0 argv [])) <= 66).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [discriminate| intros _; lia]. }
clear Hc.
eapply crz_conseq; [| apply (shape_1 (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl))].
csym_run3_to_with src0tbl_ok HS 0x20440.
cfpf_memcpy_lit HS HR HW HK 10%nat 27%nat (strB " INPUT" ++ nl) rodata_input_src1 (-553).
csym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
csym_run3_with src0tbl_ok HS.
cwl_writev2 HS Hfd2 38%nat.
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
csrc0_exit_tac HS. }
{
assert (HL2 : 67 <= Z.of_nat (length (nth 0 argv []))).
{ revert Hc. rewrite branch_geu_U, U_neg_off, U_SLit by (evalE; unfold M64; lia). evalE.
change (zcanon 7) with 7. destruct (Z.ltb_spec (- (Z.of_nat (length (nth 0 argv [])) + -73)) 7); [intros _; lia| discriminate]. }
clear Hc.
rewrite (app_assoc (strB "usage: ") (nth 0 argv []) (strB " INPUT" ++ nl)).
csym_run3_with src0tbl_ok HS.
sym_assume_with3 src0tbl_ok HS false.
{ rewrite U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE. apply Z.eqb_neq. lia. }
csym_run3_with src0tbl_ok HS.
cwl_writev2 HS Hfd2 27%nat.
{ rewrite iovcnt_val, U_add_off_atom, !U_off by (evalE; unfold M64; lia). evalE.
rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
{ rewrite U_SLit, !U_off by (evalE; unfold M64; lia). change (zcanon 7) with 7. lia. }
{ rdn_buf HS HK. }
{ rdn_rodata HS rodata_input_src1. }
{ rewrite U_SLit, U_off by (evalE; unfold M64; lia). evalE. change (zcanon 7) with 7. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_off by (evalE; unfold M64; lia). evalE. lia. }
{ rewrite !U_SLit. change (zcanon 66265) with 66265. change (zcanon 7) with 7. lia. }
{ rewrite !U_SLit. change (zcanon 66265) with 66265. change (zcanon 7) with 7. evalE. lia. }
csym_run3_with src0tbl_ok HS.
cwl_writev0 HS Hfd2.
csrc0_exit_tac HS. }
Qed.
End c.
Theorem src0_usage_hyp_cf : usage_hyp_cf.
Proof using.
unfold usage_hyp_cf. intros sp argv envp tid rnd ms model Hsp Hva Hve Hfits Hargc HS HR Hh Hlz Hch.
exact (src0_usage_cf sp argv envp tid rnd Hsp Hva Hve Hfits Hargc ms model HS HR Hh Hlz Hch).
Qed.
End b.
