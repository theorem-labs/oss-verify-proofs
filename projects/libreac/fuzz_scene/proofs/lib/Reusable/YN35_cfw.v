(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN35.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN35.v; 29 of its 69 lines of code are new or changed and 62 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YH00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0d YH02 YN35 YK15_cfw YP03_cfw YP0n_cfw.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_sym_exit : forall E ss ms model (code : Z),
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
is_exit_no (sv_denot E (sr_get (ss_regs ss) 17)) ->
sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 code -> 0 <= code < 256 ->
crealizes B (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof using.
intros E ss ms model code Hh Hlz HS Hrv Hno Ha0 Hc.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
apply (crz_exit_small B).
- exact Hh.
- exact Hlz.
- rewrite (Hregs 17%bv). exact Hno.
- rewrite (Hregs 10%bv). exact Ha0.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small; lia.
Qed.

Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Theorem crealizes_exit_by_run : forall E ss ms model code,
st_ok segs E ss ms ->
0 <= code < 256 ->
exit_run_check segs tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
crealizes B (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof using tbl_ok.
intros E ss ms model code HS Hcode Hchk Hh Hlz. unfold exit_run_check in Hchk.
destruct (sym_runN segs tbl FUEL ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate.
destruct (sr_get (ss_regs ss') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct (sr_get (ss_regs ss') 10) as [c| | | | | | | | | |] eqn:H10; try discriminate.
destruct (ss_resv ss') eqn:Hrv; try discriminate.
apply andb_prop in Hchk as [Hno Hc]. apply Z.eqb_eq in Hc. subst c.
eapply (crz_run_ecall B tbl tbl_ok FUEL E ss ss' ms model _ Hh Hlz HS Hrun).
intros ms' HS' _.
apply (crz_sym_exit E ss' ms' model code Hh Hlz HS' Hrv).
- rewrite H17. cbn [sv_denot]. apply orb_prop in Hno as [Hno|Hno]; apply Z.eqb_eq in Hno; subst no;
[left | right]; reflexivity.
- rewrite H10. reflexivity.
- exact Hcode.
Qed.
End b.
Theorem src0_exit_cf : forall E ss ms model code,
st_ok src0segs E ss ms ->
0 <= code < 256 ->
exit_run_check src0segs src0tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
crealizes src0_msyms (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof using. exact (crealizes_exit_by_run src0_msyms src0tbl src0tbl_ok). Qed.
End a.
