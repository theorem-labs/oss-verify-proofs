(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN35.v, with its module paths and addresses changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SRC1_EXIT : Z := 0x15b38.
Definition SRC1_STDIO_WRITE : Z := 0x180c0.
Definition SRC1_CLOSE_STDOUT_RET : Z := 0x17f60.
Definition SRC1_STDOUT_FILE : Z := 0x1f868.
Section b.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Definition exit_run_check (ss : sstate) (code : Z) : bool :=
match sym_runN segs tbl FUEL ss with
| (ss', RS_ecall) =>
match sr_get (ss_regs ss') 17, sr_get (ss_regs ss') 10, ss_resv ss' with
| SLit no, SLit c, None => ((no =? 93) || (no =? 94)) && (c =? code)
| _, _, _ => false
end
| _ => false
end.
Theorem realizes_exit_by_run : forall E ss ms model code,
st_ok segs E ss ms ->
0 <= code < 256 ->
exit_run_check ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
realizes segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros E ss ms model code HS Hcode Hchk Hh Hlz. unfold exit_run_check in Hchk.
destruct (sym_runN segs tbl FUEL ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate.
destruct (sr_get (ss_regs ss') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct (sr_get (ss_regs ss') 10) as [c| | | | | | | | | |] eqn:H10; try discriminate.
destruct (ss_resv ss') eqn:Hrv; try discriminate.
apply andb_prop in Hchk as [Hno Hc]. apply Z.eqb_eq in Hc. subst c.
eapply (rz_run_ecall segs tbl tbl_ok FUEL E ss ss' ms model _ Hh Hlz HS Hrun).
intros ms' HS' _.
apply (rz_sym_exit segs E ss' ms' model code Hh Hlz HS' Hrv).
- rewrite H17. cbn [sv_denot]. apply orb_prop in Hno as [Hno|Hno]; apply Z.eqb_eq in Hno; subst no;
[left | right]; reflexivity.
- rewrite H10. reflexivity.
- exact Hcode.
Qed.
Definition run_to_check (stop : Z) (ss : sstate) : option sstate :=
match sym_run_toN segs tbl FUEL stop ss with
| (ss', RS_running) => if ss_pc ss' =? stop then Some ss' else None
| _ => None
end.
Theorem realizes_run_to : forall stop E ss ss1 ms model T,
st_ok segs E ss ms ->
run_to_check stop ss = Some ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
(forall ms1, st_ok segs E ss1 ms1 ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
realizes segs (mkCfg ms1 model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros stop E ss ss1 ms model T HS Hchk Hh Hlz K. unfold run_to_check in Hchk.
destruct (sym_run_toN segs tbl FUEL stop ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate.
destruct (ss_pc ss' =? stop); [|discriminate]. injection Hchk as ->.
exact (rz_run_to_running segs tbl tbl_ok FUEL stop E ss ss1 ms model T Hh Hlz HS Hrun K).
Qed.
End b.
Theorem src0_exit : forall E ss ms model code,
st_ok src0segs E ss ms ->
0 <= code < 256 ->
exit_run_check src0segs src0tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
realizes src0segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof. exact (realizes_exit_by_run src0segs src0tbl src0tbl_ok). Qed.
Theorem src0_exit_to_flush : forall E ss ss1 ms model T,
st_ok src0segs E ss ms ->
run_to_check src0segs src0tbl SRC1_STDIO_WRITE ss = Some ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
(forall ms1, st_ok src0segs E ss1 ms1 ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
realizes src0segs (mkCfg ms1 model) T) ->
realizes src0segs (mkCfg ms model) T.
Proof. exact (realizes_run_to src0segs src0tbl src0tbl_ok SRC1_STDIO_WRITE). Qed.
End a.
Ltac src0_exit_tac HS :=
first
[ lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (src0_exit E ss ms model code HS); [lia | vm_compute; reflexivity | assumption | assumption]
end end
| sym_run_with src0tbl_ok HS; sym_exit_with HS ].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
End d.
