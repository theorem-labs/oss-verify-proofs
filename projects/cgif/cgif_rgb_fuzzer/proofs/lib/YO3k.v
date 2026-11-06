(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition SRC1_EXIT : Z := 0x171d8.
Definition SRC1_STDIO_WRITE : Z := 0x19c58.
Definition SRC1_CLOSE_STDOUT_RET : Z := 0x1a178.
Definition SRC1_STDOUT_FILE : Z := 0x21ad8.
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

End b.
Theorem src2_exit : forall E ss ms model code,
st_ok src2segs E ss ms ->
0 <= code < 256 ->
exit_run_check src2segs src2tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
realizes src2segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof. exact (realizes_exit_by_run src2segs src2tbl src2tbl_ok). Qed.

End a.
Ltac src2_exit_tac HS :=
first
[ lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (src2_exit E ss ms model code HS); [lia | vm_compute; reflexivity | assumption | assumption]
end end
| sym_run_with src2tbl_ok HS; sym_exit_with HS ].
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
End d.
