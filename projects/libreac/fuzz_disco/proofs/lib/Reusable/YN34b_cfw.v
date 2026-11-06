(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YN34.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN34b_cfw.v, with its module paths changed; 2 of its 77 lines of code are new or changed and 2 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO00 YN3v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YH00 YN35 YN3f YN3g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO0d YH02 YN34 YK15_cfw YN34_cfw YN35_cfw.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem crealizes_writev_msg_by_run : forall E ss ms model ch k msg s2 fd T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
wx_msg_check k ss msg = Some (s2, fd) ->
fdchan (Z_to_bv 64 fd) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s2 ms' -> frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
skeleton (ss_mem s2) = skeleton (ss_mem ss) -> mem_atoms_lt k (ss_mem s2) = true ->
crealizes src0_msyms (mkCfg ms' model) T) ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) msg) T).
Proof using.
intros E ss ms model ch k msg s2 fd T HS Hh Hlz Hck Hch Hk. unfold wx_msg_check in Hck.
destruct (wx_step k ss) as [[[[s1 s2'] zs] fd']|] eqn:Hwx; [|discriminate].
destruct (zlist_eqb zs (map bv_unsigned msg)) eqn:Heq; [|discriminate].
injection Hck as <- <-. apply zlist_eqb_eq in Heq. subst zs.
rewrite <- (map_Z_to_bv8_unsigned msg).
eapply crealizes_stdio_writev_by_run; eauto.
Qed.
Theorem crealizes_diag_exit_by_run : forall E ss ms model ch k msg code fd,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] -> 0 <= code < 256 ->
diag_exit_check k ss msg code = Some fd ->
fdchan (Z_to_bv 64 fd) ch model ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs model))).
Proof using.
intros E ss ms model ch k msg code fd HS Hh Hlz Hcode Hck Hch. unfold diag_exit_check in Hck.
destruct (wx_msg_check k ss msg) as [[s2 fd']|] eqn:Hwx; [|discriminate].
destruct (exit_run_check src0segs src0tbl s2 code) eqn:Hex; [|discriminate]. injection Hck as <-.
eapply crealizes_writev_msg_by_run; eauto.
intros ms' ws HS' _ _ _. eapply (src0_exit_cf (havoc E k ws)); eauto.
Qed.
End e.
Ltac csrc0_diag_exit_tac HS Hch k :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- crealizes _ _ (t_emit (map _ ?msg) (t_exit (Z_to_bv 64 ?code) _)) =>
let r := eval vm_compute in (diag_exit_check k ss msg code) in
lazymatch r with
| Some _ =>
apply (crealizes_diag_exit_by_run E ss ms model ch k msg code fd HS);
[ assumption | assumption | lia | vm_compute; reflexivity | exact Hch ]
| None => fail "csrc0_diag_exit_tac: diag_exit_check failed (inspect wx_step / exit_run_check on this state)"
end
end end end.
Ltac csrc0_fwrite_tac HS Hch k :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- crealizes _ _ (t_emit (map _ ?msg) _) =>
let r := eval vm_compute in (wx_msg_check k ss msg) in
lazymatch r with
| Some (?s2, _) =>
let Hck := fresh "Hck" in
assert (Hck : wx_msg_check k ss msg = Some (s2, fd)) by (vm_compute; reflexivity);
apply (crealizes_writev_msg_by_run E ss ms model ch k msg s2 fd _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in let HF := fresh "HF" in
let Hsk := fresh "Hsk" in let Hma := fresh "Hma" in
intros ms' ws HS HF Hsk Hma;
sym_transport src0segs E ss s2 ms' HS HF; try clear Hsk Hma
| None => fail "csrc0_fwrite_tac: wx_msg_check failed on this state"
end
end end end.
