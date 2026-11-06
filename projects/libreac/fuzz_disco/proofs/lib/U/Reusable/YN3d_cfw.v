(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YN3d.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN3d_cfw.v, with its module paths changed; 2 of its 96 lines of code are new or changed and 2 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO00 YN3v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YH00 YN3e YN35 YN3f YN3g YN34.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0d YH02 YN3d YK15_cfw YP03_cfw YP0n_cfw YN34_cfw.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_sym_ioctl_winsz : forall E ss ms model fd ch T,
m_halted model = None -> m_vm_lazy model = [] -> st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17)) = 29 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
cmd32 (sv_denot E (sr_get (ss_regs ss) 11)) = TIOCGWINSZ ->
(forall ms', st_ok segs E (resume ss (SLit (2^64 - 25)) (ss_mem ss) (ss_facts ss)) ms' ->
ms_mem ms' = ms_mem ms -> crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using.
intros E ss ms model fd ch T Hh Hlz HS Hrv H17 H10 [Hlk _] H32 H11 Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hk.
eapply (crz_ioctl_winsz B regs _ mem (seg_rom segs) model fd _ T Hh Hlz).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- intros rd wr; discriminate.
- rewrite (Hregs 11%bv). exact H11.
- apply Hk; [|reflexivity].
replace (errno_ret ENOTTY) with (sv_denot E (SLit (2^64 - 25)))
by (apply bv_eq; vm_compute; reflexivity).
apply st_ok_resume_sv; auto.
Qed.
End b.
Theorem crealizes_printf0_by_run : forall E ss ms model ch k ret s5 zs T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
pf0_check k ss ret = Some (s5, zs) ->
fdchan (Z_to_bv 64 1) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s5 ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes src0_msyms (mkCfg ms' model) T) ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) zs)) T).
Proof using.
intros E ss ms model ch k ret s5 zs T HS Hh Hlz Hck Hch Hk. unfold pf0_check in Hck.
destruct (sym_runN src0segs src0tbl FUEL ss) as [s1 st] eqn:Hrun. destruct st; try discriminate.
destruct (ss_pc s1 =? IOCTL_PC) eqn:Hpc; [|discriminate]. cbn [negb] in Hck.
destruct (sr_get (ss_regs s1) 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p|]; try discriminate. do 5 (destruct p as [p|p|]; try discriminate).
destruct (sr_get (ss_regs s1) 10) as [a0| | | | | | | | | |] eqn:H10; try discriminate.
destruct a0 as [|p|]; try discriminate. destruct p; try discriminate.
destruct (sr_get (ss_regs s1) 11) as [a1| | | | | | | | | |] eqn:H11; try discriminate.
destruct a1 as [|p|]; try discriminate. do 15 (destruct p as [p|p|]; try discriminate).
destruct (ss_resv s1) eqn:Hrv; try discriminate.
set (s2 := resume s1 (SLit (2^64 - 25)) (ss_mem s1) (ss_facts s1)) in Hck.
destruct (wx_step k s2) as [[[[s3 s4] zs'] fd]|] eqn:Hwx; [|discriminate].
destruct fd as [|p|]; try discriminate. destruct p; try discriminate.
destruct (skeleton_eqb (skeleton (ss_mem ss)) (skeleton (ss_mem s3))) eqn:Hsk; [|discriminate].
apply skeleton_eqb_eq in Hsk.
destruct (sym_run_toN src0segs src0tbl FUEL ret s4) as [s5' st'] eqn:Hrun2. destruct st'; try discriminate.
destruct (ss_pc s5' =? ret); [|discriminate]. injection Hck as <- <-.
eapply (crz_run_ecall src0_msyms src0tbl src0tbl_ok FUEL E ss s1 ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF1.
eapply (crz_sym_ioctl_winsz src0_msyms E s1 ms1 model (Z_to_bv 64 1) ch _ Hh Hlz HS1 Hrv).
- rewrite H17. reflexivity.
- rewrite H10. reflexivity.
- exact Hch.
- reflexivity.
- rewrite H11. apply bv_eq. vm_compute. reflexivity.
- intros ms2 HS2 Hm2. fold s2 in HS2.
destruct (sym_run_sound src0segs src0tbl src0tbl_ok _ E ss s1 RS_ecall ms HS Hrun) as (_ & _ & _ & Hsk1 & _).
eapply (crealizes_stdio_writev_by_run E s2 ms2 model ch k s3 s4 zs' (Zpos xH) _ HS2 Hh Hlz Hwx Hch).
intros ms4 ws HS4 HF4 Hsk4 Hma4.
eapply (crz_run_to_running src0_msyms src0tbl src0tbl_ok FUEL ret (havoc E k ws) s4 s5' ms4 model _ Hh Hlz HS4 Hrun2).
intros ms5 HS5 HF5. apply (Hk ms5 ws HS5).
assert (Hsk2 : skeleton (ss_mem s2) = skeleton (ss_mem ss)) by (subst s2; cbn [resume ss_mem]; exact Hsk1).
apply (frame_of_trans E (ss_mem ss) (ss_mem s2) (ms_mem ms) (ms_mem ms2) (ms_mem ms5)).
+ symmetry. exact Hsk2.
+ rewrite Hm2. exact HF1.
+ apply (frame_of_trans E (ss_mem s2) (ss_mem s4) (ms_mem ms2) (ms_mem ms4) (ms_mem ms5)).
* rewrite Hsk4, Hsk2. reflexivity.
* exact HF4.
* eapply frame_of_agree; [apply env_agree_havoc | exact Hma4 | exact HF5].
Qed.
End a.
