(* ___errno_location (0x90a7c) on fuzz_link.asan: the SRr contract of lib/A/Rt/RtErrnoLoc.v, read off the released
   walk of the same 12 bytes (lib/A/Prog/__errno_location.v __errno_location_holds, plugin-hostd/fuzz_command's
   lib/A/Prog walk at link's address; its contract lib/A/Prog/__errno_location_c.v is stated with lib/Lib `evt` over
   A/Img0.rsegs, the machine state with its registers written out as mkR).
   The walk is read at the call site by A/Rt/RtBzLift.v srr_of_canon (the register map moved by
   lib/Lib/RegisterBridge.v, each lib/Lib step a step of the A machine); the return configuration is
   RtBzLift.unrestrict_ret; the memory after the call is the call site's memory (the walk writes none: munrestrict of
   mrestrict); AR of it under the materialized model is the AR frame law al_frame (YG0d.v:446), with nothing changed.
   `link_errno_location_closed` discharges `AR_laws tfibsegs B` by the kit's law proof (Reusable/YG0q.v
   AR_laws_ok), as A/Rt/RtClosed.v does; it needs no per-binary record. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtBzLift RtErrnoLoc.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.__errno_location_c.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.__errno_location.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Module ElRg := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Regs6ss.
Module ElC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.__errno_location_c.
Module ElP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.__errno_location.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem link_errno_location : forall B, AR_laws tfibsegs B -> aerrno_location_realizes tfibsegs B 0x90a7c.
Proof.
intros B LAWS ly S W regs mem md HAR Hra.
pose proof ElP.__errno_location_holds as HC. unfold ElC.__errno_location_contract in HC.
eapply (srr_of_canon W 0x90a7c regs mem md).
{ unfold canon_at, ElRg.mkR_of. apply HC. }
intros ms0 ms' model' HQ Heqv Hsbm _. cbv beta in HQ.
pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _).
assert (M0 : ms_mem ms0 = mrestrict (w_H W) mem) by (rewrite HQ; reflexivity).
assert (MEM : forall x, munrestrict (w_H W) mem (ms_mem ms') x = mem x).
{ intros x. rewrite <- Emem, M0. unfold munrestrict, mrestrict. destruct (w_H W x); reflexivity. }
assert (P0 : ms_pc_val ms0 = LMS.ret_pc (getr regs 1)) by (rewrite HQ; reflexivity).
assert (F0 : ms_fregs ms0 = fp_regs) by (rewrite HQ; reflexivity).
assert (S0 : ms_svc_pending ms0 = None) by (rewrite HQ; reflexivity).
assert (R0 : ms_resv ms0 = None) by (rewrite HQ; reflexivity).
assert (C0 : ms_fcsr ms0 = fp_csr) by (rewrite HQ; reflexivity).
assert (RO0 : ms_rom ms0 = seg_rom tfibsegs) by (rewrite HQ; reflexivity).
split; [reflexivity|].
exists (ms_regs ms'), (munrestrict (w_H W) mem (ms_mem ms')), model'.
split; [unfold cfg_at; f_equal; exact (unrestrict_ret regs (w_H W) mem ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0)|].
split.
{ destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
  apply (al_frame _ _ LAWS ly S W mem md _ model' HAR).
  - intros a _ _. apply aview_same. apply MEM.
  - intros a Hv. rewrite (aview_same (w_H W) mem (munrestrict (w_H W) mem (ms_mem ms')) a (MEM _)). exact Hv.
  - exact E1.
  - exact E2.
  - exact E3.
  - intros a _ _. apply MEM. }
split; [exact Hsbm|].
split.
{ rewrite (ms_eqv_getr ms0 ms' _ Heqv), HQ. reflexivity. }
split; [|exact MEM].
intros r Hr Hn. rewrite (ms_eqv_getr ms0 ms' _ Heqv), HQ.
assert (Hr' : r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 11 \/ r = 12 \/
              r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/ r = 31) by lia.
clear Hr Hn.
repeat (destruct Hr' as [Hr'|Hr']; [subst r; vm_compute; reflexivity|]).
subst r; vm_compute; reflexivity.
Qed.

Theorem link_errno_location_closed : forall B, aerrno_location_realizes tfibsegs B 0x90a7c.
Proof. intros B. exact (link_errno_location B (YG0q.AR_laws_ok tfibsegs B)). Qed.

(* The premise a caller supplies besides its own AR invariant, at link's six call sites: ra is the `jal 0x90a7c`'s pc
   + 4 (fuzz_socket 0x82204, fuzz_send 0x822f8, fuzz_recv 0x825ec, nl_talk 0x88c20 / 0x88c40 / 0x88c60), an even
   address, which `ret` leaves unchanged. *)
Lemma link_errno_location_sites_ret_ok :
Forall (fun a => YK0s.ret_ok (w64 a)) [0x82208; 0x822fc; 0x825f0; 0x88c24; 0x88c44; 0x88c64].
Proof. repeat constructor; apply YK0s.ret_ok_even; vm_compute; reflexivity. Qed.

End c.

About link_errno_location_closed.
Print Assumptions link_errno_location_closed.
