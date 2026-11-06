(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names and addresses changed; 1175 of its 1288 lines of code are new or changed and 1596 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F17b.v, with its module paths, module names, addresses and numbers changed; 510 of its 556 lines of code are new or changed and 1242 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R5.v blob ae88d9629939 at the glue base f32c86d5c0b9
   (a working branch).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: R5.v states NO run lemma (seg_R5 :444 steps its run inline with Tac_slot.sl_run, :508-583), so there is
   no R5.<r> of evt type for a constr_eq pin. INSTEAD (a Theorem Labs lane, 04:1xZ): seg_R5_of_F below re-derives R5.v's own
   seg_R5 from r5_evt_F at ExecF.RNG_all (R5.v's proof, with the inline evt replaced by r5_evt_of_F), and
   seg_R5_of_F_verbatim checks by constr_eq that its type IS R5.seg_R5's type, term for term. That derivation
   replaces the pin: it shows r5_evt_F carries everything the source segment proof takes from its run.
   Written by a Theorem Labs lane, in a NEW file of the Seg family (no file of the Seg family's _F writer is
   edited); a Theorem Labs lane's _F convention throughout. Mechanical re-run; input to the ported walk only.
   rule 24: no function proved (a segment run). *)

(* The footprint (ExecF.evtF) form of segment R5's run (0x81588 -> 0x815cc of LLVMFuzzerTestOneInput, 17
   instructions, no call, no branch): R5.v's inline run re-stepped with lib.Lib StepF under a universally quantified
   footprint RNG (first binder), with the premises the inline run uses (R5.v :502-507 and :574: s1 = A, s2 = mrow,
   0 <= A < 2^60, the save area writable, the spill [A + 128] = fr + 544) and its post predicate (R5.v :509-525)
   verbatim, the end state in the `exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ ..`
   shape sl_run takes. The ghost input g_in g of the source becomes the binder inp (the run reads only mrow inp).
   Its data accesses, one ExecF.rng premise per region (rows in R5Fs.rng.tsv):
     ExecF.rng RNG A 120          the six 8-byte stores into the spill block [A, A + 120): A + 8 (0x81590),
                                  A + 112 (0x81594), A (0x8159c), A + 104 (0x815b4), A + 96 (0x815bc), A + 64
                                  (0x815c4); the region of the run's own premise ULMem.wr_at rsegs mem A 120
     ExecF.rng RNG (A + 128) 8    the load ld a0,128(s1) (0x815c8), the cell of the premise q64 mem (A + 128) ..
   Instruction fetch is not an access. R5.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 53 of its code lines changed or removed, 53 added.
   R5.v's run is on the UL engine (lib/A/Tk/UL: UL Exec.evt, UL MState.MS, UL Mem's wa / le8 / wr_at); StepF steps
   lib.Lib's machine state. As Seg/A2F.v and Seg/F10F.v do: the twin states lib.Lib's MS (the same record by delta),
   its post names R5.v's own constants (ULMem.wa / ULMem.le8, Sem.reg_get, mrow), and r5F_evtF_evt carries lib.Lib's
   evt to the UL engine's for the corollary. The register map is expanded by r5F_mkR_of_expand (F10F.v's
   f10F_mkR_of_expand over the lib.Lib map), the stores' store_ok and the load's ov_read_bytes are R5.v's own facts
   (:540-581) restated over lib.Lib's wa, and the spill cell is carried across the six stores by R5.v's
   r5_q64_other.

   IMPORTS: R5.v's block, verbatim, then StepF last (its step / finish shadow the UL engine's), then, for the
   derivation, R5.v's block again so that every name of R5.v's proof (UL wa / le8 / evt / MS, R5.v's tactics
   r5_q / r5_out / r5_keep_cells) resolves as in R5.v.

   QUALIFIED NAMES (a Theorem Labs lane, for ctrlgate 4468e8a23a4a-49a5f33bf5c7's DUP gate): every short use of a
   twin-family name the gate reports (--all-uses) is written with the full path of the copy Locate binds at that
   point, with no change of meaning (Set Printing All + Print of every touched declaration byte-equal before and
   after).  Before the second import block: getr / seg_rom -> A.Reusable.YK11; wa / le8 / wr_at / wr_at_store_ok /
   wr_at_write / length_le8 / bytes_at_ov_read -> Lib.Mem; MS -> Lib.MState; step -> Lib.StepF; simp_regs ->
   Lib.Step; word_eq_tac -> Lib.ZBridge.  After it: getr / seg_rom / mkst -> A.Reusable.YK11; wa / le8 / wr_at /
   length_le8 -> A.Tk.UL.Mem; MState.MS -> A.Tk.UL.MState; evt -> A.Tk.UL.Exec.  Uses through this file's module
   aliases (UE, ULMem, LMS, LFr, LF, AC, AF: an alias path writes no .glob reference) are written with the absolute
   path of the module the alias names; the alias declarations themselves are kept. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot RcPro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R5.
(* Last but YK11: StepF's step / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11's getr / FPState / fp_regs / seg_rom (the names R5.v's statements use). *)
Import YK11.
Open Scope Z_scope.

Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module ULMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* ---- Engine glue (A2F.v's a2F_evtF_evt): lib.Lib's mstep and the UL engine's are the same relation (both
   `ms_svc_pending ms = None /\ RiscvSemantics.step rsegs ms = MachineOk ms'`), so a lib.Lib run is a UL run. ---- *)
Lemma r5F_evtF_evt : forall RNG (Q : machine_state -> Prop) ms,
  ExecF.evtF rsegs RNG Q ms -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.evt rsegs Q ms.
Proof.
  intros RNG Q ms H. destruct (ExecF.evtF_evt rsegs RNG Q ms H) as (ms' & Hs & HQ).
  exists ms'. split; [clear HQ H | exact HQ].
  induction Hs as [s|s s1 s2 Hs _ IH]; [apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.msteps_refl|].
  eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.msteps_cons; [exact Hs | exact IH].
Qed.

(* mkR_of regs as the explicit lib.Lib 31-slot register map StepF's simp_regs reads (F10F.v:88). *)
Lemma r5F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 1)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 5)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 6)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 7)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 10)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 11)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 12)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 13)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 14)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 15)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 16)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 17)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 25)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 27)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 28)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 29)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 30)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F10F.v's f10F_subst_slot: rewrite a register slot of the expanded map with an `rg` fact. *)
Ltac r5F_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* The spill cell across a chain of 8-byte stores (R5.v's r5_q over the lib.Lib store terms StepF leaves): each
   store is missed, by R5.v's r5_q64_other. *)
Ltac r5F_q :=
  repeat lazymatch goal with
  | |- q64 (write_to_mem ?m (Z_to_bv 64 ?a) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 ?w)) ?c ?v =>
      refine (R5.r5_q64_other m a w c v _ ltac:(lia) ltac:(lia) ltac:(lia))
  end.

(* R5.v's r5_regeq / r5_wlit over the lib.Lib register map. *)
Ltac r5F_regeq :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs;
  first [ reflexivity
        | match goal with H : rg _ _ _ |- _ => symmetry; exact H end
        | OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ZBridge.word_eq_tac
        | apply bv_eq; vm_compute; reflexivity ].
Ltac r5F_wlit :=
  first [ exact eq_refl | OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ZBridge.word_eq_tac
        | apply bv_eq; vm_compute; reflexivity ].

Section S.
Context {fx : FPState}.

(* ---- R5.v's inline run (seg_R5 :508-583) under a footprint. ---- *)
Lemma r5_evt_F : forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (A fr : Z)
    (inp : list byte),
  rg regs 9 A -> rg regs 18 (mrow inp) -> 0 <= A < 2 ^ 60 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at rsegs mem A 120 -> q64 mem (A + 128) (fr + 544) ->
  ExecF.rng RNG A 120 -> ExecF.rng RNG (A + 128) 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R fp_regs pc' fp_csr None mem'
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x815cc /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\
       Sem.reg_get R 4 = Sem.reg_get regs 4 /\ Sem.reg_get R 8 = Sem.reg_get regs 8 /\
       Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 25 = Sem.reg_get regs 25 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\
       Sem.reg_get R 23 = Z_to_bv 64 0 /\ Sem.reg_get R 24 = Z_to_bv 64 36 /\
       Sem.reg_get R 10 = Z_to_bv 64 (fr + 544) /\
       (exists w16 w112 w8 w104 w96 w64 : word,
          mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w16))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa A)
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 64))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w64) /\
          w104 = Z_to_bv 64 0x21140 /\ w96 = Z_to_bv 64 0x1234 /\ w64 = Z_to_bv 64 0xe38f0000 /\
          w112 = Sem.reg_get regs 18 /\
          w16 = Z_to_bv 64 (mrow inp + 16) /\ w8 = Z_to_bv 64 (mrow inp + 20)))
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81588) fp_csr None mem
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros RNG regs mem A fr inp Hr9 Hr18 HAr HwrU H128 RA R128.
  assert (Hwr : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at rsegs mem A 120) by exact HwrU. clear HwrU.
  pose proof (R5.r5_mrow_rng inp) as Hmr.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  rewrite r5F_mkR_of_expand.
  r5F_subst_slot Hr9. r5F_subst_slot Hr18.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x81588 li s7,0 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x8158c addi a0,s2,16 *)
  assert (HS16 : store_ok rsegs mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 8)) 8 = true).
  { apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs mem A 120 8 8 Hwr); lia. }
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x81590 sd a0,8(s1) *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m1 _) =>
    assert (HS112 : store_ok rsegs m1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 112)) 8 = true) by
      (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs m1 A 120 112 8);
       [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_write; exact Hwr | lia | lia]) end.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x81594 sd s2,112(s1) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x81598 addi s2,s2,20 *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m2 _) =>
    assert (HS8 : store_ok rsegs m2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa A) 8 = true) by
      (pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs m2 A 120 0 8
                     ltac:(repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_write; exact Hwr)
                     ltac:(lia) ltac:(lia)) as HS0;
       rewrite Z.add_0_r in HS0; exact HS0) end.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x8159c sd s2,0(s1) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815a0 auipc a0,0xfffa0 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815a4 lui a1,0x1 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815a8 lui a2,0xe38f *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815ac li s8,36 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815b0 addi a0,a0,-1064 *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m3 _) =>
    assert (HS104 : store_ok rsegs m3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 104)) 8 = true) by
      (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs m3 A 120 104 8);
       [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_write; exact Hwr | lia | lia]) end.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815b4 sd a0,104(s1) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815b8 addiw a0,a1,564 *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m4 _) =>
    assert (HS96 : store_ok rsegs m4 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 96)) 8 = true) by
      (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs m4 A 120 96 8);
       [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_write; exact Hwr | lia | lia]) end.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815bc sd a0,96(s1) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815c0 slli a2,a2,0x4 *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m5 _) =>
    assert (HS64 : store_ok rsegs m5 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 64)) 8 = true) by
      (apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_store_ok rsegs m5 A 120 64 8);
       [repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wr_at_write; exact Hwr | lia | lia]) end.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815c4 sd a2,64(s1) *)
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m6 _) =>
    assert (HB6 : q64 m6 (A + 128) (fr + 544)) by (r5F_q; exact H128) end.
  match goal with |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ _ _ _ ?m6 _) =>
    assert (HR128 : ov_read_bytes rsegs m6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A + 128)) 8 =
                    Some (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 544)))) end.
  { pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 (Z_to_bv 64 (fr + 544))) as L8.
    pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_ov_read rsegs _ (A + 128)
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 544))) 0 8 HB6
                  ltac:(lia)) as H.
    rewrite Z.add_0_r, skipn_O in H.
    rewrite firstn_all2 in H by lia. exact H. }
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x815c8 ld a0,128(s1) *)
  apply ExecF.evtF_done. hnf. do 3 eexists. split; [reflexivity|].
  split; [reflexivity|].
  do 13 (split; [r5F_regeq|]).
  do 6 eexists. split; [reflexivity|].
  split; [r5F_wlit|]. split; [r5F_wlit|]. split; [r5F_wlit|].
  split; [symmetry; exact Hr18|].
  split; reflexivity.
Qed.

End S.

(* ---- Back to R5.v's name context for the derivation: R5.v's import block again, in R5.v's order, after StepF
   (so the UL engine's evt / MS / wa / le8 / length_le8 and R5.v's tactics resolve as in R5.v). ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot RcPro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R5.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.

(* ---- The inline run's own form (the UL Exec.evt sl_run takes at R5.v:508-525, with g_in g := inp), from
   r5_evt_F at ExecF.RNG_all; each rng premise from A's bound. ---- *)
Section O.
Context {fx : YK11.FPState}.

Lemma r5_evt_of_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr : Z) (inp : list byte),
  rg regs 9 A -> rg regs 18 (mrow inp) -> 0 <= A < 2 ^ 60 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at rsegs mem A 120 -> q64 mem (A + 128) (fr + 544) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.evt rsegs
    (fun ms => exists R pc' mem',
       ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS R fp_regs pc' fp_csr None mem'
              (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x815cc /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\
       Sem.reg_get R 4 = Sem.reg_get regs 4 /\ Sem.reg_get R 8 = Sem.reg_get regs 8 /\
       Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 25 = Sem.reg_get regs 25 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\
       Sem.reg_get R 23 = Z_to_bv 64 0 /\ Sem.reg_get R 24 = Z_to_bv 64 36 /\
       Sem.reg_get R 10 = Z_to_bv 64 (fr + 544) /\
       (exists w16 w112 w8 w104 w96 w64 : word,
          mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w16))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa A)
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 64))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w64) /\
          w104 = Z_to_bv 64 0x21140 /\ w96 = Z_to_bv 64 0x1234 /\ w64 = Z_to_bv 64 0xe38f0000 /\
          w112 = Sem.reg_get regs 18 /\
          w16 = Z_to_bv 64 (mrow inp + 16) /\ w8 = Z_to_bv 64 (mrow inp + 20)))
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81588)
       fp_csr None mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem A fr inp Hr9 Hr18 HAr Hwr H128.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  apply (r5F_evtF_evt ExecF.RNG_all).
  apply (r5_evt_F ExecF.RNG_all regs mem A fr inp Hr9 Hr18 HAr Hwr H128); apply ExecF.rng_all; lia.
Qed.

End O.

(* ---- R5.v's seg_R5, re-derived: R5.v's Section R5 shape and R5.v's proof (:445-748), with the inline run
   (:527-588) replaced by r5_evt_of_F (that is, by r5_evt_F at ExecF.RNG_all). R5.v's Section-local lemmas
   r5_fra_store / r5_ent_store are cited at this Section's variables (local definitions of the same names, so
   R5.v's script reads unchanged). ---- *)
Section R5D.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.AsanAllocAPI
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* R5.v's r5_keep_cells (R5.v:432-442), verbatim: R5.v defines it inside its Section R5, so it does not survive
   that Section's End and is restated here (a frame cell the six stores miss: the frame lies below A). *)
Ltac r5_keep_cells Hc :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  destruct Hc as (k & Hk); exists k;
  lazymatch type of Hk with
  | _ _ ?m _ _ =>
      match goal with
      | MU : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch ?W m ?m',
        WM : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono _ m ?m' |- _ =>
          apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport rsegs W m m' _ _ Hk MU WM)
      end
  end;
  cbn; repeat split; lia.

Lemma seg_R5_of_F : Hat B APIf ra (Inv_A815cc_at B APIf ra) 0%nat -> Hcut B APIf ra (Inv_A81588 B APIf ra).
Proof.
  pose (r5_fra_store := @R5.r5_fra_store LS rc B APIf SH SK ra empty FF).
  pose (r5_ent_store := @R5.r5_ent_store fx rc B APIf SH SK ra).
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HCUR & HOUR & HOUT & HID & HFG &
    (A1 & H9a & H128) & HPRO & H21 & (A3 & H9c & H152) & (A4 & H9d & H144) & (A5 & H9e & H208) &
    Hidr & Hjnk & (A6 & H9f & H280) & (A7 & H9g & H240) & Hjy & Hscr &
    (A8 & H9h & H48) & (A9 & H9i & H56) & (A10 & H9j & H88) & (A11 & H9k & H80) & (A12 & H9l & H72) &
    (A13 & H9m & H192) & (A14 & H9n & H216) & Hfg72 & Hid38 & H18).
  destruct HPRO as ((P1 & H9o & H40) & (P2 & H9p & H120) & (P3 & H9q & H136) & (P4 & H9r & H160) &
    (P5 & H9s & H168) & (P6 & H9t & H176) & (P7 & H9u & H200) & (P8 & H9v & H248) & Hour6 & Hinb & Hinl &
    (P9 & H9w & H184) & (P10 & H9x & H256) & (P11 & H9y & H264) & (P12 & H9z & H272) & (P13 & H9z2 & H32)).
  subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.a_laws_stack_high _ _ _ _ _
                (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.aa_laws
                   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH)
    as Hhigh.
  assert (HSS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP60 : 2 ^ 60 = 1152921504606846976) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh. unfold APPMEM_END in HAPP.
  assert (HAr : 0 <= A < 2 ^ 60) by lia.
  assert (EA1 : A1 = A) by exact (r5_spill_base regs mem A A1 128 (fr + 544) Hr9 H9a H128 HAr ltac:(lia)).
  assert (EP1 : P1 = A) by exact (r5_spill_base regs mem A P1 40 _ Hr9 H9o H40 HAr ltac:(lia)).
  assert (EP2 : P2 = A) by exact (r5_spill_base regs mem A P2 120 _ Hr9 H9p H120 HAr ltac:(lia)).
  assert (EP3 : P3 = A) by exact (r5_spill_base regs mem A P3 136 _ Hr9 H9q H136 HAr ltac:(lia)).
  assert (EP4 : P4 = A) by exact (r5_spill_base regs mem A P4 160 _ Hr9 H9r H160 HAr ltac:(lia)).
  assert (EP5 : P5 = A) by exact (r5_spill_base regs mem A P5 168 _ Hr9 H9s H168 HAr ltac:(lia)).
  assert (EP6 : P6 = A) by exact (r5_spill_base regs mem A P6 176 _ Hr9 H9t H176 HAr ltac:(lia)).
  assert (EP7 : P7 = A) by exact (r5_spill_base regs mem A P7 208 _ Hr9 H9u H200 HAr ltac:(lia)).
  assert (EP8 : P8 = A) by exact (r5_spill_base regs mem A P8 248 _ Hr9 H9v H248 HAr ltac:(lia)).
  assert (EP9 : P9 = A) by exact (r5_spill_base regs mem A P9 184 _ Hr9 H9w H184 HAr ltac:(lia)).
  assert (EP10 : P10 = A) by exact (r5_spill_base regs mem A P10 256 _ Hr9 H9x H256 HAr ltac:(lia)).
  assert (EP11 : P11 = A) by exact (r5_spill_base regs mem A P11 264 _ Hr9 H9y H264 HAr ltac:(lia)).
  assert (EP12 : P12 = A) by exact (r5_spill_base regs mem A P12 272 _ Hr9 H9z H272 HAr ltac:(lia)).
  assert (EP13 : P13 = A) by exact (r5_spill_base regs mem A P13 32 _ Hr9 H9z2 H32 HAr ltac:(lia)).
  subst P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13.
  clear H9o H9p H9q H9r H9s H9t H9u H9v H9w H9x H9y H9z H9z2.
  assert (EA3 : A3 = A) by exact (r5_spill_base regs mem A A3 152 (Sfr fr + 68) Hr9 H9c H152 HAr ltac:(lia)).
  assert (EA4 : A4 = A) by exact (r5_spill_base regs mem A A4 144 (fr + 2688) Hr9 H9d H144 HAr ltac:(lia)).
  assert (EA5 : A5 = A) by exact (r5_spill_base regs mem A A5 192 (fr + 2768) Hr9 H9e H208 HAr ltac:(lia)).
  assert (EA6 : A6 = A) by exact (r5_spill_base regs mem A A6 280 (fr + 3040) Hr9 H9f H280 HAr ltac:(lia)).
  assert (EA7 : A7 = A) by exact (r5_spill_base regs mem A A7 240 (fr + 3056) Hr9 H9g H240 HAr ltac:(lia)).
  assert (EA8 : A8 = A) by exact (r5_spill_base regs mem A A8 48 _ Hr9 H9h H48 HAr ltac:(lia)).
  assert (EA9 : A9 = A) by exact (r5_spill_base regs mem A A9 56 _ Hr9 H9i H56 HAr ltac:(lia)).
  assert (EA10 : A10 = A) by exact (r5_spill_base regs mem A A10 88 _ Hr9 H9j H88 HAr ltac:(lia)).
  assert (EA11 : A11 = A) by exact (r5_spill_base regs mem A A11 80 _ Hr9 H9k H80 HAr ltac:(lia)).
  assert (EA12 : A12 = A) by exact (r5_spill_base regs mem A A12 72 _ Hr9 H9l H72 HAr ltac:(lia)).
  assert (EA13 : A13 = A) by exact (r5_spill_base regs mem A A13 200 _ Hr9 H9m H192 HAr ltac:(lia)).
  assert (EA14 : A14 = A) by exact (r5_spill_base regs mem A A14 216 _ Hr9 H9n H216 HAr ltac:(lia)).
  subst A1 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14.
  clear H9a H9c H9d H9e H9f H9g H9h H9i H9j H9k H9l H9m H9n.
  (* s2 = mrow, stored at 0x81594 into [A + 112] (the loop head's row spill) *)
  assert (E112 : Sem.reg_get regs 18 = Z_to_bv 64 (mrow (g_in g))).
  { unfold rg in H18. rewrite <- H18. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr.
    cbn [bv_eqb negb]. reflexivity. }
  (* The stores' window [A, A + 120) is inside the entry-anchored slot window, so writable. *)
  assert (Hwr : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at rsegs mem A 120).
  { pose proof Hwin as (Hw0 & Hw1 & Hwv). split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hwv (A + i) ltac:(lia))). }
  eapply (sl_run regs (Z_to_bv 64 0x81588) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x815cc /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\
       Sem.reg_get R 4 = Sem.reg_get regs 4 /\ Sem.reg_get R 8 = Sem.reg_get regs 8 /\
       Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 25 = Sem.reg_get regs 25 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\
       Sem.reg_get R 23 = Z_to_bv 64 0 /\ Sem.reg_get R 24 = Z_to_bv 64 36 /\
       Sem.reg_get R 10 = Z_to_bv 64 (fr + 544) /\
       (exists w16 w112 w8 w104 w96 w64 : word,
          mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w16))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w112))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa A)
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w8))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w104))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w96))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A + 64))
                   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 w64) /\
          w104 = Z_to_bv 64 0x21140 /\ w96 = Z_to_bv 64 0x1234 /\ w64 = Z_to_bv 64 0xe38f0000 /\
          w112 = Sem.reg_get regs 18 /\
          w16 = Z_to_bv 64 (mrow (g_in g) + 16) /\ w8 = Z_to_bv 64 (mrow (g_in g) + 20)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run 0x81588 .. 0x815c8: r5_evt_F at ExecF.RNG_all, in the inline run's own form *)
    exact (r5_evt_of_F regs mem A fr (g_in g) Hr9 H18 HAr Hwr H128).
  - intros R pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E22 & E25 & E21 & E23 & E24 & E10 & Hmem) Hreg Hmat.
    subst pc'.
    destruct Hmem as (w16 & w112 & w8 & w104 & w96 & w64 & -> & -> & -> & -> & -> & -> & ->).
    assert (G2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 2 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 3 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G4 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 4 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G8 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 8 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 9 =
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G19 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 19 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G26 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 26 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G22 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 22 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G25 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 25 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 25)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G23 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 23 = Z_to_bv 64 0)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G21 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 21 =
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G24 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 24 = Z_to_bv 64 36)
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    assert (G10 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs' 10 = Z_to_bv 64 (fr + 544))
      by ((etransitivity; [apply Hreg|]); unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr;
          cbn [bv_eqb negb]; eassumption).
    match goal with |- SR _ (mkCfg (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkst _ _ ?m6 _) _) _ =>
      assert (HFRA6 : FRA B APIf ra g fr [] regs m6 md);
      [| assert (MU : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch [(A, A + 120)] mem m6)] end.
    { apply (r5_fra_store g fr [] regs _ md A 64 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 96 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
      apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia]. }
    { apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_write;
      [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch_refl | | | ] | | | ] | | | ] | | | ]
        | | | ] | | | ];
        try (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8);
        try (cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.inside]; left);
        lia. }
    match goal with |- SR _ (mkCfg (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkst _ _ ?m6 _) _) _ =>
      assert (WM : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono rsegs mem m6)
        by (repeat apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono_write;
            apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono_refl) end.
    (* the save area [A, A + 120) is application memory (it is in the slot window, above stklo) *)
    assert (Happ8 : forall a, A <= a < A + 120 -> app_mem a)
      by (intros a Ha; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
    assert (HFRA' := sl_fra_move B APIf ra g fr [] regs regs' _ md md' HFRA6 G2 G3 G4 G8 G9 G19 G26 Hmat).
    (* ENT across the same six stores, then across the model step *)
    match goal with |- SR _ (mkCfg (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.mkst _ _ ?m6 _) _) _ =>
      assert (HENT6 : ENT APIf g [] m6 md) end.
    { apply (r5_ent_store g fr [] regs _ md A 64 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
      - apply (r5_fra_store g fr [] regs _ md A 96 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
        apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
      - apply (r5_ent_store g fr [] regs _ md A 96 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
        + apply (r5_fra_store g fr [] regs _ md A 104 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
          apply (r5_fra_store g fr [] regs _ md A 8 _ _); [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
        + apply (r5_ent_store g fr [] regs _ md A 104 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
          * apply (r5_fra_store g fr [] regs _ md A 0 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
            apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
            apply (r5_fra_store g fr [] regs _ md A 8 _ _);
              [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
          * apply (r5_ent_store g fr [] regs _ md A 0 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
            -- apply (r5_fra_store g fr [] regs _ md A 112 _ _); [| exact Hr9 | exact HAr | lia | lia | lia | lia].
               apply (r5_fra_store g fr [] regs _ md A 8 _ _);
                 [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
            -- apply (r5_ent_store g fr [] regs _ md A 112 _ _); [| | exact Hr9 | exact HAr | lia | lia | lia].
               ++ apply (r5_fra_store g fr [] regs _ md A 8 _ _);
                    [exact HFRA | exact Hr9 | exact HAr | lia | lia | lia | lia].
               ++ apply (r5_ent_store g fr [] regs _ md A 8 _ _);
                    [exact HFRA | exact HENT | exact Hr9 | exact HAr | lia | lia | lia]. }
    assert (HENT' : ENT APIf g [] _ md') by exact (ent_mat APIf g [] _ md md' HENT6 Hmat).
    assert (Hr9' : rg regs' 9 A) by (unfold rg; rewrite G9; exact Hr9).
    assert (LID : length (RID (g_in g) 0) = 38%nat) by reflexivity.
    assert (LFG : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
    rewrite <- SEGS. apply Hexit.
    do 4 eexists. split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hn|].
    split.
    { destruct HCUR as (Hc7 & H22 & H25).
      unfold RS, RB, CUR, OURb, IDBr, FGBr, rg in *.
      split; [lia|].
      split; [split; [exact Hc7|]; split; [rewrite G22; exact H22 | rewrite G25; exact H25]|].
      split.
      { eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length. intros x Hx. r5_out. }
      split; [rewrite G23; reflexivity|].
      split.
      { eapply fl_bytes; [exact HID | exact MU |]. rewrite LID. intros x Hx. r5_out. }
      { eapply fl_bytes; [exact HFG | exact MU |]. rewrite LFG. intros x Hx. r5_out. } }
    split; [exact (r5_addr_keep A mem _ (fr + 544) 1492 MU Happ8 HOUT)|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H128. }
    (* PRO (push 13B): the eight spills by the store chain, our[]'s shadow byte (the save area is application
       memory), and the input pair (the save area is at or above the slot window's base: RcPro.rc_away_hi) *)
    split.
    { unfold PRO.
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H40. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H120. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H136. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H160. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H168. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H176. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H200. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H248. }
      split; [exact (r5_addr_keep A mem _ (fr + 2624) 6 MU Happ8 Hour6)|].
      pose proof (rc_in_keep B APIf ra g fr [] regs mem _ md _ HFRA MU) as HK.
      specialize (HK ltac:(intros x Hx; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside] in Hx;
                           apply (rc_away_hi B APIf ra g fr [] regs mem md x HFRA); lia) (conj Hinb Hinl)).
      destruct HK as (Hinb' & Hinl').
      split; [exact Hinb'|]. split; [exact Hinl'|].
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H184. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H256. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H264. }
      split. { exists A. split; [exact Hr9'|]. r5_q. exact H272. }
      exists A. split; [exact Hr9'|]. r5_q. exact H32. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split; [exact G10|].
    split; [exact G24|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. }
    split.
    { exists A. split; [exact Hr9'|]. rewrite E112. r5_q. }
    split; [unfold rg; rewrite G21; exact H21|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H152. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H144. }
    split; [exact (r5_addr_keep A mem _ (fr + 2176) 38 MU Happ8 Hid38)|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H208. }
    split; [r5_keep_cells Hidr|]. split; [r5_keep_cells Hjnk|].
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H280. }
    split.
    { exists A. split; [exact Hr9'|]. r5_q. exact H240. }
    split; [r5_keep_cells Hjy|]. split; [r5_keep_cells Hscr|].
    (* push 10, RXS: [A + 48 / 56 / 88 / 80 / 72 / 200 / 216] carried (outside the six stores), this segment's own
       [A + 8] = mrow + 16 (0x8158c / 0x81590) and [A + 0] = mrow + 20 (0x81598 / 0x8159c), and the 72 fragment
       bytes addressable (the save area is application memory) *)
    unfold RXS.
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H48. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H56. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H88. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H80. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H72. }
    split. { exists A. split; [exact Hr9'|]. r5_q. }
    split. { exists A. split; [exact Hr9'|]. rewrite Z.add_0_r. r5_q. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H192. }
    split. { exists A. split; [exact Hr9'|]. r5_q. exact H216. }
    exact (r5_addr_keep A mem _ (fr + 2256) 72 MU Happ8 Hfg72).
Qed.

End R5D.

(* The derivation states R5.v's seg_R5, term for term (constr_eq: syntactic, not up to conversion). *)
Example seg_R5_of_F_verbatim : True.
Proof.
  let a := type of @R5.seg_R5 in let b := type of @seg_R5_of_F in constr_eq a b.
  exact I.
Qed.
