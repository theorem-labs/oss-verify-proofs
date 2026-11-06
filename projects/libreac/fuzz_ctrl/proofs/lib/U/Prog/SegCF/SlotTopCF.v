(* The cut-free (agreement) slot of fuzz_ctrl's ubsan build: lib_contract_cg for every j < 4, from the cut-free
   copy of the slot proof (SlotInvCF.v, SegCF/*.v) under the agreement frame's facts (SlotInvCF.frame_facts: the
   halts frame's facts with the cut-free allocator and the agreement room 128 <= sb_cap <= CAP_AG). The frame's
   cut-free malloc contract (SlotAgree.malloc_contract_cf, room_cf) gives the slot's form (malloc_contract_cfg,
   room_ag) under the frame's run-limit law (SRC_LIM_MIN <= vm_limit at every MR state; zlib_limit at the
   agreement instance): malloc_cfg_of_cf. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO03 YO0i YM0b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI SlotAgree AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Slot SlotLink Segs.
Open Scope Z_scope.

Lemma malloc_cfg_of_cf : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B),
  (forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md)) ->
  @malloc_contract_cf fx rc B API -> @malloc_contract_cfg rc fx B API.
Proof.
  intros rc fx B API HLIM HM L A regs mem md n b CP RO H10 RES (HR & Hc & Hb).
  apply (HM L A regs mem md n b CP RO H10 RES).
  destruct CP as (HMR & _).
  exact (room_cf_of_limit md b n (HLIM L A mem md HMR) HR Hc Hb).
Qed.

Theorem ctrl_ubsan_slot_cg : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms)
    (APIf : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat -> lib_contract_cg B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF j Hj.
  exact (@slot_of_lemmas fx rc B APIf LS SH SK ra empty FF
           (@segs fx rc B APIf LS SH SK ra empty FF callee_contracts_holds fragment_contract_holds) j Hj).
Qed.
