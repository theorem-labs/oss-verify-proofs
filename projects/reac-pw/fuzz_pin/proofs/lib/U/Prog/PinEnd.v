(* ubsan_halts of reac-pw/fuzz_pin from the UBSan frame and the slot of LLVMFuzzerTestOneInput: the plain
   lib/Prog/PinEnd.v (libreac/fuzz_ctrl's released U/Prog/Seg/Segs.v + SlotLink.v, origin/ossv/recipes 25e3d17bdb50)
   on the UBSan build's files.
   - segs_holds: the segment lemmas (U LLVMFuzzerTestOneInput_c.seg_lemmas) for every instance that satisfies
     U/FrameAPI.frame_facts_ubsan, from U/Prog/Seg/E01.v (memchr: the released leaf U/Prog/memchr.v), U/Prog/Seg/M01.v
     (pin_mid_contract, proved by U/Prog/pin_mid.v from memcpy and strlen (released leaves) and the contracts of pin's
     own callees) and U/Prog/Seg/X01.v (free: frame_allocator, inside frame_facts_ubsan).
   - ubsan_halts_of_callees: Statements.ubsan_halts from FrameProof.frame_ubsan_holds through PinSlot.ubsan_halts_of_frame,
     with the contracts of pin's own functions check_known, check_row, check_label, fuzz_catalogue_row and
     reac_box_pin_parse as its one premise (the unit's top discharges it with their
     _holds theorems).
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of the
   segment lemmas with the slot); LLVMFuzzerTestOneInput's walk is closed here modulo the five callee contracts. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require memchr_c memchr memcpy_c memcpy strlen_c strlen
  check_known_c check_row_c check_label_c fuzz_catalogue_row_c reac_box_pin_parse_c pin_mid PinSlot.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.Seg Require E01 M01 X01.
From OSSVerify.reac_pw.fuzz_pin Require Statements.

(* The contracts of pin's own callees of LLVMFuzzerTestOneInput (the leaves memchr, memcpy and strlen are discharged
   below by their released _holds theorems; malloc and free come from the frame). *)
Definition pin_callee_contracts : Prop :=
  check_known_c.check_known_contract /\ check_row_c.check_row_contract /\ check_label_c.check_label_contract /\
  fuzz_catalogue_row_c.fuzz_catalogue_row_contract /\ reac_box_pin_parse_c.reac_box_pin_parse_contract.

(* The middle segment's evt, from its walk. *)
Lemma pin_mid_of_callees : pin_callee_contracts -> pin_mid_contract.
Proof.
  intros (CK & CR & CL & CAT & PARSE).
  exact (pin_mid.pin_mid_holds memcpy.memcpy_holds strlen.strlen_holds CAT PARSE CK CR CL).
Qed.

(* A segment lemma as its file states it once its Section closes, each premise found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Theorem segs_holds : pin_callee_contracts ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros CC fx rc B APIf LS SH SK ra empty FF.
  pose proof (pin_mid_of_callees CC) as MID.
  pose proof memchr.memchr_holds as MCHR.
  assert (FREE : free_contract B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_ubsan in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [seg E01.seg_E01|].
  split; [seg M01.seg_M01|].
  seg X01.seg_X01.
Qed.

Theorem ubsan_halts_of_callees : pin_callee_contracts -> Statements.ubsan_halts.
Proof. intros CC. exact (PinSlot.ubsan_halts_of_frame (segs_holds CC) FrameProof.frame_ubsan_holds). Qed.
