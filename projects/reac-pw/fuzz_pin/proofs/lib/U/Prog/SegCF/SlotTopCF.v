(* The cut-free (agreement) slot of reac-pw/fuzz_pin's UBSan build: lib_contract_cg for every j < 4, from the
   cut-free copy of the slot proof (U/Prog/SlotInvCF.v, SegCF/*.v) under the agreement frame's facts
   (SlotInvCF.frame_facts_cf: U/FrameAPI.frame_facts_ubsan with the cut-free allocator and the agreement room
   128 <= sb_cap <= CAP_AG). libreac/fuzz_ctrl's released U/Prog/SegCF/SlotTopCF.v with its SegCF/Segs.v
   (origin/ossv/recipes 25e3d17bdb50), for pin's three segments:
   - segs_cf: the cut-free segment lemmas (StmtsCF.seg_lemmas) for every instance with frame_facts_cf, from
     SegCF/E01.v (memchr: the released leaf U/Prog/memchr.v), SegCF/M01.v (pin_mid_contract, proved by
     U/Prog/pin_mid.v from memcpy and strlen (released leaves) and the _holds theorems of pin's own callees in this
     base) and SegCF/X01.v (free: the cut-free free contract inside frame_facts_cf);
   - pin_ubsan_slot_cg: SegCF/PinSlotCF.slot_of_lemmas with segs_cf.
   The frame's malloc contract in cut-free form gives the slot's (malloc_contract_cfg) in AgreePin.malloc_cfg_of_cf.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the cut-free segment lemmas with the cut-free slot). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require memchr memcpy strlen bcmp check_known check_row
  check_label fuzz_catalogue_row reac_box_pin_parse strcspn memset strchrnul reac_box_catalogue strncmp pin_mid.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF Require E01 M01 X01 PinSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* The middle segment's evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma pin_mid_holds_cf : pin_mid_contract.
Proof.
  exact (pin_mid.pin_mid_holds memcpy.memcpy_holds strlen.strlen_holds
           (fuzz_catalogue_row.fuzz_catalogue_row_holds strlen.strlen_holds bcmp.bcmp_holds)
           (reac_box_pin_parse.reac_box_pin_parse_holds
              (strcspn.strcspn_holds memset.memset_holds strchrnul.strchrnul_holds)
              reac_box_catalogue.reac_box_catalogue_holds strlen.strlen_holds strncmp.strncmp_holds)
           check_known.check_known_holds check_row.check_row_holds check_label.check_label_holds).
Qed.

(* A segment lemma as its file states it once its Section closes, each premise found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Theorem segs_cf : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF.
  pose proof pin_mid_holds_cf as MID.
  pose proof memchr.memchr_holds as MCHR.
  assert (FREE : free_contract_cf B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_cf in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [seg E01.seg_E01|].
  split; [seg M01.seg_M01|].
  seg X01.seg_X01.
Qed.

Theorem pin_ubsan_slot_cg : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms)
    (APIf : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF j Hj.
  exact (PinSlotCF.slot_of_lemmas B APIf ra empty FF (segs_cf fx rc B APIf LS SH SK ra empty FF) j Hj).
Qed.
