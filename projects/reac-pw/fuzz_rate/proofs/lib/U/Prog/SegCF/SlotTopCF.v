(* The cut-free (agreement) slot of reac-pw/fuzz_rate's UBSan build: lib_contract_cg for every j < 4, from the
   cut-free copy of the slot proof (U/Prog/SlotInvCF.v, SegCF/*.v) under the agreement frame's facts
   (SlotInvCF.frame_facts_cf: U/FrameAPI.frame_facts_ubsan with the cut-free allocator and the agreement room
   128 <= sb_cap <= CAP_AG). Model: reac-pw/fuzz_role's U/Prog/SegCF/SlotTopCF.v (reac-pw/fuzz_pin's, and libreac/fuzz_ctrl's released U/Prog/SegCF/SlotTopCF.v with its SegCF/Segs.v,
   origin/ossv/recipes 25e3d17bdb50), for rate's five segments:
   - the three evt contracts of the UBSan LLVMFuzzerTestOneInput are U/Prog/RateTop.v's build_ok (the walk
     U/Prog/rate_build.v from memset, memcpy, strlen and pod_write_ent), check_ok (U/Prog/rate_check.v from the
     contracts of rate's own callees, pod_nearest_ok included) and csv_ok (U/Prog/rate_csv.v from memset,
     reac_rate_drivable_csv and check_csv);
   - segs_cf: the cut-free segment lemmas (StmtsCF.seg_lemmas) for every instance with frame_facts_cf, from
     SegCF/E01.v (malloc inside frame_facts_cf), SegCF/M01.v (rate_build_contract), SegCF/M02.v
     (rate_check_contract), SegCF/M03.v (malloc inside frame_facts_cf and rate_csv_contract) and SegCF/X01.v (the
     cut-free free contract inside frame_facts_cf);
   - rate_ubsan_slot_cg: SegCF/RateSlotCF.slot_of_lemmas with segs_cf.
   The frame's malloc contract in cut-free form gives the slot's (malloc_contract_cfg) in AgreeRate.malloc_cfg_of_cf.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the cut-free segment lemmas with the cut-free slot). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require RateTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require E01 M01 M02 M03 X01 RateSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* A segment lemma as its file states it once its Section closes, each premise found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Theorem segs_cf : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF.
  pose proof RateTop.build_ok as BUILD.
  pose proof RateTop.check_ok as CHECK.
  pose proof RateTop.csv_ok as CSV.
  assert (FREE : free_contract_cf B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_cf in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [seg E01.seg_E01|].
  split; [seg M01.seg_M01|].
  split; [seg M02.seg_M02|].
  split; [seg M03.seg_M03|].
  seg X01.seg_X01.
Qed.

Theorem rate_ubsan_slot_cg : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms)
    (APIf : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF j Hj.
  exact (RateSlotCF.slot_of_lemmas B APIf ra empty FF (segs_cf fx rc B APIf LS SH SK ra empty FF) j Hj).
Qed.
