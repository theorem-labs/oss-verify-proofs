(* The cut-free (agreement) slot of reac-pw/fuzz_headamp's UBSan build: lib_contract_cg for every j < 4, from the
   cut-free copy of the slot proof (U/Prog/SlotInvCF.v, SegCF/*.v) under the agreement frame's facts
   (SlotInvCF.frame_facts_cf: U/FrameAPI.frame_facts_ubsan with the cut-free allocator and the agreement room
   128 <= sb_cap <= CAP_AG). Model: reac-pw/fuzz_role's U/Prog/SegCF/SlotTopCF.v (itself reac-pw/fuzz_pin's and libreac/fuzz_ctrl's released U/Prog/SegCF/SlotTopCF.v with its
   SegCF/Segs.v, origin/ossv/recipes 25e3d17bdb50), for headamp's six segments:
   - segs_cf_of_evts: the cut-free segment lemmas (StmtsCF.seg_lemmas) for every instance with frame_facts_cf, from
     SegCF/E01.v (malloc inside frame_facts_cf), SegCF/M01.v (headamp_build_contract), SegCF/M02.v
     (headamp_dup_pod_contract), SegCF/M03.v (headamp_check_contract), SegCF/M04.v (headamp_dup_first_contract,
     headamp_plain_contract) and SegCF/X01.v (the cut-free free contract inside frame_facts_cf), with the five evt
     contracts of the UBSan LLVMFuzzerTestOneInput as premises;
   - head_ubsan_slot_cg_of_evts: SegCF/HeadSlotCF.slot_of_lemmas with segs_cf_of_evts and the n >= 2^26 run's evt
     discharged by U/Prog/headamp_early.headamp_early_holds;
   - head_ubsan_slot_cg_of_contracts: the same with four evts discharged by their UBSan walks (U/Prog/headamp_build.v
     from the leaves memset, memcpy, strlen and pod_write_ent; headamp_dup_pod.v and headamp_dup_first.v from memcpy;
     headamp_plain.v from memset and its two callee contracts): modulo headamp_check_contract and the plain evt's
     callees reac_headamp_prop_parse_contract and check_plain_contract.
   The frame's malloc contract in cut-free form gives the slot's (malloc_contract_cfg) in AgreeHead.malloc_cfg_of_cf.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the cut-free segment lemmas with the cut-free slot). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require headamp_build headamp_dup_pod headamp_dup_first
  headamp_plain headamp_early memset memcpy strlen pod_write_ent memset_c reac_headamp_prop_parse_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require E01 M01 M02 M03 M04 X01 HeadSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* A segment lemma as its file states it once its Section closes, each premise found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Theorem segs_cf_of_evts : headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros BUILD DUPPOD CHECK DUPFIRST PLAIN fx rc B APIf LS SH SK ra empty FF.
  assert (FREE : free_contract_cf B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_cf in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [seg E01.seg_E01|].
  split; [seg M01.seg_M01|].
  split; [seg M02.seg_M02|].
  split; [seg M03.seg_M03|].
  split; [seg M04.seg_M04|].
  seg X01.seg_X01.
Qed.

Theorem head_ubsan_slot_cg_of_evts : headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros BUILD DUPPOD CHECK DUPFIRST PLAIN fx rc B APIf LS SH SK ra empty FF j Hj.
  exact (HeadSlotCF.slot_of_lemmas B APIf ra empty FF headamp_early.headamp_early_holds
           (segs_cf_of_evts BUILD DUPPOD CHECK DUPFIRST PLAIN fx rc B APIf LS SH SK ra empty FF) j Hj).
Qed.

(* The builder, dup_pod, dup_first and plain evts discharged by their UBSan walks and the leaves' _holds theorems. *)
Theorem head_ubsan_slot_cg_of_contracts : headamp_check_contract ->
  reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract -> check_plain_c.check_plain_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros CHECK PARSE CPLAIN.
  exact (head_ubsan_slot_cg_of_evts
           (headamp_build.headamp_build_holds memset.memset_holds memcpy.memcpy_holds strlen.strlen_holds
              (pod_write_ent.pod_write_ent_holds memcpy.memcpy_holds memset.memset_holds))
           (headamp_dup_pod.headamp_dup_pod_holds memcpy.memcpy_holds) CHECK
           (headamp_dup_first.headamp_dup_first_holds memcpy.memcpy_holds)
           (headamp_plain.headamp_plain_holds memset.memset_holds PARSE CPLAIN)).
Qed.
