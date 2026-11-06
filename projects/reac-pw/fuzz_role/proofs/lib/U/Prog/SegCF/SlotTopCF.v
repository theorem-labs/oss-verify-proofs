(* The cut-free (agreement) slot of reac-pw/fuzz_role's UBSan build: lib_contract_cg for every j < 4, from the
   cut-free copy of the slot proof (U/Prog/SlotInvCF.v, SegCF/*.v) under the agreement frame's facts
   (SlotInvCF.frame_facts_cf: U/FrameAPI.frame_facts_ubsan with the cut-free allocator and the agreement room
   128 <= sb_cap <= CAP_AG). Model: reac-pw/fuzz_pin's U/Prog/SegCF/SlotTopCF.v (libreac/fuzz_ctrl's released
   U/Prog/SegCF/SlotTopCF.v with its SegCF/Segs.v, origin/ossv/recipes 25e3d17bdb50), for role's four segments:
   - role_build_holds_cf / role_check_holds_cf: the two evt contracts of the UBSan LLVMFuzzerTestOneInput, from the
     walks U/Prog/role_build.v (the leaves memset, memcpy, strlen and pod_write_ent) and U/Prog/role_check.v (the
     contracts of role's own callees: the libc leaves, the parse, the checks, and pod_nearest with its binary128 value
     facts, Prog/NearSFClose.v, and its five soft-float callees at the UBSan image, CJ/RL/I/InstU.v);
   - segs_cf: the cut-free segment lemmas (StmtsCF.seg_lemmas) for every instance with frame_facts_cf, from
     SegCF/E01.v (malloc inside frame_facts_cf), SegCF/M01.v (role_build_contract), SegCF/M02.v
     (role_check_contract) and SegCF/X01.v (the cut-free free contract inside frame_facts_cf);
   - role_ubsan_slot_cg: SegCF/RoleSlotCF.slot_of_lemmas with segs_cf.
   The frame's malloc contract in cut-free form gives the slot's (malloc_contract_cfg) in AgreeRole.malloc_cfg_of_cf.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the cut-free segment lemmas with the cut-free slot). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require role_build role_check memset memcpy strlen strcmp
  pod_write_ent reac_role_prop_parse pod_nearest check_absent check_role check_malformed reac_role_cfg_changes
  reac_role_cfg_apply_state check_answer reac_role_refuse_code check_code.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require NearSFClose.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require InstU.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require E01 M01 M02 X01 RoleSlotCF.
Import ListNotations.
Open Scope Z_scope.

(* The builder segment's evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma role_build_holds_cf : role_build_contract.
Proof.
  exact (role_build.role_build_holds memset.memset_holds memcpy.memcpy_holds strlen.strlen_holds
           (pod_write_ent.pod_write_ent_holds memcpy.memcpy_holds memset.memset_holds)).
Qed.

(* The checking segment's evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma role_check_holds_cf : role_check_contract.
Proof.
  exact (role_check.role_check_holds memcpy.memcpy_holds
           (reac_role_prop_parse.reac_role_prop_parse_holds strcmp.strcmp_holds) strcmp.strcmp_holds
           (pod_nearest.pod_nearest_holds NearSFClose.near_sf_facts_ok
              InstU.N_extendsftf2_contract InstU.N_letf2_contract InstU.N_floatditf_contract
              InstU.N_subtf3_contract InstU.N_getf2_contract)
           check_absent.check_absent_holds check_role.check_role_holds check_malformed.check_malformed_holds
           reac_role_cfg_changes.reac_role_cfg_changes_holds reac_role_cfg_apply_state.reac_role_cfg_apply_state_holds
           (check_answer.check_answer_holds strcmp.strcmp_holds) reac_role_refuse_code.reac_role_refuse_code_holds
           (check_code.check_code_holds strcmp.strcmp_holds)).
Qed.

(* A segment lemma as its file states it once its Section closes, each premise found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Theorem segs_cf : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF.
  pose proof role_build_holds_cf as BUILD.
  pose proof role_check_holds_cf as CHECK.
  assert (FREE : free_contract_cf B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_cf in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [seg E01.seg_E01|].
  split; [seg M01.seg_M01|].
  split; [seg M02.seg_M02|].
  seg X01.seg_X01.
Qed.

Theorem role_ubsan_slot_cg : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms)
    (APIf : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) B (APIf rc) [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF j Hj.
  exact (RoleSlotCF.slot_of_lemmas B APIf ra empty FF (segs_cf fx rc B APIf LS SH SK ra empty FF) j Hj).
Qed.
