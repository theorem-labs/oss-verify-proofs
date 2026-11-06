From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import memcpy_c memset_c bcmp_c
  reac_ctrl_build_scene_step_c check_step_c reac_ctrl_scene_set_mac_c reac_ctrl_scene_build_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require memcpy memset bcmp reac_ctrl_build_scene_step check_step
  reac_ctrl_parse kind_of_link1 reac_ctrl_checksum_verify reac_ctrl_scene_set_mac reac_ctrl_scene_build
  reac_ctrl_block_cksum_stamp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv SCut SEarly SSlot.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.SegCF Require Import CInv CTac CSlot
  CSegE CSegB CSegT CSegC CSegM CSegD CSegF CSegG.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require ZAllocator FrameProof ZTraceSpec AllocCf SlotTopG AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* The ubsan slot of fuzz_scene in the cut-free form of the agreement frame: the entry from the cut-free segment
   lemmas, the slot (SlotAgree.lib_contract_cg) for every shape whose room is the agreement room, and the frame's
   instance (the frame of U.FrameProof.frame_ubsan_holds; the run limit law from AgreeZlib.zlib_limit). *)

Section Entry.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract_cf B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis FREE : free_contract_cf B (APIf rc).
Hypothesis MEMC : memcpy_contract.
Hypothesis MEMS : memset_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis BUILD : reac_ctrl_build_scene_step_contract.
Hypothesis CHECK : check_step_contract.
Hypothesis SETMAC : reac_ctrl_scene_set_mac_contract.
Hypothesis SBUILD : reac_ctrl_scene_build_contract.

Theorem slot_entry_cf : Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  assert (HG : Hcut_cf B APIf ra (Inv_K15458 B APIf ra empty)) by (eapply seg_G_cf; eassumption).
  assert (HF : Hcut_cf B APIf ra (Inv_K15450 B APIf ra empty)) by (eapply seg_F_cf; eassumption).
  assert (HD : Hcut_cf B APIf ra (Inv_K152a0 B APIf ra empty)) by (eapply seg_D_cf; eassumption).
  assert (HM : Hcut_cf B APIf ra (Inv_K15298 B APIf ra empty)) by (eapply seg_M_cf; eassumption).
  assert (HC : Hcut_cf B APIf ra (Inv_K15294 B APIf ra empty)) by (eapply seg_C_cf; eassumption).
  assert (HT : Hcut_cf B APIf ra (Inv_K151b4 B APIf ra empty)) by (eapply seg_T_cf; eassumption).
  assert (HB : Hcut_cf B APIf ra (Inv_K15010 B APIf ra empty)) by (eapply seg_B_cf; eassumption).
  eapply seg_E_cf; eassumption.
Qed.

End Entry.

(* The instance: the frame's allocator and image facts, any shape with the silent output and the agreement room. *)
Section Inst.
Import OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YH02 OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YI5b
  OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YI5c OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YL0s
  OSSVerify.Proofs.libreac.fuzz_scene.lib.U.ZAllocator OSSVerify.Proofs.libreac.fuzz_scene.lib.U.FrameProof
  OSSVerify.Proofs.libreac.fuzz_scene.lib.U.AllocCf OSSVerify.Proofs.libreac.fuzz_scene.lib.U.SlotTopG.

Theorem scene_slot_cg_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall n b, @lib_delta LS n b = b) ->
  (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
      [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HLIBK HDELTA HROOM rc fx j _.
  assert (FF : frame_facts src0_msyms (@zlib_API) LS src0_sink_head src0_sink RA_LIB EMPTY).
  { unfold frame_facts.
    split; [exact ms_segs_rsegs|].
    split; [vm_compute; reflexivity|].
    do 4 (split; [reflexivity|]).
    split; [exact errno_below_ceiling|].
    do 12 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact ctx_not_ro|].
    split; [exact frame_G_facts|].
    split; [exact frame_RELRO_facts|].
    split; [exact HLIBK|].
    split; [exact HDELTA|].
    split; [exact zlib_frame_allocator|].
    split; reflexivity. }
  pose proof memcpy.memcpy_holds as MEMC. pose proof memset.memset_holds as MEMS. pose proof bcmp.bcmp_holds as BCMP.
  pose proof (reac_ctrl_build_scene_step.reac_ctrl_build_scene_step_holds MEMS MEMC
    reac_ctrl_block_cksum_stamp.reac_ctrl_block_cksum_stamp_holds) as BUILD.
  pose proof (check_step.check_step_holds BCMP MEMC
    (reac_ctrl_parse.reac_ctrl_parse_holds MEMS MEMC BCMP kind_of_link1.kind_of_link1_holds)
    reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds) as CHECK.
  pose proof (reac_ctrl_scene_set_mac.reac_ctrl_scene_set_mac_holds MEMC) as SETMAC.
  pose proof (reac_ctrl_scene_build.reac_ctrl_scene_build_holds MEMS MEMC) as SBUILD.
  apply (slot_lib_cg src0_msyms (@zlib_API) RA_LIB EMPTY FF scene_early_holds HROOM).
  apply (slot_entry_cf src0_msyms (@zlib_API) RA_LIB EMPTY FF (@zlib_malloc_contract_cf fx rc) (AgreeZlib.zlib_limit rc)
    (@zlib_free_contract_cf fx rc) MEMC MEMS BCMP BUILD CHECK SETMAC SBUILD).
Qed.

End Inst.
