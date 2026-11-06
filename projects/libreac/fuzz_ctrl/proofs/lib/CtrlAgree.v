From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom SlotAgree AgreeShape AgreeFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require FrameProof SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require FrameProof SlotTopG ZAllocator AllocCf AgreeZlib FrameAPI
  SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Slot Segs SlotLink.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require SlotTopCF.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_ctrl's ubsan_agrees by the frame's AgreeFrame.ubsan_agrees_of_slots at the agreement shape
   ag_shape checksum_shape (no output, cap CAP_AG): the plain slot in its halts (realizes) form, whose entry room
   is 128 <= sb_cap <= CAPMAX, and the ubsan slot in cut-free form (U/Prog/SegCF/SlotTopCF.ctrl_ubsan_slot_cg),
   each from its frame facts at the zlib instance. *)

Local Abbreviation AGS := (ag_shape checksum_shape).
Local Abbreviation P_B := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YH02.src0_msyms.
Local Abbreviation P_API := (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZAllocator.zlib_API).
Local Abbreviation P_SH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b.src0_sink_head.
Local Abbreviation P_SK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c.src0_sink.
Local Abbreviation P_RA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0s.RA_LIB.
Local Abbreviation P_EMPTY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0s.EMPTY.

Lemma plain_frame_facts :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.SlotInv.frame_facts P_B P_API AGS P_SH P_SK P_RA P_EMPTY.
Proof.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.SlotInv.frame_facts.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotTopG.ms_segs_rsegs | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.errno_below_ceiling | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.frame_G_facts | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.frame_RELRO_facts
             | exact (ag_room_g checksum_shape) | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof.zlib_frame_allocator
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end) ].
Qed.

Lemma ubsan_frame_facts :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SlotInvCF.frame_facts OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YH02.src0_msyms (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.ZAllocator.zlib_API) AGS
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YL0s.RA_LIB OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YL0s.EMPTY.
Proof.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SlotInvCF.frame_facts.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.SlotTopG.ms_segs_rsegs | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.FrameProof.errno_below_ceiling | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.FrameProof.frame_G_facts | exact OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.FrameProof.frame_RELRO_facts
             | exact (ag_room_cg checksum_shape)
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end)
             | idtac ].
  intros rc fx.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.FrameProof.zlib_frame_allocator rc fx) as (_ & _ & _ & R).
  exact (conj (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF.SlotTopCF.malloc_cfg_of_cf rc fx _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.AgreeZlib.zlib_limit rc)
                 (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.AllocCf.zlib_malloc_contract_cf fx rc))
          (conj (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.AllocCf.zlib_free_contract_cf fx rc) (conj (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.AllocCf.src0_free_null_cf fx) R))).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots AGS [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.Slot.slot_of_lemmas fx rc P_B P_API AGS P_SH P_SK P_RA P_EMPTY
      plain_frame_facts
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.Segs.segs_holds fx rc P_B P_API AGS P_SH P_SK P_RA P_EMPTY
         plain_frame_facts OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.SlotLink.callee_contracts_holds
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg.SlotLink.fragment_contract_holds) j Hj).
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF.SlotTopCF.ctrl_ubsan_slot_cg fx rc OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YH02.src0_msyms (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.ZAllocator.zlib_API) AGS
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YL0s.RA_LIB OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YL0s.EMPTY
      ubsan_frame_facts j Hj).
Qed.
