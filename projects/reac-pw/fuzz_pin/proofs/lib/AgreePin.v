From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom SlotAgree AgreeShape AgreeFrame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require FrameProof SlotTopG AgreeCap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require FrameProof SlotTopG ZAllocator AllocCf AgreeZlib FrameAPI
  SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require SlotInv PinSlotAG PinEnd
  check_known check_row check_label fuzz_catalogue_row reac_box_pin_parse strlen bcmp strcspn memset strchrnul
  reac_box_catalogue strncmp.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF Require SlotTopCF.
Import ListNotations.
Open Scope Z_scope.

(* reac-pw/fuzz_pin's ubsan_agrees by the frame's AgreeFrame.ubsan_agrees_of_slots at the agreement shape
   ag_shape checksum_shape (no output, cap CAP_AG), in the form of libreac/fuzz_ctrl's released CtrlAgree.v
   (origin/ossv/recipes 25e3d17bdb50): the plain slot in its halts (realizes) form at the agreement shape
   (Prog/PinSlotAG.slot_of_lemmas_ag over the plain segment lemmas, Prog/PinEnd.segs_holds, taken at the halts
   shape checksum_shape), and the ubsan slot in cut-free form (U/Prog/SegCF/SlotTopCF.pin_ubsan_slot_cg over the
   cut-free copy of the UBSan walk), each from its frame facts at the zlib instance.
   Proves no function (kind: agreement composition of LLVMFuzzerTestOneInput's two slots). *)

Local Abbreviation AGS := (ag_shape checksum_shape).
Local Abbreviation P_B := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YH02.src0_msyms.
Local Abbreviation P_API := (@OSSVerify.Proofs.reac_pw.fuzz_pin.lib.ZAllocator.zlib_API).
Local Abbreviation P_SH := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YI5b.src0_sink_head.
Local Abbreviation P_SK := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YI5c.src0_sink.
Local Abbreviation P_RA := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YL0s.RA_LIB.
Local Abbreviation P_EMPTY := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable.YL0s.EMPTY.
Local Abbreviation U_B := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.YH02.src0_msyms.
Local Abbreviation U_API := (@OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.ZAllocator.zlib_API).
Local Abbreviation U_SH := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.YI5b.src0_sink_head.
Local Abbreviation U_SK := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.YI5c.src0_sink.
Local Abbreviation U_RA := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.YL0s.RA_LIB.
Local Abbreviation U_EMPTY := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.YL0s.EMPTY.

(* The halts frame facts at the plain zlib instance and the halts shape (FrameProof.frame_plain_holds without its
   slot obligation). *)
Lemma plain_frame_facts : frame_facts_plain P_B P_API checksum_shape P_SH P_SK P_RA P_EMPTY.
Proof.
  unfold frame_facts_plain.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.SlotTopG.ms_segs_rsegs
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.FrameProof.errno_below_ceiling
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.FrameProof.frame_G_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.FrameProof.frame_RELRO_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.FrameProof.zlib_frame_allocator
             | (intros b n H; exact H)
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end) ].
Qed.

(* The contracts of pin's own callees of the plain LLVMFuzzerTestOneInput, from their _holds theorems. *)
Lemma plain_callees : OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinEnd.pin_callee_contracts.
Proof.
  unfold OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinEnd.pin_callee_contracts.
  split; [exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.check_known.check_known_holds|].
  split; [exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.check_row.check_row_holds|].
  split; [exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.check_label.check_label_holds|].
  split.
  - exact (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.fuzz_catalogue_row.fuzz_catalogue_row_holds
             OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.strlen.strlen_holds
             OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.bcmp.bcmp_holds).
  - exact (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.reac_box_pin_parse.reac_box_pin_parse_holds
             (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.strcspn.strcspn_holds
                OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.memset.memset_holds
                OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.strchrnul.strchrnul_holds)
             OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.reac_box_catalogue.reac_box_catalogue_holds
             OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.strlen.strlen_holds
             OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.strncmp.strncmp_holds).
Qed.

(* The plain slot at the agreement shape: the segment lemmas at the halts shape, the slot's room from ag_room. *)
Lemma plain_slot_ag : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc AGS P_B (@P_API rc) P_SH P_SK [] frame_RELRO (fun _ _ => True) j ENTRY P_RA P_EMPTY
    SLOT_STACK.
Proof.
  intros rc fx j Hj.
  exact (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinSlotAG.slot_of_lemmas_ag (fx := fx) (rc := rc)
           (LS := AGS) (SH := P_SH) (SK := P_SK) P_B P_API P_RA P_EMPTY checksum_shape plain_frame_facts
           (fun pl fs K => eq_refl) (fun n b => eq_refl) (fun b n H => ag_room_g checksum_shape b n H)
           (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinEnd.segs_holds plain_callees fx rc P_B P_API
              checksum_shape P_SH P_SK P_RA P_EMPTY plain_frame_facts) j Hj).
Qed.

(* The frame's cut-free malloc contract (room_cf) gives the slot's form (malloc_contract_cfg, room_ag) under the
   frame's run-limit law (SRC_LIM_MIN <= vm_limit at every MR state; AgreeZlib.zlib_limit at the zlib instance):
   libreac/fuzz_ctrl's U/Prog/SegCF/SlotTopCF.malloc_cfg_of_cf. *)
Lemma malloc_cfg_of_cf : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B),
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  @U.SlotAgree.malloc_contract_cf fx rc B API ->
  @OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SlotInvCF.malloc_contract_cfg rc fx B API.
Proof.
  intros rc fx B API HLIM HM L A regs mem md n b CP RO H10 RES (HR & Hc & Hb).
  apply (HM L A regs mem md n b CP RO H10 RES).
  destruct CP as (HMR & _).
  exact (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AgreeCap.room_cf_of_limit md b n (HLIM L A mem md HMR) HR Hc Hb).
Qed.

(* The cut-free frame facts at the ubsan zlib instance and the agreement shape. *)
Lemma ubsan_frame_facts :
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SlotInvCF.frame_facts_cf U_B U_API AGS U_SH U_SK U_RA U_EMPTY.
Proof.
  unfold OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SlotInvCF.frame_facts_cf.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.SlotTopG.ms_segs_rsegs
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.FrameProof.errno_below_ceiling
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.FrameProof.frame_G_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.FrameProof.frame_RELRO_facts
             | exact (ag_room_cg checksum_shape)
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end)
             | idtac ].
  intros rc fx.
  destruct (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.FrameProof.zlib_frame_allocator rc fx) as (_ & _ & _ & R).
  exact (conj (malloc_cfg_of_cf rc fx _ _ (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.AgreeZlib.zlib_limit rc)
                 (@OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.AllocCf.zlib_malloc_contract_cf fx rc))
          (conj (@OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.AllocCf.zlib_free_contract_cf fx rc)
             (conj (@OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.AllocCf.src0_free_null_cf fx) R))).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots AGS [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - exact plain_slot_ag.
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF.SlotTopCF.pin_ubsan_slot_cg fx rc U_B U_API AGS
             U_SH U_SK U_RA U_EMPTY ubsan_frame_facts j Hj).
Qed.
