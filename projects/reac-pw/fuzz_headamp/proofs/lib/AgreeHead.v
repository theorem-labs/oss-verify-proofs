From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom SlotAgree AgreeShape AgreeFrame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require FrameProof SlotTopG AgreeCap.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require FrameProof SlotTopG ZAllocator AllocCf AgreeZlib FrameAPI
  SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require LLVMFuzzerTestOneInput_c HeadSlotAG HeadEnd
  headamp_build headamp_dup_pod headamp_dup_first headamp_plain memset memcpy strlen reac_headamp_prop_parse_c
  check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require SlotInvCF LLVMFuzzerTestOneInput_c
  reac_headamp_prop_parse_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require SlotTopCF.
Import ListNotations.
Open Scope Z_scope.

(* reac-pw/fuzz_headamp's ubsan_agrees by the frame's AgreeFrame.ubsan_agrees_of_slots at the agreement shape
   ag_shape checksum_shape (no output, cap CAP_AG). Model: reac-pw/fuzz_role's AgreeRole.v (itself reac-pw/fuzz_pin's AgreePin.v and libreac/fuzz_ctrl's released CtrlAgree.v, origin/ossv/recipes
   25e3d17bdb50): the plain slot in its halts (realizes) form at the agreement shape (Prog/HeadSlotAG.slot_of_lemmas_ag
   over the plain segment lemmas, Prog/HeadEnd.segs_holds with the six seg_*_holds, taken at the halts shape
   checksum_shape, and the n >= 2^26 run's Prog/headamp_early.headamp_early_holds), and the ubsan slot in cut-free form
   (U/Prog/SegCF/SlotTopCF over the cut-free copy of the UBSan walk), each from its frame facts at the zlib instance.
   - ubsan_agrees_of_evts: Statements.ubsan_agrees from the five evt contracts of each build's LLVMFuzzerTestOneInput
     (builder, dup_pod, check, dup_first, plain);
   - ubsan_agrees_of_contracts: the same with the builder, dup_pod, dup_first and plain evts of both builds discharged
     by their walks and the leaves' _holds theorems (Prog/HeadEnd.plain_halts_of_contracts's discharges, and
     SlotTopCF.head_ubsan_slot_cg_of_contracts's): modulo, per build, headamp_check_contract and the plain evt's two
     callee contracts reac_headamp_prop_parse_contract and check_plain_contract.
   Proves no function (kind: agreement composition of LLVMFuzzerTestOneInput's two slots). *)

Local Abbreviation AGS := (ag_shape checksum_shape).
Local Abbreviation P_B := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YH02.src0_msyms.
Local Abbreviation P_API := (@OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.ZAllocator.zlib_API).
Local Abbreviation P_SH := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI5b.src0_sink_head.
Local Abbreviation P_SK := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YI5c.src0_sink.
Local Abbreviation P_RA := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YL0s.RA_LIB.
Local Abbreviation P_EMPTY := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable.YL0s.EMPTY.
Local Abbreviation U_B := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.YH02.src0_msyms.
Local Abbreviation U_API := (@OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.ZAllocator.zlib_API).
Local Abbreviation U_SH := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.YI5b.src0_sink_head.
Local Abbreviation U_SK := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.YI5c.src0_sink.
Local Abbreviation U_RA := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.YL0s.RA_LIB.
Local Abbreviation U_EMPTY := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.YL0s.EMPTY.

(* The halts frame facts at the plain zlib instance and the halts shape (FrameProof.frame_plain_holds without its
   slot obligation). *)
Lemma plain_frame_facts : frame_facts_plain P_B P_API checksum_shape P_SH P_SK P_RA P_EMPTY.
Proof.
  unfold frame_facts_plain.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.SlotTopG.ms_segs_rsegs
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.FrameProof.errno_below_ceiling
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.FrameProof.frame_G_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.FrameProof.frame_RELRO_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.FrameProof.zlib_frame_allocator
             | (intros b n H; exact H)
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end) ].
Qed.

(* The plain slot at the agreement shape: the segment lemmas at the halts shape (HeadEnd.segs_holds with the six
   segment files' lemmas and the five evt contracts), the n >= 2^26 run by its walk, the slot's room from ag_room. *)
Lemma plain_slot_ag_of_evts :
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_build_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_pod_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_check_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_first_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_plain_contract ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc AGS P_B (@P_API rc) P_SH P_SK [] frame_RELRO (fun _ _ => True) j ENTRY P_RA P_EMPTY
    SLOT_STACK.
Proof.
  intros BUILD DUPPOD CHECK DUPFIRST PLAIN rc fx j Hj.
  exact (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadSlotAG.slot_of_lemmas_ag (fx := fx) (rc := rc)
           (LS := AGS) (SH := P_SH) (SK := P_SK) P_B P_API P_RA P_EMPTY checksum_shape plain_frame_facts
           OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_early.headamp_early_holds
           (fun pl fs K => eq_refl) (fun n b => eq_refl) (fun b n H => ag_room_g checksum_shape b n H)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.segs_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_E01_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_M01_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_M02_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_M03_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_M04_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadEnd.seg_X01_holds
              BUILD DUPPOD CHECK DUPFIRST PLAIN
              fx rc P_B P_API checksum_shape P_SH P_SK P_RA P_EMPTY plain_frame_facts) j Hj).
Qed.

(* The frame's cut-free malloc contract (room_cf) gives the slot's form (malloc_contract_cfg, room_ag) under the
   frame's run-limit law (SRC_LIM_MIN <= vm_limit at every MR state; U/AgreeZlib.zlib_limit at the zlib instance):
   libreac/fuzz_ctrl's U/Prog/SegCF/SlotTopCF.malloc_cfg_of_cf, as reac-pw/fuzz_role's AgreeRole.malloc_cfg_of_cf. *)
Lemma malloc_cfg_of_cf : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B),
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  @OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.SlotAgree.malloc_contract_cf fx rc B API ->
  @OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInvCF.malloc_contract_cfg rc fx B API.
Proof.
  intros rc fx B API HLIM HM L A regs mem md n b CP RO H10 RES (HR & Hc & Hb).
  apply (HM L A regs mem md n b CP RO H10 RES).
  destruct CP as (HMR & _).
  exact (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AgreeCap.room_cf_of_limit md b n (HLIM L A mem md HMR) HR Hc Hb).
Qed.

(* The cut-free frame facts at the ubsan zlib instance and the agreement shape. *)
Lemma ubsan_frame_facts :
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInvCF.frame_facts_cf U_B U_API AGS U_SH U_SK U_RA U_EMPTY.
Proof.
  unfold OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInvCF.frame_facts_cf.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.SlotTopG.ms_segs_rsegs
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameProof.errno_below_ceiling
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameProof.ctx_not_ro
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameProof.frame_G_facts
             | exact OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameProof.frame_RELRO_facts
             | exact (ag_room_cg checksum_shape)
             | (intros; reflexivity) | reflexivity
             | (match goal with |- (_ < _ < _)%Z => split; vm_compute; reflexivity | |- (_ < _)%Z => vm_compute; reflexivity
                | |- (_ mod _ = _)%Z => vm_compute; reflexivity end)
             | idtac ].
  intros rc fx.
  destruct (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameProof.zlib_frame_allocator rc fx) as (_ & _ & _ & R).
  exact (conj (malloc_cfg_of_cf rc fx _ _ (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.AgreeZlib.zlib_limit rc)
                 (@OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.AllocCf.zlib_malloc_contract_cf fx rc))
          (conj (@OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.AllocCf.zlib_free_contract_cf fx rc)
             (conj (@OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.AllocCf.src0_free_null_cf fx) R))).
Qed.

(* The composition at the agreement shape, from the plain slot and the cut-free ubsan slot. *)
Lemma ubsan_agrees_of_slots_head :
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc AGS P_B (@P_API rc) P_SH P_SK [] frame_RELRO (fun _ _ => True) j ENTRY P_RA P_EMPTY
       SLOT_STACK) ->
  (forall (fx : FPState) (rc : RunCeil) B APIf LS SH SK ra empty,
   OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInvCF.frame_facts_cf B APIf LS SH SK ra empty ->
   forall j, (j < 4)%nat ->
     OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.SlotAgree.lib_contract_cg (LS := LS) B (APIf rc) []
       OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameAPI.frame_RELRO (fun _ _ => True) j
       OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameAPI.ENTRY ra empty
       OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.
Proof.
  intros PSLOT USLOT.
  apply (ubsan_agrees_of_slots AGS [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - exact PSLOT.
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (USLOT fx rc U_B U_API AGS U_SH U_SK U_RA U_EMPTY ubsan_frame_facts j Hj).
Qed.

Theorem ubsan_agrees_of_evts :
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_build_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_pod_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_check_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_first_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_plain_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_build_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_pod_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_check_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_dup_first_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_plain_contract ->
  Statements.ubsan_agrees.
Proof.
  intros PB PDP PC PDF PP UB UDP UC UDF UP.
  exact (ubsan_agrees_of_slots_head (plain_slot_ag_of_evts PB PDP PC PDF PP)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF.SlotTopCF.head_ubsan_slot_cg_of_evts
              UB UDP UC UDF UP)).
Qed.

(* The builder, dup_pod, dup_first and plain evts of both builds discharged by their walks: modulo, per build, the
   checking evt and the plain evt's two callees. *)
Theorem ubsan_agrees_of_contracts :
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.LLVMFuzzerTestOneInput_c.headamp_check_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_plain_c.check_plain_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.LLVMFuzzerTestOneInput_c.headamp_check_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract ->
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_plain_c.check_plain_contract ->
  Statements.ubsan_agrees.
Proof.
  intros PCHECK PPARSE PCPLAIN UCHECK UPARSE UCPLAIN.
  apply ubsan_agrees_of_slots_head.
  - exact (plain_slot_ag_of_evts
             (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_build.headamp_build_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strlen.strlen_holds)
             (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_dup_pod.headamp_dup_pod_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds)
             PCHECK
             (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_dup_first.headamp_dup_first_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds)
             (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_plain.headamp_plain_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds PPARSE PCPLAIN)).
  - exact (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF.SlotTopCF.head_ubsan_slot_cg_of_contracts
             UCHECK UPARSE UCPLAIN).
Qed.
