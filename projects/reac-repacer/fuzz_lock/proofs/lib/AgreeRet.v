(* The agreement step for a fuzz target that returns 0 or -1: AgreeFrame.v's ubsan_agrees_of_slots for a return
   function, the twin of Prog/FrameRet.v's frame_ret_hyp on the halting side.

   AgreeFrame.v ubsan_agrees_of_slots asks for the plain build's lib_contract_g (Contract.v) and the UBSan
   build's lib_contract_cg (U/SlotAgree.v); the leaf of each carries lib_post_g, which fixes the return register
   and ll_ret l at 0. fuzz_lock's LLVMFuzzerTestOneInput returns -1 on an empty name and on a name byte that is
   NUL, LF or a separator (fuzz_lock.c:191-197), so neither build meets those contracts; each meets the contract
   for the return function lock_ret: Prog/FrameRet.v's lib_contract_gr ret on the plain side and
   U/Prog/AgreeRet.v's lib_contract_cgr ret on the UBSan side.

   agree_ret_hyp states ubsan_agrees_of_slots for one return function ret with values 0 and -1, used by BOTH
   builds: the two premises name the same ret, so on a payload pl the plain call and the UBSan call return the
   same value ret pl, and the driver writes the same row after each (Prog/FrameRet.v ret_row). A proof may not
   pick a return for one build alone.
   At ret = fun _ => 0 the two call premises are equivalent to those of ubsan_agrees_of_slots
   (agree_ret_plain_call_0_iff, agree_ret_ubsan_call_0_iff) and every other premise is ubsan_agrees_of_slots's
   word for word.
   This file is the specification of a change to the kit; nothing here is proved about either image. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_lock Require Statements Images.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import FrameRet.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require AgreeZlib SlotAgree ZAllocator FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require AgreeRet.
Import ListNotations.
Open Scope Z_scope.

Definition agree_ret_hyp : Prop :=
  forall ret : list byte -> Z, (forall pl, ret pl = 0 \/ ret pl = -1) ->
  forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       ret G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.Prog.AgreeRet.lib_contract_cgr fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       ret Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.

(* At ret = fun _ => 0 the plain call premise of agree_ret_hyp is equivalent to that of AgreeFrame.v
   ubsan_agrees_of_slots (Prog/FrameRet.v lib_contract_gr_0_iff, for every rc, fx and j < 4). *)
Lemma agree_ret_plain_call_0_iff : forall (LS : lib_shape) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       (fun _ => 0) G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) <->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK).
Proof.
  intros LS G GI.
  split; intros H rc fx j Hj; [apply lib_contract_g_of_gr0 | apply lib_contract_gr_of_g]; exact (H rc fx j Hj).
Qed.

(* At ret = fun _ => 0 the UBSan call premise of agree_ret_hyp is equivalent to that of AgreeFrame.v
   ubsan_agrees_of_slots (U/Prog/AgreeRet.v lib_contract_cgr_0_iff, for every rc, fx and j < 4). *)
Lemma agree_ret_ubsan_call_0_iff : forall (LS : lib_shape) (Gu : list (Z * Z))
    (GIu : nat -> (word -> option byte) -> Prop),
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.Prog.AgreeRet.lib_contract_cgr fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       (fun _ => 0) Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) <->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK).
Proof.
  intros LS Gu GIu.
  split; intros H rc fx j Hj;
    [apply U.Prog.AgreeRet.lib_contract_cg_of_cgr0 | apply U.Prog.AgreeRet.lib_contract_cgr_of_cg];
    exact (H rc fx j Hj).
Qed.
