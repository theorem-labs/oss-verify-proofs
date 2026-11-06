From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Ubsan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0k YL0p YL0q YL0n YL0g YL0m YL0s YL0y YL0w YL0x.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t YL0z.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YM0b YL0j DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YL0i_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YN3e_cfw YL0p_cfw YL0q_cfw YL0w_cfw YL0x_cfw YL0y_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YL0n_cfw YL0l_cfw YL0z_cfwi.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YL0j_cfwi.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract SlotAgree SlotAgreeI ZAllocator FrameSlotG
  AllocCf AllocCfI SlotPack SlotAgreeV AgreeZlib DriverRIPc.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* The cut-free (crealizes) driver walk for the pack resource form of the walk slot, RI := RI_Pc CS: the walk twins
   Reusable/*_cfwi.v (made by cfconv/cfwi.py from the *_cfw.v files) need only II of the slot's resource fact
   (RI_Pc_II) and the form-independent free contract free_contract_cfi (AllocCfI.free_contract_cfi_ok, from the
   cut-free free realization); the driver tree's run leaves satisfy RI_Pc CS for every CS_ok CS (driver_RI_Pc). *)

Section WalkP.
Context {rc : YM05.RunCeil} {LS : lib_shape}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable CS : list byte -> list Z.
Variable OUT : list byte -> list byte.
Hypothesis HCS : CS_ok CS.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all src0_msyms API (RI_Pc CS) src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DOB : driver_obligationsX.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis FRC : forall fx' : FPState, @free_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Theorem pack_walk_crealizes : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPECX inp).
Proof using AX HCS GIL GI0 LIBXc DOB TBL MRC FRC LIMLAW.
  exact (YL0j_cfwi.src0_realizes_specX_cf API AX GI (RI_Pc CS) OUT GIL GI0 LIBXc DOB (driver_RI_Pc CS HCS)
    (fun fx' => @free_contract_cfi_ok fx' rc src0_msyms API AX ltac:(vm_compute; reflexivity) (FRC fx'))
    TBL (RI_Pc_II CS) MRC FRC LIMLAW).
Qed.
End WalkP.

Theorem zlib_pack_walk_crealizes : forall (rc : RunCeil) (LS : lib_shape) (CS : list byte -> list Z)
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (OUT : list byte -> list byte),
  CS_ok CS ->
  G_local_T src0segs src0_G GI ->
  (forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
  lib_contract_x_Rc_all src0_msyms (@zlib_API rc) (RI_Pc CS) src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
  forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPECX (LS:=LS) inp).
Proof.
  intros rc LS CS GI OUT HCS GIL GI0 LIBXc.
  exact (@pack_walk_crealizes rc LS (@zlib_API rc) zlib_allocator_extra GI CS OUT HCS GIL GI0 LIBXc
    driver_obligationsX_proved (zlib_tables rc) (fun fx' => @src0_malloc_realizes_cf fx' rc)
    (fun fx' => @src0_free_realizes_cf fx' rc) (zlib_limit rc)).
Qed.
