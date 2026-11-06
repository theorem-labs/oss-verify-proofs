(* The plain side of fuzz_preset's ASan agreement: the plain build realizes SPECX at 2^34
   (Budgets.Standard.lim_source) at checksum_shape, the library shape of fuzz_preset's ubsan agreement.
   - plain_rz_of_halts_pg is the plain half of lib/AgreePresetH.v ubsan_agrees_of_halts_pg34: the plain HALTS pack
     slot (lib_contract_pg) gives rz_run through RI_P (lib_contract_x_R_all_of_p, driver_RI_P) and
     lib/AgreeTop.v plain_rz_of_contracts_R;
   - preset_plain_rz instantiates it as lib/Theorems.v instantiates ubsan_agrees_of_halts_pg34 for ubsan_agrees: the
     proved slot AgreePresetH.preset_plain_halts_slot (Prog.PackSlot.slot_contract_of_entry over
     Prog.LinkPlain.lp_entry_sr), slot_G, omx_GI, Prog.Statement.slot_G_frame, Prog.SlotGI.slot_G_local and
     slot_GI_init. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeLim SlotPack FrameSlotP Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreePresetH SlotTopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger LLVMFuzzerTestOneInput_c Statement
  SlotGI.
Import ListNotations.
Open Scope Z_scope.

Theorem plain_rz_of_halts_pg : forall (LS : lib_shape) (CS : list byte -> list Z)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_pg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS G frame_RELRO GI j
       ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=LS) inp).
Proof.
  intros LS CS G GI HCS HG GIL GI0 Hp.
  apply (plain_rz_of_contracts_R LS (RI_P CS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    (driver_RI_P CS HCS) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem Hm => conj eq_refl (GI0 mem Hm))).
  intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
  apply (lib_contract_x_R_all_of_p (LS:=LS) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO _ _ _ _ _ HCS).
  intros fx j Hj.
  exact (lib_contract_p_of_pg (LS:=LS) (SH:=src0_sink_head) (SK:=src0_sink)
    src0_msyms (@zlib_API rc) CS G frame_RELRO GI j _ _ _ _ (Hp rc fx j Hj)).
Qed.

Theorem preset_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=checksum_shape) inp).
Proof.
  destruct OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AgreePresetH.preset_plain_halts_slot as (CS & HCS & HP).
  exact (plain_rz_of_halts_pg checksum_shape CS
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.LLVMFuzzerTestOneInput_c.slot_G
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Ledger.omx_GI src0_msyms) HCS
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Statement.slot_G_frame
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotGI.slot_G_local src0_msyms)
    (fun mem H => OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotGI.slot_GI_init src0_msyms mem
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.SlotTopG.ms_segs_rsegs H)
    HP).
Qed.
