From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0 FrameAPI SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

(* #102 pins (agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan, sha256 27566683...):
   LLVMFuzzerTestOneInput FUNC GLOBAL 0x13718 size 336, addi sp, sp, -0x70 (no UBSan check in it since read_members is
   out of line). SLOT_K = 112 + CRT_K, the largest callee stack of the entry (U check_round_trip_c.CRT_K = 14592 on these
   pins). slot_G = U/Prog/LedgerCells.GL_runs (RwLedger's generated cell list, by name): g_fail_at and g_most, then
   g_own_ran_out, g_ran_out, g_live, g_peak, g_count, with their padding: the bytes of frame_G and of omx_G, which the
   entry writes. *)
Definition LLVMFUZZERTESTONEINPUT : Z := 0x13718.
Definition SLOT_K : Z := 14704.
Definition slot_G : list (Z * Z) := GL_runs.

Section Slot.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

(* by symbol in the #102 ubsan twin: default_malloc 0x18390, free 0x18250, realloc 0x19bfc, __stack_chk_guard 0x555b8,
   its GOT slot .got+0x80 = 0x23f98, builtin_tls+0xc8 = 0x35348 *)
Definition slot_syms : Prop :=
  ms_segs B = rsegs /\
  ms_malloc B = 0x18390 /\ ms_free B = 0x18250 /\ ms_realloc B = Some 0x19bfc /\
  ms_guard B = 0x555b8 /\ ms_got_guard B = 0x23f98 /\
  ms_tp B = 0x35348 /\ ms_errno_off B = -164.

Definition slot_apart (a : Z) : Prop :=
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

Definition slot_globals : Prop :=
  forall a, in_globals slot_G a -> slot_apart a.

Definition slot_sink_cell (a : Z) : Prop :=
  (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4).

Definition slot_sinks : Prop :=
  forall a, slot_sink_cell a -> slot_apart a /\ ~ in_globals slot_G a.

Definition slot_shape : Prop :=
  (forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) /\
  (forall n b, lib_delta n b = b).

Definition LLVMFuzzerTestOneInput_contract (CS : list byte -> list Z) : Prop :=
  forall ra empty stk,
    slot_syms ->
    slot_globals ->
    slot_sinks ->
    (forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @frame_allocator rc fx' B API) ->
    slot_shape ->
    ra mod 2 = 0 ->
    empty = 0x35230 ->
    0 < empty < 2 ^ 62 ->
    SLOT_K <= stk ->
    forall j, (j < 4)%nat ->
      lib_contract_pg B API CS slot_G frame_RELRO (omx_GI B) j LLVMFUZZERTESTONEINPUT ra empty stk.

End Slot.
