From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 FrameAPI SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

(* #102 pins (agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain, sha256 c8f4d6b8...):
   LLVMFuzzerTestOneInput FUNC GLOBAL 0x13628 size 336, addi sp, sp, -0x70. SLOT_K = 112 + CRT_K, the largest callee
   stack of the entry (check_round_trip_c.CRT_K = 14064 on these pins). slot_G = LedgerCells.GL_runs (RwLedger's generated
   cell list, by name): g_fail_at and g_most, then g_own_ran_out, g_ran_out, g_live, g_peak, g_count, with their padding:
   the bytes of frame_G and of omx_G, which the entry writes (g_own_ran_out at 0x1365c, g_ran_out by
   fuzz_alloc_ran_out_reset, g_most by fuzz_alloc_most, the alloc statics by the reader). *)
Definition LLVMFUZZERTESTONEINPUT : Z := 0x13628.
Definition SLOT_K : Z := 14176.
Definition slot_G : list (Z * Z) := GL_runs.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

(* by symbol in the #102 plain twin: default_malloc 0x178d8, free 0x17798, realloc 0x19144, __stack_chk_guard 0x54b08,
   its GOT slot .got+0x80 = 0x234e0 (it holds 0x54b08), builtin_tls+0xc8 = 0x34898 *)
Definition slot_syms : Prop :=
  ms_segs B = rsegs /\
  ms_malloc B = 0x178d8 /\ ms_free B = 0x17798 /\ ms_realloc B = Some 0x19144 /\
  ms_guard B = 0x54b08 /\ ms_got_guard B = 0x234e0 /\
  ms_tp B = 0x34898 /\ ms_errno_off B = -164.

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
    (forall fx' : YK11.FPState, @frame_allocator rc fx' B API) ->
    slot_shape ->
    ra mod 2 = 0 ->
    empty = 0x34780 ->
    0 < empty < 2 ^ 62 ->
    SLOT_K <= stk ->
    forall j, (j < 4)%nat ->
      lib_contract_pg B API CS slot_G frame_RELRO (omx_GI B) j LLVMFUZZERTESTONEINPUT ra empty stk.

End Slot.
