From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger StatementPlain.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free (agreement) slot statement of fuzz_manifest's plain build: the twin of StatementPlain.slot_fill with
   lib_contract_cg (SlotAgree.v) in place of lib_contract_g, for an agreement frame. frame_facts_cg is
   StatementPlain.frame_facts with the agreement room (128 <= sb_cap b <= CAP_AG) in place of sb_cap b = CAPMAX in
   its lib_room conjunct; the slot also takes the cut-free allocator contracts and the source limit (LIMLAW: 2^34 <= vm_limit). *)
Definition frame_facts_cg (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x14ce0 /\ ms_free B = 0x14ba0 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4f6c8 /\ ms_got_guard B = 0x1e0b8 /\
    ms_ctx B = 0x4f760 /\ ms_lock B = 0x4f758 /\ ms_libc B = 0x4f6e8 /\ ms_size_classes B = 0x10502 /\
    ms_small_cnt B = 0x10562 /\ ms_med_cnt B = 0x1057d /\ ms_debruijn B = 0x104e1 /\ ms_tp B = 0x2f458 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 33 /\
    @sk_ofl_head SH = 0x4fb18 /\ @sk_ofl_lock SK = 0x4fb10 /\ @sk_threaded SK = 0x4f6e8 + 1 /\
    empty = 0x2f350 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition slot_fill_cg : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_cg B API LS SH SK ra empty ->
    (forall (rc : RunCeil) (fx : FPState), @malloc_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @free_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) L A mem md, aa_MR (API rc) L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_cg fx rc LS B (API rc) SH SK manifest_G frame_RELRO (omx_GI B) j ENTRY ra empty SLOT_STACK.
