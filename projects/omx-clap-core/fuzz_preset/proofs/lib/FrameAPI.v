From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract SlotKept SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import LedgerCells.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := 0x13628.
Definition SLOT_STACK : Z := 65536.
(* the alloc.c / harness cells the entry writes, by name: RwLedger's generated LedgerCells.GL_runs *)
Definition frame_G : list (Z * Z) := GL_runs.
Definition frame_RELRO : list (Z * Z) := [(0x23440, 160); (0x234e8, 16)].

Lemma wx_apart_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Definition frame_allocator {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract_r B API pack_form /\ free_contract_r B API pack_form /\ free_null_contract B /\
  (forall pc, ms_realloc B = Some pc ->
     realloc_contract_r B API pack_form pc /\ realloc_null_contract_r B API pack_form pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract_r B API pack_form pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\ libc_no_locks B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a).

Definition frame_plain : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x178d8 /\ ms_free B = 0x17798 /\ ms_realloc B = (Some 0x19144) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x54b08 /\ ms_got_guard B = 0x234e0 /\
    ms_ctx B = 0x54ba0 /\ ms_lock B = 0x54b98 /\ ms_libc B = 0x54b28 /\ ms_size_classes B = 0x10570 /\
    ms_small_cnt B = 0x105d0 /\ ms_med_cnt B = 0x105eb /\ ms_debruijn B = 0x10550 /\ ms_tp B = 0x34898 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x54f58 /\ @sk_ofl_lock SK = 0x54f50 /\ @sk_threaded SK = 0x54b28 + 1 /\
    empty = 0x34780 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (CS : list byte -> list Z) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       CS_ok CS ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_pg fx rc LS B (API rc) SH SK CS G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.plain_halts).

Definition frame_facts_plain (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x178d8 /\ ms_free B = 0x17798 /\ ms_realloc B = (Some 0x19144) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x54b08 /\ ms_got_guard B = 0x234e0 /\
    ms_ctx B = 0x54ba0 /\ ms_lock B = 0x54b98 /\ ms_libc B = 0x54b28 /\ ms_size_classes B = 0x10570 /\
    ms_small_cnt B = 0x105d0 /\ ms_med_cnt B = 0x105eb /\ ms_debruijn B = 0x10550 /\ ms_tp B = 0x34898 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x54f58 /\ @sk_ofl_lock SK = 0x54f50 /\ @sk_threaded SK = 0x54b28 + 1 /\
    empty = 0x34780 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma frame_plain_split : frame_plain ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_plain B API LS SH SK ra empty /\
    (forall (CS : list byte -> list Z) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       CS_ok CS ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_pg fx rc LS B (API rc) SH SK CS G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.plain_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_plain. tauto.
Qed.
