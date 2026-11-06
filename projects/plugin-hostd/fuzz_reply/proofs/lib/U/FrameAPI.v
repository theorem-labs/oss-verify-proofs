From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract SlotKept SlotPack AllocPack3 ContractT SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := 0x1409c.
Definition SLOT_STACK : Z := 65536.
Definition frame_G : list (Z * Z) := [(0x21620, 16); (0x318a0, 512)].
Definition frame_RELRO : list (Z * Z) := [(0x20540, 160); (0x205e8, 16)].
Definition frame_MCAP : list Z := repeat 27 49.

Lemma wx_apart_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Definition frame_allocator {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract_rt B API pack3_form /\ free_contract_rt B API pack3_form /\ free_null_contract B /\
  (forall pc, ms_realloc B = Some pc ->
     realloc_contract_rt B API pack3_form pc /\ realloc_null_contract_rt B API pack3_form pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract_rt B API pack3_form pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a).

Definition frame_ubsan : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x1608c /\ ms_free B = 0x15f4c /\ ms_realloc B = (Some 0x178f8) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x51de0 /\ ms_got_guard B = 0x205e0 /\
    ms_ctx B = 0x51e78 /\ ms_lock B = 0x51e70 /\ ms_libc B = 0x51e00 /\ ms_size_classes B = 0x10500 /\
    ms_small_cnt B = 0x10560 /\ ms_med_cnt B = 0x1057b /\ ms_debruijn B = 0x104e0 /\ ms_tp B = 0x31b70 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = (Some 0x52654) /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x52230 /\ @sk_ofl_lock SK = 0x52228 /\ @sk_threaded SK = 0x51e00 + 1 /\
    empty = 0x31880 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (CS : list byte -> list Z) (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_t B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat [] mem) ->
       TB_bound GI ->
       CS_ok CS ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_p3 fx rc LS B (API rc) SH SK CS frame_MCAP G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).

Definition frame_facts_ubsan (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x1608c /\ ms_free B = 0x15f4c /\ ms_realloc B = (Some 0x178f8) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x51de0 /\ ms_got_guard B = 0x205e0 /\
    ms_ctx B = 0x51e78 /\ ms_lock B = 0x51e70 /\ ms_libc B = 0x51e00 /\ ms_size_classes B = 0x10500 /\
    ms_small_cnt B = 0x10560 /\ ms_med_cnt B = 0x1057b /\ ms_debruijn B = 0x104e0 /\ ms_tp B = 0x31b70 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = (Some 0x52654) /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x52230 /\ @sk_ofl_lock SK = 0x52228 /\ @sk_threaded SK = 0x51e00 + 1 /\
    empty = 0x31880 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma frame_ubsan_split : frame_ubsan ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B API LS SH SK ra empty /\
    (forall (CS : list byte -> list Z) (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_t B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat [] mem) ->
       TB_bound GI ->
       CS_ok CS ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_p3 fx rc LS B (API rc) SH SK CS frame_MCAP G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_ubsan. tauto.
Qed.
