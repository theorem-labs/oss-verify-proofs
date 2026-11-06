From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.libreac.fuzz_pcap Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := (symaddr Symbols.Ubsan.s_LLVMFuzzerTestOneInput).
Definition SLOT_STACK : Z := 65536.
Definition frame_G : list (Z * Z) := [((symaddr (Symbols.Ubsan.s___stderr_FILE + 0x88)%Z), 4); ((symaddr Symbols.Ubsan.s_g_file_len), 16)].
Definition frame_RELRO : list (Z * Z) := [((symaddr Symbols.Ubsan.s___init), 160); ((symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z), 16); ((symaddr Symbols.Ubsan.s___stderr_FILE), 136); ((symaddr (Symbols.Ubsan.s___stderr_FILE + 0x8c)%Z), 92)].

Lemma wx_apart_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Definition frame_allocator {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract B API /\ free_contract B API /\ free_null_contract B /\
  (forall pc, ms_realloc B = Some pc -> realloc_contract B API pc /\ realloc_null_contract B API pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract B API pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\ libc_no_locks B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a).

Definition frame_ubsan : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = (symaddr Symbols.Ubsan.s_malloc) /\ ms_free B = (symaddr Symbols.Ubsan.s_free) /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = (symaddr Symbols.Ubsan.s___stack_chk_guard) /\ ms_got_guard B = (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) /\
    ms_ctx B = (symaddr Symbols.Ubsan.s___malloc_context) /\ ms_lock B = (symaddr Symbols.Ubsan.s___malloc_lock) /\ ms_libc B = (symaddr Symbols.Ubsan.s___libc) /\ ms_size_classes B = (symaddr Symbols.Ubsan.s___malloc_size_classes) /\
    ms_small_cnt B = (symaddr Symbols.Ubsan.s_small_cnt_tab) /\ ms_med_cnt B = (symaddr Symbols.Ubsan.s_med_cnt_tab) /\ ms_debruijn B = (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x1c4)%Z) /\ ms_tp B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0xc8)%Z) /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = (symaddr Symbols.Ubsan.s_ofl_head) /\ @sk_ofl_lock SK = (symaddr Symbols.Ubsan.s_ofl_lock) /\ @sk_threaded SK = (symaddr Symbols.Ubsan.s___libc) + 1 /\
    empty = (symaddr Symbols.Ubsan.s_oft_aligned_copy_empty) /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (f : list byte -> list byte) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).

Definition frame_facts_ubsan (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = (symaddr Symbols.Ubsan.s_malloc) /\ ms_free B = (symaddr Symbols.Ubsan.s_free) /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = (symaddr Symbols.Ubsan.s___stack_chk_guard) /\ ms_got_guard B = (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) /\
    ms_ctx B = (symaddr Symbols.Ubsan.s___malloc_context) /\ ms_lock B = (symaddr Symbols.Ubsan.s___malloc_lock) /\ ms_libc B = (symaddr Symbols.Ubsan.s___libc) /\ ms_size_classes B = (symaddr Symbols.Ubsan.s___malloc_size_classes) /\
    ms_small_cnt B = (symaddr Symbols.Ubsan.s_small_cnt_tab) /\ ms_med_cnt B = (symaddr Symbols.Ubsan.s_med_cnt_tab) /\ ms_debruijn B = (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x1c4)%Z) /\ ms_tp B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0xc8)%Z) /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = (symaddr Symbols.Ubsan.s_ofl_head) /\ @sk_ofl_lock SK = (symaddr Symbols.Ubsan.s_ofl_lock) /\ @sk_threaded SK = (symaddr Symbols.Ubsan.s___libc) + 1 /\
    empty = (symaddr Symbols.Ubsan.s_oft_aligned_copy_empty) /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma frame_ubsan_split : frame_ubsan ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B API LS SH SK ra empty /\
    (forall (f : list byte -> list byte) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_ubsan. tauto.
Qed.
