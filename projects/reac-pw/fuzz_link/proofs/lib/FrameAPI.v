(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths, module names and addresses changed; 76 of its 104 lines of code are new or changed and 139 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract OutForm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile MemFileRI StdioExitMF.
From OSSVerify.reac_pw.fuzz_link Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := 0x1384c.
Definition SLOT_STACK : Z := 65536.
(* The image bytes one slot call may change (the post's image clause keeps every other one), each read from
   link's plain image and checked against the .symtab of its unstripped twin: (0x219a0, 4) __stderr_FILE + 136
   (its orientation); link's harness globals g_nl (0x31b80, 271992), g_names (0x741f8, 512) and
   msg_build.long_alias (0x743f8, 301) (fuzz_link.c); the memory FILE's globals MemFile.mf_globals: g_sink
   (0x74528, 8), g_said (0x74530, 4096), g_say (0x75530, 8) and musl's open-file list head ofl_head
   (0x95cc8, 8). *)
Definition frame_G : list (Z * Z) :=
  [(0x219a0, 4); (0x31b80, 271992); (0x741f8, 512); (0x743f8, 301);
  (0x74528, 8); (0x74530, 4096); (0x75530, 8); (0x95cc8, 8)].
Definition frame_RELRO : list (Z * Z) := [(0x207b0, 296); (0x208e0, 16); (0x21918, 136); (0x219a4, 92)].

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

Definition frame_plain : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x17514 /\ ms_free B = 0x173d4 /\ ms_realloc B = None /\ ms_calloc B = (Some 0x1729c) /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x95878 /\ ms_got_guard B = 0x208d8 /\
    ms_ctx B = 0x95910 /\ ms_lock B = 0x95908 /\ ms_libc B = 0x95898 /\ ms_size_classes B = 0x10798 /\
    ms_small_cnt B = 0x107f8 /\ ms_med_cnt B = 0x10813 /\ ms_debruijn B = 0x10778 /\ ms_tp B = 0x75608 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x95cc8 /\ @sk_ofl_lock SK = 0x95cc0 /\ @sk_threaded SK = 0x95898 + 1 /\
    empty = 0x31b60 /\ 0 < empty < 2 ^ 62 /\
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
       (forall j m, GI j m -> @mf_heads B SH link_mf m 0) ->
       (forall rc : RunCeil, mwrite_exit_contract_all B (API rc)) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.plain_halts).

Definition frame_facts_plain (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x17514 /\ ms_free B = 0x173d4 /\ ms_realloc B = None /\ ms_calloc B = (Some 0x1729c) /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x95878 /\ ms_got_guard B = 0x208d8 /\
    ms_ctx B = 0x95910 /\ ms_lock B = 0x95908 /\ ms_libc B = 0x95898 /\ ms_size_classes B = 0x10798 /\
    ms_small_cnt B = 0x107f8 /\ ms_med_cnt B = 0x10813 /\ ms_debruijn B = 0x10778 /\ ms_tp B = 0x75608 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x95cc8 /\ @sk_ofl_lock SK = 0x95cc0 /\ @sk_threaded SK = 0x95898 + 1 /\
    empty = 0x31b60 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

(** ** The T form: the slot keeps the memory FILE

    [frame_plain] asks of ENTRY a contract whose post leaves no block live ([lib_contract_o]'s
    [res_ok_slots A' (lib_delta n b)]). From link's first mark the FILE block (1304 bytes) IS live at the
    return, so that form is not what link's slot satisfies. [frame_plain_mf] asks the T form of
    Reusable/YL0i.v at the memory-FILE shape [mf_shape] (MemFileRI.v) instead: the post carries the kept
    blocks [T] and the bound [TD T T' (lib_delta n b)], and the slot's GI stays a PARAMETER with four
    generic hypotheses, one of which is that it implies the GI conjunct [mf_gi]. The frame also takes the
    exit's mwrite premise [mwrite_exit_contract_all] (lib/StdioExitMF.v). *)
Definition frame_plain_mf : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_plain B API LS SH SK ra empty /\
    (forall (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_T (ms_segs B) G GI ->
       (forall mem, G_img (ms_segs B) G mem -> GI 0%nat [] mem) ->
       (forall j T m, GI j T m -> @mf_gi B SH link_mf T m) ->
       (forall rc : RunCeil, mwrite_exit_contract_all B (API rc)) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_x_T fx rc mf_shape B (API rc) SH SK G frame_RELRO GI (fun _ => []) j ENTRY ra empty
            SLOT_STACK) ->
       Statements.plain_halts).

Lemma frame_plain_split : frame_plain ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_plain B API LS SH SK ra empty /\
    (forall (f : list byte -> list byte) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall j m, GI j m -> @mf_heads B SH link_mf m 0) ->
       (forall rc : RunCeil, mwrite_exit_contract_all B (API rc)) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.plain_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_plain. tauto.
Qed.
