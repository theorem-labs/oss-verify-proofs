From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom.
Local Open Scope Z_scope.

Definition frame_facts_ubsan (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z) : Prop :=
    ms_segs B = rsegs /\
    ms_malloc B = 0x16c7c /\ ms_free B = 0x16b3c /\ ms_realloc B = (Some 0x184e8) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x53e98 /\ ms_got_guard B = 0x22888 /\
    ms_ctx B = 0x53f30 /\ ms_lock B = 0x53f28 /\ ms_libc B = 0x53eb8 /\ ms_size_classes B = 0x10584 /\
    ms_small_cnt B = 0x105e4 /\ ms_med_cnt B = 0x105ff /\ ms_debruijn B = 0x10564 /\ ms_tp B = 0x33c28 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x542e8 /\ @sk_ofl_lock SK = 0x542e0 /\ @sk_threaded SK = 0x53eb8 + 1 /\
    empty = 0x33b20 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition slot_premise_ubsan : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_ubsan B API LS SH SK empty ->
    forall (rc : RunCeil) (fx : FPState), @fuzz_state_slot_contract fx rc LS B (API rc) SH SK empty.

Lemma omx_G_inside : forall a, in_globals omx_G a -> in_globals frame_G a.
Proof.
  intros a (lo & len & Hin & Hr). unfold frame_G, in_globals.
  cbn [omx_G In] in Hin. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
  - exists 0x33b40, 24. split; [right; left; reflexivity|lia].
  - exists 0x33b40, 24. split; [right; left; reflexivity|lia].
  - exists 0x33b40, 24. split; [right; left; reflexivity|lia].
  - exists 0x238c8, 8. split; [left; reflexivity|lia].
Qed.

Lemma omx_GI_local : forall (B : malloc_syms), G_local_c B omx_G (omx_GI B).
Proof.
  intros B j m m' Heq (peak & cnt & (W1 & W2 & W3 & W4) & HP & HC & HC2).
  assert (T : forall g v, In (g, 8) omx_G -> word_mem (ms_segs B) m g v -> word_mem (ms_segs B) m' g v).
  { intros g v Hg W k Hk. rewrite Heq; [apply W; exact Hk|].
    exists g, 8. split; [exact Hg|lia]. }
  exists peak, cnt. split; [|split; [exact HP|split; [exact HC|exact HC2]]].
  unfold alloc_words. split; [|split; [|split]]; apply T; try assumption; cbn [omx_G In]; tauto.
Qed.

Theorem ubsan_halts_of_frame : frame_ubsan -> slot_premise_ubsan -> Statements.ubsan_halts.
Proof.
  intros (B & API & LS & SH & SK & ra & empty & HS & HR & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & HF) SLOT.
  apply (HF omx_G (omx_GI B)).
  - exact omx_G_inside.
  - apply omx_GI_local.
  - intros mem HI. apply omx_GI_init; [exact HS|exact HI].
  - intros rc fx j Hj.
    refine (SLOT B API LS SH SK empty _ rc fx j ra Hj HR).
    unfold frame_facts_ubsan. tauto.
Qed.
