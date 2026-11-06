From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition manifest_G : list (Z * Z) := [(G_LIVE, 24); (G_FAIL, 8)].

Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x14f8c /\ ms_free B = 0x14e4c /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4f978 /\ ms_got_guard B = 0x1e368 /\
    ms_ctx B = 0x4fa10 /\ ms_lock B = 0x4fa08 /\ ms_libc B = 0x4f998 /\ ms_size_classes B = 0x10508 /\
    ms_small_cnt B = 0x10568 /\ ms_med_cnt B = 0x10583 /\ ms_debruijn B = 0x104e8 /\ ms_tp B = 0x2f708 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x4fdc8 /\ @sk_ofl_lock SK = 0x4fdc0 /\ @sk_threaded SK = 0x4f998 + 1 /\
    empty = 0x2f600 /\ 0 < empty < 2 ^ 62 /\
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

Definition slot_fill : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts B API LS SH SK ra empty ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_g fx rc LS B (API rc) SH SK manifest_G frame_RELRO (omx_GI B) j ENTRY ra empty SLOT_STACK.

Lemma manifest_G_sub : forall a, in_globals manifest_G a -> in_globals frame_G a.
Proof.
  intros a (lo & len & Hin & Hr). unfold manifest_G, frame_G, G_LIVE, G_FAIL in *.
  destruct Hin as [E | [E | []]]; inversion E; subst.
  - exists 0x2f620, 24. split; [right; left; reflexivity | lia].
  - exists 0x1f3a8, 8. split; [left; reflexivity | lia].
Qed.

Lemma word_mem_local : forall segs m m' a v,
  (forall i, 0 <= i < 8 -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  word_mem segs m a v -> word_mem segs m' a v.
Proof.
  intros segs m m' a v E W k Hk. rewrite E by lia. apply W. exact Hk.
Qed.

Lemma omx_GI_local : forall (B : malloc_syms), G_local_c B manifest_G (omx_GI B).
Proof.
  intros B j m m' E (peak & cnt & (W1 & W2 & W3 & W4) & HP & HC & HC2).
  exists peak, cnt. split; [|tauto].
  unfold alloc_words.
  assert (L : forall a i, in_globals manifest_G (a + i) ->
             mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) by (intros; apply E; assumption).
  unfold manifest_G, in_globals, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  repeat split; eapply word_mem_local; try eassumption; intros i Hi; apply L;
    first [ exists 0x2f620, 24; split; [left; reflexivity | lia]
          | exists 0x1f3a8, 8; split; [right; left; reflexivity | lia] ].
Qed.

Lemma omx_GI_img : forall (B : malloc_syms) mem,
  ms_segs B = rsegs -> G_img_c B manifest_G mem -> omx_GI B 0 mem.
Proof.
  intros B mem HS GI.
  assert (R : forall a, in_globals manifest_G a -> mbyte (ms_segs B) mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite (GI a Ha), HS. reflexivity. }
  exists 0, 0. unfold alloc_words.
  unfold manifest_G, in_globals, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  repeat split; try lia; intros k Hk; rewrite R;
    try first [ exists 0x2f620, 24; split; [left; reflexivity | lia]
              | exists 0x1f3a8, 8; split; [right; left; reflexivity | lia] ];
    do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.

Theorem ubsan_halts_of_frame : slot_fill -> frame_ubsan -> Statements.ubsan_halts.
Proof.
  intros SLOT (B & API & LS & SH & SK & ra & empty & H).
  repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end.
  match goal with
  | TOP : forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop), _ |- _ =>
      apply (TOP manifest_G (omx_GI B))
  end.
  - exact manifest_G_sub.
  - apply omx_GI_local.
  - intros mem Hm. apply omx_GI_img; assumption.
  - intros rc fx j Hj.
    apply (SLOT B API LS SH SK ra empty); [unfold frame_facts; repeat match goal with |- _ /\ _ => split end; assumption | exact Hj].
Qed.
