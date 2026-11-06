From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI AllocCut BlocksNodup FrameSlotG Img0 ReallocCert.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Definition plain_ivl_b (B : malloc_syms) (lo hi : Z) : bool :=
  negb (match ms_segs B with [] => true | _ => false end) &&
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved (ms_segs B)) &&
  forallb (fun q => (hi <=? fst q) || (snd q <=? lo)) (forbidden_ivl B).
Ltac in_list := solve [cbn [In]; repeat (first [left; reflexivity | right])].
Lemma plain_ivl_sound : forall B lo hi a, plain_ivl_b B lo hi = true -> lo <= a < hi ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros B lo hi a H Ha. unfold plain_ivl_b in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [Hne Hs].
  apply existsb_exists in Hs as (sg & Hsg & Hb). apply andb_prop in Hb as [S1 S2].
  apply Z.leb_le in S1. apply Z.leb_le in S2. rewrite forallb_forall in Hf.
  assert (HF : forall q, In q (forbidden_ivl B) -> fst q <= a < snd q -> False).
  { intros q Hq Hx. specialize (Hf q Hq). apply orb_prop in Hf as [D|D]; apply Z.leb_le in D; lia. }
  unfold forbidden_ivl in HF.
  split; [|split; [|split]].
  - split; [destruct (ms_segs B) as [|s l]; [discriminate Hne | discriminate] |].
    exists sg. split; [exact Hsg | lia].
  - intros Hso. unfold static_owned in Hso.
    destruct Hso as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]];
      first
        [ match goal with X : ?l <= a < ?h |- _ => apply (HF (l, h)); [in_list | cbn [fst snd]; lia] end
        | apply (HF (ms_libc B + 3, ms_libc B + 4)); [in_list | cbn [fst snd]; lia] ].
  - intros X. match goal with X : ?l <= a < ?h |- _ => apply (HF (l, h)); [in_list | cbn [fst snd]; lia] end.
  - intros X. match goal with X : ?l <= a < ?h |- _ => apply (HF (l, h)); [in_list | cbn [fst snd]; lia] end.
Qed.
Lemma plain_ivls_sound : forall B G a,
  forallb (fun p => plain_ivl_b B (fst p) (fst p + snd p)) G = true -> in_globals G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros B G a H (lo & len & Hin & Ha). rewrite forallb_forall in H.
  exact (plain_ivl_sound B lo (lo + len) a (H _ Hin) Ha).
Qed.
Lemma frame_G_facts : forall a, in_globals frame_G a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\
  ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4).
Proof. intros a Ha. exact (plain_ivls_sound src0_msyms frame_G a ltac:(vm_compute; reflexivity) Ha). Qed.
Lemma frame_RELRO_facts : forall a, in_globals frame_RELRO a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\
  ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4).
Proof. intros a Ha. exact (plain_ivls_sound src0_msyms frame_RELRO a ltac:(vm_compute; reflexivity) Ha). Qed.
Lemma not_owned_of_facts : forall (rc : RunCeil) L A mem md a,
  aa_MR (@zlib_API rc) L A mem md -> in_img src0_msyms a -> ~ static_owned src0_msyms a ->
  ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) -> ~ owned src0_msyms L A a.
Proof.
  intros rc L A mem md a HM Himg Hst Hctx [Ho|Ho].
  - exact (Hctx (ax_img (@zlib_allocator_extra rc) L A mem md a HM Himg Ho)).
  - exact (Hst Ho).
Qed.
Lemma errno_below_ceiling : forall rc : RunCeil, errno_addr src0_msyms + 4 <= @alloc_ceiling rc.
Proof.
  intros rc. pose proof (@alloc_ceiling_value rc) as [[H _] _].
  assert (E : errno_addr src0_msyms + 4 <= CEIL_MIN) by (apply Z.leb_le; vm_compute; reflexivity).
  lia.
Qed.
Lemma ctx_not_ro : forall a, ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE ->
  Mem.ro_addr (ms_segs src0_msyms) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  exact (ro_false_range (ms_segs src0_msyms) (ms_ctx src0_msyms) CTX_SIZE a ltac:(vm_compute; reflexivity) Ha).
Qed.
Lemma zlib_frame_allocator : forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx src0_msyms (@zlib_API rc).
Proof.
  intros rc fx.
  pose proof (@zlib_allocator_extra rc) as AX.
  assert (HB : ro_apart_b src0_msyms = true) by (vm_compute; reflexivity).
  assert (HX : forall L A mem md, aa_MR (@zlib_API rc) L A mem md -> MRx src0_msyms L A mem md)
    by (intros L A mem md H; exact H).
  split; [exact (malloc_contract_ok src0_msyms (@zlib_API rc) AX HB)|].
  split; [exact (free_contract_ok src0_msyms (@zlib_API rc) AX HB)|].
  split; [exact (free_null_contract_ok src0_msyms (@zlib_API rc))|].
  split; [exact zlib_realloc|].
  split; [intros pc _; exact (calloc_contract_ok src0_msyms (@zlib_API rc) AX HB pc)|].
  split; [exact (block_slack_present_ok src0_msyms (@zlib_API rc) HX)|].
  split; [exact (ctx_owned_ok src0_msyms (@zlib_API rc) HX)|].
  split; [exact (blocks_low_ok src0_msyms (@zlib_API rc))|].
  split; [exact (blocks_nodup_ok src0_msyms (@zlib_API rc) HX)|].
  split; [exact (blocks_writable_ok src0_msyms (@zlib_API rc))|].
  split; [exact (errno_unowned_ok src0_msyms (@zlib_API rc) AX src0_errno_check)|].
  split; [exact (guard_rw_ok src0_msyms (@zlib_API rc) ltac:(vm_compute; reflexivity))|].
  try (split; [exact (libc_no_locks_ok src0_msyms (@zlib_API rc) AX)|]).
  split; [exact AX|].
  split.
  - intros L A mem md a HM Ha. destruct (frame_G_facts a Ha) as (Himg & Hst & Hctx & _).
    exact (not_owned_of_facts rc L A mem md a HM Himg Hst Hctx).
  - intros L A mem md a HM Ha. destruct (frame_RELRO_facts a Ha) as (Himg & Hst & Hctx & _).
    exact (not_owned_of_facts rc L A mem md a HM Himg Hst Hctx).
Qed.
Theorem frame_plain_holds : frame_plain.
Proof.
  exists src0_msyms, (@zlib_API), checksum_shape, src0_sink_head, src0_sink, RA_LIB, EMPTY.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|].
  split; [exact frame_G_facts|].
  split; [exact frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split; [intros b n H; exact H|].
  split; [exact zlib_frame_allocator|].
  exact plain_halts_of_frame_slot.
Qed.
