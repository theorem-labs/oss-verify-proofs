From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO0o YO09 YL0g YL0i YI14 YI16 YL01 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract FrameAPI Img0 SlotKept SlotPack AllocPack
  AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_FLAGS : list Z := [0x30fc4; 0x30fc8; 0x30fcc; 0x30fd0].
Definition G_CAPSRC : Z := 0x30fdc.
Definition G_SRC : Z := 0x30ff0.
Definition G_NOUT : Z := 0x31000.
Definition G_CAPOUT : Z := 0x31008.
Definition G_OUT : Z := 0x31010.
Definition SRC_TABLE_BYTES : Z := 896.

Definition wN_at (m : word -> option byte) (a v : Z) (w : nat) : Prop :=
  forall k, (k < w)%nat -> mbyte rsegs m (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k)).

Definition flag_ok (m : word -> option byte) (a : Z) : Prop :=
  mbyte rsegs m a = Some (Z_to_bv 8 0) \/ mbyte rsegs m a = Some (Z_to_bv 8 1).

Definition kept_blocks (capsrc src capout out : Z) : list (Z * Z) :=
  (if capsrc =? 16 then [(src, SRC_TABLE_BYTES)] else []) ++ (if capout =? 0 then [] else [(out, capout)]).

Definition GI_t (j : nat) (T : list (Z * Z)) (m : word -> option byte) : Prop :=
  GI_reply j m /\ (forall a, In a G_FLAGS -> flag_ok m a) /\
  exists capsrc src nout capout out,
    wN_at m G_CAPSRC capsrc 4 /\ wN_at m G_SRC src 8 /\ wN_at m G_NOUT nout 8 /\
    wN_at m G_CAPOUT capout 8 /\ wN_at m G_OUT out 8 /\
    (capsrc = 0 \/ capsrc = 16) /\ (0 <= nout <= capout /\ capout <= TBBYTES) /\
    ((capout = 0 -> out = 0) /\ (capsrc = 0 -> src = 0)) /\
    T = kept_blocks capsrc src capout out.

Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x157a4 /\ ms_free B = 0x15664 /\ ms_realloc B = (Some 0x17010) /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x51500 /\ ms_got_guard B = 0x1fcf8 /\
  ms_ctx B = 0x51598 /\ ms_lock B = 0x51590 /\ ms_libc B = 0x51520 /\ ms_size_classes B = 0x10500 /\
  ms_small_cnt B = 0x10560 /\ ms_med_cnt B = 0x1057b /\ ms_debruijn B = 0x104e0 /\ ms_tp B = 0x31290 /\
  ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = (Some 0x51d74) /\
  @sk_ofl_head SH = 0x51950 /\ @sk_ofl_lock SK = 0x51948 /\ @sk_threaded SK = 0x51520 + 1 /\
  empty = 0x30fa0 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition fuzz_reply_slot_p3 (CS : list byte -> list Z) (MC : list Z) : Prop :=
  CS_ok CS ->
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts B API LS SH SK ra empty ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_cgp3 fx rc LS B (API rc) SH SK CS MC G_reply frame_RELRO GI_t j ENTRY ra empty SLOT_STACK.

Lemma wN_at_local : forall m m' a v w,
  (forall i, a <= i < a + Z.of_nat w -> mbyte rsegs m' i = mbyte rsegs m i) ->
  wN_at m a v w -> wN_at m' a v w.
Proof.
  intros m m' a v w EQ H k Hk. rewrite EQ by lia. apply H. exact Hk.
Qed.

Lemma GI_t_local : forall B, ms_segs B = rsegs -> G_local_t B G_reply GI_t.
Proof.
  intros B SEGS j T m m' EQ (H0 & HF & capsrc & src & nout & capout & out & H1 & H2 & H3 & H4 & H5 & HR).
  rewrite SEGS in EQ.
  assert (EQG : forall i, 0x30fc0 <= i < 0x30fc0 + 512 -> mbyte rsegs m' i = mbyte rsegs m i).
  { intros i Hi. apply EQ. left. apply in_G_bss. exact Hi. }
  split; [|split].
  - apply (GI_reply_local B SEGS j m m'); [|exact H0]. intros a Ha. rewrite SEGS. apply EQ. left. exact Ha.
  - intros a Ha. unfold flag_ok. rewrite EQG.
    + apply HF. exact Ha.
    + unfold G_FLAGS in Ha. simpl in Ha. lia.
  - exists capsrc, src, nout, capout, out.
    split; [apply (wN_at_local m); [intros i Hi; apply EQG; unfold G_CAPSRC in *; simpl in Hi; lia|exact H1]|].
    split; [apply (wN_at_local m); [intros i Hi; apply EQG; unfold G_SRC in *; simpl in Hi; lia|exact H2]|].
    split; [apply (wN_at_local m); [intros i Hi; apply EQG; unfold G_NOUT in *; simpl in Hi; lia|exact H3]|].
    split; [apply (wN_at_local m); [intros i Hi; apply EQG; unfold G_CAPOUT in *; simpl in Hi; lia|exact H4]|].
    split; [apply (wN_at_local m); [intros i Hi; apply EQG; unfold G_OUT in *; simpl in Hi; lia|exact H5]|].
    exact HR.
Qed.

Lemma img_zero_word : forall mem a w,
  (forall i, 0x30fc0 <= i < 0x30fc0 + 512 -> mbyte rsegs mem i = seg_rom rsegs (Z_to_bv 64 i)) ->
  0x30fc0 <= a -> a + Z.of_nat w <= 0x30fc0 + 512 -> (w <= 8)%nat ->
  forallb (fun i => rom_is 0 (a + i)) (map Z.of_nat (seq 0 w)) = true ->
  wN_at mem a 0 w.
Proof.
  intros mem a w H Ha Hb Hw Hz k Hk. rewrite H by lia.
  rewrite (img_is 0 a (Z.of_nat w)) by (try lia; rewrite Nat2Z.id; exact Hz).
  unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma GI_t_img : forall B, ms_segs B = rsegs -> forall mem, G_img_c B G_reply mem -> GI_t 0 [] mem.
Proof.
  intros B SEGS mem H.
  assert (HB : forall i, 0x30fc0 <= i < 0x30fc0 + 512 -> mbyte rsegs mem i = seg_rom rsegs (Z_to_bv 64 i)).
  { intros i Hi. unfold G_img_c in H. rewrite SEGS in H. apply H. apply in_G_bss. exact Hi. }
  split; [|split].
  - apply (GI_reply_img B SEGS mem H).
  - intros a Ha. left. unfold G_FLAGS in Ha. simpl in Ha.
    assert (Hr : 0x30fc0 <= a < 0x30fc0 + 512) by lia. rewrite (HB a Hr).
    destruct Ha as [<-|[<-|[<-|[<-|[]]]]]; apply rom_is_ok; try lia; vm_compute; reflexivity.
  - exists 0, 0, 0, 0, 0.
    split; [apply img_zero_word; [exact HB|unfold G_CAPSRC; lia|unfold G_CAPSRC; simpl; lia|lia|vm_compute; reflexivity]|].
    split; [apply img_zero_word; [exact HB|unfold G_SRC; lia|unfold G_SRC; simpl; lia|lia|vm_compute; reflexivity]|].
    split; [apply img_zero_word; [exact HB|unfold G_NOUT; lia|unfold G_NOUT; simpl; lia|lia|vm_compute; reflexivity]|].
    split; [apply img_zero_word; [exact HB|unfold G_CAPOUT; lia|unfold G_CAPOUT; simpl; lia|lia|vm_compute; reflexivity]|].
    split; [apply img_zero_word; [exact HB|unfold G_OUT; lia|unfold G_OUT; simpl; lia|lia|vm_compute; reflexivity]|].
    split; [left; reflexivity|].
    split; [split; [lia|unfold TBBYTES; apply Z.pow_nonneg; lia]|].
    split; [split; intros _; reflexivity|].
    reflexivity.
Qed.

Lemma GI_t_bound : TB_bound GI_t.
Proof.
  intros j T m (_ & _ & capsrc & src & nout & capout & out & _ & _ & _ & _ & _ & HC & HN & _ & ->).
  unfold kept_blocks. split.
  - destruct (capsrc =? 16), (capout =? 0); simpl; unfold TBMAX; lia.
  - intros t k Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (capsrc =? 16); [|destruct Hin]. destruct Hin as [Heq|[]]. inversion Heq.
      split; [unfold SRC_TABLE_BYTES; lia|]. unfold SRC_TABLE_BYTES, TBBYTES. apply Z.leb_le. reflexivity.
    + destruct (capout =? 0) eqn:E; [destruct Hin|]. destruct Hin as [Heq|[]]. inversion Heq; subst.
      apply Z.eqb_neq in E. lia.
Qed.
