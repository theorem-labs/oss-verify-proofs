From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO0o YO09 YL0g YL0i YI14 YI16 YL01 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract FrameAPI Img0 SlotKept SlotPack AllocPack
  AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_FLAGS : list Z := [0x318a4; 0x318a8; 0x318ac; 0x318b0].
Definition G_CAPSRC : Z := 0x318bc.
Definition G_SRC : Z := 0x318d0.
Definition G_NOUT : Z := 0x318e0.
Definition G_CAPOUT : Z := 0x318e8.
Definition G_OUT : Z := 0x318f0.
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

Definition frame_facts {rc : RunCeil} (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
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
  (forall (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition fuzz_reply_slot_p3 (CS : list byte -> list Z) (MC : list Z) : Prop :=
  CS_ok CS ->
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) (rc : RunCeil),
    frame_facts B API LS SH SK ra empty ->
    forall (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_cgp3 fx rc LS B (API rc) SH SK CS MC G_reply frame_RELRO GI_t j ENTRY ra empty SLOT_STACK.

Lemma wN_at_local : forall m m' a v w,
  (forall i, a <= i < a + Z.of_nat w -> mbyte rsegs m' i = mbyte rsegs m i) ->
  wN_at m a v w -> wN_at m' a v w.
Proof.
  intros m m' a v w EQ H k Hk. rewrite EQ by lia. apply H. exact Hk.
Qed.

Lemma in_G_data_t : forall a, G_DATA <= a < G_DATA + 16 -> in_globals G_reply a.
Proof. intros a H. exists 0x21620, 16. split; [left; reflexivity|unfold G_DATA in H; exact H]. Qed.

Lemma in_G_bss_t : forall a, 0x318a0 <= a < 0x318a0 + 512 -> in_globals G_reply a.
Proof. intros a H. exists 0x318a0, 512. split; [right; left; reflexivity|exact H]. Qed.

Lemma GI_reply_keep : forall j m m',
  (forall a, in_globals G_reply a -> mbyte rsegs m' a = mbyte rsegs m a) -> GI_reply j m -> GI_reply j m'.
Proof.
  intros j m m' EQ (H1 & H2 & H3 & H4 & H5).
  unfold GI_reply, byte_at, G_DATA, G_THREAD_UP, G_NSRC, G_LOCK, G_S in *.
  split; [|split; [|split; [|split]]]; intros i Hi.
  - rewrite EQ by (apply in_G_data_t; unfold G_DATA; lia). apply H1. exact Hi.
  - rewrite EQ by (apply in_G_bss_t; lia). apply H2. exact Hi.
  - rewrite EQ by (apply in_G_bss_t; lia). apply H3. exact Hi.
  - rewrite EQ by (apply in_G_bss_t; lia). apply H4. exact Hi.
  - rewrite EQ by (apply in_G_bss_t; lia). apply H5. exact Hi.
Qed.

Lemma GI_reply_img_t : forall mem,
  (forall a, in_globals G_reply a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)) -> GI_reply 0 mem.
Proof.
  intros mem H. unfold GI_reply, byte_at.
  split; [|split; [|split; [|split]]]; intros i Hi.
  - rewrite H by (apply in_G_data_t; lia). apply (img_is 255 G_DATA 16); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss_t; unfold G_THREAD_UP in *; lia).
    apply (img_is 0 G_THREAD_UP 1); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss_t; unfold G_NSRC in *; lia).
    apply (img_is 0 G_NSRC 4); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss_t; unfold G_LOCK in *; lia).
    apply (img_is 0 G_LOCK 40); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss_t; unfold G_S in *; lia).
    apply (img_is 0 G_S 384); [lia|vm_compute; reflexivity|exact Hi].
Qed.

Lemma GI_t_local : forall B, ms_segs B = rsegs -> G_local_t B G_reply GI_t.
Proof.
  intros B SEGS j T m m' EQ (H0 & HF & capsrc & src & nout & capout & out & H1 & H2 & H3 & H4 & H5 & HR).
  rewrite SEGS in EQ.
  assert (EQG : forall i, 0x318a0 <= i < 0x318a0 + 512 -> mbyte rsegs m' i = mbyte rsegs m i).
  { intros i Hi. apply EQ. left. apply in_G_bss_t. exact Hi. }
  split; [|split].
  - apply (GI_reply_keep j m m'); [|exact H0]. intros a Ha. apply EQ. left. exact Ha.
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
  (forall i, 0x318a0 <= i < 0x318a0 + 512 -> mbyte rsegs mem i = seg_rom rsegs (Z_to_bv 64 i)) ->
  0x318a0 <= a -> a + Z.of_nat w <= 0x318a0 + 512 -> (w <= 8)%nat ->
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
  assert (HG : forall a, in_globals G_reply a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. unfold G_img_c in H. rewrite SEGS in H. apply H. exact Ha. }
  assert (HB : forall i, 0x318a0 <= i < 0x318a0 + 512 -> mbyte rsegs mem i = seg_rom rsegs (Z_to_bv 64 i)).
  { intros i Hi. apply HG. apply in_G_bss_t. exact Hi. }
  split; [|split].
  - apply GI_reply_img_t. exact HG.
  - intros a Ha. left. unfold G_FLAGS in Ha. simpl in Ha.
    assert (Hr : 0x318a0 <= a < 0x318a0 + 512) by lia. rewrite (HB a Hr).
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
