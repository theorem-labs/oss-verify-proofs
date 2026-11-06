From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import FrameAPI Img0.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_SPILL : Z := 0x33ff0.
Definition G_REC_A : Z := 0x34028.
Definition G_QUIT_A : Z := 0x343e8.

Definition G_cmd : list (Z * Z) := frame_G.

Definition zero_at (m : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> mbyte rsegs m (a + i) = Some (Z_to_bv 8 0).

Definition GI_cmd (j : nat) (m : word -> option byte) : Prop :=
  zero_at m (G_REC_A + 8) 4 /\ zero_at m (G_REC_A + 912) 12 /\ zero_at m (G_REC_A + 928) 16 /\
  zero_at m G_SPILL 8 /\ zero_at m G_QUIT_A 4.

Definition frame_given_u (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x18c10 /\ ms_free B = 0x18ad0 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x54730 /\ ms_got_guard B = 0x22d40 /\
    ms_ctx B = 0x547c8 /\ ms_lock B = 0x547c0 /\ ms_libc B = 0x54750 /\ ms_size_classes B = 0x10c00 /\
    ms_small_cnt B = 0x10c60 /\ ms_med_cnt B = 0x10c7b /\ ms_debruijn B = 0x10be0 /\ ms_tp B = 0x344c0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\
    @sk_ofl_head SH = 0x54b80 /\ @sk_ofl_lock SK = 0x54b78 /\ @sk_threaded SK = 0x54750 + 1 /\
    empty = 0x33fd0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAP_AG) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition fuzz_command_slot_u : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_given_u B API LS SH SK ra empty -> ms_debruijn_len B = 32 ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_cg fx rc LS B (API rc) SH SK G_cmd frame_RELRO GI_cmd j ENTRY ra empty SLOT_STACK.

Lemma zseq_forall : forall (f : Z -> bool) n, forallb f (map Z.of_nat (seq 0 n)) = true ->
  forall i, 0 <= i < Z.of_nat n -> f i = true.
Proof.
  intros f n H i Hi. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat i). split; [Lia.lia|]. apply in_seq. Lia.lia.
Qed.

Definition rom0 (a : Z) : bool :=
  match seg_rom rsegs (Z_to_bv 64 a) with Some b => bv_unsigned b =? 0 | None => false end.

Lemma rom0_ok : forall a, rom0 a = true -> seg_rom rsegs (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a H. unfold rom0 in H. destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|]; [|discriminate].
  f_equal. apply bv_eq. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma img_zero : forall a n, forallb (fun i => rom0 (a + i)) (map Z.of_nat (seq 0 (Z.to_nat n))) = true ->
  forall i, 0 <= i < n -> seg_rom rsegs (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Proof.
  intros a n H i Hi. apply rom0_ok.
  apply (zseq_forall (fun i => rom0 (a + i)) (Z.to_nat n) H). Lia.lia.
Qed.

Lemma gi_in_G : forall a, G_SPILL <= a < G_SPILL + 1020 -> in_globals G_cmd a.
Proof. intros a H. exists G_SPILL, 1020. split; [left; reflexivity | exact H]. Qed.

Lemma GI_cmd_local : forall B, ms_segs B = rsegs -> G_local_c B G_cmd GI_cmd.
Proof.
  intros B SEGS j m m' EQ (H1 & H2 & H3 & H4 & H5).
  rewrite SEGS in EQ.
  unfold GI_cmd, zero_at, G_SPILL, G_REC_A, G_QUIT_A in *.
  repeat split; intros i Hi; rewrite EQ by (apply gi_in_G; unfold G_SPILL; Lia.lia);
    [apply H1 | apply H2 | apply H3 | apply H4 | apply H5]; exact Hi.
Qed.

Lemma GI_cmd_img : forall B, ms_segs B = rsegs -> forall mem, G_img_c B G_cmd mem -> GI_cmd 0 mem.
Proof.
  intros B SEGS mem H. unfold G_img_c in H. rewrite SEGS in H.
  unfold GI_cmd, zero_at, G_SPILL, G_REC_A, G_QUIT_A.
  unfold G_SPILL in *.
  repeat split; intros i Hi; rewrite H by (apply gi_in_G; unfold G_SPILL; Lia.lia).
  - apply (img_zero _ 4); [vm_compute; reflexivity | exact Hi].
  - apply (img_zero _ 12); [vm_compute; reflexivity | exact Hi].
  - apply (img_zero _ 16); [vm_compute; reflexivity | exact Hi].
  - apply (img_zero _ 8); [vm_compute; reflexivity | exact Hi].
  - apply (img_zero _ 4); [vm_compute; reflexivity | exact Hi].
Qed.
