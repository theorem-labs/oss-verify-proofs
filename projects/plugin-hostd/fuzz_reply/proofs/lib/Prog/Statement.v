From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract FrameAPI Img0.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_DATA : Z := 0x20d38.
Definition G_THREAD_UP : Z := 0x30fc0.
Definition G_NSRC : Z := 0x30fd8.
Definition G_LOCK : Z := 0x31018.
Definition G_S : Z := 0x31040.

Definition G_reply : list (Z * Z) := frame_G.

Definition byte_at (m : word -> option byte) (a v n : Z) : Prop :=
  forall i, 0 <= i < n -> mbyte rsegs m (a + i) = Some (Z_to_bv 8 v).

Definition GI_reply (j : nat) (m : word -> option byte) : Prop :=
  byte_at m G_DATA 255 16 /\ byte_at m G_THREAD_UP 0 1 /\ byte_at m G_NSRC 0 4 /\
  byte_at m G_LOCK 0 40 /\ byte_at m G_S 0 384.


Lemma zseq_forall : forall (f : Z -> bool) n, forallb f (map Z.of_nat (seq 0 n)) = true ->
  forall i, 0 <= i < Z.of_nat n -> f i = true.
Proof.
  intros f n H i Hi. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

Definition rom_is (v a : Z) : bool :=
  match seg_rom rsegs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.

Lemma rom_is_ok : forall v a, 0 <= v < 256 -> rom_is v a = true ->
  seg_rom rsegs (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros v a Hv H. unfold rom_is in H. destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|]; [|discriminate].
  f_equal. apply bv_eq. apply Z.eqb_eq in H. rewrite H. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. unfold bv_modulus. cbn. lia.
Qed.

Lemma img_is : forall v a n, 0 <= v < 256 ->
  forallb (fun i => rom_is v (a + i)) (map Z.of_nat (seq 0 (Z.to_nat n))) = true ->
  forall i, 0 <= i < n -> seg_rom rsegs (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 v).
Proof.
  intros v a n Hv H i Hi. apply rom_is_ok; [exact Hv|].
  apply (zseq_forall (fun i => rom_is v (a + i)) (Z.to_nat n) H). lia.
Qed.

Lemma in_G_data : forall a, G_DATA <= a < G_DATA + 16 -> in_globals G_reply a.
Proof. intros a H. exists 0x20d38, 16. split; [left; reflexivity|unfold G_DATA in H; exact H]. Qed.

Lemma in_G_bss : forall a, 0x30fc0 <= a < 0x30fc0 + 512 -> in_globals G_reply a.
Proof. intros a H. exists 0x30fc0, 512. split; [right; left; reflexivity|exact H]. Qed.

Lemma GI_reply_local : forall B, ms_segs B = rsegs -> G_local_c B G_reply GI_reply.
Proof.
  intros B SEGS j m m' EQ (H1 & H2 & H3 & H4 & H5).
  rewrite SEGS in EQ.
  unfold GI_reply, byte_at, G_DATA, G_THREAD_UP, G_NSRC, G_LOCK, G_S in *.
  split; [|split; [|split; [|split]]]; intros i Hi.
  - rewrite EQ by (apply in_G_data; unfold G_DATA; lia). apply H1. exact Hi.
  - rewrite EQ by (apply in_G_bss; lia). apply H2. exact Hi.
  - rewrite EQ by (apply in_G_bss; lia). apply H3. exact Hi.
  - rewrite EQ by (apply in_G_bss; lia). apply H4. exact Hi.
  - rewrite EQ by (apply in_G_bss; lia). apply H5. exact Hi.
Qed.

Lemma GI_reply_img : forall B, ms_segs B = rsegs -> forall mem, G_img_c B G_reply mem -> GI_reply 0 mem.
Proof.
  intros B SEGS mem H. unfold G_img_c in H. rewrite SEGS in H.
  unfold GI_reply, byte_at.
  split; [|split; [|split; [|split]]]; intros i Hi.
  - rewrite H by (apply in_G_data; lia). apply (img_is 255 G_DATA 16); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss; unfold G_THREAD_UP in *; lia).
    apply (img_is 0 G_THREAD_UP 1); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss; unfold G_NSRC in *; lia).
    apply (img_is 0 G_NSRC 4); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss; unfold G_LOCK in *; lia).
    apply (img_is 0 G_LOCK 40); [lia|vm_compute; reflexivity|exact Hi].
  - rewrite H by (apply in_G_bss; unfold G_S in *; lia).
    apply (img_is 0 G_S 384); [lia|vm_compute; reflexivity|exact Hi].
Qed.

