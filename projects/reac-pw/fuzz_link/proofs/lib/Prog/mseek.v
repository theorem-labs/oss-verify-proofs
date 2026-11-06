(* mseek (musl src/stdio/fmemopen.c; plain 0x19658, 156 bytes), PLAIN build: the walk of
   `mseek_set_contract` (lib/Prog/mseek_c.v) at whence = SEEK_SET with 0 <= off <= c->size.

   The walk is the one of libreac/fuzz_pcap lib/Prog/mseek.v (ossv/recipes 4b6f0df50aa); the code of
   mseek is the same in both images (ident_wide.py libreac/fuzz_pcap plain mseek: IDENTICAL). Only the
   addresses (entry 0x19658, the GOT slot 0x208d8 holding the guard address 0x95878) and the arm differ:
   at whence = 0 the base is the 0 the function stores at +0x34, the bound checks +0x50 and +0x5c pass,
   +0x90 stores c->pos = off and the function returns off.

   The 34 instructions the walk runs, from the image the proof loads (`step` reads each from it):
   +0x00 addi sp,sp,-0x30; +0x04 sd ra,0x28(sp); +0x08 sd s0,0x20(sp); +0x0c auipc a3,7;
   +0x10 ld s0,0x274(a3) (the GOT slot 0x208d8); +0x14 ld a3,0(s0) (the guard 0x95878);
   +0x18 addi a4,zero,3; +0x1c sd a3,0x18(sp); +0x20 bgeu a2,a4 (not taken); +0x24 ld a3,0x98(a0);
   +0x28 ld a0,0(a3); +0x2c ld a4,8(a3); +0x30 slli a2,a2,3; +0x34 sd zero,0(sp); +0x38 sd a0,8(sp);
   +0x3c sd a4,0x10(sp); +0x40 mv a0,sp; +0x44 add a0,a0,a2; +0x48 ld a0,0(a0); +0x4c neg a2,a0;
   +0x50 blt a1,a2 (not taken); +0x54 ld a2,0x10(a3); +0x58 sub a2,a2,a0; +0x5c bge a2,a1 (taken);
   +0x8c add a0,a0,a1; +0x90 sd a0,0(a3); +0x94 j +0x70; +0x70 ld a1,0(s0); +0x74 ld a2,0x18(sp);
   +0x78 bne a1,a2 (not taken); +0x7c ld ra,0x28(sp); +0x80 ld s0,0x20(sp); +0x84 addi sp,sp,0x30; +0x88 ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c mk_leaf mseek_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI04 YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The FILE fields as the walk reads them
   ========================================================================== *)

Lemma ms_nth_Z_to_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia.
    replace (8 + 8 * Z.of_nat k) with (8 * Z.of_nat (S k)) by lia. reflexivity.
Qed.

(* byte k of the 8-byte little-endian word v, in the two forms: `le8` (the walk) and `le_byte`
   (YI04.val_mem, the form of mf_fld) *)
Lemma ms_le8_nth : forall v k, (k < 8)%nat ->
  nth_error (le8 (wz v)) k = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)).
Proof.
  intros v k Hk. unfold le8, word_to_le_bytes, wz. rewrite ms_nth_Z_to_le_bytes by exact Hk.
  f_equal. apply Z_to_bv8_mod. unfold YO0f.le_byte.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  change (8 * Z.of_nat 8) with 64. change 256 with (2 ^ 8).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma ms_val_bytes : forall m a v, YI04.val_mem rsegs m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs m a (le8 (wz v)).
Proof.
  intros m a v H H0 H1. split; [exact H0|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi. rewrite ms_le8_nth by exact Hi. exact (H i Hi).
Qed.

Lemma ms_bytes_val : forall m a (w : word) v, bytes_at rsegs m a (le8 w) -> bv_unsigned w = v ->
  YI04.val_mem rsegs m a 8 v.
Proof.
  intros m a w v (H0 & H1 & H) <- k Hk.
  replace (le8 w) with (le8 (wz (bv_unsigned w))) in H by (unfold wz; rewrite Z_to_bv_lit_self; reflexivity).
  specialize (H k ltac:(rewrite length_le8; exact Hk)).
  rewrite ms_le8_nth in H by exact Hk. exact H.
Qed.

Lemma ms_ro_c8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ms_rw_c8 : forall m A v, bytes_at rsegs m A (le8 v) -> wr_at rsegs m A 8 -> rw_cells rsegs m A [C8 v].
Proof. intros m A v H W. split; [apply ms_ro_c8; exact H | exact W]. Qed.

Lemma ms_rw_c8_bytes : forall m A v, rw_cells rsegs m A [C8 v] -> bytes_at rsegs m A (le8 v).
Proof. intros m A v [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma ms_signed_lit : forall z, -2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Lemma ms_munch2 : forall a b c d a' b' c' d' m m', munch [(a, b); (c, d)] m m' ->
  a = a' -> b = b' -> c = c' -> d = d' -> munch [(a', b'); (c', d')] m m'.
Proof. intros a b c d a' b' c' d' m m' H <- <- <- <-. exact H. Qed.

(* ==========================================================================
   2. The walk
   ========================================================================== *)

Theorem mseek_set_proof : mseek_set_contract.
Proof.
  unfold mseek_set_contract. intros f off pos len. apply leaf_intro.
  - intros r1 r2 m E H. unfold getr_same in E. cbv beta in *.
    unfold arg, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ E H. unfold getr_same in E. cbv beta in *.
    unfold res in *. rewrite <- E. exact H.
  - unfold leaf_walk, MSEEK, MSEEK_K.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta.
    intros (HA0 & HA1 & HA2 & Hoff & Hf0 & Hf1 & HCK & HPOS & HLEN & HSZ & HW & HAP & HIMG & HPL & HGW)
      MI ST LO SP.
    rewrite mkR_a0 in HA0. rewrite mkR_a1 in HA1. rewrite mkR_a2 in HA2.
    unfold apart_frame in HAP. rewrite mkR_sp in HAP, HIMG.
    subst f off.
    assert (E2 : a2 = Z_to_bv 64 0) by (apply bv_eq; rewrite HA2; reflexivity). subst a2. clear HA2.
    unfold mf_fld, MemFile.MF_COOKIE, MemFile.MF_BLOCK, SAID_SIZE in *.
    pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. pose proof (zr_word sp) as Rsp.
    unfold inr64 in Ra0, Ra1, Rsp.
    assert (Hs1 : bv_signed a1 = bv_unsigned a1).
    { pose proof (ms_signed_lit (bv_unsigned a1) ltac:(lia)) as E. rewrite Z_to_bv_lit_self in E. exact E. }
    (* the four FILE words the walk reads, and the one it writes *)
    apply ms_val_bytes in HCK; [|lia|lia]. apply ms_ro_c8 in HCK.
    apply ms_val_bytes in HPOS; [|lia|lia].
    pose proof (ms_rw_c8 _ _ _ HPOS HW) as HPW. clear HPOS HW.
    replace (bv_unsigned a0 + (232 + 8)) with (bv_unsigned a0 + 240) in HLEN by lia.
    replace (bv_unsigned a0 + (232 + 16)) with (bv_unsigned a0 + 248) in HSZ by lia.
    apply ms_val_bytes in HLEN; [|lia|lia]. apply ms_ro_c8 in HLEN.
    apply ms_val_bytes in HSZ; [|lia|lia]. apply ms_ro_c8 in HSZ.
    (* the stack protector's two words *)
    unfold guard_words, GOT_GUARD, GUARD in HGW. destruct HGW as [HGOT [g HGD]].
    apply ms_ro_c8 in HGOT. apply ms_ro_c8 in HGD.
    unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in *.
    unfold wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp);
                            (bv_unsigned a0 + 232, bv_unsigned a0 + 232 + 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    (* +0x00 .. +0x1c: the frame and the guard; +0x20 whence < 3 *)
    step. step. step. step. step. step. step. step. step.
    if_false.
    (* +0x24 .. +0x50: c, base[] = {0, pos, len}, base[0] = 0, -base <= off *)
    step. step. step. step. step. step. step. step. step. step. step. step.
    if_false.
    (* +0x54 .. +0x5c: off <= size - base *)
    step. step. step.
    if_true.
    (* +0x8c .. +0x78: c->pos = off; the guard is unchanged *)
    step. step. step. step. step. step.
    if_false.
    (* +0x7c .. +0x88: the epilogue *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    step.
    apply evt_done. cbv beta.
    do 2 eexists. split; [reflexivity|].
    split; [apply regs_preserved_mkR|].
    split; [eapply ms_munch2; [exact MU | lia | lia | lia | lia]|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split.
    + unfold res. transitivity (bv_unsigned (Z_to_bv 64 (0 + bv_unsigned a1))); [reflexivity|].
      rewrite unsigned_lit by lia. lia.
    + eapply ms_bytes_val; [apply ms_rw_c8_bytes; exact HPW|]. rewrite ?unsigned_lit by lia. lia.
Qed.
