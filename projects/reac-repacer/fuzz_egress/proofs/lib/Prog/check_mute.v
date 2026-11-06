(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c. *)
(* Modified by Theorem Labs: for reac-repacer/fuzz_uci. Sections G / G2 are
   libreac/fuzz_decode's released lib/Prog/crt_glue.v with its module paths changed and its one decode-specific
   import (check_braid_c, for braid_map) dropped. Section Body is the invariant layer of that release's
   lib/Prog/check_round_trip.v `Section Body` (cr_inv, cr_pre, cr_inv_call, cr_inv_A, cr_inv_kept, cr_heap_E,
   cr_free_keep, cr_old_in, cr_frame_call), with the one change that the function's own stack size is the section
   variable K instead of decode's CRT_STACK, and with cr_frame_call generalised from decode's fixed frame cell list
   to any (base, cells): so fuzz_uci's check_no_overread and check_value, whose frames differ, share one copy. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/CheckGlue.v; 653 of its 768 lines of code are new or changed and 376 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require
  PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Img0 EgressFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require memcpy_c rp_mute_c bcmp_c.
Import ListNotations.

(* The machine-level segments of check_mute (plain 0x12eec), between its allocator calls. *)
Module CMSeg.
Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Img0 EgressFrame StrFun memcpy_c rp_mute_c bcmp_c.
Open Scope Z_scope.

Definition CM_MALLOC : Z := 0x14010.
Definition CM_FREE : Z := 0x13ed0.

Ltac cm_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac cm_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cm_usub_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by nia end.

Ltac cm_w := cm_usub; rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Ltac cm_fin := apply evt_done; f_equal; cm_regs; cm_w.

Lemma cm_seqz : forall n, 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (Z.max n 1).
Proof.
  intros n Hn. unfold v_sltiu. rewrite unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  destruct (Z.ltb_spec n 1); rewrite unsigned_lit by lia; f_equal; lia.
Qed.

(* Entry to the call of malloc(n ? n : 1). *)
Definition cm_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 0x12f18) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n)
               (Z_to_bv 64 (Z.max n 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
             F (Z_to_bv 64 CM_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cm_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    0 <= n <= 1600 -> 0 <= f < 2 ^ 64 ->
    evt rsegs (cm_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12eec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n lo
    ST LO HN HF.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 11 step.
  apply evt_done. unfold cm_s1_post.
  do 16 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
       eassumption. }
  f_equal. cm_regs.
  all: first [ exact (cm_seqz n ltac:(lia)) | cm_w ].
Qed.

(* Restore the frame and tail-call free(c). *)
Lemma cm_seg3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (v0 v1 v2 v3 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 s0 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CM_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    v0 v1 v2 v3 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 8 step.
  cm_fin.
Qed.

(* Byte-list facts of rp_mute's model. *)
Definition cm_keep (n : Z) (bs : list byte) : Z := if rp_mute_mutes n bs then 18 else n.

Lemma cm_mutes_lt : forall n bs, rp_mute_mutes n bs = true -> 18 < n.
Proof. intros n bs E. unfold rp_mute_mutes in E. apply andb_prop in E as [E _]. apply Z.ltb_lt in E. exact E. Qed.

Lemma cm_keep_range : forall n bs, 0 <= n -> 0 <= cm_keep n bs <= n.
Proof.
  intros n bs Hn. unfold cm_keep. destruct (rp_mute_mutes n bs) eqn:E; [pose proof (cm_mutes_lt n bs E)|]; lia.
Qed.

Lemma cm_rpm_prefix : forall n bs, length bs = Z.to_nat n ->
  firstn (Z.to_nat (cm_keep n bs)) (rp_mute_bytes n bs) = firstn (Z.to_nat (cm_keep n bs)) bs.
Proof.
  intros n bs HL. unfold cm_keep, rp_mute_bytes. destruct (rp_mute_mutes n bs) eqn:E; [|reflexivity].
  pose proof (cm_mutes_lt n bs E) as Hn. change (Z.to_nat 18) with 18%nat.
  rewrite firstn_app, firstn_length_le by lia. rewrite Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn, Nat.min_id.
  reflexivity.
Qed.

Lemma cm_rpm_len : forall n bs, length bs = Z.to_nat n -> length (rp_mute_bytes n bs) = Z.to_nat n.
Proof.
  intros n bs HL. unfold rp_mute_bytes. destruct (rp_mute_mutes n bs) eqn:E; [|exact HL].
  pose proof (cm_mutes_lt n bs E) as Hn.
  rewrite length_app, firstn_length_le, repeat_length by lia. lia.
Qed.

Lemma cm_rpm_zero : forall n bs i, length bs = Z.to_nat n -> rp_mute_mutes n bs = true -> 18 <= i < n ->
  nth_error (rp_mute_bytes n bs) (Z.to_nat i) = Some (Z_to_bv 8 0).
Proof.
  intros n bs i HL E Hi. pose proof (cm_mutes_lt n bs E) as Hn. unfold rp_mute_bytes. rewrite E.
  rewrite nth_error_app2 by (rewrite firstn_length_le by lia; lia).
  rewrite firstn_length_le by lia. apply nth_error_repeat. lia.
Qed.

Lemma cm_memcmp_prefix : forall (l r : list byte) k, (k <= length l)%nat -> (k <= length r)%nat ->
  firstn k l = firstn k r -> memcmp_model l r k = Some 0.
Proof.
  intros l r k; revert l r; induction k as [|k IH]; intros [|x l] [|y r] Hl Hr E; cbn in *; try lia; try reflexivity.
  injection E as E1 E2. subst y. rewrite Z.eqb_refl. apply IH; [lia | lia | exact E2].
Qed.

Lemma cm_firstn1 : forall (l : list byte) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  induction l as [|x l IH]; intros [|k] b H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma cm_firstn1_nth : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof. induction bs as [|b bs IH]; intros [|k] d H; cbn in *; try lia; auto. apply IH; lia. Qed.

Lemma cm_zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  apply unsigned_lit. cbn in R |- *. lia.
Qed.

Ltac cm_fold_zxb H :=
  repeat match type of H with
  | context [Z_to_bv 64 (bv_unsigned ?b)] =>
      lazymatch type of b with bv 8 => change (Z_to_bv 64 (bv_unsigned b)) with (zxb b) in H end
  end;
  rewrite ?cm_zxb_unsigned in H.

Lemma cm_bytes_of_cells : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [(_ & HB) _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma cm_wr_of_cells : forall m A k bs, rw_cells rsegs m A [CB k bs] -> wr_at rsegs m A (Z.of_nat k).
Proof. intros m A k bs [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. exact HW. Qed.

(* From the return of malloc to the tail of check_mute (0x12f9c): fuzz_dup's memcpy, rp_mute, the memcmp of the
   kept bytes and the loop over the muted ones; no abort is reachable. *)
Section S2.
Variable MC : memcpy_contract.
Variable RPM : rp_mute_contract.
Variable BC : bcmp_contract.
Variables (sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (f n c : Z) (bs : list byte).
Hypothesis HN : 0 <= n <= 1600.
Hypothesis HC : 4096 <= c /\ c + n < 2 ^ 47.
Hypothesis HF : 0 <= f /\ f + n < 2 ^ 47.
Hypothesis HD : c + n <= f \/ f + n <= c.
Hypothesis HL : length bs = Z.to_nat n.

Definition cm_s2_post : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m',
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
             F (Z_to_bv 64 0x12f9c) fc None m' (seg_rom rsegs) /\
    munch [(c, c + n)] m0 m' /\ wmono rsegs m0 m'.

Lemma cm_post_intro : forall ra' t0 t1 t2 x8 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m',
  x8 = Z_to_bv 64 c -> munch [(c, c + n)] m0 m' -> wmono rsegs m0 m' ->
  cm_s2_post (MS (mkR ra' sp gp tp t0 t1 t2 x8 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (Z_to_bv 64 0x12f9c) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' t0 t1 t2 x8 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' -> MU WM.
  unfold cm_s2_post. do 20 eexists. split; [reflexivity|]. split; assumption.
Qed.

Lemma cm_loop : forall (r : nat) (ra t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word)
    (m : word -> option byte),
  rp_mute_mutes n bs = true -> 1 <= Z.of_nat r <= n - 18 ->
  x8 = Z_to_bv 64 c -> x9 = Z_to_bv 64 n -> x10 = Z_to_bv 64 (Z.of_nat r) -> x18 = Z_to_bv 64 f ->
  x19 = Z_to_bv 64 (c + n - Z.of_nat r) ->
  bytes_at rsegs m c (rp_mute_bytes n bs) -> munch [(c, c + n)] m0 m -> wmono rsegs m0 m ->
  evt rsegs cm_s2_post
    (MS (mkR ra sp gp tp t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12f7c) fc None m (seg_rom rsegs)).
Proof.
  induction r as [|r IH]; intros ra t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m
    HM Hr -> -> -> -> -> HB MU WM; [lia|].
  assert (R : ov_read_bytes rsegs m (wa (c + (n - Z.of_nat (S r)))) 1 = Some [Z_to_bv 8 0]).
  { rewrite (bytes_at_read rsegs m c _ (n - Z.of_nat (S r)) 1 HB) by (rewrite ?cm_rpm_len by exact HL; lia).
    f_equal. apply cm_firstn1. apply cm_rpm_zero; [exact HL | exact HM | lia]. }
  step.
  step. if_false.
  do 3 step.
  if_cases HZ; zify_cond HZ.
  - apply evt_done. apply cm_post_intro; [reflexivity | exact MU | exact WM].
  - step. eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m HM); [lia | ..].
    all: first [ reflexivity | exact HB | exact MU | exact WM | cm_w ].
Qed.

Lemma cm_tail : forall (ra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word)
    (m : word -> option byte),
  x8 = Z_to_bv 64 c -> x9 = Z_to_bv 64 n -> x18 = Z_to_bv 64 f -> x19 = Z_to_bv 64 (cm_keep n bs) ->
  bytes_at rsegs m c (rp_mute_bytes n bs) -> bytes_at rsegs m f bs -> mem_inv rsegs m ->
  munch [(c, c + n)] m0 m -> wmono rsegs m0 m ->
  evt rsegs cm_s2_post
    (MS (mkR ra sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m -> -> -> -> HBc HBf MI MU WM.
  pose proof (cm_keep_range n bs ltac:(lia)) as HK.
  pose proof (cm_rpm_len n bs HL) as HL'.
  do 4 step.
  eapply evt_cut; [eapply BC with (ls := rp_mute_bytes n bs) (rs := bs) (v := 0) (m := m) |].
  { rewrite unsigned_lit by lia. exact HBc. }
  { rewrite unsigned_lit by lia. exact HBf. }
  { rewrite unsigned_lit by lia. apply cm_memcmp_prefix; [lia | lia | apply cm_rpm_prefix; exact HL]. }
  { exact MI. }
  intros ms3 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 &
    HB3 & HF3).
  cm_usub_in HB3.
  assert (MU' : munch [(c, c + n)] m0 m3).
  { apply (munch_trans _ m0 m m3 MU). refine (munch_weaken _ _ m m3 _ MU3). intros x Hx. exact I. }
  pose proof (wmono_trans rsegs m0 m m3 WM WM3) as WM'.
  rewrite ret_pc_even by first [lia | reflexivity].
  step. if_false.
  step.
  if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
  - apply evt_done. apply cm_post_intro; [reflexivity | exact MU' | exact WM'].
  - assert (HM : rp_mute_mutes n bs = true).
    { unfold cm_keep in HZ. destruct (rp_mute_mutes n bs); [reflexivity | lia]. }
    pose proof (cm_mutes_lt n bs HM) as H18.
    unfold cm_keep. rewrite HM.
    do 2 step.
    eapply (cm_loop (Z.to_nat (n - 18)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 HM); [lia | ..].
    all: first [ reflexivity | exact HB3 | exact MU' | exact WM' | cm_w ].
Qed.

Lemma cm_mid : forall (ra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word)
    (m : word -> option byte),
  0 < n -> x8 = Z_to_bv 64 c -> x9 = Z_to_bv 64 n -> x18 = Z_to_bv 64 f ->
  bytes_at rsegs m c (rp_mute_bytes n bs) -> bytes_at rsegs m f bs -> mem_inv rsegs m ->
  munch [(c, c + n)] m0 m -> wmono rsegs m0 m ->
  evt rsegs cm_s2_post
    (MS (mkR ra sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12f3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m Hn -> -> -> HBc HBf MI MU WM.
  do 3 step.
  if_cases HB; zify_cond HB; rewrite ?unsigned_lit in HB by lia.
  - (* n <= 18: keep = n *)
    eapply cm_tail; try eassumption; try reflexivity.
    unfold cm_keep, rp_mute_mutes. rewrite (proj2 (Z.ltb_ge 18 n)) by lia. reflexivity.
  - set (b16 := nth 16 bs (Z_to_bv 8 1)). set (b17 := nth 17 bs (Z_to_bv 8 1)).
    assert (RB16 : ov_read_bytes rsegs m (wa (f + 16)) 1 = Some [b16]).
    { rewrite (bytes_at_read rsegs m f bs 16 1 HBf) by lia. f_equal. apply cm_firstn1_nth. lia. }
    assert (RB17 : ov_read_bytes rsegs m (wa (f + 17)) 1 = Some [b17]).
    { rewrite (bytes_at_read rsegs m f bs 17 1 HBf) by lia. f_equal. apply cm_firstn1_nth. lia. }
    step. step.
    if_cases H16; zify_cond H16; cm_fold_zxb H16.
    + (* f[16] != 0: keep = n *)
      step. eapply cm_tail; try eassumption; try reflexivity.
      unfold cm_keep, rp_mute_mutes, frame_is_audio. fold b16.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned b16) 0)) by lia. rewrite !andb_false_r. reflexivity.
    + step. step.
      if_cases H17; zify_cond H17; cm_fold_zxb H17.
      * (* audio: keep = 18 *)
        do 2 step. eapply cm_tail; try eassumption; try reflexivity.
        unfold cm_keep, rp_mute_mutes, frame_is_audio. fold b16 b17.
        rewrite (proj2 (Z.ltb_lt 18 n)) by lia.
        rewrite (proj2 (Z.eqb_eq (bv_unsigned b16) 0)) by lia. rewrite (proj2 (Z.eqb_eq (bv_unsigned b17) 0)) by lia.
        reflexivity.
      * step. eapply cm_tail; try eassumption; try reflexivity.
        unfold cm_keep, rp_mute_mutes, frame_is_audio. fold b16 b17.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned b17) 0)) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma cm_seg2 : forall (ra t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word) (junk : list byte),
  x9 = Z_to_bv 64 n -> x10 = Z_to_bv 64 c -> x18 = Z_to_bv 64 f ->
  bytes_at rsegs m0 f bs -> rw_cells rsegs m0 c [CB (Z.to_nat n) junk] -> mem_inv rsegs m0 ->
  evt rsegs cm_s2_post
    (MS (mkR ra sp gp tp t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12f18) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 junk -> -> -> HBf HJ MI.
  pose proof (munch_refl [(c, c + n)] m0) as MU0.
  pose proof (wmono_refl rsegs m0) as WM0.
  step. if_cases H0; zify_cond H0; rewrite ?unsigned_lit in H0 by lia; [lia |].
  step. step.
  if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
  - (* n = 0: fuzz_dup copies nothing; rp_mute(c, 0) *)
    do 2 step.
    eapply evt_cut; [eapply RPM with (bs := []) (m := m0) |].
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. apply bytes_at_nil. lia. }
    { cm_usub. cbn. lia. }
    { cm_usub. split; [lia|]. split; [lia|]. intros i Hi. lia. }
    { exact MI. }
    intros ms1 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & _).
    rewrite ret_pc_even by first [lia | reflexivity].
    apply evt_done. apply cm_post_intro; [reflexivity | | exact WM1].
    refine (munch_weaken _ _ m0 m1 _ MU1). intros x Hx. cbn [outside] in *. cm_usub. split; [lia | exact I].
  - do 3 step.
    eapply evt_cut; [eapply MC with (src := bs) (junk := junk) (m := m0) |].
    { rewrite unsigned_lit by lia. exact HBf. }
    { rewrite unsigned_lit by lia. exact HL. }
    { rewrite !unsigned_lit by lia. exact HJ. }
    { rewrite !unsigned_lit by lia. lia. }
    { exact MI. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & RW1 & HF1).
    cm_usub_in MU1. cm_usub_in RW1. cm_usub_in HF1.
    rewrite ret_pc_even by first [lia | reflexivity].
    do 3 step.
    eapply evt_cut; [eapply RPM with (bs := bs) (m := m1) |].
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. exact (cm_bytes_of_cells _ _ _ _ RW1). }
    { rewrite unsigned_lit by lia. exact HL. }
    { rewrite !unsigned_lit by lia. pose proof (cm_wr_of_cells _ _ _ _ RW1) as W.
      cm_usub_in W. rewrite Z2Nat.id in W by lia. exact W. }
    { exact MI1. }
    intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
      t6'' & m2 & -> & MU2 & WM2 & MI2 & HB2).
    cm_usub_in MU2. cm_usub_in HB2.
    rewrite ret_pc_even by first [lia | reflexivity].
    eapply cm_mid; try reflexivity; [lia | exact HB2 | | exact MI2 | |].
    + eapply bytes_at_transport; [exact HF1 | exact MU2 |]. cbn [disjoint_from]. rewrite HL, Z2Nat.id by lia.
      split; [lia | exact I].
    + apply (munch_trans _ m0 m1 m2 MU1). refine (munch_weaken _ _ m1 m2 _ MU2).
      intros x Hx. cbn [outside] in *. split; [lia | exact I].
    + exact (wmono_trans rsegs m0 m1 m2 WM1 WM2).
Qed.

End S2.

End CMSeg.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import check_mute_c memcpy_c rp_mute_c bcmp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import EgressGlue.
Local Open Scope Z_scope.


Section CM.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x14010.
Hypothesis FREEPC : ms_free B = 0x13ed0.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis RPM : rp_mute_contract.
Hypothesis BC : bcmp_contract.

Lemma ck_blk : forall Lk Ak mk mdk P n, aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
  4096 <= P /\ P + n <= alloc_ceiling /\ P mod 16 = 0 /\
  forall i, 0 <= i < n -> present mk (P + i) /\ ~ in_img B (P + i) /\ ~ owned B Lk Ak (P + i).
Proof.
  intros Lk Ak mk mdk P n HM Hin.
  destruct (eg_bu Lk Ak P n Hin) as (p & Hp & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p n HM Hp)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk p n i HM Hp Hi) | exact Hno].
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f n : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CHECK_MUTE_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 f.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis HN : 0 <= n <= 1600.
Hypothesis IB : in_block L A f n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + Z.max n 1 <= 2 ^ 40.

Definition ck_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CHECK_MUTE_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition ck_kept (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\
  getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\
  getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

Definition ck_frame (m' : word -> option byte) : Prop :=
  exists junk, Step.rw_cells rsegs m' (spZ regs - 48) [Cells.CB 8 junk; Cells.C8 (getr regs 19);
    Cells.C8 (getr regs 18); Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition ck_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CHECK_MUTE_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma ck_pre : forall Lk Ak mk mdk regsk f0 K1,
  ck_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f0 -> 0 <= f0 -> 0 <= K1 -> f0 + K1 <= CHECK_MUTE_STACK ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk f0 K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hf HK1 HfK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma ck_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  ck_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CHECK_MUTE_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  ck_inv L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (eg_drop B API _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (eg_seq B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma ck_inv_A : forall Lk Ak mk mdk mk' W,
  ck_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_MUTE_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p n, forall i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  ck_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (eg_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (eg_drop B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CHECK_MUTE_STACK <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p n0 i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n0 HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p n0 i Hin Hi eq_refl)].
    - intros x [[]|(Hx & Ho & Hs)].
      destruct (HW x Hx Ho) as [H|(H1 & H2 & _)]; [contradiction | split; assumption]. }
  split; [exact I2|]. split; [exact I3|]. split; [exact Hro|].
  intros i Hi. rewrite <- (I5 i Hi).
  assert (Ho : owned B Lk Ak (ms_got_guard B + i))
    by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho) as Hr.
  apply (mbyte_munch (ms_segs B) W mk mk'); [exact Hm | lia |].
  destruct (kb_outside_dec W (ms_got_guard B + i)) as [Hout|Hout]; [exact Hout|]. exfalso.
  destruct (HW (ms_got_guard B + i) ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
Qed.

Lemma ck_free_keep : forall Lk Ak mk mdk p n0,
  ck_inv Lk Ak mk mdk -> In (p, n0) (user_blocks Ak) -> 0 < n0 ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, n0) y) ->
  forall q k, In (q, k) (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p n0 ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hn HD q k Hq Eq. subst q.
  pose proof (I3 p k Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (eg_fst_unique _ p k n0 ND Hpk Hp) as Ek. subst k.
  pose proof (HD _ (eg_ub L A p n0 Hq)) as D.
  rewrite (P1 p n0 Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma ck_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  ck_inv Lk Ak mk mdk -> ck_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  ck_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) (junk & FR) Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  exists junk. rewrite <- SEGS in FR |- *.
  apply (eg_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 48 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 48 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma ck_inv_kept : forall Lk Ak mk mdk, ck_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (eg_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma ck_kept_pres : forall r r', ck_kept r -> regs_preserved r r' -> ck_kept r'.
Proof.
  intros r r' (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r 20); [apply (Hp 20); unfold callee_saved; lia | exact K20].
  - transitivity (getr r 21); [apply (Hp 21); unfold callee_saved; lia | exact K21].
  - transitivity (getr r 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

Lemma ck_heap_E : forall Lk Ak mk mdk p n0, aa_MR API Lk Ak mk mdk -> In (p, n0) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + n0 -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p n0 HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p n0 (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

(* 0x12f9c: restore the frame, then free(c) as a tail call. *)
Lemma ck_ph4 : forall (fx7 : FPState) L1 A1 regs7 m7 md1 P c1 c2,
  frm_zero (@fp_csr fx7) ->
  ck_inv L1 A1 m7 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs7 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs7 8 = Z_to_bv 64 P -> ck_kept regs7 ->
  ck_frame m7 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 0x12f9c) m7 (seg_rom (ms_segs B))) md1) ck_final.
Proof.
  intros fx7 L1 A1 regs7 m7 md1 P c1 c2 Hfrm I Hinit Hb1 Hb0 Hres G2 G8 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  assert (Hk : 0 < Z.max n 1) by lia.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m7 md1 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs7 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (eg_runA (fx := fx7) B SEGS regs7 _ m7 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply CMSeg.cm_seg3. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs7 2) + 48)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 48 + 48) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj1 (proj2 GK))).
  assert (G11d : getr regs11 10 = Z_to_bv 64 P) by (rewrite Hg11; exact G8).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4 | exact K20 | exact K21 | exact K22
        | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]]. }
  destruct (eg_bu L1 A1 P _ ltac:(rewrite Hb1; apply eg_in_mid)) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L1 A1 regs11 m7 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs11 m7 md1)).
    apply (ck_pre L1 A1 m7 md1 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CMSeg.CM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L1 A1 regs11 m7 md1 p (Z.max n 1) (sb_malloc b (Z.max n 1)) Hpre11 I4 Hp).
    - rewrite G11d, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  assert (PW5 : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (P, Z.max n 1) (c1 ++ c2)) by (apply (eg_notin c1 c2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (eg_rm (P, Z.max n 1) c1 c2 d1 d2 ND5). rewrite <- Hb1. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 p, Z.max n 1) y).
  { intros y Hy. rewrite Ep. apply (eg_pw_mid c1 c2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (ck_free_keep L1 A1 m7 md1 p _ I Hp ltac:(lia) HD5 q k Hq)]. }
  assert (I6 : ck_inv L6 A6 m12 md6).
  { apply (ck_inv_call L1 A1 m7 md1 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (ck_heap_E L1 A1 m7 md1 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply SR_ret. exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (ck_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* 0x12f18, malloc returned c: the segment up to 0x12f9c, in normalized memory. *)
Lemma ck_ph3 : forall L1 A1 regs2 m2 md1 P c1 c2,
  ck_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 9 = Z_to_bv 64 n -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 18 = Z_to_bv 64 f -> ck_kept regs2 -> ck_frame m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x12f18) m2 (seg_rom (ms_segs B))) md1) ck_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G9 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InP : In (P, Z.max n 1) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_mid).
  destruct (ck_blk L1 A1 m2 md1 P _ M1 InP) as (HP1 & HP2 & HP3 & HPi).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  assert (Hq' : In (q, k) (c1 ++ c2)) by (rewrite <- Hb0; exact Hq).
  assert (HqL : In (q, k) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_ins; exact Hq').
  destruct (ck_blk L1 A1 m2 md1 q k M1 HqL) as (HQ1 & HQ2 & _ & HQi).
  pose proof (eg_pw_mid c1 c2 _ _ PW1 Hq') as DPQ. unfold ranges_disjoint in DPQ. cbn [fst snd] in DPQ.
  assert (STf : Frame.stk rsegs (normalize rsegs m2) f (f + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m2 f n I4); [lia | lia |].
    intros i Hi. destruct (HQi (f - q + i) ltac:(lia)) as (X1 & X2 & _).
    replace (q + (f - q + i)) with (f + i) in X1, X2 by ring. split; assumption. }
  assert (STc : Frame.stk rsegs (normalize rsegs m2) P (P + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m2 P n I4); [lia | lia |].
    intros i Hi. destruct (HPi i ltac:(lia)) as (X1 & X2 & _). split; assumption. }
  destruct (Frame.stk_bytes rsegs _ f (f + n) STf ltac:(lia)) as (bs & HLb & HBf).
  replace (f + n - f) with n in HLb by ring.
  destruct (Frame.stk_carve rsegs _ P (P + n) (Z.to_nat n) STc ltac:(lia)) as (_ & junk & HJ).
  rewrite Z2Nat.id in HJ by lia. replace (P + n - n) with P in HJ by ring.
  eapply (eg_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { pose proof YM05.alloc_ceiling_lt as Hc47. pose proof (Z.le_max_l n 1) as Hmx.
    unfold rmk. eapply (CMSeg.cm_seg2 MC RPM BC) with (f := f) (n := n) (c := P) (bs := bs);
      first [ eassumption | exact (mem_inv_normalize rsegs m2) | lia | destruct DPQ; [left | right]; lia ]. }
  { intros ms (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' & t4' &
      t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' &
    t4' & t5' & t6' & m' & -> & MU & WM) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  set (W := [(P, P + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold W in Hout. cbn [Frame.outside] in Hout.
    apply (eg_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
    replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_MUTE_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p n0 i, In (p, n0) (user_blocks A) -> 0 <= i < n0 -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. unfold W in Hout. cbn [Frame.outside] in Hout. right.
    destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2). replace (P + (x - P)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p n0 i Hp Hi E.
    assert (Y1 : In (ptr_addr L p, n0) (c1 ++ c2)) by (rewrite <- Hb0; exact (eg_ub L A p n0 Hp)).
    pose proof (eg_pw_mid c1 c2 _ _ PW1 Y1) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (ck_inv_A L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : ck_frame (ms_mem ms)).
  { destruct FR as (junk' & FRc). exists junk'. rewrite <- SEGS in FRc |- *.
    apply (eg_cells_keep B m2 (ms_mem ms) _ _ FRc). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  apply (ck_ph4 (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 P c1 c2 FRM I7 Hinit Hb1 Hb0 Hres);
    [rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K20 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26
      | exact K27].
Qed.

(* Entry: the frame, then malloc(n ? n : 1). *)
Lemma ck_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_MUTE) mem (seg_rom (ms_segs B))) md) ck_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  pose proof (eg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  destruct (ck_blk L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  assert (I0 : ck_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p n0 Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CHECK_MUTE_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CHECK_MUTE_STACK L A regs mem md PRE ltac:(lia))).
  eapply (eg_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk, CHECK_MUTE. rewrite R10, R11.
    eapply CMSeg.cm_seg1; [exact ST | unfold spZ; lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12f18) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (Z.max n 1)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 9 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
  assert (K1 : ck_kept regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); rewrite Hg1;
        reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (eg_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (eg_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : ck_inv L A m1 md).
  { apply (ck_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (eg_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (eg_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : ck_frame m1) by (exists junk; exact FR1).
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CHECK_MUTE_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_slots b (Z.max n 1)) by (apply room_slots_small; lia).
  replace (Z_to_bv 64 CMSeg.CM_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC L A regs1 m1 md (Z.max n 1) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : ck_inv L1 A1 m2 md1).
  { apply (ck_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : ck_frame m2).
  { apply (ck_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (ck_ph3 L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 9); [apply (Hp2 9); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - exact (ck_kept_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_mute_holds : check_mute_contract B API.
Proof.
  intros L A regs mem md f n b _ H1 H2 H3 H4 H5 H6 H7 H8 H9.
  eapply ck_entry; eassumption.
Qed.

End CM.
