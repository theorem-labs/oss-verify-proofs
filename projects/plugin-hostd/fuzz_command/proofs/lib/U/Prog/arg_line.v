(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 532 of its 622 lines of code are new or changed and 927 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma al_sx32 : forall z, (-2^31 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2^64)%Z with 18446744073709551616%Z. change (2^31)%Z with 2147483648%Z in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma al_lts : forall x y, (-2^63 <= x < 2^63)%Z -> (-2^63 <= y < 2^63)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808%Z.
  change (bv_modulus 64) with 18446744073709551616%Z.
  change (2^63)%Z with 9223372036854775808%Z in Hx, Hy.
  rewrite !Z.mod_small by lia.
  all: f_equal; lia.
Qed.

Lemma al_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa (a + 0)) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  f_equal.
Qed.

Lemma al_land7 : forall e, (0 <= e < 2 ^ 64)%Z -> (e mod 8 = 0)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 e)) 7) = Z_to_bv 64 0.
Proof.
  intros e He Hm. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2 ^ 3)%Z with 8%Z. rewrite Hm. reflexivity.
Qed.

Lemma al_addiw : forall z, (0 <= z < 2 ^ 31 - 1)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 1)%Z) = Z_to_bv 64 (z + 1)%Z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2 ^ 31)%Z with 2147483648%Z in Hz.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma al_ovf : forall x y z, (0 <= y)%Z -> (y <= x < 2 ^ 64)%Z -> (0 <= z < 6)%Z ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)))
                                                      (bv_unsigned (v_slti (Z_to_bv 64 z) 0%Z))))) 1%Z) = Z_to_bv 64 1.
Proof.
  intros x y z Hy Hxy Hz. rewrite v_sltu_b2z, v_slti_b2z. rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  replace (x <? y)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  assert (C : (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5)%Z) by lia.
  destruct C as [C | [C | [C | [C | [C | C]]]]]; subst z; vm_compute; reflexivity.
Qed.

Lemma al_run6 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e lo : Z),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 6)) ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (0 < e)%Z -> (e mod 8 = 0)%Z ->
  (e + 8 <= bv_unsigned sp - 32)%Z ->
  evt rsegs (fun ms' => exists a0' a1' m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
                munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e lo HE ST LO E0 EA ES.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (UE : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 4 step.
  step. if_false.
  do 2 step.
  rewrite al_land7 by lia.
  step. if_false.
  step.
  match goal with H : bytes_at rsegs ?mm (e + 4) _ |- _ => pose proof (al_rd4 mm (e + 4) _ H) as RD end.
  step. rewrite al_sx32 by lia. step. step.
  rewrite al_lts by lia. replace (5 <? 6)%Z with true by reflexivity. cbv iota.
  do 5 step.
  replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp
    by (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; eassumption.
Qed.

Definition al_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e line : Z) (T slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x1664c) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 e) (Z_to_bv 64 line)
                  (Z_to_bv 64 line) (Z_to_bv 64 (Z.of_nat (length T))) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15980) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' line (T ++ Z_to_bv 8 0 :: slack).

Lemma al_run1 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e line mv lo : Z) (T slack : list byte),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 mv)) -> (0 <= mv < 6)%Z ->
  bytes_at rsegs m line (T ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) T ->
  ((- (line + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (0 < e)%Z -> (e mod 8 = 0)%Z ->
  (e + 8 <= bv_unsigned sp - 32)%Z ->
  (line + Z.of_nat (length (T ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= line)%Z ->
  mem_inv rsegs m ->
  evt rsegs (al_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e line T slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 line) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e line mv lo T slack HE HM BS NONUL PAD ST LO E0 EA ES DISJ MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB, DISJ. cbn [length] in SB, DISJ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (US : bv_unsigned (Z_to_bv 64 line) = line) by (apply unsigned_lit; lia).
  assert (UE : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 4 step.
  step. if_false.
  do 2 step.
  rewrite al_land7 by lia.
  step. if_false.
  step.
  match goal with H : bytes_at rsegs ?mm (e + 4) _ |- _ => pose proof (al_rd4 mm (e + 4) _ H) as RD end.
  step. rewrite al_sx32 by lia. step. step.
  rewrite al_lts by lia. destruct (Z.ltb_spec 5 mv) as [C|_]; [lia|]. cbv iota.
  do 2 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T slack).
  1-4: rewrite ?US; first [eassumption | lia].
  cbv delta [mkR].
  do 3 step.
  apply evt_done. unfold al_mid.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition al_fin (ra0 sp0 r3 r4 x5 x6 x7 s0v s1v x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (e mv p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4' m',
    ms' = MS (mkR ra0 sp0 r3 r4 x5 x6 x7 s0v s1v (Z_to_bv 64 p) a1' a2' a3' a4' x15 x16 x17
                  r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m' /\ wmono rsegs m m'
    /\ bytes_at rsegs m' (e + 4) (le4 (Z_to_bv 64 (mv + 1))) /\ bytes_at rsegs m' (e + 8 + 8 * mv) (le8 (Z_to_bv 64 p)).

Lemma al_run3 : forall r1 ra0 sp0 r3 r4 x5 x6 x7 s0v s1v x9 x11 x12 x13 x14 x15 x16 x17
    r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 (F : bvmap 5 word) fc (m : word -> option byte)
    (e mv p : Z) (junk : list byte),
  bytes_at rsegs m (e + 4) (le4 (Z_to_bv 64 mv)) -> (0 <= mv < 6)%Z -> wr_at rsegs m e 56 ->
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra0] ->
  (0 <= e)%Z -> (e + 56 <= bv_unsigned sp0 - 32)%Z -> (32 <= bv_unsigned sp0)%Z -> (0 <= p < 2 ^ 64)%Z ->
  evt rsegs (al_fin ra0 sp0 r3 r4 x5 x6 x7 s0v s1v x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc e mv p m)
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp0 - 32)) r3 r4 x5 x6 x7 (Z_to_bv 64 e) x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
             r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x1664c) fc None m (seg_rom rsegs)).
Proof.
  intros r1 ra0 sp0 r3 r4 x5 x6 x7 s0v s1v x9 x11 x12 x13 x14 x15 x16 x17
    r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc m e mv p junk HE HM HW FR E0 ES S32 HP.
  pose proof (al_rd4 m (e + 4) _ HE) as RD.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UE : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  step. rewrite al_sx32 by lia. step.
  rewrite al_addiw by lia.
  step. rewrite al_lts by lia. if_false.
  do 3 step.
  replace (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 mv)) 3 + (e + 8))%Z) with (Z_to_bv 64 (e + 8 + 8 * mv)%Z)
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  assert (UA : bv_unsigned (Z_to_bv 64 (e + 8 + 8 * mv)%Z) = (e + 8 + 8 * mv)%Z) by (apply unsigned_lit; lia).
  assert (UA3 : bv_unsigned (Z_to_bv 64 (e + 8)%Z) = (e + 8)%Z) by (apply unsigned_lit; lia).
  pose proof (wr_at_store_ok rsegs m e 56 4 4 HW ltac:(lia) ltac:(lia)) as HS1.
  step.
  set (m1 := write_to_mem m (Z_to_bv 64 (e + 4)) (le4 (Z_to_bv 64 (mv + 1)))).
  assert (HW1 : wr_at rsegs m1 e 56) by (apply wr_at_write; exact HW).
  pose proof (wr_at_store_ok rsegs m1 e 56 (8 * mv + 8) 8 HW1 ltac:(lia) ltac:(lia)) as HS2.
  assert (L4 : Z.of_nat (length (le4 (Z_to_bv 64 (mv + 1)))) = 4%Z) by (rewrite length_le4; reflexivity).
  assert (L8 : Z.of_nat (length (le8 (Z_to_bv 64 p))) = 8%Z) by (rewrite length_le8; reflexivity).
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp0 - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra0])
    by (apply rw_cells_frame; [exact FR | lia | rewrite L4; lia | cbn [cells_size csize Nat.add]; rewrite L4; lia]).
  assert (B1 : bytes_at rsegs m1 (e + 4) (le4 (Z_to_bv 64 (mv + 1)))) by (apply bytes_at_write_same; rewrite ?L4; lia).
  assert (MU1 : munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m1).
  { apply munch_write; [exact MU | lia | rewrite L4; lia | cbn [inside]; rewrite L4; lia]. }
  assert (WM1 : wmono rsegs m m1) by (apply wmono_write; exact WM).
  clearbody m1. clear FR MU WM HS1.
  step. if_false.
  do 4 step.
  rewrite al_ovf by lia.
  step. if_false.
  step.
  set (m2 := write_to_mem m1 _ (le8 (Z_to_bv 64 p))).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra0])
    by (apply rw_cells_frame; [exact FR1 | lia | rewrite L8; lia | cbn [cells_size csize Nat.add]; rewrite L8; lia]).
  assert (B2 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 (mv + 1))))
    by (apply bytes_at_write_other; [exact B1 | lia | rewrite L8; lia | rewrite L4, L8; lia]).
  assert (B3 : bytes_at rsegs m2 (e + 8 + 8 * mv) (le8 (Z_to_bv 64 p))).
  { replace (e + 8 + 8 * mv)%Z with (e + (8 * mv + 8))%Z by lia. apply bytes_at_write_same; rewrite ?L8; lia. }
  assert (MU2 : munch [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)]%Z m m2).
  { apply munch_write; [exact MU1 | lia | rewrite L8; lia | cbn [inside]; rewrite L8; lia]. }
  assert (WM2 : wmono rsegs m m2) by (apply wmono_write; exact WM1).
  clearbody m2. clear FR1 HS2.
  do 5 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0
    by (replace (bv_unsigned sp0 - 32 + 32)%Z with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. unfold al_fin. do 5 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact B2 | exact B3].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB xmalloc_c rec_canonical_c
arg_line_c.
Local Open Scope Z_scope.

Lemma al_ro_rec : forall a, 0x33ff0 <= a < 0x343ec -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  assert (C : forallb (fun s => (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x33ff0) || (0x343ec <=? Z.of_N (seg_base s))
                                || seg_writable s) rsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ rsegs) C seg Hin) as Cs. cbv beta in Cs.
  destruct (seg_writable seg); [reflexivity|].
  rewrite orb_false_r in Cs. apply orb_prop in Cs as [Cs|Cs]; apply Z.leb_le in Cs; lia.
Qed.


Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GLOB : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis SLEN : strlen_contract.
Hypothesis REC : rec_canonical_contract B API.

Theorem arg_line_holds : arg_line_contract B API.
Proof using SEGS ERRNO_LOW GOTG GLOB AX SLEN REC.
  unfold arg_line_contract, arg_line_ret.
  intros L A regs mem md e line mv T slack b PRE A0 A1 EAL ELO EHI WRE NA MV BS NONUL LMX PAD DISJ HOME APART RES ROOM RA.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  pose proof REC as RC. unfold rec_canonical_contract in RC. rewrite SEGS in RC.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold ARG_LINE_K, REC_CANONICAL_K, XMALLOC_K, ARG_LINE, LMAX, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SC, G_REC,
    REC_SIZE,
    iv_apart in *.
  change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (Nat2Z.is_nonneg (length T)) as L0.
  set (l := Z.of_nat (length T)) in *.
  rewrite SEGS in RA, HWS, HERR, BS, NA, WRE.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB, DISJ. cbn [length] in SB, DISJ.
  assert (RECI : forall a, e <= a < e + 56 -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4)
                 /\ forall L0 A0 m0 md0, aa_MR API L0 A0 m0 md0 -> ~ owned B L0 A0 a).
  { intros a Ha. destruct (GLOB a) as (Hi & Hs & Hc & He); [exists 0x33ff0, 1020; split; [left; reflexivity | lia]|].
    split; [exact Hi|]. split; [exact He|]. intros La Aa m0 md0 HM [Ho|Ho]; [|exact (Hs Ho)].
    exact (Hc (YL01.ax_img AX _ _ _ _ a HM Hi Ho)). }
  assert (EIMG : e + 56 <= 2 ^ 21) by (destruct (RECI e ltac:(lia)) as [Hi _]; pose proof (in_img_low B SEGS e Hi);
    destruct (RECI (e + 55) ltac:(lia)) as [Hi2 _]; pose proof (in_img_low B SEGS (e + 55) Hi2); lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8272) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    unfold wview, mrd, wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  rewrite SEGS.
  assert (MVC : mv = 6 \/ mv < 6) by lia.
  destruct MVC as [M6|M6].
  - subst mv.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      assert (R10 : reg_get regs 10 = Z_to_bv 64 e) by exact A0. rewrite R10.
      eapply al_run6; [exact NA | exact ST | lia | lia | exact EAL | lia]. }
    intros ms1 (can1 & Q1 & EQ1).
    destruct Q1 as (a0' & a1' & m1 & -> & MU1 & WM1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA). rewrite RP.
    assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) ->
              outside [(bv_unsigned sp - 32, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
    assert (MR1 : aa_MR API L A m1 md).
    { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
      - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
        rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
      - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
        eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
      - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
        eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
      - reflexivity.
      - exact Hh.
      - exact Hl.
      - exact Hmat. }
    apply SR_ret.
    exists L, A, R1, m1, md.
    split; [reflexivity|].
    split.
    { intros q k i Hq _ Hi. destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
      rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split; [intros q k Hq; exact Hq|].
    split.
    { assert (BS' : bytes_at rsegs mem line (T ++ [Z_to_bv 8 0])).
      { replace (T ++ Z_to_bv 8 0 :: slack) with ((T ++ [Z_to_bv 8 0]) ++ slack) in BS by (rewrite <- app_assoc; reflexivity).
        apply bytes_at_app in BS. exact (proj1 BS). }
      apply (bytes_at_transfer rsegs mem); [exact BS'|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split.
    { intros x Hx. destruct (Z_lt_ge_dec (bv_unsigned x) (2 ^ 20)) as [Lo|Hi].
      - unfold mrd. rewrite (MU1 x) by (pose proof (bv_unsigned_in_range 64 x); cbn; split; [lia | exact I]).
        exact (RA x Hx).
      - exfalso. rewrite <- (Z_to_bv_bv_unsigned x) in Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
        unfold bv_modulus in Rx. rewrite ro_addr_hi in Hx by lia. discriminate. }
    split.
    { intros i Hi. rewrite GOTG, SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split; [lia|].
    left. split; [reflexivity|]. split; [|split; [reflexivity | exact RES]].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
    split; [intros; reflexivity|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; simp_regs; reflexivity|]).
      subst r. rewrite (getr_of_eqv _ _ _ X1) by reflexivity; simp_regs; reflexivity. }
    split; [exists (m_vmmaps md); destruct md as [f [mp lz mt] io fs pr li ti]; reflexivity|].
    split.
    { intros a HA NO1 NO2 NS NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      rewrite SEGS. split; [apply (munch_mbyte _ _ _ _ _ MU1 AR (OUT1 a AR NSP)) | apply (munch_writable _ _ _ _ _ MU1 AR (OUT1 a AR NSP))]. }
    split.
    { intros p n i Hin _ Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM1. destruct Ha as [Ha|Ha]; [apply HWS; lia | apply HERR; exact Ha].
  - assert (STN : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 8272) (bv_unsigned sp)).
    { split; [lia|]. split; [lia|]. intros a Ha.
      assert (W : writable_at rsegs mem a) by (apply HWS; lia).
      destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
      assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
      unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      assert (R10 : reg_get regs 10 = Z_to_bv 64 e) by exact A0.
      assert (R11 : reg_get regs 11 = Z_to_bv 64 line) by exact A1.
      rewrite R10, R11.
      eapply (evt_normalize rsegs); [exact WX | exact RA |].
      eapply (al_run1 SLEN);
        [apply bytes_at_normalize; [exact RA | exact NA] | lia | apply bytes_at_normalize; [exact RA | exact BS] |
         exact NONUL | exact PAD | exact STN | lia | lia | exact EAL | lia | rewrite length_app; cbn [length]; lia |
         apply mem_inv_normalize]. }
    intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
    destruct Q1 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & junk
      & -> & MU1n & WM1n & MI1n & FR1n & BS1n).
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
    revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
    pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FR1n) as FR1.
    pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) BS1n) as BS1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1664c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = Z_to_bv 64 line) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 line) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 l) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) ->
              outside [(bv_unsigned sp - 32, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
    assert (MR1 : aa_MR API L A m1 md).
    { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
      - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
        rewrite SEGS. eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
      - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
        eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
      - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
        eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
      - reflexivity.
      - exact Hh.
      - exact Hl.
      - exact Hmat. }
    assert (BS1T : bytes_at rsegs m1 line T).
    { replace (T ++ Z_to_bv 8 0 :: slack) with (T ++ (Z_to_bv 8 0 :: slack)) in BS1 by reflexivity.
      apply bytes_at_app in BS1. exact (proj1 BS1). }
    assert (LNZ : line <> 0).
    { intros E0L. pose proof HOME as HOME0. unfold str_home in HOME0.
      destruct HOME0 as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
      - lia.
      - destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR Hq ltac:(lia)) as (_ & Hlo & _). lia.
      - specialize (H3 0 ltac:(lia)). rewrite E0L, SEGS in H3. vm_compute in H3. discriminate H3. }
    eapply SR_bind.
    { eapply (RC L A R1 m1 md line T b); [ | exact E1_10 | exact E1_11 | exact BS1T | exact LNZ | exact NONUL | exact LMX
        | | | exact RES | exact ROOM | exact RA1].
      - split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
        split; [rewrite SP1; replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring;
                rewrite Z.mod_add by lia; exact HAL|].
        split; [rewrite SP1; lia|].
        split; [rewrite SP1; lia|].
        split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
        split; [rewrite E1_4; exact HTP|].
        split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
        intros HI. specialize (HAUX HI). rewrite SP1.
        destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
        exists av, ar.
        split.
        { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
          assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
          destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
        split.
        { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
          split; [lia | apply OUT1; lia]. }
        split.
        { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
        split.
        { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
        lia.
      - rewrite SP1. lia.
      - unfold str_home in HOME |- *. rewrite SP1.
        destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
        + left. lia.
        + right. left. exists q, k. split; [exact Hq | lia].
        + right. right. split; [lia|]. split; [lia|]. intros i Hi. apply H3. lia. }
    intros c2 RET. unfold rec_canonical_ret in RET.
    destruct RET as (L' & A' & R2 & m2 & md2 & p & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & UB2 & DST2 & TX2
      & RA2 & GK2 & INIT & REG2 & RES').
    rewrite SEGS in RA2. try rewrite SEGS in DST2. try rewrite SEGS in TX2.
    unfold REC_CANONICAL_K, XMALLOC_K in *. change ALLOC_STACK with 8192 in *.
    destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
    destruct BLK as (b1 & b2 & BLK1 & BLK2).
    pose proof FRESH as (FR_lo & FR_hi & FR_img).
    assert (BNI : forall L0 A0 m0 md0 q k i, aa_MR API L0 A0 m0 md0 -> In (q, k) (blocks L0 A0) -> 0 <= i < k ->
                  ~ in_img B (q + i)).
    { intros La Aa m0 md0 q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p0 k0] & Eq & Hp).
      cbn in Eq. injection Eq as <- <-. exact (YL01.ax_blocks_img AX _ _ _ _ p0 k0 i HM Hp Hi). }
    assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
    { intros a Ha. split; intros Ho;
        [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
    assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp - 32) ->
       mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
       (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
      apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; cbn beta in F; lia].
      unfold scratch_k. rewrite SP1. intros [H|H]; lia. }
    assert (REC2 : forall a, e <= a < e + 56 ->
       mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
       (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { intros a Ha. destruct (RECI a Ha) as (Hi & He & Ho).
      apply HFRAME; [right; exact Hi | exact (Ho _ _ _ _ MR1) | exact (Ho _ _ _ _ HMR') | |].
      - unfold scratch_k. rewrite SP1. intros [H|H]; [lia | exact (He H)].
      - intros Hp. apply (FR_img (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi. }
    assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_8 : reg_get R2 8 = Z_to_bv 64 e) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (E2_9 : reg_get R2 9 = Z_to_bv 64 line) by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
    assert (E2_10 : reg_get R2 10 = Z_to_bv 64 p) by exact A0'.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                    [CB 8 junk; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + i) ltac:(lia) ltac:(lia)) as [E W].
      split; [exact E | apply W]. }
    assert (NA1 : bytes_at rsegs m1 (e + 4) (le4 (Z_to_bv 64 mv))).
    { apply (bytes_at_transfer rsegs mem); [exact NA|]. intros i Hi. rewrite length_le4 in Hi.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    assert (NA2 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 mv))).
    { apply (bytes_at_transfer rsegs m1); [exact NA1|]. intros i Hi. rewrite length_le4 in Hi.
      rewrite <- SEGS. exact (proj1 (REC2 (e + 4 + i) ltac:(lia))). }
    assert (WRE2 : wr_at rsegs m2 e 56).
    { destruct WRE as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
      assert (Wm : writable_at rsegs mem (e + i)) by exact (W2 i Hi).
      assert (Wm1 : writable_at rsegs m1 (e + i)) by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia | exact Wm]).
      rewrite <- SEGS in Wm1. pose proof (proj1 (proj2 (REC2 (e + i) ltac:(lia))) Wm1) as Wm2. rewrite SEGS in Wm2.
      exact Wm2. }
    rewrite E1_1, SEGS.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2, E2_8, E2_10.
      eapply al_run3; [exact NA2 | lia | exact WRE2 | exact FR2 | lia | lia | lia | lia]. }
    intros ms3 (can3 & Q3 & EQ3). unfold al_fin in Q3.
    destruct Q3 as (a1'' & a2'' & a3'' & a4'' & m3 & -> & MU3 & WM3 & NA3 & ARG3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 56) ->
              outside [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)] a)
      by (intros a _ Ha; cbn; split; [lia | split; [lia | exact I]]).
    assert (BS' : bytes_at rsegs mem line (T ++ [Z_to_bv 8 0])).
    { replace (T ++ Z_to_bv 8 0 :: slack) with ((T ++ [Z_to_bv 8 0]) ++ slack) in BS by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in BS. exact (proj1 BS). }
    assert (MR3 : aa_MR API L' A' m3 md2).
    { eapply (mr_frame B _ LAWS L' A' m2 m3 md2 md2 HMR').
      - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
        rewrite SEGS. eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia|]].
        intros Hr. exact (proj2 (proj2 (RECI a Hr)) _ _ _ _ HMR' Ho).
      - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
        eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp].
        intros Hr. exact (proj2 (proj2 (RECI a Hr)) _ _ _ _ HMR' Ho).
      - intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 q n i HMR' Hin Hi) as (Hp & H4 & Hc & _).
        pose proof (YL01.ax_blocks_img AX _ _ _ _ q n i HMR' Hin Hi) as NI.
        eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp].
        intros Hr. exact (NI (proj1 (RECI _ Hr))).
      - reflexivity.
      - exact Hh2.
      - exact Hl2.
      - exact Hmat2. }
    apply SR_ret.
    exists L', A', R3, m3, md2.
    split; [reflexivity|].
    split.
    { intros q k i Hq _ Hi.
      destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
      pose proof (BNI _ _ _ _ q k i HMR Hq Hi) as NI.
      rewrite SEGS. rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia)).
      2: { apply OUT3; [lia|]. intros Hr. exact (NI (proj1 (RECI _ Hr))). }
      pose proof (KEPT q k i Hq (fun F => F) Hi) as KE. rewrite SEGS in KE. rewrite KE.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split; [exact UB2|].
    split.
    { apply (bytes_at_transfer rsegs mem); [exact BS'|]. intros i Hi0. rewrite length_app in Hi0. cbn [length] in Hi0.
      assert (Hi : 0 <= i < l + 1) by lia.
      rewrite (munch_mbyte _ _ _ _ (line + i) MU3 ltac:(lia)) by (apply OUT3; lia).
      assert (K12 : mbyte rsegs m2 (line + i) = mbyte rsegs m1 (line + i)).
      { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
        - rewrite <- SEGS. exact (proj1 (HI2 (line + i) ltac:(lia) ltac:(lia))).
        - pose proof (KEPT q k (line + i - q) Hq (fun F => F) ltac:(lia)) as E.
          replace (q + (line + i - q)) with (line + i) in E by ring. rewrite <- SEGS. exact E.
        - rewrite <- SEGS in RA1, RA2. rewrite <- SEGS.
          rewrite (mbyte_ro_agree _ _ _ RA2 (H3 i Hi)), (mbyte_ro_agree _ _ _ RA1 (H3 i Hi)). reflexivity. }
      rewrite K12. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split.
    { intros x Hx. destruct (Z_le_gt_dec e (bv_unsigned x)) as [D1|D1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (e + 56)) as [D2|D2]|].
      - exfalso. rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite al_ro_rec in Hx by lia. discriminate.
      - unfold mrd. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
        rewrite (MU3 x) by (apply OUT3; lia). exact (RA2 x Hx).
      - unfold mrd. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
        rewrite (MU3 x) by (apply OUT3; lia). exact (RA2 x Hx). }
    split.
    { intros i Hi. rewrite GOTG, SEGS.
      rewrite (munch_mbyte _ _ _ _ (0x22d40 + i) MU3 ltac:(lia)) by (apply OUT3; lia).
      pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. rewrite G.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    split; [exact REG2|].
    right. split; [exact M6|]. exists p.
    split.
    { split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
      split.
      { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9)) regs R1 R2 R3 _ _ X1 HPRES X3).
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
          subst r. split; reflexivity.
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
          subst r. discriminate O. }
      split; [exact HVM|].
      split.
      { intros a HA NO1 NO2 NS NE. cbn beta in NE.
        assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
        assert (NSP : ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp)).
        { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
        assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
        pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
        pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
        assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                      (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
        { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | intros F; apply NE; right; right; exact F].
          unfold scratch_k. rewrite SP1. intros [H|H]; [lia | exact (NER H)]. }
        assert (O3 : outside [(e + 4, e + 8); (e + 8 + 8 * mv, e + 16 + 8 * mv)] a).
        { cbn. split; [intros H; apply NE; left; lia | split; [intros H; apply NE; right; left; lia | exact I]]. }
        pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR O3) as E23.
        pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR O3) as W23.
        split; [rewrite E23, (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), W23; tauto]. }
      split.
      { intros q n i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
        pose proof (YL01.ax_blocks_img AX _ _ _ _ q n i HMR Hin Hi) as NI.
        rewrite (munch_mbyte _ _ _ _ (ptr_addr L q + i) MU3 ltac:(lia)).
        2: { apply OUT3; [lia|]. intros Hr. exact (NI (proj1 (RECI _ Hr))). }
        rewrite (HBLKS q n i Hin Hin' Hi).
        apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
      intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
      rewrite SEGS. apply WM3. rewrite <- SEGS.
      destruct Ha as [Ha|Ha].
      - destruct (Z_lt_ge_dec a (bv_unsigned sp - 32)) as [D|D].
        + apply HSCR. unfold scratch_k. rewrite SP1. left. lia.
        + destruct (NOWN a ltac:(lia)) as [N1 N2].
          apply (proj1 (proj2 (HFRAME a ltac:(left; lia) N1 N2 ltac:(unfold scratch_k; rewrite SP1;
                   intros [H|H]; lia) ltac:(intros F; cbn beta in F; lia)))).
          rewrite SEGS. apply WM1. apply HWS. lia.
      - apply HSCR. right. exact Ha. }
    split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
    split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
    split; [exact NA3|]. split; [exact ARG3|].
    split.
    { apply (bytes_at_transfer rsegs m2); [exact DST2|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      pose proof (canon_length T) as CL.
      apply (munch_mbyte _ _ _ _ _ MU3); [lia|]. apply OUT3; [lia|]. intros Hr.
      apply (FR_img i); [lia|]. exact (proj1 (RECI _ Hr)). }
    split; [exact INIT | exact RES'].
Qed.


End X.
