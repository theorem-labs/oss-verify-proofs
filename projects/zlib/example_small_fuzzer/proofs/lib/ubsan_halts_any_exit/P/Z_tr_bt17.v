(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.

Module Z_tr_bt14.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma find_char : forall t s FC DL HP HL HM DP BC OL SL MC ML r,
  r = gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (ML - 1) -> 0 <= r -> 0 <= ML ->
  r <= ML - 1 /\ (forall j, r < j <= ML - 1 -> arr_get BC j = 0) /\ arr_get BC r <> 0.
Proof.
  intros until r. intros Er Hr HML. rewrite Er in Hr.
  destruct (find_spec (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (ML - 1) Hr) as (A & B & C). rewrite <- Er in A, B, C, Hr.
  split; [exact A|]. split.
  - intros j Hj. rewrite <- (bt_bl_count_get s t FC DL HP HL HM DP BC OL SL MC j). apply B. exact Hj.
  - destruct C as [C|C]; [exfalso; lia|]. rewrite bt_bl_count_get in C. exact C.
Qed.

Lemma lor_hi32 : forall x, 0 <= x -> Z.lor 4294967295 (x * 4294967296) = x * 4294967296 + 4294967295.
Proof.
  intros x Hx. rewrite Z.add_comm. symmetry. apply Z.add_nocarry_lor.
  change 4294967295 with (Z.ones 32). rewrite Z.land_comm, Z.land_ones by lia. change (2^32) with 4294967296. apply Z.mod_mul. lia.
Qed.

Definition gl2R (L : dlay) (T ovf mc ML : Z) (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L + 2976 + ML * 2)) (wz ovf) (wz 18446744069414584320) (wz (dl_As L + 2976 + ML * 2)) (wz ((ML + 1) * 4294967296)) (wz 2) a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz ML) s10 s11 t3 t4 t5 t6.

Lemma wz_sub32 : forall x, wz (x * 4294967296 + 18446744069414584320) = wz ((x - 1) * 4294967296).
Proof.
  intros x. apply Z_to_bv_eqm. replace (x * 4294967296 + 18446744069414584320) with ((x - 1) * 4294967296 + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition gl2fR (L : dlay) (T ovf mc ML A0 A6 : Z) (a7 : word) (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L + 2976 + ML * 2)) (wz A0) (wz 18446744069414584320) (wz (dl_As L + 2976 + ML * 2))
      (wz ((ML + 1) * 4294967296)) (wz 2) (wz ovf) (wz A6) a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz ML) s10 s11 t3 t4 t5 t6.

Lemma gl2_find : forall (d : nat) (P : machine_state -> Prop) (L : dlay) (T ovf mc ML b r A0 A6 : Z) (BC : arr) (a7 : word)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L ->
  Z.of_nat d = b - r -> 0 <= r -> b < 15 -> (forall j, r < j <= b -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 ->
  A0 = (b + 2) * 4294967296 -> A6 = dl_As L + 2976 + (b + 1) * 2 ->
  evt psegs P (MS (gl2fR L T ovf mc ML ((r + 1) * 4294967296) (dl_As L + 2976 + r * 2) (wz (arr_get BC r)) ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf48) fc None m (seg_rom psegs)) ->
  evt psegs P (MS (gl2fR L T ovf mc ML A0 A6 a7 ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf38) fc None m (seg_rom psegs)).
Proof.
  induction d as [|d IH]; intros until m; intros BLC MI LAY Ed Rr Rb Z0 NZ RV E0 E6 K; subst A0 A6.
  - assert (b = r) by lia. subst b.
    pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read psegs m _ (av16 BC 16) r _ (wa (dl_As L + 2976 + (r + 1) * 2 + -2)) BLC (av16_nth BC 16 r ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    unfold gl2fR. zs2. rewrite zx16_small by lia. zs2. zs2.
    zstep. br_cases K2; [exfalso; lia|].
    rewrite wz_sub32. reg_as ((r + 2 - 1) * 4294967296) ((r + 1) * 4294967296). reg_as (dl_As L + 2976 + (r + 1) * 2 + -2) (dl_As L + 2976 + r * 2).
    exact K.
  - pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read psegs m _ (av16 BC 16) b _ (wa (dl_As L + 2976 + (b + 1) * 2 + -2)) BLC (av16_nth BC 16 b ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    rewrite (Z0 b ltac:(lia)) in RDb.
    unfold gl2fR. zs2. rewrite zx16_small by lia. zs2. zs2.
    zstep. br_true.
    rewrite wz_sub32.
    eapply (IH P L T ovf mc ML (b - 1) r _ _ BC); [exact BLC| exact MI| exact LAY| lia| exact Rr| lia| intros j Hj; apply Z0; lia| exact NZ| exact RV| lia| lia| exact K].
Qed.

Lemma shr31 : forall x, 0 <= x -> Z.shiftr (x * 4294967296) 31 = x * 2.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^31) with 2147483648. replace (x * 4294967296) with (x * 2 * 2147483648) by lia. apply Z.div_mul. lia. Qed.
Lemma le2_wrap16 : forall x y, x = y -> le2 (wz x) = le2 (wz (wrap16 y)).
Proof. intros x y ->. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem. reflexivity. Qed.

Notation Wg2 L := [(dl_As L + 2976, dl_As L + 3008)] (only parsing).

Definition gl2_iter_post (L : dlay) (T ovf mc ML : Z) (BC' : arr)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 pcx m',
    ms' = MS (gl2R L T (ovf - 2) mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wg2 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ ((pcx = 0x1bf2c /\ 0 < ovf - 2) \/ (pcx = 0x1bf78 /\ ovf - 2 <= 0)).

Lemma gl2_iter : forall (L : dlay) (T ovf mc ML r : Z) (BC : arr)
    (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L -> arr_len BC = 16 ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> 0 <= r <= ML - 1 -> (forall j, r < j <= ML - 1 -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 ->
  evt psegs (gl2_iter_post L T ovf mc ML (bl_adj ML BC r) ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gl2R L T ovf mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf2c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros BLC MI LAY LBC RML Ro Rr Z0 NZ RV.
  pose proof (munch_refl (Wg2 L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold gl2R. zs2. zs2. zs2.
  eapply (gl2_find (Z.to_nat (ML - 1 - r)) _ L T ovf mc ML (ML - 1) r _ _ BC); [exact BLC| exact MI| exact LAY| lia| lia| lia| exact Z0| exact NZ| exact RV| lia| lia|].
  pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gl2fR. zs2. zs2.
  rewrite signed_wz, shr31 by lia.
  a16_store BLC BC 16 (dl_As L + 2976) r (wrap16 (arr_get BC r - 1)) ltac:(apply le2_wrap16; lia).
  set (BC1 := arr_set BC r (wrap16 (arr_get BC r - 1))) in *.
  match goal with H : u8arr psegs ?mm _ (u16s (av16 BC1 16)) |- _ =>
    pose proof (u16arr_read psegs mm _ (av16 BC1 16) (r + 1) _ (wa (dl_As L + 2976 + (r + 1) * 2)) H (av16_nth BC1 16 (r + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
  zs2. zs2. zs2.
  a16_store BLC BC1 16 (dl_As L + 2976) (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2)) ltac:(apply le2_add_sx16).
  set (BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2))) in *.
  match goal with H : u8arr psegs ?mm _ (u16s (av16 BC2 16)) |- _ =>
    pose proof (u16arr_read psegs mm _ (av16 BC2 16) ML _ (wa (dl_As L + 2976 + ML * 2)) H (av16_nth BC2 16 ML ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
  zs2. zs2.
  a16_store BLC BC2 16 (dl_As L + 2976) ML (wrap16 (arr_get BC2 ML - 1)) ltac:(replace (arr_get BC2 ML - 1) with (arr_get BC2 ML + -1) by lia; apply le2_add_sx16).
  zs2. zstep.
  assert (EBA : bl_adj ML BC r = arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1))) by reflexivity.
  br_cases K; reg_as (ovf + -2) (ovf - 2).
  - apply evt_done. unfold gl2_iter_post, gl2R. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. left. split; [reflexivity| lia].
  - apply evt_done. unfold gl2_iter_post, gl2R. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. right. split; [reflexivity| lia].
Qed.

Lemma bl_adj_len : forall ML BC r, arr_len (bl_adj ML BC r) = arr_len BC.
Proof. intros. unfold bl_adj. rewrite !arr_len_set. reflexivity. Qed.
Lemma arr_set_range16 : forall (a : arr) i v n, (forall j, 0 <= j < n -> 0 <= arr_get a j < 65536) -> forall j, 0 <= j < n -> 0 <= arr_get (arr_set a i (wrap16 v)) j < 65536.
Proof.
  intros a i v n H j Hj. rewrite arr_get_set. destruct ((i =? j) && arr_inb a i); [apply SendModel.wrap16_range'| apply H; exact Hj].
Qed.
Lemma bl_adj_range : forall ML BC r, (forall j, 0 <= j < 16 -> 0 <= arr_get BC j < 65536) -> forall j, 0 <= j < 16 -> 0 <= arr_get (bl_adj ML BC r) j < 65536.
Proof. intros ML BC r H. unfold bl_adj. apply arr_set_range16. apply arr_set_range16. apply arr_set_range16. exact H. Qed.

Definition gl2_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL : Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 BC' ovf' m',
    ms' = MS (gl2R L T ovf' mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf78) fc None m' (seg_rom psegs)
    /\ munch (Wg2 L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ R = bt_upd s t FC DL HP HL HM DP BC' OL SL mc
    /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536).

Lemma gl2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T ovf mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L -> munch (Wg2 L) m0 m -> wmono psegs m0 m -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> ovf <= 2 * Z.of_nat f ->
  R = gen_bitlen_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ML ovf ->
  gb2_ok ML f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ovf ->
  evt psegs (gl2_loop_post L s t T mc ML FC DL HP HL HM DP OL SL R ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (gl2R L T ovf mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf2c) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros BLC MI LAY MU WM LBC RBC RML Ro Hf ER OK.
  { exfalso. lia. }
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (GL2_step t ML) in ER. destruct (gb2_ok_step t ML f s FC DL HP HL HM DP BC OL SL mc ovf OK) as [Hr OK'].
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) (ML - 1)) in *.
  destruct (find_char t s FC DL HP HL HM DP BC OL SL mc ML r eq_refl Hr ltac:(lia)) as (Hr1 & Z0 & NZ).
  call (gl2_iter L T ovf mc ML r BC).
  1:{ exact BLC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RML. } 1:{ exact Ro. } 1:{ lia. } 1:{ exact Z0. } 1:{ exact NZ. } 1:{ apply RBC. lia. }
  pose proof (av16_zlength (bl_adj ML BC r) 16 ltac:(lia)) as L16'.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - rewrite (proj2 (Z.ltb_lt 0 (ovf - 2)) K) in ER.
    eapply (IH L s t T (ovf - 2) mc ML FC DL HP HL HM DP (bl_adj ML BC r) OL SL R m0);
      [eassumption| eassumption| exact LAY| exact MU| exact WM| rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC| exact RML| lia| lia| exact ER| apply OK'; exact K].
  - rewrite (proj2 (Z.ltb_ge 0 (ovf - 2))) in ER by lia.
    apply evt_done. unfold gl2_loop_post. do 3 eexists. exists (bl_adj ML BC r), (ovf - 2). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
    split; [rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC].
Qed.
End Z_tr_bt14.


Module Z_tr_bt16.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma gc2_model : forall s t FC DL HP HL HM DP BC OL SL MC f nc mc n R,
  R = gen_codes_loop2 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n -> n <= mc ->
  R = (if arr_get DL n =? 0 then gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc (n + 1)
       else gen_codes_loop2 f (bt_upd s t (arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP BC OL SL MC) t
              (arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) mc (n + 1)).
Proof.
  intros until R. intros ER Hn.
  rewrite <- (bt_set_tree_fc s t FC DL HP HL HM DP BC OL SL MC FC) in ER. rewrite loop2_S in ER.
  rewrite (proj2 (Z.leb_le n mc) Hn) in ER. cbv zeta in ER. rewrite !bt_Len in ER. rewrite !bt_set_tree_fc in ER. exact ER.
Qed.

Lemma gc2_out : forall f X t nc mc n, mc < n -> gen_codes_loop2 f X t nc mc n = X.
Proof. intros. apply loop2_out. assumption. Qed.

Definition res_ok (r l : Z) : Prop := 0 <= r < 2 ^ (16 - l).
Lemma res_ok_0 : forall l, 1 <= l <= 15 -> res_ok 0 l.
Proof. intros l H. unfold res_ok. split; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.
Lemma res_ok_lor : forall c r l, 1 <= l <= 15 -> res_ok r l -> 0 <= Z.lor (c mod 2 ^ 1) r < 2 ^ 31.
Proof.
  intros c r l Hl H. unfold res_ok in H.
  assert (B : 1 < 2 ^ (16 - l)) by (apply (Z.pow_gt_1 2); lia).
  pose proof (lor_bit_bound r c (16 - l) ltac:(lia) H B) as X.
  assert (2 ^ (16 - l) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma res_ok_step : forall c r l, 2 <= l <= 15 -> res_ok r l -> res_ok (Z.lor (c mod 2 ^ 1) r * 2 ^ 1) (l - 1).
Proof.
  intros c r l Hl H. unfold res_ok in *.
  assert (B : 1 < 2 ^ (16 - l)) by (apply (Z.pow_gt_1 2); lia).
  pose proof (lor_bit_bound r c (16 - l) ltac:(lia) H B) as X.
  replace (16 - (l - 1)) with (16 - l + 1) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.


Lemma res_ok_bound : forall r l, 1 <= l <= 15 -> res_ok r l -> 0 <= r < 65536.
Proof. intros r l Hl H. unfold res_ok in H. assert (2 ^ (16 - l) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). lia. Qed.
Lemma srliw1 : forall c, 0 <= c < 65536 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 c) 1) = c / 2 ^ 1.
Proof.
  intros c Hc. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply bv_swrap32_id. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Definition gcR (T n mc1 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) (wz (bv_unsigned sp + 8)) (wz mc1) (wz 1) a4 a5 a6 a7
      (wz T) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition gc_brl_post (T n mc1 v : Z) (a4 : word)
    (ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 m',
    ms' = MS (gcR T n mc1 ra sp gp tp (wz v) t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c150) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma gc_brl : forall (d : nat) (T n mc1 c r l : Z) (a4 t0 : word)
    (ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv psegs m -> Z.of_nat d = l - 1 -> 1 <= l <= 15 -> 0 <= c < 65536 -> res_ok r l ->
  evt psegs (gc_brl_post T n mc1 (brl c r l) a4 ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gcR T n mc1 ra sp gp tp t0 t1 t2 s0 s1 a4 (wz c) (wz r) (wz (l + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c138) fc None m (seg_rom psegs)).
Proof.
  induction d as [|d IH]; intros until m; intros MI Ed Rl Rc RO.
  - assert (l = 1) by lia. subst l.
    pose proof (res_ok_lor c r 1 ltac:(lia) RO) as RB. pose proof (res_ok_bound r 1 ltac:(lia) RO) as Rr.
    unfold gcR. zs2. zs2. rewrite srliw1 by lia. zs2. zs2. zs2. zstep. br_cases K; [exfalso; lia|].
    rewrite land1_mod, Z.lor_comm. rewrite <- (brl_last c r) by lia.
    apply evt_done. unfold gc_brl_post, gcR. do 4 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - pose proof (res_ok_lor c r l ltac:(lia) RO) as RB. pose proof (res_ok_bound r l ltac:(lia) RO) as Rr. pose proof (res_ok_step c r l ltac:(lia) RO) as RO'.
    pose proof (brl_step c r l ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ES. change (2 ^ 1) with 2 in ES, RO'.
    unfold gcR. zs2. zs2. rewrite srliw1 by lia. zs2. zs2. zs2. shl_norm. zstep. br_cases K; [|exfalso; lia].
    rewrite land1_mod. change (2 ^ 1) with 2. rewrite (Z.lor_comm r). reg_as l (l - 1 + 1). rewrite ES.
    eapply evt_mono; [eapply (IH T n mc1 (c / 2) (Z.lor (c mod 2) r * 2) (l - 1)); [exact MI| lia| lia| Z.div_mod_to_equations; lia| exact RO']|].
    intros ms' H. exact H.
Qed.

Definition ncl (w0 : word) (nc : arr) : list word := upd (av16 nc 16) 0 w0.
Lemma ncl_length : forall w0 nc, length (ncl w0 nc) = 16%nat.
Proof. intros. unfold ncl. rewrite upd_length, av16_length. reflexivity. Qed.
Lemma ncl_zlength : forall w0 nc, Z.of_nat (length (u16s (ncl w0 nc))) = 32.
Proof. intros. rewrite u16s_length, ncl_length. reflexivity. Qed.
Lemma ncl_nth : forall w0 nc i, 1 <= i < 16 -> nth_error (ncl w0 nc) (Z.to_nat i) = Some (wz (arr_get nc i)).
Proof. intros w0 nc i Hi. unfold ncl. rewrite nth_error_upd_other by lia. apply av16_nth. lia. Qed.
Lemma upd_comm : forall {X} (l : list X) i j (x y : X), i <> j -> upd (upd l i x) j y = upd (upd l j y) i x.
Proof. intros X l. induction l as [|h l IH]; intros [|i] [|j] x y H; cbn [upd]; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.
Lemma ncl_write : forall m A w0 nc i (w : word) v,
  u8arr psegs m A (u16s (ncl w0 nc)) -> 1 <= i < 16 -> arr_len nc = 16 -> le2 w = le2 (wz v) ->
  u8arr psegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (u16s (ncl w0 (arr_set nc i v))).
Proof.
  intros m A w0 nc i w v ARR Hi Hn E.
  assert (EQ : u16s (ncl w0 (arr_set nc i v)) = u16s (upd (ncl w0 nc) (Z.to_nat i) w)).
  { unfold ncl. rewrite <- av16_upd by lia. rewrite (upd_comm (av16 nc 16) (Z.to_nat i) 0%nat) by lia. apply u16s_upd_le2. symmetry. exact E. }
  rewrite EQ. apply (u16arr_write psegs); [exact ARR|]. rewrite ncl_length. lia.
Qed.

Ltac nc_store ARR w0 nc A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (ncl w0 nc) idx (wa (A + 2 * idx)) ARR ltac:(rewrite ncl_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (ncl_write m0 A w0 nc idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "LNC" in pose proof (ncl_zlength w0 (arr_set nc idx v)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set nc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Notation Wgc T N sp := [(T%Z, (T + 4 * N)%Z); (bv_unsigned sp + 8, bv_unsigned sp + 40)] (only parsing).

Definition gc_iter_post (T N n mc : Z) (w0 : word) (FC' DL nc' : arr)
    (ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a4 a5 a6 a7 pcx m',
    ms' = MS (gcR T (n + 1) (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 nc'))
    /\ ((pcx = 0x1c10c /\ n + 1 <= mc) \/ (pcx = 0x1c158 /\ n = mc)).

Ltac gc_latch MU WM ARR NCA :=
  let K3 := fresh "K3" in
  zs2; zstep; br_cases K3;
  [ apply evt_done; unfold gc_iter_post, gcR; do 8 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [exact NCA|]; right; split; [reflexivity| lia]
  | apply evt_done; unfold gc_iter_post, gcR; do 8 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [exact NCA|]; left; split; [reflexivity| lia] ].

Lemma gc_iter : forall (T N n mc : Z) (w0 : word) (FC DL nc : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (bv_unsigned sp + 8) (u16s (ncl w0 nc)) -> mem_inv psegs m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  0 <= n <= mc -> mc < N -> 0 <= arr_get DL n <= 15 -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  evt psegs (gc_iter_post T N n mc w0
               (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL
               (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1)))
               ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gcR T n (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c10c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR NCA MI RT0 SEP RSP RN LFC LDL LNC Rn Rmc Rl RNC.
  pose proof (munch_refl (Wgc T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  unfold gcR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_eq _ 0) K).
    gc_latch MU WM ARR NCA.
  - rewrite (proj2 (Z.eqb_neq _ 0) K).
    set (len := arr_get DL n) in *.
    pose proof (RNC len ltac:(lia)) as Rc.
    pose proof (u16arr_read psegs m _ (ncl w0 nc) len _ (wa (bv_unsigned sp + 8 + len * 2)) NCA (ncl_nth w0 nc len ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDc.
    zs2. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zs2.
    nc_store NCA w0 nc (bv_unsigned sp + 8) len (wrap16 (arr_get nc len + 1)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (gc_brl (Z.to_nat (len - 1)) T n (mc + 1) (arr_get nc len) 0 len) end.
    1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ exact Rc. } 1:{ apply res_ok_0. lia. }
    rewrite <- bi_reverse_brl by lia.
    unfold gcR.
    ct_store_fc ARR FC DL N T n (wrap16 (bi_reverse (arr_get nc len) len)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    gc_latch MU WM ARR NCA.
Qed.

Lemma gc2_model' : forall s t FC DL HP HL HM DP BC OL SL MC f nc mc n R,
  R = gen_codes_loop2 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n -> n <= mc ->
  R = gen_codes_loop2 f (bt_upd s t (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP BC OL SL MC) t
        (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) mc (n + 1).
Proof. intros until R. intros ER Hn. pose proof (gc2_model _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ER Hn) as E. destruct (arr_get DL n =? 0); exact E. Qed.

Definition gc_loop_post (s : deflate_state) (t : tree_id) (T N mc : Z) (w0 : word) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a4 a5 a6 a7 FC' nc' m',
    ms' = MS (gcR T (mc + 1) (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c158) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 nc'))
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma gc_loop : forall (f : nat) (s : deflate_state) (t : tree_id) (T N n mc : Z) (w0 : word) (FC DL nc HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (bv_unsigned sp + 8) (u16s (ncl w0 nc)) -> mem_inv psegs m ->
  munch (Wgc T N sp) m0 m -> wmono psegs m0 m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  Z.of_nat f = mc + 1 - n -> 0 <= n <= mc -> mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  R = gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n ->
  evt psegs (gc_loop_post s t T N mc w0 DL HP HL HM DP BC OL SL MC R ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (gcR T n (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c10c) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR NCA MI MU WM RT0 SEP RSP RN LFC LDL LNC Ef Rn Rmc RDL RNC ER.
  { exfalso. lia. }
  pose proof (gc2_model' s t FC DL HP HL HM DP BC OL SL MC f nc mc n R ER ltac:(lia)) as ER'. clear ER.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  set (FC' := if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) in *.
  set (nc' := if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) in *.
  assert (LFC' : arr_len FC' = N) by (subst FC'; destruct (arr_get DL n =? 0); [exact LFC| rewrite arr_len_set; exact LFC]).
  assert (LNC' : arr_len nc' = 16) by (subst nc'; destruct (arr_get DL n =? 0); [exact LNC| rewrite arr_len_set; exact LNC]).
  assert (RNC' : forall k, 1 <= k <= 15 -> 0 <= arr_get nc' k < 65536).
  { intros k Hk. subst nc'. destruct (arr_get DL n =? 0); [apply RNC; exact Hk|].
    destruct (Z.eq_dec (arr_get DL n) k) as [<-|NE]; [rewrite arr_get_set_same by (pose proof (RDL n ltac:(lia)); lia); apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RNC; exact Hk]. }
  pose proof (avct_zlength FC' DL N ltac:(lia)) as LCT'. pose proof (ncl_zlength w0 nc') as LNCZ'.
  call (gc_iter T N n mc w0 FC DL nc).
  1:{ exact ARR. } 1:{ exact NCA. } 1:{ exact MI. } 1:{ exact RT0. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. }
  1:{ exact Rn. } 1:{ exact Rmc. } 1:{ apply RDL. lia. } 1:{ exact RNC. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - eapply (IH s t T N (n + 1) mc w0 FC' DL nc' HP HL HM DP BC OL SL MC R m0);
      [eassumption| eassumption| eassumption| exact MU| exact WM| exact RT0| exact SEP| exact RSP| exact RN| exact LFC'| exact LDL| exact LNC'| lia| lia| exact Rmc| exact RDL| exact RNC'| exact ER'].
  - rewrite gc2_out in ER' by lia. subst n.
    apply evt_done. unfold gc_loop_post. do 6 eexists. exists FC', nc'. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'| exact LFC'].
Qed.
End Z_tr_bt16.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.

Module Z_tr_bt15.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma g3i_model : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h R m_,
  R = gen_bitlen_loop3i (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  R = (if MC <? m_ then gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n (h - 1)
       else if arr_get DL m_ =? bits then gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (n - 1) (h - 1)
       else gen_bitlen_loop3i f (bt_upd s t FC (arr_set DL m_ (wrap16 bits)) HP HL HM DP BC (wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) SL MC) t MC bits (n - 1) (h - 1)).
Proof.
  intros until m_. intros ER Hn Em. rewrite GL3i_step in ER. rewrite (proj2 (Z.eqb_neq n 0) Hn) in ER. cbn [negb] in ER.
  rewrite GB3i_flat in ER. rewrite <- Em in ER.
  destruct (MC <? m_); [exact ER|]. destruct (arr_get DL m_ =? bits); exact ER.
Qed.

Lemma g3i_ok_step : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h m_,
  gb3i_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  1 <= h <= 573 /\ 0 <= m_ < 573
  /\ (if MC <? m_ then gb3i_ok t MC f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n (h - 1)
      else if arr_get DL m_ =? bits then gb3i_ok t MC f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits (n - 1) (h - 1)
      else gb3i_ok t MC f (bt_upd s t FC (arr_set DL m_ (wrap16 bits)) HP HL HM DP BC (wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) SL MC) bits (n - 1) (h - 1)).
Proof.
  intros until m_. intros OK Hn Em. cbn [gb3i_ok] in OK. rewrite (proj2 (Z.eqb_neq n 0) Hn) in OK. cbn [negb] in OK.
  destruct OK as (A & B & C). rewrite bt_heap_get in B. rewrite <- Em in B. split; [exact A|]. split; [exact B|].
  rewrite GB3i_flat in C. rewrite <- Em in C.
  destruct (MC <? m_); [exact C|]. destruct (arr_get DL m_ =? bits); exact C.
Qed.

Lemma if_negb_false : forall (A : Type) (a b : A), (if negb false then a else b) = a.
Proof. reflexivity. Qed.
Lemma gb3_ok_S : forall t MC f X bits h,
  gb3_ok t MC (S f) X bits h =
  (if negb (bits =? 0) then
     gb3i_ok t MC 574 X bits (bl_count_get X bits) h
     /\ (let '(X', h') := gen_bitlen_loop3i 574 X t MC bits (bl_count_get X bits) h in gb3_ok t MC f X' (bits - 1) h')
   else True).
Proof. reflexivity. Qed.

Lemma g3_model : forall s t FC DL HP HL HM DP BC OL SL MC f bits h R,
  R = gen_bitlen_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits h -> bits <> 0 ->
  R = (let '(X', h') := gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (arr_get BC bits) h in gen_bitlen_loop3 f X' t MC (bits - 1) h').
Proof.
  intros until R. intros ER Hb. rewrite GL3_step in ER. rewrite (proj2 (Z.eqb_neq bits 0) Hb) in ER. rewrite if_negb_false in ER.
  rewrite bt_bl_count_get in ER. exact ER.
Qed.

Lemma g3_ok_step : forall s t FC DL HP HL HM DP BC OL SL MC f bits h,
  gb3_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits h -> bits <> 0 ->
  gb3i_ok t MC 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits (arr_get BC bits) h
  /\ (let '(X', h') := gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (arr_get BC bits) h in gb3_ok t MC f X' (bits - 1) h').
Proof.
  intros until h. intros OK Hb. rewrite gb3_ok_S in OK. rewrite (proj2 (Z.eqb_neq bits 0) Hb) in OK. rewrite if_negb_false in OK.
  rewrite bt_bl_count_get in OK. exact OK.
Qed.

Definition g3_DL (DL : arr) (mc m_ bits : Z) : arr := if (mc <? m_) || (arr_get DL m_ =? bits) then DL else arr_set DL m_ (wrap16 bits).
Definition g3_OL (FC DL : arr) (OL mc m_ bits : Z) : Z :=
  if (mc <? m_) || (arr_get DL m_ =? bits) then OL else wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_).
Definition g3_n (mc m_ n : Z) : Z := if mc <? m_ then n else n - 1.

Lemma g3i_model' : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h R m_,
  R = gen_bitlen_loop3i (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  R = gen_bitlen_loop3i f (bt_upd s t FC (g3_DL DL MC m_ bits) HP HL HM DP BC (g3_OL FC DL OL MC m_ bits) SL MC) t MC bits (g3_n MC m_ n) (h - 1).
Proof.
  intros until m_. intros ER Hn Em. pose proof (g3i_model _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ER Hn Em) as E. unfold g3_DL, g3_OL, g3_n.
  destruct (MC <? m_); [exact E|]. destruct (arr_get DL m_ =? bits); exact E.
Qed.
Lemma g3i_ok_step' : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h m_,
  gb3i_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  1 <= h <= 573 /\ 0 <= m_ < 573
  /\ gb3i_ok t MC f (bt_upd s t FC (g3_DL DL MC m_ bits) HP HL HM DP BC (g3_OL FC DL OL MC m_ bits) SL MC) bits (g3_n MC m_ n) (h - 1).
Proof.
  intros until m_. intros OK Hn Em. destruct (g3i_ok_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OK Hn Em) as (A & B & C). split; [exact A|]. split; [exact B|].
  unfold g3_DL, g3_OL, g3_n. destruct (MC <? m_); [exact C|]. destruct (arr_get DL m_ =? bits); exact C.
Qed.


Definition g3R (L : dlay) (T bits n h mc A3 : Z) (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 (wz (dl_As L + 3004)) (wz h) (wz n) (wz A3) a4 a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz bits) s10 s11 t3 t4 t5 t6.

Notation Wg3 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition g3_trip_post (L : dlay) (s : deflate_state) (T N bits n' h mc : Z) (FC DL' : arr) (OL' SL : Z)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a5 a6 A3' h0 h1 h2 h3 h4 pcx m',
    ms' = MS (g3R L T bits n' (h - 1) mc A3' ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1bfb8 /\ n' <> 0 /\ A3' = dl_As L + 3004 + 4 * (h - 1)) \/ (pcx = 0x1bf8c /\ n' = 0)).

Lemma wz_mulmod : forall a b c, wz (a mod 18446744073709551616 * b + c) = wz (wrap64 (c + a * b)).
Proof.
  intros a b c. apply Z_to_bv_eqm. rewrite wrap64_mod, Z.mod_mod by lia. change 18446744073709551616 with (2^64).
  rewrite (Z.add_comm c). rewrite Z.add_mod by lia. rewrite (Z.mul_mod (a mod 2^64) b) by lia. rewrite Z.mod_mod by lia.
  rewrite <- Z.mul_mod by lia. rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Ltac g3_latch L h n MU WM ARR GD :=
  let K3 := fresh "K3" in
  zs2; zstep; br_cases K3;
  [ reg_as (h + -1) (h - 1); reg_as (n + -1) (n - 1);
    apply evt_done; unfold g3_trip_post, g3R, bD_cells; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [close_cells GD|]; right; split; [reflexivity| lia]
  | zs2; shl_norm; zs2; reg_as (h + -1) (h - 1); reg_as (n + -1) (n - 1);
    apply evt_done; unfold g3_trip_post, g3R, bD_cells; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [close_cells GD|]; left; split; [reflexivity|]; split; [lia| lia] ].

Lemma g3_trip : forall (L : dlay) (s : deflate_state) (T N bits n h mc A3 m_ OL SL : Z) (FC DL HP : arr) (h0 h1 h2 h3 h4 : list byte)
    (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  A3 = dl_As L + 3004 + 4 * h -> 1 <= n < 65536 -> 1 <= h <= 573 -> m_ = arr_get HP (h - 1) -> 0 <= m_ < 573 -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  evt psegs (g3_trip_post L s T N bits (g3_n mc m_ n) h mc FC (g3_DL DL mc m_ bits) (g3_OL FC DL OL mc m_ bits) SL
               ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (g3R L T bits n h mc A3 ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA GD MI LAY RT1 RT2 RN LFC LDL LHP EA3 Rn Rh Em Rm Rmc Rb RDL RFC ROL. subst A3.
  pose proof (munch_refl (Wg3 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read psegs m _ (av32 HP 573) (h - 1) _ (wa (dl_As L + 3004 + 4 * h)) HPA (av32_nth HP 573 (h - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  unfold g3R. zs2. zs2. zs2. zstep. br_cases K.
  -
    assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (En' : g3_n mc m_ n = n) by (unfold g3_n; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    rewrite EDL, EOL, En'. reg_as (h + -1) (h - 1).
    apply evt_done. unfold g3_trip_post, g3R, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ARR|]. split; [exact GD|]. left. split; [reflexivity|]. split; [lia|]. lia.
  - assert (En' : g3_n mc m_ n = n - 1) by (unfold g3_n; rewrite (proj2 (Z.ltb_ge mc m_)) by lia; reflexivity). rewrite En'.
    pose proof (u16arr_read psegs m T (avct FC DL N) (2 * m_ + 1) _ (wa (T + m_ * 4 + 2)) ARR (avct_nth_dl FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
    pose proof (u16arr_read psegs m T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) ARR (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
    pose proof (RDL m_ ltac:(lia)) as Rl. pose proof (RFC m_ ltac:(lia)) as Rf.
    zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K2.
    +
      assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      rewrite EDL, EOL.
      g3_latch L h n MU WM ARR GD.
    + zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2.
      rewrite wz_mulmod. zs2.
      ct_store_dl ARR FC DL N T m_ (wrap16 bits) ltac:(apply le2_wrap16; reflexivity).
      zs2.
      assert (NEb : (arr_get DL m_ =? bits) = false) by (apply Z.eqb_neq; lia).
      assert (EDL : g3_DL DL mc m_ bits = arr_set DL m_ (wrap16 bits)) by (unfold g3_DL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) by (unfold g3_OL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      rewrite EDL, EOL.
      g3_latch L h n MU WM ARR GD.
Qed.

Lemma g3_DL_len : forall DL mc m_ bits, arr_len (g3_DL DL mc m_ bits) = arr_len DL.
Proof. intros. unfold g3_DL. destruct (_ || _); [reflexivity| apply arr_len_set]. Qed.
Lemma g3_DL_range : forall DL mc m_ bits n, (forall j, 0 <= j < n -> 0 <= arr_get DL j < 65536) -> forall j, 0 <= j < n -> 0 <= arr_get (g3_DL DL mc m_ bits) j < 65536.
Proof. intros DL mc m_ bits n H. unfold g3_DL. destruct (_ || _); [exact H| apply arr_set_range16; exact H]. Qed.
Lemma g3_OL_range : forall FC DL OL mc m_ bits, 0 <= OL < 2^64 -> 0 <= g3_OL FC DL OL mc m_ bits < 2^64.
Proof. intros. unfold g3_OL. destruct (_ || _); [assumption| apply wrap64_range]. Qed.

Definition g3i_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N bits mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state * Z)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a5 a6 A3' h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (g3R L T bits 0 h' mc A3' ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf8c) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc, h')
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= h' <= 573.

Lemma g3i_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits n h mc A3 OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> munch (Wg3 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  A3 = dl_As L + 3004 + 4 * h -> 1 <= n < 65536 -> 0 <= h -> h < Z.of_nat f -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits n h ->
  gb3i_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits n h ->
  evt psegs (g3i_loop_post L s t T N bits mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3R L T bits n h mc A3 ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb8) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP EA3 Rn Rh0 Hf Rmc Rb RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  destruct (g3i_ok_step' s t FC DL HP HL HM DP BC OL SL mc f bits n h (arr_get HP (h - 1)) OK ltac:(lia) eq_refl) as (Rh & Rm & OK').
  pose proof (g3i_model' s t FC DL HP HL HM DP BC OL SL mc f bits n h R (arr_get HP (h - 1)) ER ltac:(lia) eq_refl) as ER'. clear ER OK.
  set (m_ := arr_get HP (h - 1)) in *.
  pose proof (avct_zlength FC (g3_DL DL mc m_ bits) N ltac:(lia)) as LCT'.
  call (g3_trip L s T N bits n h mc A3 m_ OL SL FC DL HP h0 h1 h2 h3 h4).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact EA3. } 1:{ exact Rn. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rm. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & EA')|(-> & K)] end.
  - assert (Rn' : 1 <= g3_n mc m_ n < 65536) by (revert K; unfold g3_n; destruct (mc <? m_); lia).
    match goal with HT : u8arr psegs ?mm T _, HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s _ SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N bits (g3_n mc m_ n) (h - 1) mc _ (g3_OL FC DL OL mc m_ bits) SL FC (g3_DL DL mc m_ bits) HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| exact LFC| rewrite g3_DL_len; exact LDL| exact LHP
        | exact EA'| exact Rn'| lia| lia| exact Rmc| exact Rb| apply g3_DL_range; exact RDL| exact RFC| apply g3_OL_range; exact ROL| exact ER'| exact OK'] end.
  - rewrite K in ER'. rewrite GL3i_done in ER'.
    rewrite K.
    apply evt_done. unfold g3i_loop_post. do 9 eexists. exists (g3_DL DL mc m_ bits), (g3_OL FC DL OL mc m_ bits), (h - 1). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'|].
    split; [rewrite g3_DL_len; exact LDL|]. split; [apply g3_DL_range; exact RDL|]. split; [apply g3_OL_range; exact ROL|]. lia.
Qed.

Definition g3oR (L : dlay) (T bits h mc : Z) (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 (wz (dl_As L + 3004)) (wz h) a2 a3 a4 a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz bits) s10 s11 t3 t4 t5 t6.

Definition g3_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5 a6 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (g3oR L T 0 h' mc ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bff8) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = bt_upd s t FC DL' HP HL HM DP BC OL' SL mc
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64.

Lemma g3_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> munch (Wg3 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  Z.of_nat f = bits -> 1 <= bits <= 15 -> 0 <= h <= 573 -> -1 <= mc < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits h ->
  gb3_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits h ->
  evt psegs (g3_loop_post L s t T N mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3oR L T bits h mc ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf94) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP LBC Ef Rb Rh Rmc RBC RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (g3_model s t FC DL HP HL HM DP BC OL SL mc f bits h R ER ltac:(lia)) as ER'.
  destruct (g3_ok_step s t FC DL HP HL HM DP BC OL SL mc f bits h OK ltac:(lia)) as [OKi OKo]. clear ER OK.
  assert (TAIL : forall (DL' : arr) (OL' h' : Z) (g0 g1 g2 g3 g4 : list byte) (b2 b3 b4 b5 b6 : word) (m' : mem),
    u8arr psegs m' T (u16s (avct FC DL' N)) -> u32arr psegs m' (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC 16)) ->
    rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL g0 g1 g2 g3 g4) -> mem_inv psegs m' -> munch (Wg3 L T N) m0 m' -> wmono psegs m0 m' ->
    arr_len DL' = N -> (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) -> 0 <= OL' < 2^64 -> 0 <= h' <= 573 ->
    R = gen_bitlen_loop3 f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) t mc (bits - 1) h' ->
    gb3_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) (bits - 1) h' ->
    evt psegs (g3_loop_post L s t T N mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3oR L T bits h' mc ra sp gp tp t0 t1 t2 s1 b2 b3 b4 b5 b6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1bf8c) fc None m' (seg_rom psegs))).
  { intros DL' OL' h' g0 g1 g2 g3 g4 b2 b3 b4 b5 b6 m' ARR' HPA' BLC' GD' MI' MU' WM' LDL' RDL' ROL' Rh' ER2 OK2.
    unfold g3oR. zs2. zstep. br_cases K; reg_as (bits + -1) (bits - 1).
    - replace (bits - 1) with 0 in * by lia. rewrite GL3_done in ER2.
      apply evt_done. unfold g3_loop_post, g3oR. do 10 eexists. exists DL', OL', h'. eexists.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ARR'|]. split; [exact GD'|]. split; [exact ER2|].
      split; [exact LDL'|]. split; [exact RDL'| exact ROL'].
    - eapply (IH L s t T N (bits - 1) h' mc OL' SL FC DL' HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact ARR'| exact HPA'| exact BLC'| exact GD'| exact MI'| exact LAY| exact MU'| exact WM'| exact RT1| exact RT2| exact RN| exact LFC| exact LDL'| exact LHP| exact LBC
        | lia| lia| exact Rh'| exact Rmc| exact RBC| exact RDL'| exact RFC| exact ROL'| exact ER2| exact OK2]. }
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u16arr_read psegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  pose proof (RBC bits ltac:(lia)) as Rn.
  unfold g3oR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  - zs2. shl_norm. zs2.
    call (g3i_loop 574 L s t T N bits (arr_get BC bits) h mc _ OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4
            (gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits (arr_get BC bits) h) m).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ change (Z.of_nat 574) with 574. lia. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. }
    1:{ exact ROL. } 1:{ reflexivity. } 1:{ exact OKi. }
    match goal with E : gen_bitlen_loop3i 574 _ _ _ _ _ _ = (_, _) |- _ => rewrite E in ER', OKo end.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS (g3R _ _ _ _ ?hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (TAIL dl' ol' hh g0 g1 g2 g3 g4); [exact HT| eassumption| eassumption| exact HG| eassumption| exact MU| exact WM| assumption| assumption| assumption| lia| exact ER'| exact OKo] end.
  -
    rewrite K in ER', OKo. rewrite GL3i_done in ER', OKo.
    zs2.
    eapply (TAIL DL OL h h0 h1 h2 h3 h4); [exact ARR| exact HPA| exact BLC| exact GD| exact MI| exact MU| exact WM| exact LDL| exact RDL| exact ROL| exact Rh| exact ER'| exact OKo].
Qed.
End Z_tr_bt15.

Module Z_tr_bt19p.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).



Section Flat.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).

Definition btX0 : deflate_state :=
  bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) 0 573 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t).

Lemma btX0_eq : set_heap_max (set_heap_len s 0) HEAP_SIZE = btX0.
Proof. unfold btX0. rewrite <- (bt_upd_self s t) at 1. rewrite bt_set_heap_len, bt_set_heap_max. reflexivity. Qed.

Lemma safe_s0 : bt_safe s t ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_fc s t) i < 65536) /\ 0 <= ds_opt_len s < 2 ^ 64 /\ 0 <= ds_static_len s < 2 ^ 64.
Proof. intros H. destruct H as (A & B & C & _). split; [exact A|]. split; [exact B| exact C]. Qed.

Lemma safe_s3 : bt_safe s t ->
  forall FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1 mc1 FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2 mc2,
  build_tree_loop1 (Z.to_nat E) btX0 t E 0 (-1) = (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1, mc1) ->
  build_tree_loop2 2 (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1) t mc1 = (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2, mc2) ->
  (forall i, 1 <= i <= HL2 -> 0 <= arr_get HP2 i < tsize t)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP2 i < 256)
  /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get FC2 i < 65536)
  /\ forall FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4,
     build_tree_loop3 (Z.to_nat (HL2 / 2)) (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2) t (HL2 / 2) = bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 ->
     build_tree_loop4 573 (bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3) t E = bt_upd s t FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4 ->
     arr_len HP4 = 573 -> 1 <= HM4 <= 573 ->
     (forall h, HM4 - 1 + 1 <= h < 573 -> 0 <= arr_get (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) h < tsize t)
     /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get DL4 i < 65536)
     /\ gb1_ok t mc2 573 (bt_upd s t FC4 (arr_set DL4 (arr_get HP4 1) (wrap16 0)) (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 (arr_fill BC4 0 16 0) OL4 SL4 MC4) (HM4 - 1 + 1) 0
     /\ (forall X10 ovf,
           gen_bitlen_loop1 573 (bt_upd s t FC4 (arr_set DL4 (arr_get HP4 1) (wrap16 0)) (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 (arr_fill BC4 0 16 0) OL4 SL4 MC4)
              t mc2 (sd_extra_base t) ML (HM4 - 1 + 1) 0 = (X10, ovf) -> ovf <> 0 ->
           gb2_ok ML 573 X10 ovf /\ gb3_ok t mc2 (Z.to_nat ML) (gen_bitlen_loop2 573 X10 ML ovf) ML 573)
     /\ (forall i, 0 <= i <= mc2 -> 0 <= Len (gen_bitlen (bt_upd s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4) t) t i <= 15).
Proof.
  intros SAFE. intros until mc2. intros E1 E2.
  unfold bt_safe in SAFE. rewrite btX0_eq in SAFE. cbv zeta in SAFE. rewrite E1 in SAFE. cbv beta iota in SAFE. rewrite E2 in SAFE. cbv beta iota in SAFE.
  rewrite !bt_set_max_code, !bt_heap_len in SAFE.
  destruct SAFE as (_ & _ & _ & PQ & RDP & RFC & REST).
  split; [intros i Hi; rewrite <- (bt_heap_get s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply PQ; exact Hi|].
  split; [intros i Hi; rewrite <- (bt_depth_get s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply RDP; exact Hi|].
  split; [intros i Hi; rewrite <- (bt_Freq s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply RFC; exact Hi|].
  intros until MC4. intros E3 E4 LHP4 RHM4.
  rewrite E3, E4 in REST. rewrite !bt_heap_max, !bt_set_heap_max, !bt_heap_get, !bt_heap_set, !bt_heap_max in REST.
  rewrite !bt_bl_count, !bt_set_bl_count, !bt_heap_max, !bt_heap_get, !bt_set_Len, !bt_heap_max in REST.
  change (MAX_BITS + 1) with 16 in REST. unfold HEAP_SIZE, SMALLEST in REST.
  rewrite (arr_get_set_same HP4 (HM4 - 1) (arr_get HP4 1)) in REST by lia.
  destruct REST as (RHP & RDL & OK1 & OK23 & LEN).
  split; [intros h Hh; rewrite <- (bt_heap_get s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4); apply RHP; exact Hh|].
  split; [intros i Hi; rewrite <- (bt_tree_dl s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4); apply RDL; exact Hi|].
  split; [exact OK1|]. split; [| exact LEN].
  intros X10 ovf EQ NZ. rewrite EQ in OK23. exact (OK23 NZ).
Qed.

Lemma build_tree_flat :
  forall FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1 mc1 FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2 mc2
         FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4,
  build_tree_loop1 (Z.to_nat E) btX0 t E 0 (-1) = (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1, mc1) ->
  build_tree_loop2 2 (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1) t mc1 = (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2, mc2) ->
  build_tree_loop3 (Z.to_nat (HL2 / 2)) (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2) t (HL2 / 2) = bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 ->
  build_tree_loop4 573 (bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3) t E = bt_upd s t FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4 ->
  build_tree s t = gen_codes (gen_bitlen (bt_upd s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4) t) t mc2.
Proof.
  intros until MC4. intros E1 E2 E3 E4.
  unfold build_tree. cbv zeta. rewrite btX0_eq, E1, E2. rewrite bt_set_max_code, bt_heap_len, E3, E4.
  rewrite bt_heap_max, bt_set_heap_max, bt_heap_max, bt_heap_get, bt_heap_set. unfold SMALLEST. reflexivity.
Qed.
End Flat.


Definition STP (t : tree_id) : Z := match t with TL => 0x11db0 | TD => 0x12230 | TB => 0 end.
Definition XP (t : tree_id) : Z := match t with TL => 0x122a8 | TD => 0x1231c | TB => 0x12394 end.
Definition SDA (t : tree_id) : Z := match t with TL => 0x29008 | TD => 0x29028 | TB => 0x29048 end.
Definition sd_cells (t : tree_id) : list cell :=
  [C8 (wz (STP t)); C8 (wz (XP t)); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))].

Lemma SDA_range : forall t, 0x29008 <= SDA t <= 0x29048. Proof. destruct t; cbn; lia. Qed.
Lemma STP_range : forall t, 0 <= STP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_range : forall t, 0 <= XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma SDA_desc : forall t, SDA t = match t with TL => Z_SL_DESC | TD => Z_SD_DESC | TB => Z_SBL_DESC end.
Proof. destruct t; reflexivity. Qed.

Ltac relro_cells A cs n :=
  let RC := fresh "RC" in intros m RC; unfold relro_clean, RELRO_LO, RELRO_HI in RC;
  apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast psegs m A [CB n (cells_bytes cs)] cs);
  [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 psegs m A (cells_bytes cs));
    [ intros a Ha; apply RC; change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n) in Ha; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n); lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].

Lemma sdesc_relro_l : forall m, relro_clean m -> rw_cells psegs m 0x29008 [C8 (wz 0x11db0); C8 (wz 0x122a8); C4 (wz 257); C4 (wz 286); C4 (wz 15)].
Proof. relro_cells 0x29008 [C8 (wz 0x11db0); C8 (wz 0x122a8); C4 (wz 257); C4 (wz 286); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_d : forall m, relro_clean m -> rw_cells psegs m 0x29028 [C8 (wz 0x12230); C8 (wz 0x1231c); C4 (wz 0); C4 (wz 30); C4 (wz 15)].
Proof. relro_cells 0x29028 [C8 (wz 0x12230); C8 (wz 0x1231c); C4 (wz 0); C4 (wz 30); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_bl : forall m, relro_clean m -> rw_cells psegs m 0x29048 [C8 (wz 0); C8 (wz 0x12394); C4 (wz 0); C4 (wz 19); C4 (wz 7)].
Proof. relro_cells 0x29048 [C8 (wz 0); C8 (wz 0x12394); C4 (wz 0); C4 (wz 19); C4 (wz 7)] 28%nat. Qed.

Lemma sdesc_relro : forall t m, relro_clean m -> rw_cells psegs m (SDA t) (sd_cells t).
Proof.
  intros t m RC. destruct t; cbn [SDA sd_cells STP XP sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS;
    [apply sdesc_relro_l| apply sdesc_relro_d| apply sdesc_relro_bl]; exact RC.
Qed.

Lemma rod_extra_blbits : forall m, mem_inv psegs m -> bytes_at psegs m 0x12394 (u32s (av32 extra_blbits_a 19)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

Lemma static_ltree_dl_range : forall n, 0 <= n < 288 -> 0 <= arr_get static_ltree_dl n < 16.
Proof. intros n H. ztab_tac 288 (fun i => (0 <=? arr_get static_ltree_dl i) && (arr_get static_ltree_dl i <? 16)) H. lia. Qed.
Lemma static_dtree_dl_range : forall n, 0 <= n < 30 -> 0 <= arr_get static_dtree_dl n < 16.
Proof. intros n H. ztab_tac 30 (fun i => (0 <=? arr_get static_dtree_dl i) && (arr_get static_dtree_dl i <? 16)) H. lia. Qed.
Lemma extra_blbits_range : forall c, 0 <= c < 19 -> 0 <= arr_get extra_blbits_a c < 16.
Proof. intros c H. ztab_tac 19 (fun i => (0 <=? arr_get extra_blbits_a i) && (arr_get extra_blbits_a i <? 16)) H. lia. Qed.

Lemma stree_view_of : forall t, stree_view t (STP t).
Proof.
  intros [| |]; cbn [STP].
  - right. split; [lia|]. split; [reflexivity|]. intros mm node MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_LTREE (avct static_ltree_fc static_ltree_dl 288) (2 * node + 1)); [apply rod_static_ltree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_LTREE; f_equal; lia].
    + cbn [stree_Len]. apply static_ltree_dl_range. lia.
  - right. split; [lia|]. split; [reflexivity|]. intros mm node MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_DTREE (avct static_dtree_fc static_dtree_dl 30) (2 * node + 1)); [apply rod_static_dtree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_DTREE; f_equal; lia].
    + cbn [stree_Len]. apply static_dtree_dl_range. lia.
  - left. split; reflexivity.
Qed.

Lemma stree_view_n_of : forall t, stree_view_n t (STP t).
Proof.
  intros [| |]; cbn [STP]; unfold stree_view_n; cbn [sd_elems stree_has stree_Len]; unfold L_CODES, D_CODES.
  - right. split; [lia|]. split; [reflexivity|]. intros mm n MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_LTREE (avct static_ltree_fc static_ltree_dl 288) (2 * n + 1)); [apply rod_static_ltree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_LTREE; f_equal; lia].
    + apply static_ltree_dl_range. lia.
  - right. split; [lia|]. split; [reflexivity|]. intros mm n MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_DTREE (avct static_dtree_fc static_dtree_dl 30) (2 * n + 1)); [apply rod_static_dtree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_DTREE; f_equal; lia].
    + apply static_dtree_dl_range. lia.
  - left. split; reflexivity.
Qed.

Lemma xbits_view_of : forall t, xbits_view t (XP t).
Proof.
  intros [| |]; unfold xbits_view; cbn [XP sd_extra_base sd_elems sd_extra_bits]; unfold LITERALS, L_CODES, D_CODES, BL_CODES; intros mm n MI Hn; split.
  - apply (u32ro_read mm Z_EXTRA_LBITS (av32 extra_lbits_a 29) (n - (256 + 1))); [apply rod_extra_lbits; exact MI| apply av32_nth; lia| lia| unfold Z_EXTRA_LBITS; f_equal; lia].
  - pose proof (extra_lbits_facts (n - (256 + 1)) ltac:(lia)). lia.
  - apply (u32ro_read mm Z_EXTRA_DBITS (av32 extra_dbits_a 30) (n - 0)); [apply rod_extra_dbits; exact MI| apply av32_nth; lia| lia| unfold Z_EXTRA_DBITS; f_equal; lia].
  - pose proof (extra_dbits_facts (n - 0) ltac:(lia)). lia.
  - apply (u32ro_read mm 0x12394 (av32 extra_blbits_a 19) (n - 0)); [apply rod_extra_blbits; exact MI| apply av32_nth; lia| lia| f_equal; lia].
  - apply extra_blbits_range. lia.
Qed.


Lemma rw_cells_app_iff : forall m A l1 l2,
  rw_cells psegs m A (l1 ++ l2) <-> rw_cells psegs m A l1 /\ rw_cells psegs m (A + Z.of_nat (cells_size l1)) l2.
Proof.
  intros m A l1 l2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add. split.
  - intros (([W1 W2] & BY) & WR).
    rewrite bytes_at_app in BY. destruct BY as [B1 B2]. rewrite (cells_bytes_length l1 W1) in B2.
    apply wr_at_app in WR; [| lia| lia]. destruct WR as [R1 R2].
    split; (split; [split|]); assumption.
  - intros (([W1 B1] & R1) & ([W2 B2] & R2)). split; [split; [split; assumption|]|].
    + apply bytes_at_app. rewrite (cells_bytes_length l1 W1). split; assumption.
    + apply wr_at_app; [lia| lia|]. split; assumption.
Qed.

Lemma rw_cells_split2 : forall m A l1 l2 B, rw_cells psegs m A (l1 ++ l2) -> B = A + Z.of_nat (cells_size l1) ->
  rw_cells psegs m A l1 /\ rw_cells psegs m B l2.
Proof. intros m A l1 l2 B H ->. apply rw_cells_app_iff. exact H. Qed.
Lemma rw_cells_join2 : forall m A l1 l2 B, rw_cells psegs m A l1 -> rw_cells psegs m B l2 -> B = A + Z.of_nat (cells_size l1) ->
  rw_cells psegs m A (l1 ++ l2).
Proof. intros m A l1 l2 B H1 H2 ->. apply rw_cells_app_iff. split; assumption. Qed.
End Z_tr_bt19p.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).



Definition eqm (a b : Z) : Prop := a mod 2 ^ 16 = b mod 2 ^ 16.
Lemma eqm_refl : forall a, eqm a a. Proof. intros. reflexivity. Qed.
Lemma eqm_add : forall a a' b b', eqm a a' -> eqm b b' -> eqm (a + b) (a' + b').
Proof. unfold eqm. intros a a' b b' H1 H2. rewrite Zplus_mod, H1, H2, <- Zplus_mod. reflexivity. Qed.
Lemma eqm_addc : forall a a' b b', eqm a b' -> eqm b a' -> eqm (a + b) (a' + b').
Proof. intros a a' b b' H1 H2. rewrite (Z.add_comm a' b'). apply eqm_add; assumption. Qed.
Lemma eqm_mul2 : forall a a', eqm a a' -> eqm (a * 2) (a' * 2 ^ 1).
Proof. unfold eqm. intros a a' H. change (2 ^ 1) with 2. rewrite Zmult_mod, H, <- Zmult_mod. reflexivity. Qed.
Lemma eqm_shl1 : forall a a', eqm a a' -> eqm (Z.shiftl a 1) (a' * 2 ^ 1).
Proof. intros a a' H. rewrite Z.shiftl_mul_pow2 by lia. unfold eqm. rewrite Zmult_mod, H, <- Zmult_mod. reflexivity. Qed.
Lemma eqm_mod64 : forall a a', eqm a a' -> eqm (a mod 18446744073709551616) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_mod64. exact H. Qed.
Lemma eqm_uwz : forall a a', eqm a a' -> eqm (bv_unsigned (wz a)) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_unsigned_wz. exact H. Qed.
Lemma eqm_sx16 : forall a a', eqm a a' -> eqm (bv_unsigned (sx16 (wz a))) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_sx16, lo16_unsigned_wz. exact H. Qed.
Lemma eqm_zx16 : forall a a', eqm a a' -> eqm (bv_unsigned (zx16 (wz a))) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_zx16, lo16_unsigned_wz. exact H. Qed.

Ltac eqm_go := first
  [ apply eqm_refl
  | apply eqm_mod64; eqm_go
  | apply eqm_shl1; eqm_go
  | apply eqm_mul2; eqm_go
  | apply eqm_sx16; eqm_go
  | apply eqm_zx16; eqm_go
  | apply eqm_uwz; eqm_go
  | apply eqm_add; eqm_go
  | apply eqm_addc; eqm_go ].

Lemma NC_get : forall blc k, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) -> 1 <= k <= 15 ->
  arr_get (NC blc) k = wrap16 (gcode (arr_get blc) (Z.to_nat k)).
Proof. intros blc k RB Hk. destruct (NC_spec blc RB) as [_ E]. rewrite <- (E (Z.to_nat k)) by lia. f_equal. lia. Qed.

Lemma le2_eqm_NC : forall blc (w : word) k, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) -> 1 <= k <= 15 ->
  eqm (bv_unsigned w) (gcode (arr_get blc) (Z.to_nat k)) -> le2 w = le2 (wz (arr_get (NC blc) k)).
Proof.
  intros blc w k RB Hk E. apply le2_wz_mod. rewrite (NC_get blc k RB Hk). rewrite wrap16_mod. rewrite lo16_idem. exact E.
Qed.

Lemma le2_of_bytes : forall j : list byte, length j = 2%nat -> exists w0 : word, le2 w0 = j.
Proof.
  intros [|x [|y [|z l]]] H; try discriminate.
  exists (wz (bv_unsigned x + 256 * bv_unsigned y)).
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry. unfold bv_modulus in Rx, Ry. cbn in Rx, Ry.
  unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z_to_le_bytes].
  rewrite Z.mod_small by (cbn; lia).
  f_equal; [| f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  - change (2 ^ Z.of_N 8) with 256. Z.div_mod_to_equations. lia.
  - change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma zseq_16 : zseq 16 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]. Proof. reflexivity. Qed.

Lemma ncl_intro : forall m A j0 blc (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : word),
  rw_cells psegs m A [CB 2 j0; C2 r1; C2 r2; C2 r3; C2 r4; C2 r5; C2 r6; C2 r7; C2 r8; C2 r9; C2 r10; C2 r11; C2 r12; C2 r13; C2 r14; C2 r15] ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  eqm (bv_unsigned r1) (gcode (arr_get blc) 1) -> eqm (bv_unsigned r2) (gcode (arr_get blc) 2) -> eqm (bv_unsigned r3) (gcode (arr_get blc) 3) ->
  eqm (bv_unsigned r4) (gcode (arr_get blc) 4) -> eqm (bv_unsigned r5) (gcode (arr_get blc) 5) -> eqm (bv_unsigned r6) (gcode (arr_get blc) 6) ->
  eqm (bv_unsigned r7) (gcode (arr_get blc) 7) -> eqm (bv_unsigned r8) (gcode (arr_get blc) 8) -> eqm (bv_unsigned r9) (gcode (arr_get blc) 9) ->
  eqm (bv_unsigned r10) (gcode (arr_get blc) 10) -> eqm (bv_unsigned r11) (gcode (arr_get blc) 11) -> eqm (bv_unsigned r12) (gcode (arr_get blc) 12) ->
  eqm (bv_unsigned r13) (gcode (arr_get blc) 13) -> eqm (bv_unsigned r14) (gcode (arr_get blc) 14) -> eqm (bv_unsigned r15) (gcode (arr_get blc) 15) ->
  exists w0, u8arr psegs m A (u16s (ncl w0 (NC blc))).
Proof.
  intros until r15. intros FR RB E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
  destruct FR as [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [Lj _].
  destruct (le2_of_bytes j0 Lj) as [w0 Ew]. exists w0.
  cbn [cells_bytes cbytes app] in BY. cbn [cells_size csize Nat.add] in WR.
  unfold ncl, av16. rewrite zseq_16. cbn [map upd u16s].
  rewrite Ew.
  rewrite <- (le2_eqm_NC blc r1 1 RB ltac:(lia) E1), <- (le2_eqm_NC blc r2 2 RB ltac:(lia) E2), <- (le2_eqm_NC blc r3 3 RB ltac:(lia) E3),
          <- (le2_eqm_NC blc r4 4 RB ltac:(lia) E4), <- (le2_eqm_NC blc r5 5 RB ltac:(lia) E5), <- (le2_eqm_NC blc r6 6 RB ltac:(lia) E6),
          <- (le2_eqm_NC blc r7 7 RB ltac:(lia) E7), <- (le2_eqm_NC blc r8 8 RB ltac:(lia) E8), <- (le2_eqm_NC blc r9 9 RB ltac:(lia) E9),
          <- (le2_eqm_NC blc r10 10 RB ltac:(lia) E10), <- (le2_eqm_NC blc r11 11 RB ltac:(lia) E11), <- (le2_eqm_NC blc r12 12 RB ltac:(lia) E12),
          <- (le2_eqm_NC blc r13 13 RB ltac:(lia) E13), <- (le2_eqm_NC blc r14 14 RB ltac:(lia) E14), <- (le2_eqm_NC blc r15 15 RB ltac:(lia) E15).
  split.
  - destruct j0 as [|x [|y [|z l]]]; try discriminate. cbn [app] in BY |- *. exact BY.
  - rewrite !length_app, !length_le2, Lj. cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact WR.
Qed.


Definition ncR (L : dlay) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition nc_phase_post (L : dlay) (BC : arr) (ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 w0 m',
    ms' = MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c0e4) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp + 8, bv_unsigned sp + 40)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 (NC BC))).

Ltac eqmk := cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm_go.

Lemma nc_phase : forall (L : dlay) (BC : arr) (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] -> mem_inv psegs m -> dlay_ok L ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  evt psegs (nc_phase_post L BC ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bff8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros BLC FR MI LAY LBC RBC SEP RSP.
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 40)] m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (RBC 0 ltac:(lia)) as R0. pose proof (RBC 1 ltac:(lia)) as R1. pose proof (RBC 2 ltac:(lia)) as R2. pose proof (RBC 3 ltac:(lia)) as R3.
  pose proof (RBC 4 ltac:(lia)) as R4. pose proof (RBC 5 ltac:(lia)) as R5. pose proof (RBC 6 ltac:(lia)) as R6. pose proof (RBC 7 ltac:(lia)) as R7.
  pose proof (RBC 8 ltac:(lia)) as R8. pose proof (RBC 9 ltac:(lia)) as R9. pose proof (RBC 10 ltac:(lia)) as R10. pose proof (RBC 11 ltac:(lia)) as R11.
  pose proof (RBC 12 ltac:(lia)) as R12. pose proof (RBC 13 ltac:(lia)) as R13. pose proof (RBC 14 ltac:(lia)) as R14.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite zseq_16 in BLC. cbn [map c2s] in BLC.
  unfold ncR.
  zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  zs2. zs2. zs2.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep.
  match goal with FRf : rw_cells psegs ?mm (bv_unsigned sp + 8) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (ncl_intro _ _ _ BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRf RBC ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)
                ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)) as [w0 NCA] end.
  apply evt_done. unfold nc_phase_post, ncR. do 8 eexists. exists w0. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact NCA].
Qed.


Definition gcs_post (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3x FC' junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz T) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c158) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ rw_cells psegs m' (bv_unsigned sp + 8) [CB 32 junk']
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma ncl_cb32 : forall m A w0 nc, u8arr psegs m A (u16s (ncl w0 nc)) -> rw_cells psegs m A [CB 32 (u16s (ncl w0 nc))].
Proof. intros m A w0 nc H. apply rw_cells_of_u8arr in H. rewrite u16s_length, ncl_length in H. exact H. Qed.

Lemma gcs_phase : forall (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  -1 <= mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  R = gen_codes (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt psegs (gcs_post s t L T N mc DL HP HL HM DP BC OL SL MC R ra sp gp tp t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 (wz T) (wz mc) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bff8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR BLC FR MI LAY RT1 RT2 RN LFC LDL LBC RBC SEP RSP Rmc RDL ER.
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gen_codes in ER. rewrite bt_bl_count in ER. change (gen_codes_loop1 16 BC (arr_make (MAX_BITS + 1) 0) 0 1) with (NC BC) in ER.
  pose proof (munch_refl (Wgc T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (nc_phase L BC junk).
  1:{ exact BLC. } 1:{ exact FR. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RBC. } 1:{ exact SEP. } 1:{ exact RSP. }
  unfold ncR. zstep. br_cases K.
  -
    replace (mc + 1) with 0 in ER by lia. cbn [Z.to_nat] in ER. rewrite loop2_0 in ER.
    apply evt_done. unfold gcs_post. do 11 eexists. exists FC. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply ncl_cb32; eassumption|]. split; [exact ER| exact LFC].
  - zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (Z.mod_small (mc + 1) 4294967296) by lia.
    destruct (NC_spec BC RBC) as [LNC _].
    lazymatch goal with HN : u8arr psegs ?mm (bv_unsigned sp + 8) (u16s (ncl ?w0 (NC BC))) |- evt _ _ (MS _ _ _ _ _ ?mm' _) =>
      call (gc_loop (Z.to_nat (mc + 1)) s t T N 0 mc w0 FC DL (NC BC) HP HL HM DP BC OL SL MC R mm') end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ exact RSP. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RDL. } 1:{ intros k Hk. apply NC_range; [exact RBC| exact Hk]. }
    1:{ exact ER. }
    unfold gcR. apply evt_done. unfold gcs_post. do 11 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' DL N)) |- _ => exists fc' end. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply ncl_cb32; eassumption|]. split; assumption.
Qed.
