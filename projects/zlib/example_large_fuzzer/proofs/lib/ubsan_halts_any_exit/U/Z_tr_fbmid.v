(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees FillWinModel FlushBlockModel TreesTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma mb_search : forall X (f : nat) mb k, mb - 2 <= Z.of_nat f -> 2 <= k <= mb ->
  (forall j, k < j <= mb -> Len X TB (arr_get bl_order_a j) = 0) -> (k = 2 \/ Len X TB (arr_get bl_order_a k) <> 0) ->
  build_bl_tree_loop f X mb = k.
Proof.
  induction f as [|f IH]; intros mb k Hf Hk HZ HK.
  - cbn [build_bl_tree_loop]. lia.
  - cbn [build_bl_tree_loop]. destruct (Z.leb_spec 3 mb) as [C|C]; [|lia].
    destruct (Z.eq_dec k mb) as [->|NE].
    + destruct HK as [->|HK]; [lia|]. rewrite (proj2 (Z.eqb_neq _ _) HK). reflexivity.
    + rewrite (proj2 (Z.eqb_eq _ _) (HZ mb ltac:(lia))). cbn [negb]. apply IH; [lia| lia| intros j Hj; apply HZ; lia| exact HK].
Qed.

Lemma ltu_neg_true : forall p a, 0 <= a -> a + Z.pos p < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 (Zneg p)) = true.
Proof.
  intros p a Ha Hp. unfold bv_ltu. rewrite (Z_to_bv_eqm (Zneg p) (2^64 - Z.pos p)).
  2:{ rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia. f_equal. }
  rewrite !unsigned_lit by lia. apply Z.ltb_lt. lia.
Qed.

Definition tfb_mbs_post (L : dlay) (X : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (tfb_mb X)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c668) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Ltac mb_done mb ACC K :=
  let E := fresh "E" in
  assert (E : tfb_mb _ = mb) by (unfold tfb_mb; apply mb_search; [lia| lia| exact ACC| right; exact K]);
  apply evt_done; unfold tfb_mbs_post, utfR; rewrite E; do 2 eexists; split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl| assumption].

Lemma tfb_mbsearch : forall (L : dlay) (X : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2748) (u16s (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)) -> mem_inv usegs m -> dlay_ok L ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X) i < 65536) ->
  evt usegs (tfb_mbs_post L X sp last len bufp ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c4c4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR MI LAY HDL. pose proof LAY as LAY'. lay_open LAY'. unfold utfR.
  pose proof (avct_zlength (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 ltac:(lia)) as LCT.
  assert (ACC : forall j, 18 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0) by (intros; lia).
  zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). zs2.
  zstep. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; rewrite ltu_neg_true by lia; reflexivity] end.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 15 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 15 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 15 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 15 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 15)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 18 ACC K]; clear RD RV.
  assert (ACC18 : forall j, 18 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 18) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC18 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 1 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 1 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 1 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 1 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 1)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 17 ACC K]; clear RD RV.
  assert (ACC17 : forall j, 17 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 17) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC17 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 14 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 14 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 14 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 14 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 14)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 16 ACC K]; clear RD RV.
  assert (ACC16 : forall j, 16 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 16) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC16 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 2 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 2 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 2 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 2 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 2)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 15 ACC K]; clear RD RV.
  assert (ACC15 : forall j, 15 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC15 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 13 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 13 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 13 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 13 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 13)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 14 ACC K]; clear RD RV.
  assert (ACC14 : forall j, 14 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 14) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC14 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 3 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 3 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 3 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 3 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 3)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 13 ACC K]; clear RD RV.
  assert (ACC13 : forall j, 13 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 13) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC13 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 12 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 12 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 12 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 12 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 12)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 12 ACC K]; clear RD RV.
  assert (ACC12 : forall j, 12 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 12) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC12 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 4 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 4 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 4 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 4 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 4)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 11 ACC K]; clear RD RV.
  assert (ACC11 : forall j, 11 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 11) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC11 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 11 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 11 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 11 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 11 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 11)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 10 ACC K]; clear RD RV.
  assert (ACC10 : forall j, 10 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 10) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC10 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 5 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 5 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 5 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 5 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 5)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 9 ACC K]; clear RD RV.
  assert (ACC9 : forall j, 9 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 9) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC9 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 10 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 10 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 10 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 10 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 10)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 8 ACC K]; clear RD RV.
  assert (ACC8 : forall j, 8 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 8) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC8 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 6 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 6 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 6 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 6 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 6)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 7 ACC K]; clear RD RV.
  assert (ACC7 : forall j, 7 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 7) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC7 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 9 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 9 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 9 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 9 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 9)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 6 ACC K]; clear RD RV.
  assert (ACC6 : forall j, 6 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 6) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC6 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 7 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 7 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 7 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 7 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 7)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 5 ACC K]; clear RD RV.
  assert (ACC5 : forall j, 5 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 5) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC5 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 8 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 8 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 8 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 8 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 8)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 4 ACC K]; clear RD RV.
  assert (ACC4 : forall j, 4 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 4) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC4 into ACC.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 0 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 0 + 1))) ARR (avct_nth_dl _ _ 39 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 0 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 0)) by lia. zs2. zs2.
  destruct (Z.eq_dec (arr_get (ds_bl_tree_dl X) 0) 0) as [K|K].
  - rewrite K. change (Z.lxor (Z.b2z (0 <? 1)) 3) with 2.
    assert (E : tfb_mb X = 2) by (unfold tfb_mb; apply mb_search; [lia| lia| intros j Hj; destruct (Z.eq_dec j 3) as [->|]; [exact K| apply ACC; lia]| left; reflexivity]).
    apply evt_done. unfold tfb_mbs_post, utfR. rewrite E. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| assumption].
  - replace (arr_get (ds_bl_tree_dl X) 0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.lxor (Z.b2z false) 3) with 3.
    mb_done 3 ACC K.
Qed.
