(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.



Definition ubt1R (L : dlay) (T E n mc stp : Z) (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) :=
  mkR ra sp gp tp (wz (ONES - (dl_As L + 3008))) (wz (dl_As L + 5308)) (wz (ONES - (dl_As L + 5308))) s0 s1 (wz stp) (wz E) (wz n) (wz n)
      (wz (dl_As L + 3008)) (wz (T + 4 * n + 2)) (wz (4 * n + 2)) (wz 573) s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11
      (wz 572) (wz mc) x30 x31.

Notation ubt_f16 dsc t L T := ([C8 (wz dsc); C8 (wz 0); C8 (wz (sd_elems t)); C8 (wz (dl_As L + 5912)); C8 (wz (ONES - T)); C8 (wz (dl_As L))])%list (only parsing).

Notation Wbt1 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition ubt1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x30 x31 DL' HP' HL' DP' mc' m',
    ms' = MS (ubt1R L T (sd_elems t) (sd_elems t) mc' stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1X) fc None m' (seg_rom usegs)
    /\ munch (Wbt1 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL' HP' HL' HM DP' BC OL SL MC, mc')
    /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ 0 <= HL' <= sd_elems t /\ -1 <= mc' < sd_elems t.

Lemma ubt_loop1 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N stp dsc : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (DL HP : arr) (HL : Z) (DP : arr) (n mc : Z)
    (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> munch (Wbt1 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> sd_elems t < N -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) ->
  0 <= HL <= n -> 0 <= n -> Z.of_nat (S f) = sd_elems t - n -> -1 <= mc < sd_elems t ->
  R = L1 t (bt_upd s t FC DL HP HL HM DP BC OL SL MC) n mc ->
  evt usegs (ubt1_post L s t T N stp FC BC HM OL SL MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m0)
      (MS (ubt1R L T (sd_elems t) n mc stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC F16 MI LAY MU WM Bsp Rsp AL4 RT1 RT2 REN LFC LDL LHP LDP RFC RHL Rn Ef Rmc ER.
  all: pose proof (RefBuildTree1.elems_range t) as RE.
  all: lay_open LAY.
  all: rewrite RefBuildTree1.L1_step in ER by lia.
  all: pose proof (RFC n ltac:(lia)) as Rf.
  all: pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n) _ (wa (T + 4 * n + 2 + -2)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  all: pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  all: unfold ubt1R, BT_L1; zs2; reg_as (mc + 0) mc; zs2; reg_as (4 * n + 2 + -2) (n * 4); zs2; ustep BT_TRAP; zs2; ustep BT_TRAP.
  all: zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. reg_as (mc + 0) mc. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [|exfalso; lia].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite RefBuildTree1.L1_end in ER.
    apply evt_done. unfold ubt1_post, ubt1R, BT_L1X. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. reg_as (n + 0) n. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [exfalso; lia|].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite RefBuildTree1.L1_end in ER.
    apply evt_done. unfold ubt1_post, ubt1R, BT_L1X. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [eassumption|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. reg_as (mc + 0) mc. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [exfalso; lia|].
    eapply (IH L s t T N stp dsc FC BC HM OL SL MC R m0 (arr_set DL n (wrap16 0)) HP HL DP (n + 1) mc);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| eassumption| exact LAY| exact MU| exact WM| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact REN| exact LFC
      | rewrite arr_len_set; exact LDL| exact LHP| exact LDP| exact RFC| lia| lia| lia| exact Rmc| exact ER].
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. reg_as (n + 0) n. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [|exfalso; lia].
    eapply (IH L s t T N stp dsc FC BC HM OL SL MC R m0 DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) (n + 1) n);
      [exact ARR| exact HPA| exact DPA| eassumption| eassumption| eassumption| exact LAY| exact MU| exact WM| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact REN| exact LFC| exact LDL
      | rewrite arr_len_set; exact LHP| rewrite arr_len_set; exact LDP| exact RFC| lia| lia| lia| lia| exact ER].
Qed.
